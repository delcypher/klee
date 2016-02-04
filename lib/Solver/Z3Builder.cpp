//===-- Z3Builder.cpp ----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "klee/Config/config.h"
#ifdef ENABLE_Z3
#include "Z3Builder.h"

#include "klee/Expr.h"
#include "klee/Solver.h"
#include "klee/util/Bits.h"

#include "ConstantDivision.h"
#include "klee/SolverStats.h"

#include "llvm/Support/CommandLine.h"

#include <cstdio>

#include <algorithm> // max, min
#include <cassert>
#include <map>
#include <sstream>
#include <vector>

using namespace klee;

namespace {
llvm::cl::opt<bool> UseConstructHashZ3(
    "use-construct-hash-z3",
    llvm::cl::desc("Use hash-consing during Z3 query construction."),
    llvm::cl::init(true));
}

void custom_z3_error_handler(Z3_context ctx, Z3_error_code ec) {
  llvm::errs() << "Error: Incorrect use of Z3. [" << ec << "]" <<
               ::Z3_get_error_msg(ctx, ec) << "\n";
  abort();
}

Z3ArrayExprHash::~Z3ArrayExprHash() {}

Z3Builder::Z3Builder() {
  // FIXME: Should probably let the client pass in a Z3_config instead
  Z3_config cfg = Z3_mk_config();
  // It is very important that we ask Z3 to let us manage memory so that
  // we are able to cache expressions and sorts.
  ctx = Z3_mk_context_rc(cfg);
  // Make sure we handle any errors reported Z3.
  Z3_set_error_handler(ctx, custom_z3_error_handler);
  Z3_del_config(cfg);
}

Z3Builder::~Z3Builder() { Z3_del_context(ctx); }

Z3ASTHandle Z3Builder::buildArray(const char *name, unsigned indexWidth,
                             unsigned valueWidth) {
  // XXX don't rebuild if this stuff cons's
  // FIXME: Leak!
  Z3_sort t1 = Z3_mk_bv_sort(ctx, indexWidth);
  Z3_sort t2 = Z3_mk_bv_sort(ctx, valueWidth);
  Z3_sort t = Z3_mk_array_sort(ctx, t1, t2);
  Z3_symbol s = Z3_mk_string_symbol(ctx, const_cast<char *>(name));
  return Z3ASTHandle(Z3_mk_const(ctx, s, t), ctx);
}

// FIXME: The return type here look wrong!
/**
 * Make 1-bit bitvector whose only element is 1.
 */
Z3ASTHandle Z3Builder::getTrue() { return Z3ASTHandle(Z3_mk_true(ctx), ctx); }

// FIXME: The return type here look wrong!
/**
 * Make 1-bit bitvector whose only element is 0.
 */
Z3ASTHandle Z3Builder::getFalse() { return Z3ASTHandle(Z3_mk_false(ctx), ctx); }

Z3ASTHandle Z3Builder::bvOne(unsigned width) { return bvZExtConst(width, 1); }

Z3ASTHandle Z3Builder::bvZero(unsigned width) { return bvZExtConst(width, 0); }

Z3ASTHandle Z3Builder::bvMinusOne(unsigned width) {
  return bvSExtConst(width, (int64_t)-1);
}

Z3ASTHandle Z3Builder::bvConst32(unsigned width, uint32_t value) {
  // FIXME: sort Leak
  Z3_sort t = Z3_mk_bv_sort(ctx, width);
  return Z3ASTHandle(Z3_mk_unsigned_int(ctx, value, t), ctx);
}

Z3ASTHandle Z3Builder::bvConst64(unsigned width, uint64_t value) {
  // FIXME: sort Leak
  Z3_sort t = Z3_mk_bv_sort(ctx, width);
  return Z3ASTHandle(Z3_mk_unsigned_int64(ctx, value, t), ctx);
}

Z3ASTHandle Z3Builder::bvZExtConst(unsigned width, uint64_t value) {
  if (width <= 64)
    return bvConst64(width, value);

  Z3ASTHandle expr = Z3ASTHandle(bvConst64(64, value), ctx);
  Z3ASTHandle zero = Z3ASTHandle(bvConst64(64, 0), ctx);
  for (width -= 64; width > 64; width -= 64)
    expr = Z3ASTHandle(Z3_mk_concat(ctx, zero, expr), ctx);
  return Z3ASTHandle(Z3_mk_concat(ctx, bvConst64(width, 0), expr), ctx);
}

Z3ASTHandle Z3Builder::bvSExtConst(unsigned width, uint64_t value) {
  if (width <= 64)
    return bvConst64(width, value);

  // FIXME: sort leak
  Z3_sort t = Z3_mk_bv_sort(ctx, width - 64);
  if (value >> 63) {
    Z3ASTHandle r = Z3ASTHandle(Z3_mk_int64(ctx, -1, t), ctx);
    return Z3ASTHandle(Z3_mk_concat(ctx, r, bvConst64(64, value)), ctx);
  }

  Z3ASTHandle r = Z3ASTHandle(Z3_mk_int64(ctx, 0, t), ctx);
  return Z3ASTHandle(Z3_mk_concat(ctx, r, bvConst64(64, value)), ctx);
}

Z3ASTHandle Z3Builder::bvBoolExtract(Z3ASTHandle expr, int bit) {
  return Z3ASTHandle(Z3_mk_eq(ctx, bvExtract(expr, bit, bit), bvOne(1)), ctx);
}

Z3ASTHandle Z3Builder::bvExtract(Z3ASTHandle expr, unsigned top, unsigned bottom) {
  return Z3ASTHandle(Z3_mk_extract(ctx, top, bottom, expr), ctx);
}

Z3ASTHandle Z3Builder::eqExpr(Z3ASTHandle a, Z3ASTHandle b) {
  return Z3ASTHandle(Z3_mk_eq(ctx, a, b), ctx);
}

// logical right shift
Z3ASTHandle Z3Builder::bvRightShift(Z3ASTHandle expr, unsigned shift) {
  unsigned width = getBVLength(expr);

  if (shift == 0) {
    return expr;
  } else if (shift >= width) {
    return bvZero(width); // Overshift to zero
  } else {
    return Z3ASTHandle(Z3_mk_concat(ctx, bvZero(shift), bvExtract(expr, width - 1, shift)), ctx);
  }
}

// logical left shift
Z3ASTHandle Z3Builder::bvLeftShift(Z3ASTHandle expr, unsigned shift) {
  unsigned width = getBVLength(expr);

  if (shift == 0) {
    return expr;
  } else if (shift >= width) {
    return bvZero(width); // Overshift to zero
  } else {
    return Z3ASTHandle(Z3_mk_concat(ctx, bvExtract(expr, width - shift - 1, 0),
                                    bvZero(shift)),
                       ctx);
  }
}

// left shift by a variable amount on an expression of the specified width
Z3ASTHandle Z3Builder::bvVarLeftShift(Z3ASTHandle expr, Z3ASTHandle shift) {
  unsigned width = getBVLength(expr);
  Z3ASTHandle res = bvZero(width);

  // construct a big if-then-elif-elif-... with one case per possible shift
  // amount
  for (int i = width - 1; i >= 0; i--) {
    res =
        iteExpr(eqExpr(shift, bvConst32(width, i)), bvLeftShift(expr, i), res);
  }

  // If overshifting, shift to zero
  Z3ASTHandle ex = bvLtExpr(shift, bvConst32(getBVLength(shift), width));
  res = iteExpr(ex, res, bvZero(width));
  return res;
}

// logical right shift by a variable amount on an expression of the specified
// width
Z3ASTHandle Z3Builder::bvVarRightShift(Z3ASTHandle expr, Z3ASTHandle shift) {
  unsigned width = getBVLength(expr);
  Z3ASTHandle res = bvZero(width);

  // construct a big if-then-elif-elif-... with one case per possible shift
  // amount
  for (int i = width - 1; i >= 0; i--) {
    res =
        iteExpr(eqExpr(shift, bvConst32(width, i)), bvRightShift(expr, i), res);
  }

  // If overshifting, shift to zero
  Z3ASTHandle ex = bvLtExpr(shift, bvConst32(getBVLength(shift), width));
  res = iteExpr(ex, res, bvZero(width));
  return res;
}

// arithmetic right shift by a variable amount on an expression of the specified
// width
Z3ASTHandle Z3Builder::bvVarArithRightShift(Z3ASTHandle expr, Z3ASTHandle shift) {
  unsigned width = getBVLength(expr);

  // get the sign bit to fill with
  Z3ASTHandle signedBool = bvBoolExtract(expr, width - 1);

  // start with the result if shifting by width-1
  Z3ASTHandle res = constructAShrByConstant(expr, width - 1, signedBool);

  // construct a big if-then-elif-elif-... with one case per possible shift
  // amount
  // XXX more efficient to move the ite on the sign outside all exprs?
  // XXX more efficient to sign extend, right shift, then extract lower bits?
  for (int i = width - 2; i >= 0; i--) {
    res = iteExpr(eqExpr(shift, bvConst32(width, i)),
                  constructAShrByConstant(expr, i, signedBool), res);
  }

  // If overshifting, shift to zero
  Z3ASTHandle ex = bvLtExpr(shift, bvConst32(getBVLength(shift), width));
  res = iteExpr(ex, res, bvZero(width));
  return res;
}

Z3ASTHandle Z3Builder::bvMinusExpr(unsigned width, Z3ASTHandle minuend,
                              Z3ASTHandle subtrahend) {
  Z3ASTHandle plainExpr = Z3ASTHandle(Z3_mk_bvsub(ctx, minuend, subtrahend), ctx);
  if (getBVLength(plainExpr) == width)
    return plainExpr;

  // FIXME: Do we ever hit this?
  assert(0);
  //return Z3ASTHandle(Z3_mk_extract(ctx, width - 1, 0, plainExpr), ctx);
}

Z3ASTHandle Z3Builder::bvPlusExpr(unsigned width, Z3ASTHandle augend, Z3ASTHandle addend) {
  Z3ASTHandle plainExpr = Z3ASTHandle(Z3_mk_bvadd(ctx, augend, addend), ctx);
  if (getBVLength(plainExpr) == width)
    return plainExpr;

  // FIXME: Do we ever hit this?
  assert(0);
  //return Z3ASTHandle(Z3_mk_extract(ctx, width - 1, 0, plainExpr), ctx);
}

Z3ASTHandle Z3Builder::bvMultExpr(unsigned width, Z3ASTHandle multiplacand,
                             Z3ASTHandle multiplier) {
  Z3ASTHandle plainExpr = Z3ASTHandle(Z3_mk_bvmul(ctx, multiplacand, multiplier), ctx);
  if (getBVLength(plainExpr) == width)
    return plainExpr;

  // FIXME: Do we ever hit this?
  assert(0);
  //return Z3ASTHandle(Z3_mk_extract(ctx, width - 1, 0, plainExpr), ctx);
}

Z3ASTHandle Z3Builder::bvDivExpr(unsigned width, Z3ASTHandle dividend, Z3ASTHandle divisor) {
  Z3ASTHandle plainExpr = Z3ASTHandle(Z3_mk_bvudiv(ctx, dividend, divisor), ctx);
  if (getBVLength(plainExpr) == width)
    return plainExpr;

  // FIXME: Do we ever hit this?
  assert(0);
  //return Z3_mk_extract(ctx, width - 1, 0, plainExpr);
}

Z3ASTHandle Z3Builder::sbvDivExpr(unsigned width, Z3ASTHandle dividend, Z3ASTHandle divisor) {
  Z3ASTHandle plainExpr = Z3ASTHandle(Z3_mk_bvsdiv(ctx, dividend, divisor), ctx);
  if (getBVLength(plainExpr) == width)
    return plainExpr;

  // FIXME: Do we ever hit this?
  assert(0);
  //return Z3_mk_extract(ctx, width - 1, 0, plainExpr);
}

Z3ASTHandle Z3Builder::bvModExpr(unsigned width, Z3ASTHandle dividend, Z3ASTHandle divisor) {
  // FIXME: is this the right call?
  Z3ASTHandle plainExpr = Z3ASTHandle(Z3_mk_bvurem(ctx, dividend, divisor), ctx);
  if (getBVLength(plainExpr) == width)
    return plainExpr;

  // FIXME: Do we ever hit this?
  assert(0);
  //return Z3_mk_extract(ctx, width - 1, 0, plainExpr);
}

Z3ASTHandle Z3Builder::sbvModExpr(unsigned width, Z3ASTHandle dividend, Z3ASTHandle divisor) {
  // FIXME: An alternative is to use Z3_mk_bvsmod, need to check which one is
  // good
  Z3ASTHandle plainExpr = Z3ASTHandle(Z3_mk_bvsrem(ctx, dividend, divisor), ctx);
  if (getBVLength(plainExpr) == width)
    return plainExpr;

  // FIXME: Do we ever hit this?
  assert(0);
  //return Z3_mk_extract(ctx, width - 1, 0, plainExpr);
}

Z3ASTHandle Z3Builder::notExpr(Z3ASTHandle expr) {
  return Z3ASTHandle(Z3_mk_not(ctx, expr), ctx);
}

Z3ASTHandle Z3Builder::bvNotExpr(Z3ASTHandle expr) {
  return Z3ASTHandle(Z3_mk_bvnot(ctx, expr), ctx);
}

Z3ASTHandle Z3Builder::andExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  ::Z3_ast args[2] = {lhs, rhs};
  return Z3ASTHandle(Z3_mk_and(ctx, 2, args), ctx);
}

Z3ASTHandle Z3Builder::bvAndExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_bvand(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::orExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  ::Z3_ast args[2] = {lhs, rhs};
  return Z3ASTHandle(Z3_mk_or(ctx, 2, args), ctx);
}

Z3ASTHandle Z3Builder::bvOrExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_bvor(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::iffExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  // FIXME: Do we always need to do this with bitvectors rather than
  // Z3_mk_iff() ?
  // a <== > ===  (not a) xor b
  Z3ASTHandle xorExpr = Z3ASTHandle(Z3_mk_bvxor(ctx,
                                                Z3ASTHandle(Z3_mk_bvnot(ctx, lhs), ctx),
                                                rhs),
                                    ctx);
  return Z3ASTHandle(Z3_mk_extract(ctx, 0, 0, xorExpr), ctx);
}

Z3ASTHandle Z3Builder::bvXorExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_bvxor(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::bvSignExtend(Z3ASTHandle src, unsigned width) {
  // FIXME: Sort leak?
  unsigned src_width = Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, src));
  assert(src_width <= width && "attempted to extend longer data");

  return Z3ASTHandle(Z3_mk_sign_ext(ctx, width - src_width, src), ctx);
}

Z3ASTHandle Z3Builder::writeExpr(Z3ASTHandle array, Z3ASTHandle index, Z3ASTHandle value) {
  return Z3ASTHandle(Z3_mk_store(ctx, array, index, value), ctx);
}

Z3ASTHandle Z3Builder::readExpr(Z3ASTHandle array, Z3ASTHandle index) {
  return Z3ASTHandle(Z3_mk_select(ctx, array, index), ctx);
}

Z3ASTHandle Z3Builder::iteExpr(Z3ASTHandle condition, Z3ASTHandle whenTrue, Z3ASTHandle whenFalse) {
  return Z3ASTHandle(Z3_mk_ite(ctx, condition, whenTrue, whenFalse), ctx);
}

unsigned Z3Builder::getBVLength(Z3ASTHandle expr) {
  // FIXME: Sort leak?
  return Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, expr));
}

Z3ASTHandle Z3Builder::bvLtExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_bvult(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::bvLeExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_bvule(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::sbvLtExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_bvslt(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::sbvLeExpr(Z3ASTHandle lhs, Z3ASTHandle rhs) {
  return Z3ASTHandle(Z3_mk_bvsle(ctx, lhs, rhs), ctx);
}

Z3ASTHandle Z3Builder::constructAShrByConstant(Z3ASTHandle expr, unsigned shift,
                                          Z3ASTHandle isSigned) {
  unsigned width = getBVLength(expr);

  if (shift == 0) {
    return expr;
  } else if (shift >= width) {
    return bvZero(width); // Overshift to zero
  } else {
    // FIXME: Is this really the best way to interact with Z3?
    return iteExpr(isSigned,
                   Z3ASTHandle(Z3_mk_concat(ctx,
                                            bvMinusOne(shift),
                                            bvExtract(expr, width - 1, shift)),
                               ctx),
                   bvRightShift(expr, shift));
  }
}

Z3ASTHandle Z3Builder::getInitialArray(const Array *root) {

  assert(root);
  Z3ASTHandle array_expr;
  bool hashed = _arr_hash.lookupArrayExpr(root, array_expr);

  if (!hashed) {
    // STP uniques arrays by name, so we make sure the name is unique by
    // including the address.
    char buf[32];
    unsigned const addrlen =
        sprintf(buf, "_%p", (const void *)root) + 1; // +1 for null-termination
    unsigned const space = (root->name.length() > 32 - addrlen)
                               ? (32 - addrlen)
                               : root->name.length();
    memmove(buf + space, buf, addrlen); // moving the address part to the end
    memcpy(buf, root->name.c_str(), space); // filling out the name part

    array_expr = buildArray(buf, root->getDomain(), root->getRange());

    if (root->isConstantArray()) {
      // FIXME: Flush the concrete values into STP. Ideally we would do this
      // using assertions, which is much faster, but we need to fix the caching
      // to work correctly in that case.
      for (unsigned i = 0, e = root->size; i != e; ++i) {
        Z3ASTHandle prev = array_expr;
        array_expr = writeExpr(
            prev, construct(ConstantExpr::alloc(i, root->getDomain()), 0),
            construct(root->constantValues[i], 0));
      }
    }

    _arr_hash.hashArrayExpr(root, array_expr);
  }

  return (array_expr);
}

Z3ASTHandle Z3Builder::getInitialRead(const Array *root, unsigned index) {
  return readExpr(getInitialArray(root), bvConst32(32, index));
}

Z3ASTHandle Z3Builder::getArrayForUpdate(const Array *root, const UpdateNode *un) {
  if (!un) {
    return (getInitialArray(root));
  } else {
    // FIXME: This really needs to be non-recursive.
    Z3ASTHandle un_expr;
    bool hashed = _arr_hash.lookupUpdateNodeExpr(un, un_expr);

    if (!hashed) {
      un_expr = writeExpr(getArrayForUpdate(root, un->next),
                          construct(un->index, 0), construct(un->value, 0));

      _arr_hash.hashUpdateNodeExpr(un, un_expr);
    }

    return (un_expr);
  }
}

/** if *width_out!=1 then result is a bitvector,
    otherwise it is a bool */
Z3ASTHandle Z3Builder::construct(ref<Expr> e, int *width_out) {
  if (!UseConstructHashZ3 || isa<ConstantExpr>(e)) {
    return constructActual(e, width_out);
  } else {
    ExprHashMap<std::pair<Z3ASTHandle, unsigned> >::iterator it =
        constructed.find(e);
    if (it != constructed.end()) {
      if (width_out)
        *width_out = it->second.second;
      return it->second.first;
    } else {
      int width;
      if (!width_out)
        width_out = &width;
      Z3ASTHandle res = constructActual(e, width_out);
      constructed.insert(std::make_pair(e, std::make_pair(res, *width_out)));
      return res;
    }
  }
}

/** if *width_out!=1 then result is a bitvector,
    otherwise it is a bool */
Z3ASTHandle Z3Builder::constructActual(ref<Expr> e, int *width_out) {
  int width;
  if (!width_out)
    width_out = &width;

  ++stats::queryConstructs;

  switch (e->getKind()) {
  case Expr::Constant: {
    ConstantExpr *CE = cast<ConstantExpr>(e);
    *width_out = CE->getWidth();

    // Coerce to bool if necessary.
    if (*width_out == 1)
      return CE->isTrue() ? getTrue() : getFalse();

    // Fast path.
    if (*width_out <= 32)
      return bvConst32(*width_out, CE->getZExtValue(32));
    if (*width_out <= 64)
      return bvConst64(*width_out, CE->getZExtValue());

    ref<ConstantExpr> Tmp = CE;
    Z3ASTHandle Res = bvConst64(64, Tmp->Extract(0, 64)->getZExtValue());
    while (Tmp->getWidth() > 64) {
      Tmp = Tmp->Extract(64, Tmp->getWidth() - 64);
      unsigned Width = std::min(64U, Tmp->getWidth());
      Res = Z3ASTHandle(Z3_mk_concat(ctx,
                                     bvConst64(Width, Tmp->Extract(0, Width)->getZExtValue()),
                                     Res),
                        ctx);
    }
    return Res;
  }

  // Special
  case Expr::NotOptimized: {
    NotOptimizedExpr *noe = cast<NotOptimizedExpr>(e);
    return construct(noe->src, width_out);
  }

  case Expr::Read: {
    ReadExpr *re = cast<ReadExpr>(e);
    assert(re && re->updates.root);
    *width_out = re->updates.root->getRange();
    return readExpr(getArrayForUpdate(re->updates.root, re->updates.head),
                    construct(re->index, 0));
  }

  case Expr::Select: {
    SelectExpr *se = cast<SelectExpr>(e);
    Z3ASTHandle cond = construct(se->cond, 0);
    Z3ASTHandle tExpr = construct(se->trueExpr, width_out);
    Z3ASTHandle fExpr = construct(se->falseExpr, width_out);
    return iteExpr(cond, tExpr, fExpr);
  }

  case Expr::Concat: {
    ConcatExpr *ce = cast<ConcatExpr>(e);
    unsigned numKids = ce->getNumKids();
    Z3ASTHandle res = construct(ce->getKid(numKids - 1), 0);
    for (int i = numKids - 2; i >= 0; i--) {
      res = Z3ASTHandle(Z3_mk_concat(ctx, construct(ce->getKid(i), 0), res), ctx);
    }
    *width_out = ce->getWidth();
    return res;
  }

  case Expr::Extract: {
    ExtractExpr *ee = cast<ExtractExpr>(e);
    Z3ASTHandle src = construct(ee->expr, width_out);
    *width_out = ee->getWidth();
    if (*width_out == 1) {
      return bvBoolExtract(src, ee->offset);
    } else {
      return bvExtract(src, ee->offset + *width_out - 1, ee->offset);
    }
  }

  // Casting

  case Expr::ZExt: {
    int srcWidth;
    CastExpr *ce = cast<CastExpr>(e);
    Z3ASTHandle src = construct(ce->src, &srcWidth);
    *width_out = ce->getWidth();
    if (srcWidth == 1) {
      return iteExpr(src, bvOne(*width_out), bvZero(*width_out));
    } else {
      return Z3ASTHandle(Z3_mk_concat(ctx, bvZero(*width_out - srcWidth), src), ctx);
    }
  }

  case Expr::SExt: {
    int srcWidth;
    CastExpr *ce = cast<CastExpr>(e);
    Z3ASTHandle src = construct(ce->src, &srcWidth);
    *width_out = ce->getWidth();
    if (srcWidth == 1) {
      return iteExpr(src, bvMinusOne(*width_out), bvZero(*width_out));
    } else {
      return bvSignExtend(src, *width_out);
    }
  }

  // Arithmetic

  case Expr::Add: {
    AddExpr *ae = cast<AddExpr>(e);
    Z3ASTHandle left = construct(ae->left, width_out);
    Z3ASTHandle right = construct(ae->right, width_out);
    assert(*width_out != 1 && "uncanonicalized add");
    return bvPlusExpr(*width_out, left, right);
  }

  case Expr::Sub: {
    SubExpr *se = cast<SubExpr>(e);
    Z3ASTHandle left = construct(se->left, width_out);
    Z3ASTHandle right = construct(se->right, width_out);
    assert(*width_out != 1 && "uncanonicalized sub");
    return bvMinusExpr(*width_out, left, right);
  }

  case Expr::Mul: {
    MulExpr *me = cast<MulExpr>(e);
    assert(*width_out != 1 && "uncanonicalized mul");
    Z3ASTHandle right = construct(me->right, width_out);
    Z3ASTHandle left = construct(me->left, width_out);
    return bvMultExpr(*width_out, left, right);
  }

  case Expr::UDiv: {
    UDivExpr *de = cast<UDivExpr>(e);
    Z3ASTHandle left = construct(de->left, width_out);
    assert(*width_out != 1 && "uncanonicalized udiv");

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(de->right)) {
      if (CE->getWidth() <= 64) {
        uint64_t divisor = CE->getZExtValue();
        if (bits64::isPowerOfTwo(divisor))
          return bvRightShift(left, bits64::indexOfSingleBit(divisor));
      }
    }

    Z3ASTHandle right = construct(de->right, width_out);
    return bvDivExpr(*width_out, left, right);
  }

  case Expr::SDiv: {
    SDivExpr *de = cast<SDivExpr>(e);
    Z3ASTHandle left = construct(de->left, width_out);
    assert(*width_out != 1 && "uncanonicalized sdiv");
    Z3ASTHandle right = construct(de->right, width_out);
    return sbvDivExpr(*width_out, left, right);
  }

  case Expr::URem: {
    URemExpr *de = cast<URemExpr>(e);
    Z3ASTHandle left = construct(de->left, width_out);
    assert(*width_out != 1 && "uncanonicalized urem");

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(de->right)) {
      if (CE->getWidth() <= 64) {
        uint64_t divisor = CE->getZExtValue();

        if (bits64::isPowerOfTwo(divisor)) {
          unsigned bits = bits64::indexOfSingleBit(divisor);

          // special case for modding by 1 or else we bvExtract -1:0
          if (bits == 0) {
            return bvZero(*width_out);
          } else {
            return Z3ASTHandle(Z3_mk_concat(ctx,
                                            bvZero(*width_out - bits),
                                            bvExtract(left, bits - 1, 0)),
                               ctx);
          }
        }
      }
    }

    Z3ASTHandle right = construct(de->right, width_out);
    return bvModExpr(*width_out, left, right);
  }

  case Expr::SRem: {
    SRemExpr *de = cast<SRemExpr>(e);
    Z3ASTHandle left = construct(de->left, width_out);
    Z3ASTHandle right = construct(de->right, width_out);
    assert(*width_out != 1 && "uncanonicalized srem");
    return sbvModExpr(*width_out, left, right);
  }

  // Bitwise

  case Expr::Not: {
    NotExpr *ne = cast<NotExpr>(e);
    Z3ASTHandle expr = construct(ne->expr, width_out);
    if (*width_out == 1) {
      return notExpr(expr);
    } else {
      return bvNotExpr(expr);
    }
  }

  case Expr::And: {
    AndExpr *ae = cast<AndExpr>(e);
    Z3ASTHandle left = construct(ae->left, width_out);
    Z3ASTHandle right = construct(ae->right, width_out);
    if (*width_out == 1) {
      return andExpr(left, right);
    } else {
      return bvAndExpr(left, right);
    }
  }

  case Expr::Or: {
    OrExpr *oe = cast<OrExpr>(e);
    Z3ASTHandle left = construct(oe->left, width_out);
    Z3ASTHandle right = construct(oe->right, width_out);
    if (*width_out == 1) {
      return orExpr(left, right);
    } else {
      return bvOrExpr(left, right);
    }
  }

  case Expr::Xor: {
    XorExpr *xe = cast<XorExpr>(e);
    Z3ASTHandle left = construct(xe->left, width_out);
    Z3ASTHandle right = construct(xe->right, width_out);

    if (*width_out == 1) {
      // XXX check for most efficient?
      return iteExpr(left, Z3ASTHandle(notExpr(right)), right);
    } else {
      return bvXorExpr(left, right);
    }
  }

  case Expr::Shl: {
    ShlExpr *se = cast<ShlExpr>(e);
    Z3ASTHandle left = construct(se->left, width_out);
    assert(*width_out != 1 && "uncanonicalized shl");

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(se->right)) {
      return bvLeftShift(left, (unsigned)CE->getLimitedValue());
    } else {
      int shiftWidth;
      Z3ASTHandle amount = construct(se->right, &shiftWidth);
      return bvVarLeftShift(left, amount);
    }
  }

  case Expr::LShr: {
    LShrExpr *lse = cast<LShrExpr>(e);
    Z3ASTHandle left = construct(lse->left, width_out);
    assert(*width_out != 1 && "uncanonicalized lshr");

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(lse->right)) {
      return bvRightShift(left, (unsigned)CE->getLimitedValue());
    } else {
      int shiftWidth;
      Z3ASTHandle amount = construct(lse->right, &shiftWidth);
      return bvVarRightShift(left, amount);
    }
  }

  case Expr::AShr: {
    AShrExpr *ase = cast<AShrExpr>(e);
    Z3ASTHandle left = construct(ase->left, width_out);
    assert(*width_out != 1 && "uncanonicalized ashr");

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(ase->right)) {
      unsigned shift = (unsigned)CE->getLimitedValue();
      Z3ASTHandle signedBool = bvBoolExtract(left, *width_out - 1);
      return constructAShrByConstant(left, shift, signedBool);
    } else {
      int shiftWidth;
      Z3ASTHandle amount = construct(ase->right, &shiftWidth);
      return bvVarArithRightShift(left, amount);
    }
  }

  // Comparison

  case Expr::Eq: {
    EqExpr *ee = cast<EqExpr>(e);
    Z3ASTHandle left = construct(ee->left, width_out);
    Z3ASTHandle right = construct(ee->right, width_out);
    if (*width_out == 1) {
      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(ee->left)) {
        if (CE->isTrue())
          return right;
        return notExpr(right);
      } else {
        return iffExpr(left, right);
      }
    } else {
      *width_out = 1;
      return eqExpr(left, right);
    }
  }

  case Expr::Ult: {
    UltExpr *ue = cast<UltExpr>(e);
    Z3ASTHandle left = construct(ue->left, width_out);
    Z3ASTHandle right = construct(ue->right, width_out);
    assert(*width_out != 1 && "uncanonicalized ult");
    *width_out = 1;
    return bvLtExpr(left, right);
  }

  case Expr::Ule: {
    UleExpr *ue = cast<UleExpr>(e);
    Z3ASTHandle left = construct(ue->left, width_out);
    Z3ASTHandle right = construct(ue->right, width_out);
    assert(*width_out != 1 && "uncanonicalized ule");
    *width_out = 1;
    return bvLeExpr(left, right);
  }

  case Expr::Slt: {
    SltExpr *se = cast<SltExpr>(e);
    Z3ASTHandle left = construct(se->left, width_out);
    Z3ASTHandle right = construct(se->right, width_out);
    assert(*width_out != 1 && "uncanonicalized slt");
    *width_out = 1;
    return sbvLtExpr(left, right);
  }

  case Expr::Sle: {
    SleExpr *se = cast<SleExpr>(e);
    Z3ASTHandle left = construct(se->left, width_out);
    Z3ASTHandle right = construct(se->right, width_out);
    assert(*width_out != 1 && "uncanonicalized sle");
    *width_out = 1;
    return sbvLeExpr(left, right);
  }

// unused due to canonicalization
#if 0
  case Expr::Ne:
  case Expr::Ugt:
  case Expr::Uge:
  case Expr::Sgt:
  case Expr::Sge:
#endif

  default:
    assert(0 && "unhandled Expr type");
    return getTrue();
  }
}
#endif // ENABLE_Z3
