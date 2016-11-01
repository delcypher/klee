klee_add_component(kleeSupport
	CompressionStream.cpp
	ErrorHandling.cpp
	MemoryUsage.cpp
	PrintVersion.cpp
	RNG.cpp
	Time.cpp
	Timer.cpp
	TreeStream.cpp
)

target_link_libraries(kleeSupport PRIVATE ${ZLIB_LIBRARIES})
