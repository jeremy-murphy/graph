message(CHECK_START "Checking for Google Benchmark")
find_package(Benchmark CONFIG)
if(Benchmark_FOUND)
	message(CHECK_PASS "Found ${Benchmark_VERSION}")

	if(CMAKE_BUILD_TYPE STREQUAL "Debug")
		message(WARNING "Benchmarks not useful in Debug mode.")
	endif()

	add_executable(disjoint_sets disjoint_sets.cpp
		DisjointSets.hpp)
	target_link_libraries(disjoint_sets benchmark::benchmark_main boost_graph)
endif()
