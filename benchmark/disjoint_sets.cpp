#include <boost/pending/disjoint_sets.hpp>

#include <benchmark/benchmark.h>
#include <numeric>

using boost::disjoint_sets_with_storage;
using boost::identity_property_map;
using boost::find_with_path_halving;
using boost::find_with_full_path_compression;

namespace {

#include <vector>
#include <numeric>

template <typename DisjointSet>
void BM_constructor(benchmark::State& state) {
    std::vector<std::size_t> elts(state.range(0));
    std::iota(begin(elts), end(elts), 0);

    for (auto _ : state) {
        DisjointSet ds{elts.size()};
        benchmark::DoNotOptimize(ds);
    }
}

template <typename DisjointSet>
void BM_make_set(benchmark::State& state) {
    std::vector<std::size_t> elts(state.range(0));
    std::iota(begin(elts), end(elts), 0);
    DisjointSet ds{elts.size()};

    for (auto _ : state) {
        for (auto x : elts) {
            ds.make_set(x);
        }
        benchmark::DoNotOptimize(ds);
    }

    state.SetComplexityN(state.range(0));
}

template <typename DisjointSet>
void BM_find_set(benchmark::State& state) {
    std::vector<std::size_t> elts(state.range(0));
    std::iota(begin(elts), end(elts), 0);
    DisjointSet ds{elts.size()};
    for (auto x : elts) {
        ds.make_set(x);
    }

    for (auto _ : state) {
        for (decltype(state.range(0)) i = 0; i != state.range(0); i++) {
            benchmark::DoNotOptimize(ds.find_set(i));
        }
    }

    state.SetComplexityN(state.range(0));
}


template <typename DisjointSet>
void BM_union_set(benchmark::State& state)
{
    std::vector<std::size_t> elts(state.range(0));
    std::iota(begin(elts), end(elts), 0);
    DisjointSet ds{elts.size()};
    for (auto x : elts) {
        ds.make_set(x);
    }

    for (auto _ : state)
    {
        for (decltype(state.range(0)) i = 0; i != state.range(0) - 1; i++)
        {
            ds.union_set(i, i + 1);
            benchmark::DoNotOptimize(ds);
        }
    }

    state.SetComplexityN(state.range(0));
}

} // namespace

using ds_path_halving = disjoint_sets_with_storage< identity_property_map,
    identity_property_map, find_with_path_halving >;

using ds_path_compression = disjoint_sets_with_storage< identity_property_map,
    identity_property_map, find_with_full_path_compression>;

// BENCHMARK(BM_constructor<ds_path_halving>)->Range(8U, 1U<<20U);
// BENCHMARK(BM_constructor<ds_path_compression>)->Range(8U, 1U<<20U);
// BENCHMARK(BM_make_set<ds_path_halving>)->Range(8U, 1U<<20U)->Complexity();
// BENCHMARK(BM_make_set<ds_path_compression>)->Range(8U, 1U<<20U)->Complexity();
// BENCHMARK(BM_find_set<ds_path_halving>)->Range(8U, 1U<<20U)->Complexity();
// BENCHMARK(BM_find_set<ds_path_compression>)->Range(8U, 1U<<20U)->Complexity();

BENCHMARK(BM_union_set<ds_path_halving>)->Range(8U, 1U<<20U)->Complexity();
BENCHMARK(BM_union_set<ds_path_compression>)->Range(8U, 1U<<20U)->Complexity();
