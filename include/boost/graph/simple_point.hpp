//=======================================================================
// Copyright 2005 Trustees of Indiana University
// Authors: Andrew Lumsdaine, Douglas Gregor
//
// Distributed under the Boost Software License, Version 1.0. (See
// accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//=======================================================================
#ifndef BOOST_GRAPH_SIMPLE_POINT_HPP
#define BOOST_GRAPH_SIMPLE_POINT_HPP

#include <boost/container_hash/hash.hpp>

#include <cmath>

namespace boost
{

template < typename T > struct simple_point
{
    T x;
    T y;

    // Euclidean distance between two simple_point<T> using std::hypot
    constexpr friend
    T distance(const simple_point& a, const simple_point& b)
    {
        return std::hypot(a.x - b.x, a.y - b.y);
    }

    constexpr friend
    bool operator==(simple_point const &a, simple_point const &b) noexcept
    {
        return a.x == b.x && a.y == b.y;
    }

    constexpr friend
    bool operator!=(simple_point const &a, simple_point const &b) noexcept
    {
        return !(a == b);
    }

    friend constexpr
    std::size_t hash_value(simple_point const& p)
    {
        std::size_t seed = 0;

        boost::hash_combine(seed, p.x);
        boost::hash_combine(seed, p.y);

        return seed;
    }
};


} // end namespace boost

#endif // BOOST_GRAPH_SIMPLE_POINT_HPP
