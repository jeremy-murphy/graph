//=======================================================================
// Copyright 2018 Jeremy William Murphy
//
// Distributed under the Boost Software License, Version 1.0. (See
// accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//=======================================================================

#ifndef BOOST_GRAPH_DETAIL_BIT_ROTATE_HPP
#define BOOST_GRAPH_DETAIL_BIT_ROTATE_HPP

#include <boost/core/enable_if.hpp>

#include <boost/type_traits/is_unsigned.hpp>

#include <cstdlib>

namespace boost
{
  template <typename N, typename Integer>
  typename enable_if_c<is_unsigned<N>::value, void>::type
  bit_rotate_block(N &block, Integer first, Integer middle, Integer last)
  {
    std::size_t BOOST_CONSTEXPR width = sizeof(N) * CHAR_BIT;

    BOOST_ASSERT(last < width);
    BOOST_ASSERT(middle <= last);
    BOOST_ASSERT(first <= middle);

    if (first == middle || middle == last) return;

    N first_mask = (N(1) << first) - N(1),
      second_mask = (N(1) << middle) - N(1),
      third_mask = (N(1) << last) - N(1),
      other_mask = (N(1) << first + last - middle) - N(1);

    N a = (block >> middle - first) & (second_mask ^ first_mask), // new start
      b = (block << last - middle) & (third_mask ^ other_mask), // rotate old start to the end
      c = block & (first_mask | ~third_mask); // outside
    block = a | b | c;
    return;
  }


  template <typename IntegralIterator, typename Integer>
  void bit_rotate(IntegralIterator start,
                  Integer first, Integer middle, Integer last)
  {
    typedef typename std::iterator_traits<IntegralIterator>::value_type T;

    std::size_t BOOST_CONSTEXPR width = sizeof(T) * CHAR_BIT;

    BOOST_CONCEPT_ASSERT((Mutable_RandomAccessIterator<IntegralIterator>));
    BOOST_ASSERT(first < width);
    BOOST_ASSERT(first <= middle);
    BOOST_ASSERT(middle <= last);
    if (first == middle) return;
    if (middle == last) return;

    Integer const n = middle - first;
    // 'first' is its own offset.
    Integer middle_offset = middle % width;

    IntegralIterator start2 = start + middle / width,
    start3 = start + last / width;

    Integer diff = middle % width - first;

    T tmp = *start;

    T first_mask = (T(1) << first) - T(1),
    second_mask = (T(1) << middle_offset) - T(1),
    third_mask = (T(1) << width - last % width) - 1 << last % width;

    if (start == start2 && start2 == start3)
    {
      T a = (*start >> diff) & (second_mask ^ first_mask), // new start
      b = (*start << last - middle) & ~(second_mask | third_mask), // rotate old start to the end
      c = *start & (first_mask | third_mask); // outside
      *start = a | b | c;
      return;
    }
    //   0011001100110011001100110000000000000000000001010101010101010101
    //   0011001100110000000000000101010101110011001100000000000101010101

    // TODO: handle first T differently


    if (diff < 0)
    {
      *start = *start2 << -diff | *start & first_mask;
      *start2 = tmp >> diff | *start2 & second_mask;
    }
    else
    {
      *start = *start2 >> diff | *(start2 + 1) << width - diff | *start & first_mask;
      *start2 = tmp >> diff | *start2 & second_mask;
    }


    do
    {
      tmp = *start;
      if (diff < 0)
      {
        *start = *start2 << -diff | *(start2 - 1) >> width + diff;
        *start2 = tmp >> diff | *(start - 1) << width - diff;
      }
      else
      {
        *start = *start2 >> diff | *(start2 - 1) << width - diff;
        *start2 = tmp << -diff | *(start - 1) >> width + diff;
      }
    }
    while (start2 != start3);

  }


}

#endif
