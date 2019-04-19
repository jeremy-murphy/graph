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

#include <algorithm>
#include <iterator>
#include <cstdlib>

namespace boost
{
  /**
   * @name bit_rotate_block
   * @brief Rotates bits within a block.
   *
   * @tparam N        Block type, must be unsigned integral.
   * @tparam Integer  Any integer type.
   *
   * @param block   Object in which bits will be rotated.
   * @param first   Starting bit of first block.
   * @param middle  Boundary of first and second block.
   * @param last    Last bit plus one of second block.
   */
  template <typename N, typename Integer>
  typename enable_if_c<is_unsigned<N>::value, Integer>::type
  bit_rotate_block(N &block, Integer first, Integer middle, Integer last)
  {
    std::size_t BOOST_CONSTEXPR width = sizeof(N) * CHAR_BIT;

    BOOST_ASSERT(last < width);
    BOOST_ASSERT(middle <= last);
    BOOST_ASSERT(first <= middle);

    if (first == middle) return last;
    if (middle == last) return first;

    N first_mask = (N(1) << first) - N(1),
      middle_mask = (N(1) << middle) - N(1),
      last_mask = (N(1) << last) - N(1),
      new_middle_mask = (N(1) << first + last - middle) - N(1);

    N const k = middle - first;
    N a = (block >> k) & (middle_mask ^ first_mask), // new start
      b = (block << last - middle) & (last_mask ^ new_middle_mask), // rotate old start to the end
      c = block & (first_mask | ~last_mask); // outside
    block = a | b | c;
    return last - k;
  }


  /**
   * @name copy_bits
   *
   * Copy n bits starting from the leading offset of source, to dest.
   *
   */
  template <typename I>
  I copy_bits(I source, int leading_offset, int n, I dest)
  {
    typedef typename std::iterator_traits<I>::value_type T;
    std::size_t BOOST_CONSTEXPR width = sizeof(T) * CHAR_BIT;
    int const m = n + leading_offset; // source number of bits.
    int const trailing_offset = n % width;
    int const source_blocks = m / width + static_cast<bool>(m % width),
              dest_blocks = n / width + static_cast<bool>(trailing_offset);

    T const leading_mask = (T(1) << leading_offset) - T(1);
    T const trailing_mask = (T(1) << trailing_offset) - T(1);

    if (leading_offset != 0)
    {
      T leading_data = *source >> leading_offset;

      if (source_blocks > 1)
      {
        T const trailing_data = (*(source + 1) << width - leading_offset) & ~trailing_mask;
        *dest++ = leading_data | trailing_data;
      }
      else
      {
        T const trailing_data = *dest & ~trailing_mask;
        leading_data &= trailing_mask;
        *dest++ = leading_data | trailing_data;
      }

    }
    else
      dest = std::copy(source, source + source_blocks - 1, dest);

    if (trailing_offset != 0)
    {

    }
    else
      *dest++ = *(source + source_blocks - 1);

    return dest;
  }

  /**
   * @name copy_bits
   *
   * Copy n bits starting from the first bit of source to the leading_offset of
   * dest.
   *
   * @param source          Start of source data.
   * @param n               Number of bits to copy.
   * @param dest            Start of destination.
   * @param leading_offset  Offset from dest to copy to.
   */
  template <typename I>
  I copy_bits(I source, int n, I dest, int leading_offset)
  {
    BOOST_ASSERT(leading_offset >= 0);
    BOOST_ASSERT(n >= 0);

    typedef typename std::iterator_traits<I>::value_type T;
    std::size_t BOOST_CONSTEXPR width = sizeof(T) * CHAR_BIT;

    BOOST_ASSERT(leading_offset < width);

    int const m = n + leading_offset;
    int const trailing_offset = m % width;
    int const source_blocks = n / width + static_cast<bool>(n % width),
              dest_blocks = m / width + static_cast<bool>(trailing_offset);
    T const trailing_mask = (T(1) << trailing_offset) - T(1);

    if (leading_offset != 0)
    {
      T const leading_mask = (T(1) << leading_offset) - T(1);

      if (dest_blocks == 1)
      {
        T const frame = *dest & leading_mask | *dest & ~trailing_mask;
        T const picture = *source << leading_offset;
        *dest++ = frame | picture;
        return dest;
      }

      *dest = *dest & leading_mask | *source << leading_offset;
      dest++;

      for (int i = 0; i != dest_blocks - 2; i++, source++)
      {
        T const a = *source >> width - leading_offset;
        T const b = *(source + 1) << leading_offset;
        *dest++ = a | b;
      }
    }
    else
      dest = std::copy(source, source + source_blocks - 1, dest);

    if (trailing_offset != 0)
    {
      T const thing = *dest & ~trailing_mask;
      *dest++ = thing | *source >> width - trailing_offset;
    }
    else
    {
      *dest++ = *(source + source_blocks - 1);
    }

    return dest;
  }

}

#endif
