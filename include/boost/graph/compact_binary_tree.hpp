#ifndef BOOST_GRAPH_COMPACT_BINARY_TREE
#define BOOST_GRAPH_COMPACT_BINARY_TREE

#include <boost/config.hpp>

#include <boost/dynamic_bitset.hpp>

#include <boost/graph/graph_traits.hpp>

#include <boost/iterator/counting_iterator.hpp> // compact

#include <boost/static_assert.hpp>

#include <boost/concept_check.hpp>
#include <boost/concept/assert.hpp>

#include <boost/function.hpp>

#include <utility>

namespace boost
{
  template <typename IntegralIterator, typename Integer>
  Integer bit_rotate(IntegralIterator start,
                              Integer first, Integer middle, Integer last)
  {
    typedef typename std::iterator_traits<IntegralIterator>::value_type T;

    std::size_t BOOST_CONSTEXPR width = sizeof(T) * CHAR_BIT;

    BOOST_CONCEPT_ASSERT((Mutable_RandomAccessIterator<IntegralIterator>));
    BOOST_ASSERT(first < width);
    BOOST_ASSERT(first <= middle);
    BOOST_ASSERT(middle <= last);

    if (first == middle) return last;
    if (middle == last) return first;

    Integer const n = middle - first;
    // 'first' is its own offset.
    Integer middle_offset = middle % width;

    IntegralIterator start2 = start + middle / width,
                     start3 = start + last / width;

    T first_mask = (T(1) << first) - T(1),
      second_mask = (T(1) << middle_offset) - T(1);

    // TODO: handle first T differently
    Integer diff = middle % width - first;

    T tmp = *start;

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

  template <typename Vertex = short unsigned>
  class compact_binary_tree
  {
  public:
    BOOST_STATIC_CONSTEXPR short unsigned k = 2;

    // *** Graph interface ***

    typedef Vertex vertex_descriptor;
    typedef std::pair<vertex_descriptor, vertex_descriptor> edge_descriptor;
    typedef disallow_parallel_edge_tag edge_parallel_category;
    typedef std::size_t degree_size_type;
    typedef std::size_t vertices_size_type;
    typedef bidirectional_tag directed_category;
    class traversal_category : public vertex_list_graph_tag {};

  private:
    typedef boost::dynamic_bitset<> storage_type;

  public:
    friend
    bool
    has_left_successor(vertex_descriptor u, compact_binary_tree const &g)
    {
      return g.ltag(u);
    }

    friend
    bool
    has_right_successor(vertex_descriptor u, compact_binary_tree const &g)
    {
      return g.rtag(u);
    }

    /*
     *    BOOST_STATIC_CONSTEXPR
     *    vertex_descriptor max_size()
     *    {
     *      return is_signed<vertex_descriptor>::value ?
     *        std::numeric_limits<vertex_descriptor>::max() :
     *        std::numeric_limits<vertex_descriptor>::max() >> 1 ;
  }
  */

    BOOST_STATIC_CONSTEXPR
    vertex_descriptor null_vertex()
    {
      return vertex_descriptor(-1);
    }

    // *** VertexListGraph interface ***

    typedef counting_iterator<vertex_descriptor> vertex_iterator;
    typedef vertex_descriptor vertex_size_type;

    friend
    vertex_size_type num_vertices(compact_binary_tree const& g)
    {
      return g.nodes.size() / 2;
    }

    friend
    std::pair<vertex_iterator, vertex_iterator>
    vertices(compact_binary_tree const& g)
    {
      return std::make_pair(vertex_iterator(0), vertex_iterator(num_vertices(g)));
    }

    /// *** MutableGraph interface ***

    friend
    vertex_descriptor add_vertex(compact_binary_tree &g)
    {
      g.nodes.resize(g.nodes.size() + 2);
      /*
       *      if (!g.roots.empty())
       *        g.nodes[g.roots.back()].sibling = true;
       *      g.roots.push_back(g.nodes.size());
       */
      return num_vertices(g);
    }

    friend
    std::pair<edge_descriptor, bool>
    add_edge(vertex_descriptor u, vertex_descriptor v, compact_binary_tree &g)
    {
      BOOST_ASSERT(u < num_vertices(g) + 1);
      BOOST_ASSERT(v < num_vertices(g) + 1 || v == u + 1);

      edge_descriptor const new_edge(u, v);

      if (v == u + 1)
      {
        BOOST_ASSERT(!has_left_successor(u, g));
        g.ltag(u, 1);
        return std::make_pair(new_edge, true);
      }

      if (!has_left_successor(u, g))
      {
        // rotate the tree rooted at v to u + 1.

      }

    }

    /*
     *            a
     *           / \
     *          b   c
     *         /   / \
     *        d   e   f
     *
     *  11 10 00 11 00 00
     *0  1  1  0  1  0  *
     */

    friend
    vertex_descriptor rightmost(vertex_descriptor u, compact_binary_tree &g)
    {
      unsigned i = 0;

      bool left = has_left_successor(u, g);
      bool right = has_right_successor(u, g);

      while (right || left || i)
      {
        if (!left)
          i--;
        if (right)
          i++;

        u++;
        left = has_left_successor(u, g);
        right = has_right_successor(u, g);
      }

      return u;
    }

    friend
    void
    remove_edge(edge_descriptor e, compact_binary_tree &g)
    {
      BOOST_ASSERT(e.first >= 0);
      BOOST_ASSERT(e.second >= 0);
      BOOST_ASSERT(e.first < num_vertices(g));
      BOOST_ASSERT(e.second < num_vertices(g));
      BOOST_ASSERT(e.first != e.second);
      BOOST_ASSERT(has_left_successor(e.first, g)
      || has_right_successor(e.first, g));

      if (has_left_successor(e.first, g))
      {
        if (left_successor(e.first, g) == e.second)
        {
          g.nodes[e.first].child = false;
          return;
        }
      }

      // TODO: else?
    }

  private:
    bool ltag(vertex_descriptor u) const
    {
      return nodes[2 * u];
    }

    bool rtag(vertex_descriptor u) const
    {
      return nodes[2 * u + 1];
    }

    bool ltag(vertex_descriptor u, bool value)
    {
      return nodes[2 * u] = value;
    }

    bool rtag(vertex_descriptor u, bool value)
    {
      return nodes[2 * u + 1] = value;
    }

    storage_type nodes;
    // std::vector<vertex_descriptor> roots;
  };

}

#endif
