//=======================================================================
// Copyright 2018 Jeremy William Murphy
//
// Distributed under the Boost Software License, Version 1.0. (See
// accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//=======================================================================

#ifndef BOOST_GRAPH_K_ARY_TREE
#define BOOST_GRAPH_K_ARY_TREE

#include <boost/config.hpp>

#include <boost/graph/graph_traits.hpp>
#include <boost/graph/graph_mutability_traits.hpp>
#include <boost/graph/graph_selectors.hpp>
#include <boost/property_map/property_map.hpp>
#include <boost/graph/detail/indexed_properties.hpp>

#include <boost/iterator/iterator_facade.hpp>
#include <boost/iterator/transform_iterator.hpp>

#include <boost/type_traits/conditional.hpp>

#include <boost/iterator/counting_iterator.hpp> // compact

#include <utility>

namespace boost
{
  namespace order {
    enum visit { pre, in, post };
  }
}

#include <boost/graph/detail/k-ary_tree.hpp>

namespace boost
{
  template <typename Graph>
  bool empty(typename graph_traits<Graph>::vertex_descriptor u, Graph const&)
  {
    return u == graph_traits<Graph>::null_vertex();
  }

  template <std::size_t K, bool Predecessor, typename Vertex = std::size_t>
  class k_ary_tree;

  // Directed (forward) tree
  template <std::size_t K, typename Vertex>
  class k_ary_tree<K, false, Vertex>
    : public detail::k_ary_tree_base<K, Vertex,
              detail::k_ary_tree_forward_node<k_ary_tree<K, false, Vertex> > >
  {
    typedef detail::k_ary_tree_base<K, Vertex,
      detail::k_ary_tree_forward_node<k_ary_tree<K, false, Vertex> > > super_t;

  public:
    typedef directed_tag directed_category;
    class traversal_category : public incidence_graph_tag,
                               public vertex_list_graph_tag {};
    typedef typename super_t::edge_descriptor edge_descriptor;
    typedef typename super_t::vertex_descriptor vertex_descriptor;

    // *** VertexListGraph interface ***

    struct vertex_iterator : public iterator_facade<
                                                  vertex_iterator,
                                                  vertex_descriptor const,
                                                  multi_pass_input_iterator_tag
                                                     >
    {
      typedef iterator_facade<vertex_iterator,
                              vertex_descriptor const,
                              forward_traversal_tag> super_t;
    public:
      vertex_iterator(k_ary_tree const& g)
        : g(&g)
      {}

      vertex_iterator(vertex_descriptor start, k_ary_tree const& g)
        : last(g.null_vertex()), g(&g)
      {
        traversal.push(start);
        while (has_left_successor(traversal.top(), g))
          traversal.push(left_successor(traversal.top(), g));
      }

      typedef typename super_t::value_type value_type;
      typedef typename super_t::reference reference;

    private:
      friend class iterator_core_access;

      reference dereference() const
      {
        return traversal.top();
      }

      void increment()
      {
        if (has_right_successor(traversal.top(), *g))
        {
          if (right_successor(traversal.top(), *g) != last)
          {
            traversal.push(right_successor(traversal.top(), *g));
            while (has_left_successor(traversal.top(), *g))
              traversal.push(left_successor(traversal.top(), *g));
            return;
          }

        }

        do
        {
          last = traversal.top();
          traversal.pop();
        }
        while (!traversal.empty()
              && (!has_right_successor(traversal.top(), *g)
                  || right_successor(traversal.top(), *g) == last));
      }

      bool equal(vertex_iterator const &other) const
      {
        if (traversal.empty())
          return other.traversal.empty();

        if (other.traversal.empty())
          return false;

        return traversal.top() == other.traversal.top()
              // && *g == *other.g
              ;
      }

      vertex_descriptor last;
      std::stack<vertex_descriptor> traversal;
      k_ary_tree const *g;
    };

    friend
    std::pair<vertex_iterator, vertex_iterator>
    vertices(k_ary_tree const &g)
    {
      return std::make_pair(vertex_iterator(vertex_descriptor(), g),
                            vertex_iterator(g));
    }



    // *** MutableGraph interface ***

    friend
    std::pair<edge_descriptor, bool>
    add_edge(vertex_descriptor u, vertex_descriptor v, k_ary_tree &g)
    {
      return g.add_edge(u, v);
    }

    friend
    void
    remove_edge(vertex_descriptor u, vertex_descriptor v, k_ary_tree &g)
    {
      g.remove_edge(u, v);
    }

    friend
    void
    remove_edge(edge_descriptor e, k_ary_tree &g)
    {
      remove_edge(e.first, e.second, g);
    }

    friend
    void
    clear_vertex(vertex_descriptor u, k_ary_tree &g)
    {
      g.clear_vertex(u);
    }
  };

  // Bidirectional tree
  template <std::size_t K, typename Vertex>
  class k_ary_tree<K, true, Vertex>
    : public detail::k_ary_tree_base<K, Vertex,
          detail::k_ary_tree_bidirectional_node<k_ary_tree<K, true, Vertex> > >
  {
    typedef detail::k_ary_tree_base<K, Vertex,
    detail::k_ary_tree_bidirectional_node<k_ary_tree<K, true, Vertex> > > super_t;

  public:
    typedef bidirectional_tag directed_category;
    class traversal_category : public bidirectional_graph_tag,
                               public vertex_list_graph_tag {};
    typedef typename super_t::edge_descriptor edge_descriptor;
    typedef typename super_t::vertex_descriptor vertex_descriptor;
    typedef typename super_t::degree_size_type degree_size_type;
    using super_t::k;

  private:
    struct make_in_edge_descriptor
    {
      make_in_edge_descriptor(vertex_descriptor target) : target(target) {}

      edge_descriptor operator()(vertex_descriptor source) const
      {
        return edge_descriptor(source, target);
      }

      vertex_descriptor target;
    };

  public:
    typedef transform_iterator<make_in_edge_descriptor, vertex_descriptor const *,
                                              edge_descriptor> in_edge_iterator;

    // *** VertexListGraph interface ***

    struct vertex_iterator : public iterator_facade<
                                                  vertex_iterator,
                                                  vertex_descriptor const,
                                                  multi_pass_input_iterator_tag
                                                     >
    {
      typedef iterator_facade<vertex_iterator,
                              vertex_descriptor const,
                              forward_traversal_tag> super_t;
    public:
      vertex_iterator(k_ary_tree const& g) : current(g.null_vertex()), g(&g) {}

      vertex_iterator(vertex_descriptor start, k_ary_tree const& g)
        : current(start), g(&g)
      {
        while (has_left_successor(current, g))
          current = (left_successor(current, g));
      }

      typedef typename super_t::value_type value_type;
      typedef typename super_t::reference reference;

    private:
      friend class iterator_core_access;

      reference dereference() const
      {
        return current;
      }

      void increment()
      {
        if (has_right_successor(current, *g))
        {
          if (right_successor(current, *g) != last)
          {
            current = (right_successor(current, *g));
            while (has_left_successor(current, *g))
              current = (left_successor(current, *g));
            return;
          }
        }

        do
        {
          last = current;
          current = predecessor(current, *g);
        }
        while (current != g->null_vertex()
              && (!has_right_successor(current, *g)
                  || right_successor(current, *g) == last));
      }

      bool equal(vertex_iterator const &other) const
      {
        return current == other.current
               && (last == other.last || current == g->null_vertex());
              // && *g == *other.g
              ;
      }

      vertex_descriptor current, last;
      k_ary_tree const *g;
    };

    friend
    std::pair<vertex_iterator, vertex_iterator>
    vertices(k_ary_tree const &g)
    {
      return std::make_pair(vertex_iterator(vertex_descriptor(), g),
                            vertex_iterator(g));
    }


    // NOTE: This function will be an infinite loop if called on a recurrent
    // tree (which is not a tree any more).
    friend
    vertex_descriptor
    root(vertex_descriptor u, k_ary_tree const &g)
    {
      BOOST_ASSERT(u != graph_traits<k_ary_tree>::null_vertex());

      while (g[u].predecessor != graph_traits<k_ary_tree>::null_vertex())
      {
        u = g[u].predecessor;
      }

      BOOST_ASSERT(u != graph_traits<k_ary_tree>::null_vertex());
      return u;
    }

    friend
    bool
    is_left_successor(vertex_descriptor u, k_ary_tree const &g)
    {
      BOOST_ASSERT(!empty(u, g));

      vertex_descriptor v = predecessor(u, g);
      return left_successor(v, g) == u;
    }


    friend
    bool
    is_right_successor(vertex_descriptor u, k_ary_tree const &g)
    {
      BOOST_ASSERT(!empty(u, g));

      vertex_descriptor v = predecessor(u, g);
      return right_successor(v, g) == u;
    }

    friend
    bool
    has_predecessor(vertex_descriptor u, k_ary_tree const &g)
    {
      BOOST_ASSERT(!empty(u, g));
      BOOST_ASSERT(u < g.nodes.size());

      return g[u].predecessor != graph_traits<k_ary_tree>::null_vertex();
    }

    friend
    vertex_descriptor
    predecessor(vertex_descriptor u, k_ary_tree const &g)
    {
      BOOST_ASSERT(!empty(u, g));
      BOOST_ASSERT(u < g.nodes.size());

      return g[u].predecessor;
    }


    friend
    std::pair<in_edge_iterator, in_edge_iterator>
    in_edges(vertex_descriptor u, k_ary_tree const &g)
    {
      std::ptrdiff_t const i = g.nodes[u].predecessor != g.null_vertex();
      return std::make_pair(in_edge_iterator(&g.nodes[u].predecessor,
                                             make_in_edge_descriptor(u)),
                            in_edge_iterator(&g.nodes[u].predecessor + i,
                                             make_in_edge_descriptor(u)));
    }

    friend
    degree_size_type
    in_degree(vertex_descriptor v, k_ary_tree const &g)
    {
      return g.nodes[v].predecessor != g.null_vertex();
    }

    friend
    degree_size_type
    degree(vertex_descriptor v, k_ary_tree const &g)
    {
      return in_degree(v, g) + out_degree(v, g);
    }

    // *** MutableGraph interface ***

    friend
    std::pair<edge_descriptor, bool>
    add_edge(vertex_descriptor u, vertex_descriptor v, k_ary_tree &g)
    {
      if (!g.add_vertex(v) && predecessor(v, g) != g.null_vertex())
          return std::make_pair(edge_descriptor(), false);
      g.add_vertex(u);

      std::pair<edge_descriptor, bool> const result = g.add_edge_strict(u, v);
      if (result.second)
        g.nodes[v].predecessor = u;
      return result;
    }

    friend
    void
    remove_edge(vertex_descriptor u, vertex_descriptor v, k_ary_tree &g)
    {
      BOOST_ASSERT(predecessor(v, g) == u);
      g.remove_edge(u, v);
      g.nodes[v].predecessor = super_t::null_vertex();
    }

    friend
    void
    remove_edge(edge_descriptor e, k_ary_tree &g)
    {
      remove_edge(e.first, e.second, g);
    }

    friend
    void
    clear_vertex(vertex_descriptor u, k_ary_tree &g)
    {
      g.clear_childrens_predecessor(u);
      g.clear_vertex(u);
      g.nodes[u].predecessor = super_t::null_vertex();
    }


    friend
    void
    remove_vertex(vertex_descriptor u, k_ary_tree &g)
    {
      BOOST_ASSERT(in_degree(u, g) == 0);

      g.remove_vertex(u);
    }


    void
    clear_childrens_predecessor(vertex_descriptor u)
    {
      for (int i = 0; i != k; i++)
      {
        super_t::nodes[super_t::nodes[u].successors[i]].predecessor = super_t::null_vertex();
      }
    }
  };

  // IncidenceGraph interface

  typedef k_ary_tree<2, false> forward_binary_tree;
  typedef k_ary_tree<2, true> bidirectional_binary_tree;

  namespace detail
  {
    template <typename Tree, typename Visitor>
    Visitor traverse_nonempty(typename graph_traits<Tree>::vertex_descriptor u,
                              Tree const &g, Visitor vis)
    {
      BOOST_ASSERT(!empty(u, g));

      vis(order::pre, u);
      if (has_left_successor(u, g))
        vis = traverse_nonempty(left_successor(u, g), g, vis);
      vis(order::in, u);
      if (has_right_successor(u, g))
        vis = traverse_nonempty(right_successor(u, g), g, vis);
      vis(order::post, u);
      return vis;
    }

    template <typename Graph>
    int traverse_step(order::visit &v,
                      typename graph_traits<Graph>::vertex_descriptor &u,
                      Graph const &g)
    {
      // Requires BidirectionalTree<Graph>
      int result;

      switch (v)
      {
        case order::pre:
          if (has_left_successor(u, g)) {
            u = left_successor(u, g);
            result = 1;
          }
          else {
            v = order::in;
            result = 0;
          }
          break;

        case order::in:
          if (has_right_successor(u, g)) {
            v = order::pre;
            u = right_successor(u, g);
            result = 1;
          }
          else {
            v = order::post;
            result = 0;
          }
          break;

        case order::post:
          if (is_left_successor(u, g))
            v = order::in;
          u = predecessor(u, g);
          result = -1;
          break;
      }
      return result;
    }

    template <typename Graph, typename Visitor>
    Visitor traverse(typename graph_traits<Graph>::vertex_descriptor u,
                    Graph const &g, Visitor vis)
    {
      if (empty(u, g))
        return vis;
      typename graph_traits<Graph>::vertex_descriptor root = u;
      order::visit v = order::pre;
      vis(v, u);
      do {
        traverse_step(v, u, g);
        vis(v, u);
      } while (u != root || v != order::post);
      return vis;
    }


    // This is for forward trees.
    template <typename Graph0, typename Graph1>
    bool
    bifurcate_isomorphic_nonempty(typename graph_traits<Graph0>::vertex_descriptor u,
                                  Graph0 const &g,
                                  typename graph_traits<Graph1>::vertex_descriptor v,
                                  Graph1 const &h)
    {
      BOOST_ASSERT(!empty(u, g));
      BOOST_ASSERT(!empty(v, h));

      if (has_left_successor(u, g)) {
        if (has_left_successor(v, h)) {
          if (!bifurcate_isomorphic_nonempty(left_successor(u, g),
                                             left_successor(v, h)))
            return false;
        }
        else
          return false;
      }
      else
        if (has_left_successor(u, g))
          return false;

      if (has_right_successor(u, g)) {
        if (has_right_successor(v, h)) {
          if (!bifurcate_isomorphic_nonempty(right_successor(u, g),
                                             right_successor(v, h)))
            return false;
        }
        else
          return false;
      }
      else
        if (has_right_successor(u, g))
          return false;

      return true;
    }

    // This is for bidirectional trees.
    template <typename Graph0, typename Graph1>
    bool
    bifurcate_isomorphic(typename graph_traits<Graph0>::vertex_descriptor u,
                         Graph0 const &g,
                         typename graph_traits<Graph1>::vertex_descriptor v,
                         Graph1 const &h)
    {
      if (empty(u, g))
        return empty(v, h);
      if (empty(v, h))
        return false;
      typename graph_traits<Graph0>::vertex_descriptor root0 = u;
      order::visit visit0 = order::pre;
      order::visit visit1 = order::pre;
      while (true) {
        traverse_step(visit0, u, g);
        traverse_step(visit1, v, h);
        if (visit0 != visit1)
          return false;
        if (u == root0 && visit0 == order::post)
          return true;
      }
    }
  }


  template <typename Vertex, typename DFSTreeVisitor, typename ColorMap>
  void
  depth_first_visit(k_ary_tree<2, false, Vertex> &g,
                    typename boost::graph_traits<
                              k_ary_tree<2, false, Vertex>
                                                >::vertex_descriptor s,
                    DFSTreeVisitor &vis, ColorMap)
  {
    if (!empty(s, g))
      vis = detail::traverse_nonempty(s, g, vis);
  }

  template <typename Vertex, typename DFSTreeVisitor, typename ColorMap>
  void
  depth_first_visit(k_ary_tree<2, true, Vertex> &g,
                    typename boost::graph_traits<
                              k_ary_tree<2, false, Vertex>
                                                >::vertex_descriptor s,
                    DFSTreeVisitor &vis, ColorMap)
  {
    vis = detail::traverse(s, g, vis);
  }

  template <typename Vertex0, typename Vertex1>
  bool
  isomorphism(k_ary_tree<2, false, Vertex0> const &/*g*/, k_ary_tree<2, false, Vertex1> const &/*h*/)
  {
    // return detail::bifurcate_isomorphic(u, g, v, h);
    return true;
  }


  template <typename Vertex0, typename Vertex1>
  bool
  isomorphism(k_ary_tree<2, true, Vertex0> const &g,
              k_ary_tree<2, true, Vertex1> const &h)
  {
    return detail::bifurcate_isomorphic(0, g, 0, h);
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
    typedef typename std::vector<bool>::iterator node_iterator;
    typedef typename std::vector<bool>::const_iterator const_node_iterator;

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
    BOOST_STATIC_CONSTEXPR
    vertex_descriptor max_size()
    {
      return is_signed<vertex_descriptor>::value ?
        std::numeric_limits<vertex_descriptor>::max() :
        std::numeric_limits<vertex_descriptor>::max() >> 1 ;
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
      if (!g.roots.empty())
        g.nodes[g.roots.back()].sibling = true;
      g.roots.push_back(g.nodes.size());
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

    std::vector<bool> nodes;
    // std::vector<vertex_descriptor> roots;
  };

}

#endif
