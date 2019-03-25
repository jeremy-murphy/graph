//=======================================================================
// Copyright 2018 Jeremy William Murphy
//
// Distributed under the Boost Software License, Version 1.0. (See
// accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//=======================================================================

#define BOOST_TEST_MODULE k-ary tree
#define BOOST_TEST_DYN_LINK

#include <boost/test/unit_test.hpp>

#include <boost/graph/k-ary_tree.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/graph_concepts.hpp>
#include <boost/graph/compact_binary_tree.hpp>


#include <boost/array.hpp>
#include <boost/range.hpp>
#include <boost/range/algorithm.hpp>

#include <boost/mpl/list.hpp>

#include <utility>

template <typename MutableGraph>
void create_full_tree(MutableGraph &tree,
                      typename boost::graph_traits<MutableGraph>::vertex_descriptor weight)
{
  typedef typename boost::graph_traits<MutableGraph>::vertex_descriptor vertex_descriptor;

  vertex_descriptor child, parent = add_vertex(tree);

  do
  {
    child = add_vertex(tree);
    add_edge(parent, child, tree);
    if (!(child & 1))
      parent++;
  }
  while (child != weight - 1);
}

template <typename Tree>
void empty_binary_tree()
{
  Tree tree;
  BOOST_CHECK(num_vertices(tree) == 0);
}

template <typename Tree>
void push_pop_binary_tree()
{
  Tree tree;
  typedef typename boost::graph_traits<Tree>::vertex_descriptor vertex_descriptor;
  vertex_descriptor u = add_vertex(tree);
  BOOST_ASSERT(num_vertices(tree) == 1);
  remove_vertex(u, tree);
  BOOST_ASSERT(num_vertices(tree) == 0);

  std::vector<vertex_descriptor> added;
  added.push_back(add_vertex(tree));
  added.push_back(add_vertex(tree));
  added.push_back(add_vertex(tree));
  BOOST_ASSERT(num_vertices(tree) == 3);
  remove_vertex(added.back(), tree);
  added.pop_back();
  remove_vertex(added.back(), tree);
  added.pop_back();
  remove_vertex(added.back(), tree);
  added.pop_back();
  BOOST_ASSERT(num_vertices(tree) == 0);
}


template <typename Tree>
void insert_remove_randomly()
{
  Tree tree;
  typedef typename boost::graph_traits<Tree>::vertex_descriptor vertex_descriptor;

  std::vector<vertex_descriptor> added;
  added.push_back(add_vertex(tree));
  added.push_back(add_vertex(tree));
  added.push_back(add_vertex(tree));
  BOOST_ASSERT(num_vertices(tree) == 3);
  remove_vertex(added[0], tree);
  BOOST_ASSERT(num_vertices(tree) == 2);
  remove_vertex(added[1], tree);
  BOOST_ASSERT(num_vertices(tree) == 1);
  added[0] = add_vertex(tree);
  BOOST_ASSERT(num_vertices(tree) == 2);
  added[1] = add_vertex(tree);
  BOOST_ASSERT(num_vertices(tree) == 3);
  add_edge(added[0], added[1], tree);
  add_edge(4, 5, tree);
}

template <typename Tree>
void incidence_graph()
{
  Tree tree;
  typedef typename boost::graph_traits<Tree>::vertex_descriptor vertex_descriptor;

  vertex_descriptor u = add_vertex(tree);
  BOOST_CHECK(boost::distance(out_edges(u, tree)) == 0);
  BOOST_CHECK(out_degree(u, tree) == 0);
  add_edge(u, u + 1, tree);
  BOOST_CHECK(boost::distance(out_edges(u, tree)) == 1);
  BOOST_CHECK(out_degree(u, tree) == 1);
}

void bidirectional_graph()
{
  boost::bidirectional_binary_tree tree;
  create_full_tree(tree, 5);
  BOOST_CHECK(boost::distance(in_edges(0, tree)) == 0);
  BOOST_CHECK(in_degree(0, tree) == 0);
  BOOST_CHECK(boost::distance(in_edges(1, tree)) == 1);
  BOOST_CHECK(in_degree(1, tree) == 1);
  BOOST_CHECK(boost::distance(in_edges(2, tree)) == 1);
  BOOST_CHECK(in_degree(2, tree) == 1);
  BOOST_CHECK(root(0, tree) == 0);
  BOOST_CHECK(root(1, tree) == 0);
  BOOST_CHECK(root(2, tree) == 0);
  BOOST_CHECK(root(3, tree) == 0);
  BOOST_CHECK(root(4, tree) == 0);
  // detach the (1(3, 4)) subtree.
  remove_edge(0, 1, tree);
  BOOST_CHECK(!has_left_successor(0, tree));
  BOOST_CHECK(root(0, tree) == 0);
  BOOST_CHECK(root(1, tree) == 1);
  BOOST_CHECK(root(2, tree) == 0);
  BOOST_CHECK(root(3, tree) == 1);
  BOOST_CHECK(root(4, tree) == 1);
}

template <typename Order, typename Vertex>
struct tree_visitor
{
  void operator()(Order visit, Vertex u)
  {
    visited.push_back(std::make_pair(visit, u));
  }

  std::vector< std::pair<Order, Vertex> > visited;
};


template <bool Predecessor>
void depth_first_search()
{
  typedef boost::k_ary_tree<2, Predecessor> Tree;
  boost::k_ary_tree<2, Predecessor> tree;
  typedef typename boost::graph_traits<Tree>::vertex_descriptor vertex_descriptor;

  create_full_tree(tree, 3);

  std::vector<boost::default_color_type> color;
  typedef std::pair<boost::order::visit, vertex_descriptor> visiting;
  boost::array< visiting, 9> const expected_seq =
  {{
    std::make_pair(boost::order::pre, 0),
    std::make_pair(boost::order::pre, 1),
    std::make_pair(boost::order::in, 1),
    std::make_pair(boost::order::post, 1),
    std::make_pair(boost::order::in, 0),
    std::make_pair(boost::order::pre, 2),
    std::make_pair(boost::order::in, 2),
    std::make_pair(boost::order::post, 2),
    std::make_pair(boost::order::post, 0)
  }};
  tree_visitor<boost::order::visit, vertex_descriptor> visitor;
  depth_first_visit(tree, 0, visitor, color);
  BOOST_CHECK(boost::equal(visitor.visited, expected_seq));
}


void mutable_bidirectional()
{
  typedef boost::k_ary_tree<2, true> Tree;
  Tree tree;
  typedef boost::graph_traits<Tree>::vertex_descriptor vertex_descriptor;

  create_full_tree(tree, 3);

  BOOST_CHECK(predecessor(vertex_descriptor(1), tree) == 0);
  BOOST_CHECK(predecessor(vertex_descriptor(2), tree) == 0);

  BOOST_CHECK(has_left_successor(vertex_descriptor(0), tree));
  BOOST_CHECK(has_right_successor(vertex_descriptor(0), tree));

  clear_vertex(vertex_descriptor(0), tree);

  BOOST_CHECK(num_vertices(tree) == 3);

  vertex_descriptor null = boost::graph_traits<Tree>::null_vertex();

  BOOST_CHECK(predecessor(vertex_descriptor(1), tree) == null);
  BOOST_CHECK(predecessor(vertex_descriptor(2), tree) == null);

  BOOST_CHECK(!has_left_successor(vertex_descriptor(0), tree));
  BOOST_CHECK(!has_right_successor(vertex_descriptor(0), tree));

  // Remove after clearing.
  remove_vertex(vertex_descriptor(0), tree);

  BOOST_CHECK(num_vertices(tree) == 2);

}


template <bool Predecessor>
void binary_tree()
{
  typedef boost::k_ary_tree<2, Predecessor> Tree;
  boost::k_ary_tree<2, Predecessor> tree;
  typedef typename boost::graph_traits<Tree>::vertex_descriptor vertex_descriptor;

  std::vector<vertex_descriptor> added;

  added.push_back(add_vertex(tree));
  added.push_back(add_vertex(tree));
  added.push_back(add_vertex(tree));
  add_edge(added[0], added[1], tree);
  add_edge(added[0], added[2], tree);
  BOOST_CHECK(has_left_successor(added[0], tree));
  BOOST_CHECK(has_right_successor(added[0], tree));
  BOOST_CHECK(!has_left_successor(added[1], tree));
  BOOST_CHECK(!has_right_successor(added[1], tree));
  BOOST_CHECK(!has_left_successor(added[2], tree));
  BOOST_CHECK(!has_right_successor(added[2], tree));

  BOOST_CHECK(isomorphism(tree, tree));

  remove_edge(added[0], added[1], tree);
  remove_edge(added[0], added[2], tree);
  BOOST_CHECK(!has_left_successor(added[0], tree));
  BOOST_CHECK(!has_right_successor(added[0], tree));
}

BOOST_AUTO_TEST_SUITE(VertexListGraphSemantics);

typedef boost::mpl::list<boost::forward_binary_tree, boost::bidirectional_binary_tree> trees;

namespace boost
{
  template <std::size_t K, bool Predecessor, typename Vertex>
  std::ostream& operator<<(std::ostream& os, k_ary_tree<K, Predecessor, Vertex> const& tree)
  {
    return os;
  }
}

BOOST_AUTO_TEST_CASE_TEMPLATE(VLG, Tree, trees)
{
  Tree tree;
  typedef typename boost::graph_traits<Tree>::vertex_descriptor vertex_descriptor;

  create_full_tree(tree, 7);

  boost::array<vertex_descriptor, 7> actual,
                                      expected = {{3, 1, 4, 0, 5, 2, 6}};
  boost::copy(vertices(tree), boost::begin(actual));
  BOOST_TEST(actual == expected);
}

BOOST_AUTO_TEST_CASE(compact_binary_tree_test)
{
  boost::compact_binary_tree<> tree;

  typedef boost::compact_binary_tree<>::vertex_descriptor vertex_descriptor;

  create_full_tree(tree, 7);

  boost::array<vertex_descriptor, 7> actual,
                                     expected = {{0, 1, 2, 3, 4, 5, 6}};
  boost::copy(vertices(tree), boost::begin(actual));
  BOOST_CHECK(actual == expected);
}

BOOST_AUTO_TEST_SUITE_END();

BOOST_AUTO_TEST_CASE(test_bit_rotate)
{
  typedef boost::array<unsigned int, 10> Array;
  Array data;
  int result = boost::bit_rotate(boost::begin(data), 0, 0, 0);
}


BOOST_AUTO_TEST_CASE(test_rightmost)
{
  typedef boost::compact_binary_tree<> BinaryTree;
  BinaryTree tree;
  typedef boost::graph_traits<BinaryTree>::vertex_descriptor vertex_descriptor;

  create_full_tree(tree, 7);
  vertex_descriptor result = rightmost(0, tree);
  BOOST_TEST(result == 6);
}

int test_main(int, char*[])
{
  using namespace boost::concepts;
  using boost::forward_binary_tree;
  using boost::bidirectional_binary_tree;
  using boost::compact_binary_tree;

  BOOST_CONCEPT_ASSERT((BidirectionalGraph<bidirectional_binary_tree>));
  BOOST_CONCEPT_ASSERT((MutableGraph<bidirectional_binary_tree>));
  BOOST_CONCEPT_ASSERT((MutableGraph<forward_binary_tree>));
  BOOST_CONCEPT_ASSERT((VertexListGraph<forward_binary_tree>));
  BOOST_CONCEPT_ASSERT((VertexListGraph<bidirectional_binary_tree>));
  BOOST_CONCEPT_ASSERT((VertexListGraph< compact_binary_tree<> >));
  // BOOST_CONCEPT_ASSERT((EdgeListGraph<forward_binary_tree>));
  // BOOST_CONCEPT_ASSERT((EdgeListGraph<bidirectional_binary_tree>));

  empty_binary_tree<forward_binary_tree>();
  empty_binary_tree<bidirectional_binary_tree>();
  empty_binary_tree< compact_binary_tree<> >();
  push_pop_binary_tree<forward_binary_tree>();
  push_pop_binary_tree<bidirectional_binary_tree>();
  insert_remove_randomly<forward_binary_tree>();
  insert_remove_randomly<bidirectional_binary_tree>();
  incidence_graph<forward_binary_tree>();
  incidence_graph<bidirectional_binary_tree>();
  bidirectional_graph();

  binary_tree<0>();
  binary_tree<1>();

  depth_first_search<0>();
  depth_first_search<1>();

  mutable_bidirectional();

  return 0;
}
