//=======================================================================
// Copyright 2018 Jeremy William Murphy
//
// Distributed under the Boost Software License, Version 1.0. (See
// accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//=======================================================================

#define BOOST_TEST_MODULE k-ary tree
#define BOOST_TEST_DYN_LINK

#include <boost/graph/k-ary_tree.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/graph_concepts.hpp>
#include <boost/graph/compact_binary_tree.hpp>

#include <boost/test/unit_test.hpp>

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

BOOST_AUTO_TEST_SUITE(VertexListGraphSemantics)

typedef boost::mpl::list<boost::forward_binary_tree, boost::bidirectional_binary_tree> trees;

BOOST_AUTO_TEST_CASE_TEMPLATE(VLG, Tree, trees)
{
  Tree tree;
  typedef typename boost::graph_traits<Tree>::vertex_descriptor vertex_descriptor;

  create_full_tree(tree, 7);

  boost::array<vertex_descriptor, 7> actual,
                                      expected = {{3, 1, 4, 0, 5, 2, 6}};
  boost::copy(vertices(tree), boost::begin(actual));
  BOOST_CHECK_EQUAL_COLLECTIONS(actual.begin(), actual.end(), expected.begin(), expected.end());
}

// BOOST_AUTO_TEST_CASE(compact_binary_tree_test)
// {
//   boost::compact_binary_tree<> tree;
//
//   typedef boost::compact_binary_tree<>::vertex_descriptor vertex_descriptor;
//
//   create_full_tree(tree, 7);
//
//   boost::array<vertex_descriptor, 7> actual,
//                                      expected = {{0, 1, 2, 3, 4, 5, 6}};
//   boost::copy(vertices(tree), boost::begin(actual));
//   BOOST_CHECK_EQUAL_COLLECTIONS(actual.begin(), actual.end(), expected.begin(), expected.end());
// }

BOOST_AUTO_TEST_SUITE_END()

BOOST_AUTO_TEST_CASE(test_copy_to_unaligned_bits)
{
  boost::array<char unsigned, 10> source = { 0xAA, 0x11, 0x22, 0x33, 0x44,
                                             0x55, 0x66, 0x77, 0x88, 0x99 };
  boost::array<char unsigned, 10> dest = {0};

  dest[0] = 0xFF;
  BOOST_CHECK_EQUAL(dest.begin() + 1, boost::copy_bits(source.begin(), 4, dest.begin(), 2));
  BOOST_CHECK_EQUAL(dest[0], 0xEB);
  dest[0] = 0x00;

  BOOST_CHECK_EQUAL(dest.begin() + 1, boost::copy_bits(source.begin(), 6, dest.begin(), 2));
  BOOST_CHECK_EQUAL(dest[0], 0xA8);
  dest[0] = 0x00;

  BOOST_CHECK_EQUAL(dest.begin() + 2, boost::copy_bits(source.begin(), 8, dest.begin(), 2));
  BOOST_CHECK_EQUAL(dest[0], 0xA8);
  BOOST_CHECK_EQUAL(dest[1], 0x02);

  dest[0] = dest[1] = 0x00;

  BOOST_CHECK_EQUAL(dest.begin() + 3, boost::copy_bits(source.begin(), 16, dest.begin(), 2));
  BOOST_CHECK_EQUAL(dest[0], 0xA8);
  BOOST_CHECK_EQUAL(dest[1], 0x46);

  dest[0] = dest[1] = 0x00;

  BOOST_CHECK_EQUAL(dest.begin() + 2, boost::copy_bits(source.begin(), 16, dest.begin(), 0));
  BOOST_CHECK_EQUAL(dest[0], source[0]);
  BOOST_CHECK_EQUAL(dest[1], source[1]);
}


BOOST_AUTO_TEST_CASE(test_copy_from_unaligned_bits)
{
  boost::array<char unsigned, 10> source = { 0xAA, 0x11, 0x22, 0x33, 0x44,
                                             0x55, 0x66, 0x77, 0x88, 0x99 };
  boost::array<char unsigned, 10> dest = {0};

  // dest[0] = 0xFF;
  BOOST_CHECK_EQUAL(dest.begin() + 1,
                    boost::copy_bits(source.begin(), 0, 8, dest.begin()));
  BOOST_CHECK_EQUAL(dest[0], 0xAA);
  BOOST_CHECK_EQUAL(dest[1], 0x00);
  dest[0] = 0x00;

  BOOST_CHECK_EQUAL(dest.begin() + 1,
                    boost::copy_bits(source.begin(), 2, 4, dest.begin()));
  BOOST_CHECK_EQUAL(dest[0], 0x0A);
  BOOST_CHECK_EQUAL(dest[1], 0x00);
  dest[0] = 0x00;

  BOOST_CHECK_EQUAL(dest.begin() + 1,
                    boost::copy_bits(source.begin(), 4, 4, dest.begin()));
  BOOST_CHECK_EQUAL(dest[0], 0x0A);
  BOOST_CHECK_EQUAL(dest[1], 0x00);
  dest[0] = 0x00;

  BOOST_CHECK_EQUAL(dest.begin() + 1,
                    boost::copy_bits(source.begin(), 4, 8, dest.begin()));
  BOOST_CHECK_EQUAL(dest[0], 0x1A);
  BOOST_CHECK_EQUAL(dest[1], 0x00);
  dest[0] = dest[1] = 0x00;

  BOOST_CHECK_EQUAL(dest.begin() + 2,
                    boost::copy_bits(source.begin(), 4, 16, dest.begin()));
  BOOST_CHECK_EQUAL(dest[0], 0x1A); // 00011010
  BOOST_CHECK_EQUAL(dest[1], 0x21); // 00100001
  dest[0] = dest[1] = dest[2] = 0x00;

  BOOST_CHECK_EQUAL(dest.begin() + 3,
                    boost::copy_bits(source.begin(), 0, 24, dest.begin()));
  BOOST_CHECK_EQUAL(dest[0], 0xAA);
  BOOST_CHECK_EQUAL(dest[1], 0x11);
  BOOST_CHECK_EQUAL(dest[2], 0x22);
  dest[0] = dest[1] = dest[2] = 0x00;

  BOOST_CHECK_EQUAL(dest.begin() + 3,
                    boost::copy_bits(source.begin(), 4, 24, dest.begin()));
  BOOST_CHECK_EQUAL(dest[0], 0x1A);
  BOOST_CHECK_EQUAL(dest[1], 0x21);
  BOOST_CHECK_EQUAL(dest[2], 0x32);
  dest[0] = dest[1] = dest[2] = 0x00;

  dest = source;

  BOOST_CHECK_EQUAL(dest.begin() + 1,
                    boost::copy_bits(source.begin(), 2, 4, dest.begin()));
  BOOST_CHECK_EQUAL(dest[0], 0xAA);
  BOOST_CHECK_EQUAL(dest[1], 0x11);


  BOOST_CHECK_EQUAL(dest.begin() + 1,
                    boost::copy_bits(source.begin(), 4, 8, dest.begin()));
  BOOST_CHECK_EQUAL(dest[0], 0x1A);
  BOOST_CHECK_EQUAL(dest[1], 0x11);
  dest = source;
}

BOOST_AUTO_TEST_CASE(test_bit_rotate_block)
{
  boost::dynamic_bitset<> input(std::string("0011001100110011001100110000000000000000000001010101010101010101"));
  boost::dynamic_bitset<>  expected(std::string("0011001100110000000000000101010101110011001100000000000101010101"));
  boost::bit_rotate_block(*input.data(), 10, 30, 50);
  BOOST_CHECK_EQUAL(input, expected);

  input = boost::dynamic_bitset<>(std::string("0101111000110111000"));
  boost::bit_rotate_block(*input.data(), 3, 12, 15);
  expected = boost::dynamic_bitset<>(std::string("0101000110111111000"));
  BOOST_CHECK_EQUAL(input, expected);

  input = boost::dynamic_bitset<>(std::string("0101111000110111000"));
  boost::bit_rotate_block(*input.data(), 3, 6, 12);
  expected = boost::dynamic_bitset<>(std::string("0101111111000110000"));
  BOOST_CHECK_EQUAL(input, expected);
}

/*
BOOST_AUTO_TEST_CASE(test_bit_rotate_two_blocks)
{
  boost::dynamic_bitset<char unsigned>    input(std::string("1111111100000000"));
  boost::dynamic_bitset<char unsigned> expected(std::string("1111100000011100"));
  boost::bit_rotate_two_blocks(input.data(), 1, 7, 11);

  BOOST_CHECK_EQUAL(input, expected);

}

BOOST_AUTO_TEST_CASE(test_bit_rotate_blocks)
{
  boost::dynamic_bitset<char unsigned> input(std::string("001100110101010100000000"));
  boost::dynamic_bitset<char unsigned> expected(std::string("001100010100110101000000"));
  boost::bit_rotate_reverse(input.data(), 6, 12, 20);
  // BOOST_CHECK_EQUAL(input, expected);

}
*/


BOOST_AUTO_TEST_CASE(test_rightmost)
{
  typedef boost::compact_binary_tree<> BinaryTree;
  BinaryTree tree;
  typedef boost::graph_traits<BinaryTree>::vertex_descriptor vertex_descriptor;

  create_full_tree(tree, 7);
  vertex_descriptor result = rightmost(0, tree);
  // BOOST_TEST(result == 6);
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
