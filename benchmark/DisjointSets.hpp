#ifndef DISJOINTSETS_H
#define DISJOINTSETS_H

#include <vector>


class UnionFind {
private:
    // parent[x] stores the parent of x.
    // If parent[x] is negative, x is a root, and -parent[x] represents the size of its set.
    std::vector<int> parent;

public:
    // Initialize N disjoint sets, each of size 1 (stored as -1)
    explicit UnionFind(int n) : parent(n, -1) {}

           // Find the representative root of the set containing x (with Path Compression)
    int find_set(int x) {
        if (parent[x] < 0) {
            return x;
        }
        // Path compression: flatten the structure by pointing directly to the root
        return parent[x] = find_set(parent[x]);
    }

           // Merge the sets containing x and y (with Union by Size)
    bool union_set(int x, int y) {
        int root_x = find_set(x);
        int root_y = find_set(y);

        if (root_x == root_y) {
            return false; // Already in the same set
        }

               // Union by size: attach the smaller tree under the larger tree
        if (parent[root_x] > parent[root_y]) {
            std::swap(root_x, root_y);
        }

               // parent[root_x] is more negative, so it represents the larger set
        parent[root_x] += parent[root_y]; // Update size of the new root
        parent[root_y] = root_x;          // Make root_x the parent of root_y

        return true; // Successfully merged
    }

           // Check if x and y belong to the same set
    bool connected(int x, int y) {
        return find_set(x) == find_set(y);
    }

           // Return the size of the set containing x
    int getSize(int x) {
        return -parent[find_set(x)];
    }
};


#endif // DISJOINTSETS_H
