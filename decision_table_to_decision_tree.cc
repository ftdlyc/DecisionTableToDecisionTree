// author: ftdlyc <yclu.cn@gmail.com>
// convert single action decision table to decision tree
// method: dynamic programming

#include <cstdio>

#include <algorithm>
#include <map>
#include <queue>
#include <stack>
#include <unordered_set>
#include <vector>

inline void BitToVector(int num, int n, std::vector<int>& v) {
  int val = num & 0x1;
  for (int i = 0; i < n; ++i) {
    v[i] = val;
    num  = num >> 1;
    val  = num & 0x1;
  }
}

inline void BitToVector(int num, int n, const std::vector<int>& pos, std::vector<int>& v) {
  int val = num & 0x1;
  for (int i = 0; i < n; ++i) {
    v[pos[i]] = val;
    num       = num >> 1;
    val       = num & 0x1;
  }
}

inline int CombinationNumber(int n, int m) {
  int v1 = 1, v2 = 1;
  for (int i = n; i > n - m; --i) {
    v1 *= i;
  }
  for (int i = 2; i <= m; ++i) {
    v2 *= i;
  }
  return v1 / v2;
}

void Combinate(int m, int pos, const std::vector<int>& in,
               std::vector<std::vector<int>>& out1, std::vector<std::vector<int>>& out2,
               std::vector<int>& buf1, std::vector<int>& buf2) {
  int n   = in.size();
  int len = buf1.size() - m;

  if (m == 0) {
    out1.emplace_back(buf1);
    if (pos <= n) {
      for (int i = pos; i < n; ++i) {
        buf2[i - len] = in[i];
      }
      out2.emplace_back(buf2);
    }
    return;
  }

  if (n - pos >= m) {
    buf1[len] = in[pos];
    Combinate(m - 1, pos + 1, in, out1, out2, buf1, buf2);
  }
  if (n - pos - 1 >= m) {
    buf2[pos - len] = in[pos];
    Combinate(m, pos + 1, in, out1, out2, buf1, buf2);
  }
}

// select m number in vector
void Combinate(int m, const std::vector<int>& in, std::vector<std::vector<int>>& out1, std::vector<std::vector<int>>& out2) {
  if (m > in.size()) return;
  out1.clear();
  out2.clear();
  std::vector<int> buf1(m), buf2(in.size() - m);
  Combinate(m, 0, in, out1, out2, buf1, buf2);
}

struct TreeNode {
  int value;
  TreeNode* ltree;
  TreeNode* rtree;

  TreeNode()
      : value(0)
      , ltree(nullptr)
      , rtree(nullptr) {}
  TreeNode(int n)
      : value(n)
      , ltree(nullptr)
      , rtree(nullptr) {}
};

class SingleActionDecisionTable {
public:
  SingleActionDecisionTable(int num_conditions, int num_actions)
      : num_conditions_(num_conditions)
      , num_actions_(num_actions)
      , num_rules_(0) {
    if (num_conditions <= 0) {
      fprintf(stderr, "Number of conditions must be gather than 0.\n");
      return;
    }
    if (num_actions <= 0) {
      fprintf(stderr, "Number of actions must be gather than 0.\n");
      return;
    }
    table_.resize(1 << num_conditions);
    std::fill(table_.begin(), table_.end(), -1);
  }

  SingleActionDecisionTable()  = delete;
  ~SingleActionDecisionTable() = default;

  bool Empty() const {
    return num_rules_ == 0;
  }

  int AddRule(const std::vector<int>& status, int action) {
    int pos        = GetPos(status);
    int old_action = table_[pos];
    table_[pos]    = action;
    if (old_action == -1) ++num_rules_;
    return old_action;
  }

  int DeleteRule(const std::vector<int>& status) {
    int pos        = GetPos(status);
    int old_action = table_[pos];
    table_[pos]    = -1;
    if (old_action != -1) --num_rules_;
    return old_action;
  }

  int Test(const std::vector<int>& status) const {
    return table_[GetPos(status)];
  }

  int GetNumActions() const {
    return num_actions_;
  }

  int GetNumContditions() const {
    return num_conditions_;
  }

  void Print() const {
    printf("\n");
    printf("Decision Table : %d rules, %d conditions, %d actions\n", num_rules_, num_conditions_, num_actions_);
    printf("         ");
    for (int i = 0; i < num_conditions_; ++i) {
      printf("c%d  ", i);
    }
    printf("action\n");

    std::vector<int> status(num_conditions_);
    for (int i = 0; i < table_.size(); ++i) {
      printf("rule %d: ", i);
      BitToVector(i, num_conditions_, status);
      for (int j = 0; j < num_conditions_; ++j) {
        printf("%2d, ", status[j]);
      }
      printf("%2d\n", table_[i]);
    }
    printf("\n");
  }

private:
  int GetPos(const std::vector<int>& status) const {
    int pos = status[0];
    for (int i = 1; i < num_conditions_; ++i) {
      if (status[i] > 0) {
        pos += 2 << (i - 1);
      }
    }
    return pos;
  }

  int num_actions_;
  int num_conditions_;
  int num_rules_;
  std::vector<int> table_;
};

class DecisionTree {
public:
  DecisionTree(const SingleActionDecisionTable& table)
      : num_conditions_(table.GetNumContditions())
      , num_actions_(table.GetNumActions())
      , root_(nullptr) {
    if (num_conditions_ <= 0) {
      fprintf(stderr, "Number of conditions must be gather than 0.\n");
      return;
    }
    if (num_actions_ <= 0) {
      fprintf(stderr, "Number of actions must be gather than 0.\n");
      return;
    }
    DecisionTableToTree(table);
  }

  DecisionTree() = delete;

  ~DecisionTree() {
    DeleteTree(root_);
  }

  bool Empty() const {
    return root_ == nullptr;
  };

  int Test(const std::vector<int>& status) const {
    TreeNode* cur = root_;

    int n = 0;
    while (cur->ltree != nullptr && cur->rtree != nullptr) {
      if (status[n] > 0) {
        cur = cur->rtree;
      } else {
        cur = cur->ltree;
      }
      ++n;
    }
    return cur->value;
  }

  void PreOrderTraverse() const {
    printf("Pre Order Traverse\n");
    std::stack<TreeNode*> s;
    TreeNode* cur = root_;
    while (cur != nullptr || !s.empty()) {
      while (cur != nullptr) {
        printf("%d ", cur->value);
        s.push(cur);
        cur = cur->ltree;
      }
      cur = s.top();
      s.pop();
      cur = cur->rtree;
    }
    printf("\n\n");
  };

  void InOrderTraverse() const {
    printf("In Order Traverse\n");
    std::stack<TreeNode*> s;
    TreeNode* cur = root_;
    while (cur != nullptr || !s.empty()) {
      while (cur != nullptr) {
        s.push(cur);
        cur = cur->ltree;
      }
      cur = s.top();
      printf("%d ", cur->value);
      s.pop();
      cur = cur->rtree;
    }
    printf("\n\n");
  };

  void PostOrderTraverse() const {
    printf("Post Order Traverse\n");
    std::stack<TreeNode*> s;
    TreeNode* cur  = root_;
    TreeNode* last = nullptr;
    while (cur != nullptr || !s.empty()) {
      while (cur != nullptr) {
        s.push(cur);
        cur = cur->ltree;
      }
      cur = s.top();
      if (cur->rtree != nullptr && last != cur->rtree) {
        cur = cur->rtree;
      } else if (cur->rtree == nullptr || last == cur->rtree) {
        printf("%d ", cur->value);
        last = cur;
        s.pop();
        cur = nullptr;
      }
    }
    printf("\n\n");
  };

  void LevelOrderTraverse() const {
    printf("Level Order Traverse\n");
    std::queue<TreeNode*> q;
    TreeNode* cur = root_;
    q.push(cur);
    while (!q.empty()) {
      cur = q.front();
      q.pop();
      printf("%d ", cur->value);
      if (cur->ltree != nullptr) q.push(cur->ltree);
      if (cur->rtree != nullptr) q.push(cur->rtree);
    }
    printf("\n\n");
  }

private:
  struct Cude {
    int dash_pos;
    int gain;
    std::unordered_set<int> action;

    Cude()
        : dash_pos(0)
        , gain(0) {}
    Cude(int pos, int g, const std::unordered_set<int>& a1, const std::unordered_set<int>& a2)
        : dash_pos(pos)
        , gain(g)
        , action(a1) {
      action.insert(a2.begin(), a2.end());
    }
  };

  void TracingBackCudeTables(int n, TreeNode*& root,
                             const std::vector<int>& status, const std::vector<std::map<std::vector<int>, Cude>>& cube_tables) {
    if (n < 0) return;

    const auto& cube = cube_tables[n].find(status)->second;
    if (cube.action.size() == 1) {
      root = new TreeNode(*cube.action.begin());
      return;
    }

    int pos = cube.dash_pos;
    root    = new TreeNode(pos);

    std::vector<int> status0(status);
    status0[pos] = 0;
    TracingBackCudeTables(n - 1, root->ltree, status0, cube_tables);

    std::vector<int> status1(status);
    status1[pos] = 1;
    TracingBackCudeTables(n - 1, root->rtree, status1, cube_tables);
  }

  void DecisionTableToTree(const SingleActionDecisionTable& table) {
    std::vector<std::map<std::vector<int>, Cude>> cude_tables(num_conditions_ + 1);
    std::vector<int> status(num_conditions_, 0);

    std::vector<int> pos_all(num_conditions_);
    for (int i = 0; i < num_conditions_; ++i) {
      pos_all[i] = i;
    }

    // 0-cude
    for (int i = 0; i < (1 << num_conditions_); ++i) {
      BitToVector(i, num_conditions_, status);
      Cude cube;
      cube.action.emplace(table.Test(status));
      cude_tables[0].emplace(status, cube);
    }

    // cal 1-cube ~ n-cude (DP)
    for (int i = 1; i <= num_conditions_; ++i) {
      auto& cur_ct  = cude_tables[i];
      auto& last_ct = cude_tables[i - 1];

      std::vector<std::vector<int>> pos_dash, pos_01;
      Combinate(i, pos_all, pos_dash, pos_01);
      int num_combinations = pos_dash.size();

      for (int j = 0; j < num_combinations; ++j) {
        for (int k = 0; k < i; ++k) {
          status[pos_dash[j][k]] = 2;
        }

        int n_01 = num_conditions_ - i;
        for (int k = 0; k < (1 << n_01); ++k) {
          BitToVector(k, n_01, pos_01[j], status);

          int max_idx = 0, max_gain = INT32_MIN;
          Cude *max_cude0, *max_cude1;
          for (int l = 0; l < i; ++l) {
            int pos     = pos_dash[j][l];
            status[pos] = 0;
            Cude& cube0 = last_ct[status];
            status[pos] = 1;
            Cude& cube1 = last_ct[status];
            status[pos] = 2;
            int gain    = cube0.gain + cube1.gain + (cube0.action == cube1.action);
            if (gain > max_gain) {
              max_gain  = gain;
              max_idx   = pos;
              max_cude0 = &cube0;
              max_cude1 = &cube1;
            }
          }
          cur_ct.emplace(status, Cude(max_idx, max_gain, max_cude0->action, max_cude1->action));
        }
      }
    }

    // recursively tracing back to create desicion tree
    std::fill(status.begin(), status.end(), 2);
    TracingBackCudeTables(num_conditions_, root_, status, cude_tables);
  }

  void DeleteTree(TreeNode* root) {
    if (root == nullptr) return;
    DeleteTree(root->ltree);
    DeleteTree(root->rtree);
    delete root;
  }

  int num_actions_;
  int num_conditions_;
  TreeNode* root_;
};

void SetTable(SingleActionDecisionTable& table) {
  table.AddRule({0, 0, 0, 0, 0}, 0);
  table.AddRule({0, 1, 0, 0, 0}, 0);
  table.AddRule({0, 0, 1, 0, 0}, 0);
  table.AddRule({0, 0, 0, 1, 0}, 0);
  table.AddRule({0, 0, 0, 0, 1}, 0);
  table.AddRule({0, 1, 1, 0, 0}, 0);
  table.AddRule({0, 1, 0, 1, 0}, 0);
  table.AddRule({0, 1, 0, 0, 1}, 0);
  table.AddRule({0, 0, 1, 1, 0}, 0);
  table.AddRule({0, 0, 1, 0, 1}, 0);
  table.AddRule({0, 0, 0, 1, 1}, 0);
  table.AddRule({0, 1, 1, 1, 0}, 0);
  table.AddRule({0, 1, 1, 0, 1}, 0);
  table.AddRule({0, 1, 0, 1, 1}, 0);
  table.AddRule({0, 0, 1, 1, 1}, 0);
  table.AddRule({0, 1, 1, 1, 1}, 0);
  table.AddRule({1, 0, 0, 0, 0}, 1);
  table.AddRule({1, 1, 0, 0, 0}, 2);
  table.AddRule({1, 0, 1, 0, 0}, 3);
  table.AddRule({1, 0, 0, 1, 0}, 4);
  table.AddRule({1, 0, 0, 0, 1}, 5);
  table.AddRule({1, 1, 1, 0, 0}, 3);
  table.AddRule({1, 1, 0, 1, 0}, 6);
  table.AddRule({1, 1, 0, 0, 1}, 5);
  table.AddRule({1, 0, 1, 1, 0}, 3);
  table.AddRule({1, 0, 1, 0, 1}, 3);
  table.AddRule({1, 0, 0, 1, 1}, 7);
  table.AddRule({1, 1, 1, 1, 0}, 3);
  table.AddRule({1, 1, 1, 0, 1}, 3);
  table.AddRule({1, 1, 0, 1, 1}, 7);
  table.AddRule({1, 0, 1, 1, 1}, 3);
  table.AddRule({1, 1, 1, 1, 1}, 3);
}

int main() {
  SingleActionDecisionTable table(5, 8);
  SetTable(table);
  table.Print();

  DecisionTree tree(table);
  tree.PreOrderTraverse();
  tree.InOrderTraverse();
  tree.PostOrderTraverse();
  tree.LevelOrderTraverse();

  return 0;
}

