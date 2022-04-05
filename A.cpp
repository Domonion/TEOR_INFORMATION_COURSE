#include <iostream>
#include <iomanip>
#include <cmath>
#include <algorithm>
#include <random>
#include <vector>
#include <stack>
#include <deque>
#include <queue>
#include <array>
#include <list>
#include <bitset>
#include <set>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <climits>
#include <functional>
#include <utility>
#include <string>
#include <cstring>
#include <cassert>

#define TASK ""
#define forn(i, s, n) for(auto (i) = (s); (i) < (n); (i)++)
#define forb(i, s, n) for(auto (i) = (s); (i) >= (n); (i)--)
#define fora(i, a) for(auto (i) : (a))
#define foraa(i, a) for(auto & (i) : (a))
#define size(a) (int((a).size()))
#define sqr(i) ((i) * (i))
#define all(a) (a).begin(), (a).end()
#define rall(a) (a).rbegin(), (a).rbegin()
#define vec vector
#define pr pair
#define sc second
#define fs first
#define umap unordered_map
#define uset unordered_set
#define pq priority_queue
#define lb lower_bound
#define ub upper_bound
#define mp make_pair
#define pb push_back

typedef long long ll;
typedef long double ld;
typedef unsigned long long ull;

using namespace std;

class RandomDevice {
private:
    mt19937 randomer;
    uint32_t current;
    int lastBit;
    normal_distribution<double> normalDistribution;
public:
    RandomDevice() {
        randomer.seed(time(nullptr));
        lastBit = 0;
        current = randomer();
    }

    char getLast() {
        if (lastBit == 32) {
            lastBit = 0;
            current = randomer();
        }

        return (current >> lastBit++) & 1;
    }

    ld deviate(ld deviation) {
        return normalDistribution(randomer) * deviation;
    }
};

const int K = 1000;
const int N = 1000;

char g[K][N];
char minspan[N][N];
char info[K];
char encoded[N];
ld noised[N];
char decoded[N];
int n, k;
RandomDevice rd;

void generateRandom() {
    forn(i, 0, k) {
        info[i] = rd.getLast();
    }
}

void encode() {
    forn(i, 0, n) {
        forn(j, 0, k) {
            encoded[i] ^= info[j] & g[j][i];
        }
    }
}

void addNoise(ld deviation) {
    forn(i, 0, n) {
        noised[i] = 1.0 - 2.0 * encoded[i] + rd.deviate(deviation);
    }
}

char check() {
//    forn (i, 0, n) {
//        char cur = encoded[i] + '0';
//        cout << cur << ' ';
//    }
    forn(i, 0, n) {
        if (encoded[i] != decoded[i])
            return 1;
    }

    return 0;
}

void copyg() {
    forn(i, 0, k) {
        forn(j, 0, n) {
            minspan[i][j] = g[i][j];
        }
    }
}

void gauss(char shouldSwap = true) {
    int j = 0;
    vec<int> fixed;

    while (size(fixed) < k) {
        vec<int> selected;
        int currentLine = size(fixed);
        int startLine;

        if (shouldSwap) {
            startLine = currentLine;
        } else {
            startLine = 0;
        }

        forn(i, startLine, k) {
            char ok = 1;

            if (!shouldSwap && find(all(fixed), i) != fixed.end()) {
                ok = 0;
            }

            if (ok && minspan[i][j]) {
                selected.pb(i);
            }
        }

        if (!selected.empty()) {
            int mainLine = selected[0];

            forn(l, 1, size(selected)) {
                forn(j, 0, n) {
                    minspan[selected[l]][j] ^= minspan[mainLine][j];
                }
            }

            if (shouldSwap && mainLine != currentLine) {
                forn (i, 0, n) {
                    swap(minspan[mainLine][i], minspan[currentLine][i]);
                }
            }

            if (shouldSwap) {
                fixed.pb(currentLine);
            } else {
                fixed.pb(mainLine);
            }
        }

        j++;
    }
}
char buffer[N][N];
void rotate180() {
    forn(i, 0, k) {
//        cout << "line " << i << " before rotate" << endl;
//        forn (j, 0, n) {
//            char cur = minspan[i][j] + '0';
//            cout << cur << ' ';
//        }
//        cout << endl;
//        cout << "line " << k - 1 - i << " before rotate" << endl;
//        forn (j, 0, n) {
//            char cur = minspan[k - 1 - i][j] + '0';
//            cout << cur << ' ';
//        }
//        cout << endl;
        forn (j, 0, n) {
            buffer[i][j] = minspan[k - 1 - i][n - 1 - j];
        }
//        cout << "line " << i << " after rotate" << endl;
//        forn (j, 0, n) {
//            char cur = minspan[i][j] + '0';
//            cout << cur << ' ';
//        }
//        cout << endl;
//        cout << "line " << k - 1 - i << " after rotate" << endl;
//        forn (j, 0, n) {
//            char cur = minspan[k - 1 - i][j] + '0';
//            cout << cur << ' ';
//        }
//        cout << '\n';
    }

    forn(i, 0, k) {
        forn (j, 0, n) {
            minspan[i][j] = buffer[i][j];
        }
    }
}

class Node {
public:
    ull mask;
    Node *prev = nullptr;
    Node *next[2];
    char from = 0;
    ld val = -1e9;

    Node(ull _mask) {
        next[0] = next[1] = nullptr;
        mask = _mask;
    }
};

class Range {
private:
    int myL, myR;
public:
    Range(int l, int r) {
        myL = l;
        myR = r;

        assert(l <= r);
    }

    char in(int x) {
        return myL <= x && x < myR;
    }
};

class Trellis {
public:
    vec<vec<Node>> nodes = vec<vec<Node>>(n + 1);

    Node &getNode(int i, ull mask) {
        int l = 0;
        int r = size(nodes[i]);
        while (r - l > 1) {
            int mid = (r + l) / 2;

            if (nodes[i][mid].mask <= mask) {
                l = mid;
            } else {
                r = mid;
            }
        }

        return nodes[i][l];
    }

    ull getNextMask(int which, vec<int> &direct, vec<int> &reverse, ull mask, ull from) {
        if (which > 0) {
            return mask & (~(1ul << direct[0]));
        } else if (which < 0) {
            return mask ^ (from << reverse[0]);
        } else {
            return mask;
        }
    }

    vector<int> minus(vector<int> from, vector<int> what) {
        set<int> other(all(what));
        vector<int> result;

        if (other.empty())
            return from;

        fora(i, from) {
            if (other.find(i) == other.end()) {
                result.pb(i);
            }
        }

        return result;
    }

    Trellis() {
        copyg();
//        cout << "MATRIX copied" << endl;
//        forn (i,0,k) {
//            forn(j, 0, n){
//                char cur = minspan[i][j] + '0';
//                cout << cur << ' ';
//            }
//            cout << '\n';
//        }
//        cout << "MATRIX END" << endl;
        gauss();
//        cout << "MATRIX after first" << endl;
//        forn (i,0,k) {
//            forn(j, 0, n){
//                char cur = minspan[i][j] + '0';
//                cout << cur << ' ';
//            }
//            cout << '\n';
//        }
//        cout << "MATRIX END" << endl;
        rotate180();
//        cout << "MATRIX after rotate" << endl;
//        forn (i,0,k) {
//            forn(j, 0, n){
//                char cur = minspan[i][j] + '0';
//                cout << cur << ' ';
//            }
//            cout << '\n';
//        }
//        cout << "MATRIX END" << endl;
        gauss(false);
        rotate180();
//        cout << "MATRIX after second" << endl;
//        forn (i,0,k) {
//            forn(j, 0, n){
//                char cur = minspan[i][j] + '0';
//                cout << cur << ' ';
//            }
//            cout << '\n';
//        }
//        cout << "MATRIX END" << endl;
        vec<Range> activeBits;

        forn(i, 0, k) {
            int startActiveBit = -1;
            int endActiveBit = -1;

            forn(j, 0, n) {
                if (minspan[i][j]) {
                    endActiveBit = j;

                    if (startActiveBit == -1) {
                        startActiveBit = j;
                    }
                }
            }

            activeBits.pb(Range(startActiveBit, endActiveBit));
        }

        vec<vec<int>> activeLines(n + 1);

        forn(i, 0, n) {
            forn(j, 0, k) {
                if (activeBits[j].in(i)) {
                    activeLines[i + 1].pb(j);
                }
            }
        }

//        cout << "ACTIVE" << endl;
//        forn(i, 0, size(activeLines)) {
//            fora(j, activeLines[i]) {
//                cout << j << ' ';
//            }
//            cout << '\n';
//        }
//        cout << "ACTIVE END" << endl;

        nodes[0].pb(Node(0u));

        forn (j, 1, n + 1) {
            ull layerNodesAmount = 1ul << size(activeLines[j]);

            forn(currentNode, 0, layerNodesAmount) {
                ull currentMask = 0;

                forn(l, 0, size(activeLines[j])) {
                    if ((currentNode & (1ul << l)) != 0) {
                        currentMask = currentMask | (1ul << activeLines[j][l]);
                    }
                }

                nodes[j].pb(Node(currentMask));
            }
        }

        forn (i, 0, n) {
            vector<int> direct = minus(activeLines[i], activeLines[i + 1]);
            vector<int> reverse = minus(activeLines[i + 1], activeLines[i]);
            int diff = size(activeLines[i]) - size(activeLines[i + 1]);

            foraa(node, nodes[i]) {
                ull mask = node.mask;
//                cout << "MASK - " << mask << endl;

                forn(to, 0, 2) {
                    ull nextMask = getNextMask(diff, direct, reverse, mask, to);
//                    cout << "NEXTMASK - " << nextMask << endl;
                    Node &nextNode = getNode(i + 1, nextMask);
//                    cout << "NEXT_NODE_MASK - " << nextNode.mask << endl;
                    ull edgeValue = 0;

                    forn(j, 0, k) {
                        ull bestMask = max(mask, nextMask);
                        edgeValue = edgeValue ^ (minspan[j][i] & ((bestMask >> j) % 2));
//                        char cur = edgeValue + '0';
//                        cout << "EDGEVALUE - " << cur << endl;
                    }

                    node.next[edgeValue] = &nextNode;
                }
            }
        }
    }

    void decode() {
        nodes[0][0].val = 0;
        forn(i, 1, n + 1) {
            foraa(node, nodes[i]) {
                node.val = -1e9;
                node.from = 0;
                node.prev = nullptr;
            }
        }

        forn(j, 0, n) {
            foraa(node, nodes[j]) {
                forn(edge, 0, 2) {
                    ld val;

                    if (edge == 0) {
                        val = 1;
                    } else {
                        val = -1;
                    }

                    Node *next = node.next[edge];

                    if (next == nullptr)
                        continue;

                    ld newVal = node.val + val * noised[j];

                    if (newVal > next->val) {
                        next->from = edge;
                        next->prev = &node;
                        next->val = newVal;
                    }
                }
            }
        }

        Node &node = nodes[n][0];

        forb(j, n - 1, 0) {
            decoded[j] = node.from;
            if (node.prev != nullptr)
                node = *node.prev;
        }
    }
};

int main() {
    freopen("input.txt", "r", stdin);
    freopen("output.txt", "w", stdout);
    //freopen(TASK".in", "r", stdin);
    //freopen(TASK".out", "w", stdout);
    iostream::sync_with_stdio(0);
    cin.tie(0);
    cout.tie(0);
    cin >> n >> k;

    forn(i, 0, k) {
        forn(j, 0, n) {
            cin >> g[i][j];
            g[i][j] -= '0';
        }
    }

//    cout << "calculating trellis" << endl;
    Trellis trellis = Trellis();

    forn(i, 0, n + 1) {
        cout << size(trellis.nodes[i]) << ' ';
    }
    cout << endl;

    string s;

    while (cin >> s) {
        if (s == "Encode") {
            forn(i, 0, k) {
                cin >> info[i];
                info[i] -= '0';
            }

            forn(i, 0, n)encoded[i] = 0;

            encode();

            forn(i, 0, n) {
                encoded[i] += '0';
                cout << encoded[i] << ' ';
            }

            cout << '\n';
        } else if (s == "Decode") {
            forn(i, 0, n) {
                cin >> noised[i];
            }

            forn(i, 0, n)decoded[i] = 0;

            trellis.decode();

            forn(i, 0, n) {
                decoded[i] += '0';
                cout << decoded[i] << ' ';
            }
            cout << '\n';
        } else if (s == "Simulate") {
            ld probability;
            int tries, errors, currentTry = 1;

            cin >> probability >> tries >> errors;

            int currentErrors = 0;
            ld deviation = sqrtl((1.0 / (((1.0 * k) / n) * powl(10.0, probability / 10.0))) / 2.0);
//            cout << deviation << '\n';
            for (; currentTry <= tries; currentTry++) {
//                if (currentTry % 100 == 0)
//                    cout << currentTry << endl;
                forn(i, 0, n)encoded[i] = 0;
                forn(i, 0, n)decoded[i] = 0;
                generateRandom();
//                cout << "INFO VECTOR\n";
//                forn (i, 0, k) {
//                    char cur = info[i] + '0';
//                    cout << cur << ' ';
//                }
//                cout << endl;
                encode();
//                cout << "ENCODED VECTOR\n";
//                forn (i, 0, n) {
//                    char cur = encoded[i] + '0';
//                    cout << cur << ' ';
//                }
//                cout << endl;
                addNoise(deviation);
//                cout << "NOISED VECTOR\n";
//                forn (i, 0, n) {
//                    cout << noised[i] << ' ';
//                }
//                cout << endl;
                trellis.decode();
//                cout << "DECODED VECTOR\n";
//                forn (i, 0, n) {
//                    char cur = decoded[i] + '0';
//                    cout << cur << ' ';
//                }
//                cout << endl;
                currentErrors += check();

                if (currentErrors >= errors)
                    break;
            }

            currentTry = min(currentTry, tries);

            cout << 1.0 * currentErrors / currentTry << '\n';
        }
    }
    return 0;
}