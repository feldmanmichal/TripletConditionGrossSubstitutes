#include <iostream>
#include <algorithm>
#include <vector>
#include <set>
#include <time.h>
#include <random>
#include <string>
typedef long long ll;
const int OO = 1;
using namespace std;


// library code taken from kactl: https://github.com/kth-competitive-programming/kactl/blob/master/content/numerical/Simplex.h
struct LPSolver {

	typedef double T; // long double, Rational, double + mod<P>...
	typedef vector<int> vi;
	typedef vector<T> vd;
	typedef vector<vd> vvd;

	const T eps = 1e-8, inf = 1e18;
#define MP make_pair
#define ltj(X) if(s == -1 || MP(X[j],N[j]) < MP(X[s],N[s])) s=j
#define rep(i, s, e) for (int i = s; i < e; i++)
#define sz(a) a.size()

	int m, n;
	vi N, B;
	vvd D;

	LPSolver(const vvd& A, const vd& b, const vd& c) :
		m(sz(b)), n(sz(c)), N(n + 1), B(m), D(m + 2, vd(n + 2)) {
		rep(i, 0, m) rep(j, 0, n) D[i][j] = A[i][j];
		rep(i, 0, m) { B[i] = n + i; D[i][n] = -1; D[i][n + 1] = b[i]; }
		rep(j, 0, n) { N[j] = j; D[m][j] = -c[j]; }
		N[n] = -1; D[m + 1][n] = 1;
	}

	void pivot(int r, int s) {
		T *a = D[r].data(), inv = 1 / a[s];
		rep(i, 0, m + 2) if (i != r && abs(D[i][s]) > eps) {
			T *b = D[i].data(), inv2 = b[s] * inv;
			rep(j, 0, n + 2) b[j] -= a[j] * inv2;
			b[s] = a[s] * inv2;
		}
		rep(j, 0, n + 2) if (j != s) D[r][j] *= inv;
		rep(i, 0, m + 2) if (i != r) D[i][s] *= -inv;
		D[r][s] = inv;
		swap(B[r], N[s]);
	}

	bool simplex(int phase) {
		int x = m + phase - 1;
		for (;;) {
			int s = -1;
			rep(j, 0, n + 1) if (N[j] != -phase) ltj(D[x]);
			if (D[x][s] >= -eps) return true;
			int r = -1;
			rep(i, 0, m) {
				if (D[i][s] <= eps) continue;
				if (r == -1 || MP(D[i][n + 1] / D[i][s], B[i])
					< MP(D[r][n + 1] / D[r][s], B[r])) r = i;
			}
			if (r == -1) return false;
			pivot(r, s);
		}
	}

	T solve(vd &x) {
		int r = 0;
		rep(i, 1, m) if (D[i][n + 1] < D[r][n + 1]) r = i;
		if (D[r][n + 1] < -eps) {
			pivot(r, n);
			if (!simplex(2) || D[m + 1][n + 1] < -eps) return -inf;
			rep(i, 0, m) if (B[i] == -1) {
				int s = 0;
				rep(j, 1, n + 1) ltj(D[i]);
				pivot(i, s);
			}
		}
		bool ok = simplex(1); x = vd(n);
		rep(i, 0, m) if (B[i] < n) x[B[i]] = D[i][n + 1];
		return ok ? D[m][n + 1] : inf;
	}

#undef MP
#undef ltj
#undef rep
#undef sz
};

// limit on N, might be in future use
// sanity_stop: used to find bugs.
const int N = 5;
const int sanity_stop = -1;


/*
used to represent one of the 40 constraints, through 3 possible inequalities.
the LPSolver class only accepts inequalities, so to form equalities I use 2 inequalities.
*/
struct constraint {
	vector<double> IE[3], E[3];
	int nxt = 0;
	constraint() {}
	void add(vector<double> ieq, vector<double> eq) {
		IE[nxt] = ieq;
		E[nxt] = eq;
		nxt++;
	}
	pair<vector<double>, vector<double>> get(int i) const {
		return make_pair(IE[i], E[i]);
	}
};

// utility function for printing; convert from s contained in {0,1,2,3,4} to an integer through binary.
int encode(vector<int> s) {
	int res = 0;
	for (auto &i : s)
		res |= (1 << i);
	return res;
}

// used to recursively produce all 40 constraints.
void get_all(int i, vector<int> &triple, vector<int> &sub, vector<constraint> &c) {
	if (i == N) {
		if (triple.size() != 3) return;

		int e = encode(sub);
		int P1 = (1 << triple[0]), P2 = (1 << triple[1]), P3 = (1 << triple[2]);
		constraint con;
		vector<double> ieq(33), eq(33);

		for (int j = 0; j < 33; j++)
			ieq[j] = eq[j] = 0;
		ieq[e + P1] = ieq[e + P2 + P3] = 1;
		ieq[e + P2] = ieq[e + P1 + P3] = -1;
		eq[e + P2] = eq[e + P1 + P3] = 1;
		eq[e + P3] = eq[e + P1 + P2] = -1;
		con.add(ieq, eq);

		for (int j = 0; j < 33; j++)
			ieq[j] = eq[j] = 0;
		ieq[e + P2] = ieq[e + P1 + P3] = 1;
		ieq[e + P3] = ieq[e + P1 + P2] = -1;
		eq[e + P3] = eq[e + P1 + P2] = 1;
		eq[e + P1] = eq[e + P2 + P3] = -1;
		con.add(ieq, eq);

		for (int j = 0; j < 33; j++)
			ieq[j] = eq[j] = 0;
		ieq[e + P3] = ieq[e + P1 + P2] = 1;
		ieq[e + P1] = ieq[e + P2 + P3] = -1;
		eq[e + P1] = eq[e + P2 + P3] = 1;
		eq[e + P2] = eq[e + P1 + P3] = -1;
		con.add(ieq, eq);
		c.push_back(con);
		return;
	}
	get_all(i + 1, triple, sub, c);
	triple.push_back(i);
	get_all(i + 1, triple, sub, c);
	triple.pop_back();
	sub.push_back(i);
	get_all(i + 1, triple, sub, c);
	sub.pop_back();
}

// calls the recursive get_all and returns the result.
vector<constraint> get_all() {
	vector<constraint> c;
	vector<int> triple, sub;
	get_all(0, triple, sub, c);
	return c;
}

// produces the 8 constraints that contradict the triplet inequality in g.
vector<vector<double>> get8() {
	vector<vector<double>> a;
	int m1 = encode({ 2, 0 }), m2 = encode({ 3, 4, 1 });
	for (int v1 : {3, 4}) for (int v2 : {0, 1}) for (int v3 : {0, 1}) {
		vector<double> E(33, 0);
		E[encode({ v1, v2 })] = E[encode({ 2, v1 ^ 3 ^ 4, v3 })] = 1;
		E[m1] = E[m2] = -1;
		E[32] = -1;
		a.push_back(E);
	}
	return a;
}

// transforms the binary encoding of a variable into the variable name, from P({a,b,c,d,e}).
string btot(int binary) {
	string s = "";
	for (int i = 0; i < N; i++)
		if (binary & (1 << i))
			s.push_back(char('a' + i));
	return s;
}

// takes an inequality (vector of size 33) and returns a readable version, where the first 32 cells represent coefficients and the last cell represents the upperbound (<=).
string etot(vector<double> &e) {
	string res = "";
	for (int i = 0; i < 32; i++) {
		if (e[i] != 0) {
			if (e[i] > 0) {
				res += "+";
			}
			res += to_string(e[i]) + " * " + btot(i);
			res += " ";
		}
	}
	res += " <= " + to_string(e[32]);
	return res;
}

// takes an inequality and returns a readable version, where 'e' is the vector of the coefficients, and the result must be <= 'value'
string etot(vector<double> &e, double value) {
	string res = "";
	for (int i = 0; i < 32; i++) {
		if (e[i] != 0) {
			if (e[i] > 0) {
				res += "+";
			}
			res += to_string(e[i]) + " * " + btot(i);
			res += " ";
		}
	}
	res += " <= " + to_string(value);
	return res;
}

// utility function used for tests.
void test() {
	int vcnt, ecnt;
	cout << "number of variables ";
	cin >> vcnt;
	cout << "number of inequalities ";
	cin >> ecnt;

	vector<vector<double>> A;
	vector<double> b;
	A.resize(ecnt);
	b.resize(ecnt);
	for (int i = 0; i < ecnt; i++) {
		A[i].resize(vcnt);
		for (auto &j : A[i]) cin >> j;
		cin >> b[i];
	}
	cout << "maximize over c (size " << vcnt << "): ";
	vector<double> c(vcnt);
	for (auto &i : c) cin >> i;

	cout.precision(9);
	LPSolver LP(A, b, c);
	vector<double> x(vcnt);
	cout << LP.solve(x) << endl;
	for (auto &i : x) cout << i << " "; cout << endl;
}

// 'max_depth' tracks the maximum depth reached in the recursion tree, 'LP_counter' counts the number of times we solve an LP system.
// whenever 'LP_counter' is divisible by 100000, it is printed.
int max_depth = 0;
int LP_counter = 0;

/*
the function that runs on the recursion tree.
con: the vector of 40 constraints.
next_con: the next constraint to add to the system (or: the depth of the current node in the tree)
st: tracks the path from root to the current node (if necessary); the recursion stack.
A: the matrix of coefficients, along with b: the vector. A will contain the basic 8 inequalities + the inequalities found until now,
through the recursion tree. we attempt to satisfy Ax <= b, x >= 0.
c: the vector we attempt to optimize in the LPSolver. since we only care about feasibility,
then for the sake of possible optimizations, c = 0 vector, and is always passed to the LP solver.

print: a parameter used to determine whether the function runs to find any countercase,
or to find all 6-subsets of constraints that block the tree from reaching depth > 6.
it is not supposed to be user-friendly.

returns true iff we found a countercase.

note: there are a lot of printing lines that I used in order to track progress and debug.
*/
bool bruteforce(const vector<constraint> &con, int next_con, vector<int> &st,
	vector<vector<double>> &A, vector<double> &b, vector<double> &c, int print = 1) {
	if (next_con > max_depth) {
		if (print)
			cout << "new maximum depth: " << next_con << endl;
		max_depth = next_con;
	}
	if (next_con == con.size() || next_con == sanity_stop) {
		if (print) {
			// was never printed.
			cout << "counter case:" << endl;
			cout << "inequalities:" << endl;
			for (int i = 0; i < A.size(); i++) {
				cout << etot(A[i], b[i]) << endl;
			}
			cout << "vector x:" << endl;
			vector<double> x;
			LPSolver LP(A, b, c);
			LP.solve(x);
			LP_counter++;
			if (LP_counter % 100000 == 0) {
				cout << LP_counter << endl;
			}
			for (const auto &i : x) cout << i << " "; cout << endl;
			for (int i = 0; i < 32; i++)
				if (x[i] != 0) {
					cout << btot(i) << " = " << x[i] << endl;
				}
			return true;
		}
		vector<double> x;
		LPSolver LP(A, b, c);
		LP.solve(x);
		LP_counter++;
		if (LP_counter % 100000 == 0) {
			cout << LP_counter << endl;
		}
		return x.size() > 0;
	}
	int exist = -1;
	for (int i = 0; i < 3; i++) {
		if (print && next_con <= 2) {
			cout << "new progress in the tree:" << endl;
			for (const auto &j : st) cout << j << " ";
			cout << i << endl;
		}
		auto pa = con[next_con].get(i);
		vector<double> ie = pa.first, e = pa.second;

		A.push_back(ie);
		A.back().pop_back();
		A.push_back(e);
		A.back().pop_back();
		for (auto &j : e) j = -j;
		A.push_back(e);
		A.back().pop_back();

		b.push_back(ie.back());
		b.push_back(0), b.push_back(0);

		if (!print) {
			st.push_back(i);
			if (bruteforce(con, next_con + 1, st, A, b, c, print))
				return true;
			st.pop_back();
		}
		else {
			LPSolver LP(A, b, c);
			vector<double> x;
			LP.solve(x);
			LP_counter++;
			if (LP_counter % 100000 == 0) {
				cout << LP_counter << endl;
			}
			if (x.size()) {
				st.push_back(i);
				if (bruteforce(con, next_con + 1, st, A, b, c, print))
					return true;
				st.pop_back();
			}
			else {
				exist = i;
			}
		}
		A.pop_back(), A.pop_back(), A.pop_back();
		b.pop_back(), b.pop_back(), b.pop_back();
	}
	return false;
}

// 'good_sub' counts all the subsets that block the tree (for the next function)
// 'the_sub' is a vector of the subsets.

// recursively sends all subsets of constraints (of size 'size') to find which of them block the tree.
// when size = 5, there are no results. when size = 6, there are two results.
void trysubset(const vector<constraint> &con, int next_con, vector<int> &st,
	vector<vector<double>> &A, vector<double> &b, vector<double> &c, int size,
	vector<int> &sub, ll &good_sub, vector<vector<int>> &the_sub) {
	if (size == sub.size()) {
		vector<constraint> tmp;
		for (auto &i : sub)
			tmp.push_back(con[i]);

		if (!bruteforce(tmp, 0, st, A, b, c, 0)) {
			good_sub++;
			the_sub.push_back(sub);
		}
		A.resize(8);
		b.resize(8);
		st.clear();
		return;
	}
	if (next_con == con.size())
		return;

	sub.push_back(next_con);
	trysubset(con, next_con + 1, st, A, b, c, size, sub, good_sub, the_sub);
	sub.pop_back();
	trysubset(con, next_con + 1, st, A, b, c, size, sub, good_sub, the_sub);
}

// returns all subsets of given size 'S' of constraints which are enough to block the recursion tree.
// warning: it may be alot for sizes like 7+.
vector<vector<int>> subset_iteration(const vector<constraint> &con, vector<vector<double>> &A, vector<double> &b, int S) {
	vector<int> st, sub;
	vector<double> c(32, 0);
	ll good_sub = 0;
	vector<vector<int>> result;
	trysubset(con, 0, st, A, b, c, S, sub, good_sub, result);
	return result;
}

// attempts to find any countercase to the lemma. this never finds a countercase...
// (it is deterministic, but I use a randomized order of constraints to cut branches of the recursion tree).
// still, here is the implementation. you may set the flag 'print' to true to see some printing lines,
// that unfortunately only mean anything to me, for debugging reasons.
void find_countercase(const vector<constraint> &con, vector<vector<double>> &A, vector<double> &b, bool print) {
	vector<int> st;
	vector<double> c(32, 0);
	if (bruteforce(con, 0, st, A, b, c, print ? 1 : 0)) {
		cout << "found a countercase!\n...which shouldn't happen. please contact me :)" << endl;
		return;
	}
	cout << "didn't find any countercase to the lemma...\n";
}

int main() {
	ios::sync_with_stdio(0), cin.tie(0);
	// I generally use a deterministic seed, so that it's possible to reproduce results through multiple runs.
	// I scramble the 40 constraints randomly, to hopefully reduce the runtime of some recursions.
	// 527 was a nice seed:
	// for the first bruteforce, it takes ~2.2e6 LP iterations.
	// for the second bruteforce, it takes ~7.7e6 LP iterations (to find all 6-subsets).
	srand(527);

	vector<constraint> all = get_all();
	random_shuffle(all.begin(), all.end());

	/*
	this generates the 8 initial constraints, already in the form of the matrix A of coefficients.
	we want to look for solutions x satisfying Ax <= b, and c^T x is maximized. we don't care about maximization, so c = 0
	*/
	vector<vector<double>> A;
	vector<double> b;
	vector<double> c(32, 0);

	vector<vector<double>> basic8 = get8();
	for (auto &i : basic8) {
		A.push_back(i);
		A.back().pop_back();
		b.push_back(i.back());
	}

	string input = "";
	cout << "enter 'C' if you want to run the code that attempts to find any countercase to the lemma\n" <<
		"enter 'S' if you want to find subsets of a certain size that block the recursion tree\n" <<
		"(if I had no bugs, the minimum size is 6)\n";
	cin >> input;
	while (input != "C" && input != "S") {
		cout << "invalid input... try again\n";
		cin >> input;
	}

	if (input == "C") {
		cout << "going to run the bruteforce. do you want to see some printing lines in the meantime?\n" <<
			"(explanation: only means anything to the developer)\n" <<
			"enter 'Y' for yes, anything else for no\n";

		cin >> input;
		find_countercase(all, A, b, input == "Y");
		return 0;
	}
	// subset search
	cout << "enter the size of subsets you want to iterate on\n" <<
		"(warning: this will iterate over all subsets of given size, which is supposed to be difficult.\n" <<
		"nevertheless, it appears the minimum size which gives results is 6, and it takes about a few minutes to run)\n";
	int size;
	cin >> size;
	vector<vector<int>> subsets = subset_iteration(all, A, b, size);
	cout << "found " << subsets.size() << " subsets.\n";
	int next = 0;
	while (next < subsets.size()) {
		cout << "until now, listed " << next << " of these subsets. how many more to list?";
		int l;
		cin >> l;
		l = max(0, min(l, (int)subsets.size() - next));
		for (int i = next; i < next + l; i++) {
			for (const auto &j : subsets[i]) {
				// decrypt my syntax to readable syntax; find what is s and who are i,j,k
				int all_have[5] = { 0,0,0,0,0 };
				string s, ijk;
				auto pa = all[j].get(0).first;
				int count = 0;
				for (int index = 0; index < 32; index++)
					if (pa[index] != 0) {
						string tmp = btot(index);
						count++;
						for (auto &c : tmp)
							all_have[c - 'a']++;
					}
				for (int index = 0; index < 5; index++)
					if (all_have[index] == count)
						s.push_back(char('a' + index));
					else if (all_have[index] > 0)
						ijk.push_back(char('a' + index));
				cout << "i,j,k = " << ijk << ", s = " << s << '\n';
			}

		}
		next += l;
	}
	return 0;

	/*
	vector<int> st, sub;

	// the bruteforce to find any countercase.
	if (!bruteforce(all, 0, st, A, b, c)) {
	cout << "never reached a leaf -> there is no countercase." << endl;
	return 0;
	}

	// comment the above call to run the following:
	// find all subsets of constraints, of size 'size' that block the recursion tree at depth 'size'.
	// the printing format is somewhat complex, but the subsets can be derived from it:

	// every two consecutive lines in a system are 2 inequalities. ignore the inequalities; consider only the variables involved per 2 lines.
	int size = 5;
	cout << "for subsets of size: " << size << endl;
	trysubset(all, 0, st, A, b, c, size, sub);
	cout << "good subsets: " << good_sub << endl;
	for (const auto &i : the_sub) {
	for (const auto &j : i) cout << j << " "; cout << endl;
	for (const auto &j : i) {
	auto pa = all[j].get(0);
	cout << etot(pa.first) << endl << etot(pa.second) << endl;
	}
	}
	*/
}