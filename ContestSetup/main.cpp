#define _CRT_SECURE_NO_WARNINGS
#include <cassert>
#include <cctype>
#include <cerrno>
#include <cfloat>
#include <ciso646>
#include <climits>
#include <clocale>
#include <cmath>
#include <csetjmp>
#include <csignal>
#include <cstdarg>
#include <cstddef>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <ccomplex>
#include <cfenv>
#include <cinttypes>
#include <cstdalign>
#include <cstdbool>
#include <cstdint>
#include <ctgmath>
#include <cwchar>
#include <cwctype>
#include <algorithm>
#include <bitset>
#include <complex>
#include <deque>
#include <exception>
#include <fstream>
#include <functional>
#include <iomanip>
#include <ios>
#include <iosfwd>
#include <iostream>
#include <istream>
#include <iterator>
#include <limits>
#include <list>
#include <locale>
#include <map>
#include <memory>
#include <new>
#include <numeric>
#include <ostream>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <stdexcept>
#include <streambuf>
#include <string>
#include <typeinfo>
#include <utility>
#include <valarray>
#include <vector>
#include <array>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <forward_list>
#include <future>
#include <initializer_list>
#include <mutex>
#include <random>
#include <ratio>
#include <regex>
#include <scoped_allocator>
#include <system_error>
#include <thread>
#include <tuple>
#include <typeindex>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>

namespace abesse
{
	template<typename T>
	T gcd(T a, T b)
	{
		return b ? gcd(b, a % b) : a;
	}

	template<typename T>
	T lcm(T a, T b)
	{
		return (a * b) / gcd(a, b);
	}

	bool is_prime(unsigned long long a)
	{
		for (size_t i = 2; i * i <= a; i++)
		{
			if (a % i == 0)
				return 0;
		}
		return a == 1;
	}

	/*
	* cantor_numeration(x, y) == cantor_numeration(y, x)
	* if {a, b) != {c, d} ==> cantor_numeration(a, b) != cantor_numeration(c, d)
	*/
	inline long long cantor_numeration(long long x, long long y)
	{
		return (1 + ((x + y) / 2) * (((x + y) / 2) + 1) + ((x + y) % 2) * ((x + y + 1) / 2)) + abs(x - y) / 2;
	}

	template<size_t MAXN>
	class Erato
	{
		int erato[MAXN];
	public:
		Erato()
		{
			erato[1] = 1;
			for (size_t i = 2; i < MAXN; i++)
			{
				for (size_t j = i; j < MAXN; j += i)
					if (erato[j] == 0)
						erato[j] = i;
			}
		}

		bool is_prime(int x)
		{
			return (x == erato[x]);
		}

		int min_pr_div(int x)
		{
			return erato[x];
		}

		void get_pr_divs(unsigned long long x, std::vector<unsigned long long>& divs)
		{
			for (size_t i = 2; i * i <= x; i++)
			{
				if (this->is_prime(i))
				{
					if (x % i == 0)
						divs.push_back(i);
					while (x % i == 0)
						x /= i;
				}
			}
			if (x != 1)
				divs.push_back(x);
		}
	};

	template<size_t MAXN>
	class Mebius
	{
		int mu_[MAXN];
		Erato<MAXN> erato;
	public:
		Mebius()
		{
			mu[1] = 1;
			for (size_t i = 2; i < MAXN; ++i)
			{
				size_t p = erato[i];
				if (p != erato[i / p])
				{
					mu_[i] = -mu_[i / p];
				}
				else
				{
					mu_[i] = 0;
				}
			}
		}

		int mu(int x)
		{
			return mu_[x];
		}

		bool is_prime(int x)
		{
			return erato.is_prime(x);
		}

		//Minimum prime divisor of x
		int min_pr_div(int x)
		{
			return erato.min_pr_div(x);
		}

		void get_pr_divs(unsigned long long x, std::vector<unsigned long long>& divs)
		{
			return erato.get_pr_divs(x, divs);
		}
	};

	template<typename T>
	class Diffarray
	{
	public:
		std::vector<T> dif;
		Diffarray(std::vector<T> const& v)
		{
			dif.resize(v.size(), 0);
			for (auto i = 0; i != v.size(); i++)
			{
				dif[i] = (i != 0 ? v[i] - v[i - 1] : v[i]);
			}
		}

		std::vector<T> recover()
		{
			std::vector<T> rec(dif.size(), 0);
			for (size_t i = 0; i < rec.size(); i++)
			{
				rec[i] = (i != 0 ? rec[i - 1] + dif[i] : dif[i]);
			}
			return move(rec);
		}

		//add value to elements of array in segment [l, r)
		void addval(unsigned int l, unsigned int r, T val)
		{
			dif[l] += val;
			if (r < dif.size())
				dif[r] -= val;
		}
	};

	template<typename T>
	class PreffSum
	{
	public:
		std::vector<T> preffsum;
		PreffSum(std::vector<T> const& v)
		{
			preffsum.resize(v.size(), 0);
			for (auto i = 0; i != v.size(); i++)
			{
				preffsum[i] = (i != 0 ? v[i] + preffsum[i - 1] : v[i]);
			}
		}

		std::vector<T> recover()
		{
			std::vector<T> rec(preffsum.size(), 0);
			for (size_t i = 0; i < rec.size(); i++)
			{
				rec[i] = (i != 0 ? preffsum[i] - preffsum[i - 1] : preffsum[i]);
			}
			return move(rec);
		}
		//sum of array elems in segment [l, r)
		T get_sum(unsigned int l, unsigned int r)
		{
			return preffsum[r - 1] - preffsum[l - 1];
		}
	};

	template<class T>
	class SegTree
	{
		T defVal;
		std::vector<T> tree;
		T(*op)(T, T);
		int n;
	public:
		SegTree(std::vector<T> const& v, T defVal, T(*op_)(T, T))
			: defVal(defVal), tree(std::vector<T>(count_size(v.size()), defVal)), op(op_), n(tree.size() / 2)
		{
			for (int i = 0; i < v.size(); ++i)
			{
				tree[i + n] = v[i];
			}
			build();
		}

		void build()
		{
			for (int i = n - 1; i > 0; --i)
			{
				tree[i] = op(tree[i << 1], tree[i << 1 | 1]);
			}
		}
		T query(int l, int r)
		{
			T res = defVal;
			for (l += n, r += n; l < r; l >>= 1, r >>= 1)
			{
				if (l & 1)
					res = op(res, tree[l++]);

				if (r & 1)
					res = op(res, tree[--r]);
			}

			return res;
		}
		void update(int i, T val)
		{
			i += n;
			for (tree[i] = val; i > 1; i >>= 1)
			{
				tree[i >> 1] = op(tree[i], tree[i ^ 1]);
			}
		}
	private:
		static unsigned long long count_size(size_t x)
		{
			unsigned long long ans = 1;
			while (ans < x)
				ans <<= 1;
			return ans << 1;
		}

	};

	template<typename T>
	class SparseTable
	{
		std::vector<std::vector<T> > st;
		T(*op)(T, T);
	public:
		SparseTable(std::vector<T> const& v, T(*op_)(T, T)) : st(ceil(log2(v.size())) + 1, std::vector<T>(v.size())), op(op_)
		{
			int h = floor(log2(v.size()));

			for (int j = 0; j < v.size(); j++)
				st[0][j] = v[j];

			for (int i = 1; i <= h; i++)
				for (int j = 0; j + (1 << i) <= v.size(); j++)
					st[i][j] = op(st[i - 1][j], st[i - 1][j + (1 << (i - 1))]);
		}

		//Compute for range [l, r)
		int query(int l, int r)
		{
			int p = this->log2_internal(r - l);
			return op(st[p][l], st[p][r - (1 << p)]);
		}

		int log2_internal(int x)
		{
#if defined(_MSC_VER)
			return 31 - __lzcnt(x);
#else
			return 31 - __builtin_clz(x);
#endif
		}
	};

	template <typename T>
	class DisjointSparseTable
	{
	public:
		explicit DisjointSparseTable(std::vector<T> arr, T(*op_)(T, T), T defval_) : op(op_), defval(defval_)
		{
			// Find the highest cnt such that pow2 = 2^cnt >= x
			int pow2 = 1, cnt = 0;
			for (; pow2 < arr.size(); pow2 *= 2, ++cnt);

			arr.resize(pow2, defval);
			sum.resize(cnt, std::vector<T>(pow2));

			for (int level = 0; level < sum.size(); ++level)
			{
				for (int block = 0; block < 1 << level; ++block)
				{
					// The first half of the block contains suffix sums,
					// the second half contains prefix sums
					const auto start = block << (sum.size() - level);
					const auto end = (block + 1) << (sum.size() - level);
					const auto middle = (end + start) / 2;

					auto val = arr[middle];
					sum[level][middle] = val;
					for (int x = middle + 1; x < end; ++x)
					{
						val = op(val, arr[x]);
						sum[level][x] = val;
					}

					val = arr[middle - 1];
					sum[level][middle - 1] = val;
					for (int x = middle - 2; x >= start; --x)
					{
						val = op(val, arr[x]);
						sum[level][x] = val;
					}
				}
			}
		}
		/*! Returns Monoid sum over range [l, r)*/
		T query(int l, int r) const
		{
			assert(l < r);
			// Convert half open interval to closed interval
			--r;
			if (r == l - 1)
			{
				return defval;
			}
			if (l == r)
			{
				return sum.back()[l];
			}
			// Position of the leftmost different bit from the right
#if defined(_MSC_VER)
			const auto pos_diff = (sizeof(long long) * CHAR_BIT) - 1 - __lzcnt64(l ^ r);
#else
			const auto pos_diff = (sizeof(long long) * CHAR_BIT) - 1 - __builtin_clzll(l ^ r);
#endif
			const auto level = sum.size() - 1 - pos_diff;
			return op(sum[level][l], sum[level][r]);
		}
	private:
		std::vector<std::vector<T> > sum;
		T(*op)(T, T);
		T defval;
	};

	class DSU
	{
	public:
		DSU(int n)
		{
			parent = new int[n];
			sz = new int[n];
			for (int i = 0; i < n; ++i)
			{
				parent[i] = i;
				sz[i] = 1;
			}
		}

		~DSU()
		{
			delete[] parent;
			delete[] sz;
		}

		void union_sets(int u, int v)
		{
			u = find_parent(u);
			v = find_parent(v);
			if (sz[u] > sz[v]) swap(u, v);
			parent[u] = v;
			sz[v] += sz[u];
		}

		bool same_set(int u, int v)
		{
			return find_parent(u) == find_parent(v);
		}

		int find_parent(int u)
		{
			if (parent[u] == u)  return u;
			return parent[u] = find_parent(parent[u]);
		}

		void swap(int& a, int& b)
		{
			int c = a;
			a = b;
			b = c;
		}

		int* parent;
		int* sz;
	private:
	};

	class BigInteger
	{
	private:
		std::string number;
		bool sign;
	public:

		BigInteger() // empty constructor initializes zero
		{
			number = "0";
			sign = false;
		}
		//-------------------------------------------------------------
		BigInteger(std::string s) // "string" constructor
		{
			if (isdigit(s[0])) // if not signed
			{
				setNumber(s);
				sign = false; // +ve
			}
			else
			{
				setNumber(s.substr(1));
				sign = (s[0] == '-');
			}
		}
		//-------------------------------------------------------------
		BigInteger(std::string s, bool sin) // "string" constructor
		{
			setNumber(s);
			setSign(sin);
		}
		//-------------------------------------------------------------
		BigInteger(int n) // "int" constructor
		{
			std::stringstream ss;
			std::string s;
			ss << n;
			ss >> s;


			if (isdigit(s[0])) // if not signed
			{
				setNumber(s);
				setSign(false); // +ve
			}
			else
			{
				setNumber(s.substr(1));
				setSign(s[0] == '-');
			}
		}
		//-------------------------------------------------------------
		void setNumber(std::string s)
		{
			number = s;
		}
		//-------------------------------------------------------------
		const std::string& getNumber() // retrieves the number
		{
			return number;
		}
		//-------------------------------------------------------------
		void setSign(bool s)
		{
			sign = s;
		}
		//-------------------------------------------------------------
		const bool& getSign()
		{
			return sign;
		}
		//-------------------------------------------------------------
		// returns the absolute value
		BigInteger absolute()
		{
			return BigInteger(getNumber()); // +ve by default
		}
		//-------------------------------------------------------------
		void operator = (BigInteger b)
		{
			setNumber(b.getNumber());
			setSign(b.getSign());
		}
		//-------------------------------------------------------------
		bool operator == (BigInteger b)
		{
			return equals((*this), b);
		}
		//-------------------------------------------------------------
		bool operator != (BigInteger b)
		{
			return !equals((*this), b);
		}
		//-------------------------------------------------------------
		bool operator > (BigInteger b)
		{
			return greater((*this), b);
		}
		//-------------------------------------------------------------
		bool operator < (BigInteger b)
		{
			return less((*this), b);
		}
		//-------------------------------------------------------------
		bool operator >= (BigInteger b)
		{
			return equals((*this), b)
				|| greater((*this), b);
		}
		//-------------------------------------------------------------
		bool operator <= (BigInteger b)
		{
			return equals((*this), b)
				|| less((*this), b);
		}
		//-------------------------------------------------------------
		// increments the value, then returns its value
		BigInteger& operator ++() // prefix
		{
			(*this) = (*this) + 1;
			return (*this);
		}
		//-------------------------------------------------------------
		// returns the value, then increments its value
		BigInteger operator ++(int) // postfix
		{
			BigInteger before = (*this);

			(*this) = (*this) + 1;

			return before;
		}
		//-------------------------------------------------------------
		// decrements the value, then return it
		BigInteger& operator --() // prefix
		{
			(*this) = (*this) - 1;
			return (*this);

		}
		//-------------------------------------------------------------
		// return the value, then decrements it
		BigInteger operator --(int) // postfix
		{
			BigInteger before = (*this);

			(*this) = (*this) - 1;

			return before;
		}
		//-------------------------------------------------------------
		BigInteger operator + (BigInteger b)
		{
			BigInteger addition;
			if (getSign() == b.getSign()) // both +ve or -ve
			{
				addition.setNumber(add(getNumber(), b.getNumber()));
				addition.setSign(getSign());
			}
			else // sign different
			{
				if (absolute() > b.absolute())
				{
					addition.setNumber(subtract(getNumber(), b.getNumber()));
					addition.setSign(getSign());
				}
				else
				{
					addition.setNumber(subtract(b.getNumber(), getNumber()));
					addition.setSign(b.getSign());
				}
			}
			if (addition.getNumber() == "0") // avoid (-0) problem
				addition.setSign(false);

			return addition;
		}
		//-------------------------------------------------------------
		BigInteger operator - (BigInteger b)
		{
			b.setSign(!b.getSign()); // x - y = x + (-y)
			return (*this) + b;
		}
		//-------------------------------------------------------------
		BigInteger operator * (BigInteger b)
		{
			BigInteger mul;

			mul.setNumber(multiply(getNumber(), b.getNumber()));
			mul.setSign(getSign() != b.getSign());

			if (mul.getNumber() == "0") // avoid (-0) problem
				mul.setSign(false);

			return mul;
		}
		//-------------------------------------------------------------
		// Warning: Denomerator must be within "long long" size not "BigInteger"
		BigInteger operator / (BigInteger b)
		{
			long long den = toInt(b.getNumber());
			BigInteger div;

			div.setNumber(divide(getNumber(), den).first);
			div.setSign(getSign() != b.getSign());

			if (div.getNumber() == "0") // avoid (-0) problem
				div.setSign(false);

			return div;
		}
		//-------------------------------------------------------------
		// Warning: Denomerator must be within "long long" size not "BigInteger"
		BigInteger operator % (BigInteger b)
		{
			long long den = toInt(b.getNumber());

			BigInteger rem;
			long long rem_int = divide(number, den).second;
			rem.setNumber(toString(rem_int));
			rem.setSign(getSign() != b.getSign());

			if (rem.getNumber() == "0") // avoid (-0) problem
				rem.setSign(false);

			return rem;
		}
		//-------------------------------------------------------------
		BigInteger& operator += (BigInteger b)
		{
			(*this) = (*this) + b;
			return (*this);
		}
		//-------------------------------------------------------------
		BigInteger& operator -= (BigInteger b)
		{
			(*this) = (*this) - b;
			return (*this);
		}
		//-------------------------------------------------------------
		BigInteger& operator *= (BigInteger b)
		{
			(*this) = (*this) * b;
			return (*this);
		}
		//-------------------------------------------------------------
		BigInteger& operator /= (BigInteger b)
		{
			(*this) = (*this) / b;
			return (*this);
		}
		//-------------------------------------------------------------
		BigInteger& operator %= (BigInteger b)
		{
			(*this) = (*this) % b;
			return (*this);
		}
		//-------------------------------------------------------------
		BigInteger& operator [] (int n)
		{
			return *(this + (n * sizeof(BigInteger)));
		}
		//-------------------------------------------------------------
		BigInteger operator -() // unary minus sign
		{
			return (*this) * -1;
		}
		//-------------------------------------------------------------
		operator std::string() // for conversion from BigInteger to string
		{
			std::string signedString = (getSign()) ? "-" : ""; // if +ve, don't print + sign
			signedString += number;
			return signedString;
		}
		//-------------------------------------------------------------
	private:
		bool equals(BigInteger n1, BigInteger n2)
		{
			return n1.getNumber() == n2.getNumber()
				&& n1.getSign() == n2.getSign();
		}

		//-------------------------------------------------------------
		bool less(BigInteger n1, BigInteger n2)
		{
			bool sign1 = n1.getSign();
			bool sign2 = n2.getSign();

			if (sign1 && !sign2) // if n1 is -ve and n2 is +ve
				return true;

			else if (!sign1 && sign2)
				return false;

			else if (!sign1) // both +ve
			{
				if (n1.getNumber().length() < n2.getNumber().length())
					return true;
				if (n1.getNumber().length() > n2.getNumber().length())
					return false;
				return n1.getNumber() < n2.getNumber();
			}
			else // both -ve
			{
				if (n1.getNumber().length() > n2.getNumber().length())
					return true;
				if (n1.getNumber().length() < n2.getNumber().length())
					return false;
				return n1.getNumber().compare(n2.getNumber()) > 0; // greater with -ve sign is LESS
			}
		}
		//-------------------------------------------------------------
		bool greater(BigInteger n1, BigInteger n2)
		{
			return !equals(n1, n2) && !less(n1, n2);
		}

		//-------------------------------------------------------------
		// adds two strings and returns their sum in as a string
		std::string add(std::string number1, std::string number2)
		{
			std::string add = (number1.length() > number2.length()) ? number1 : number2;
			char carry = '0';
			int differenceInLength = abs((int)(number1.size() - number2.size()));

			if (number1.size() > number2.size())
				number2.insert(0, differenceInLength, '0'); // put zeros from left

			else// if(number1.size() < number2.size())
				number1.insert(0, differenceInLength, '0');

			for (int i = static_cast<int>(number1.size()) - 1; i >= 0; --i)
			{
				add[i] = ((carry - '0') + (number1[i] - '0') + (number2[i] - '0')) + '0';

				if (i != 0)
				{
					if (add[i] > '9')
					{
						add[i] -= 10;
						carry = '1';
					}
					else
					{
						carry = '0';
					}
				}
			}
			if (add[0] > '9')
			{
				add[0] -= 10;
				add.insert(0, 1, '1');
			}
			return add;
		}

		//-------------------------------------------------------------
		// subtracts two strings and returns their sum in as a string
		std::string subtract(std::string number1, std::string number2)
		{
			std::string sub = (number1.length() > number2.length()) ? number1 : number2;
			int differenceInLength = abs((int)(number1.size() - number2.size()));

			if (number1.size() > number2.size())
				number2.insert(0, differenceInLength, '0');

			else
				number1.insert(0, differenceInLength, '0');

			for (int i = static_cast<int>(number1.length()) - 1; i >= 0; --i)
			{
				if (number1[i] < number2[i])
				{
					number1[i] += 10;
					number1[i - 1]--;
				}
				sub[i] = ((number1[i] - '0') - (number2[i] - '0')) + '0';
			}

			while (sub[0] == '0' && sub.length() != 1) // erase leading zeros
				sub.erase(0, 1);

			return sub;
		}

		//-------------------------------------------------------------
		// multiplies two strings and returns their sum in as a string
		std::string multiply(std::string n1, std::string n2)
		{
			if (n1.length() > n2.length())
				n1.swap(n2);

			std::string res = "0";
			for (int i = static_cast<int>(n1.length()) - 1; i >= 0; --i)
			{
				std::string temp = n2;
				int currentDigit = n1[i] - '0';
				int carry = 0;

				for (int j = static_cast<int>(temp.length()) - 1; j >= 0; --j)
				{
					temp[j] = ((temp[j] - '0') * currentDigit) + carry;

					if (temp[j] > 9)
					{
						carry = (temp[j] / 10);
						temp[j] -= (carry * 10);
					}
					else
						carry = 0;

					temp[j] += '0'; // back to string mood
				}

				if (carry > 0)
					temp.insert(0, 1, (carry + '0'));

				temp.append((n1.length() - i - 1), '0'); // as like mult by 10, 100, 1000, 10000 and so on

				res = add(res, temp); // O(n)
			}

			while (res[0] == '0' && res.length() != 1) // erase leading zeros
				res.erase(0, 1);

			return res;
		}

		//-------------------------------------------------------------
		// divides string on long long, returns pair(qutiont, remainder)
		std::pair<std::string, long long> divide(std::string n, long long den)
		{
			long long rem = 0;
			std::string result; result.resize(10000);

			for (int indx = 0, len = static_cast<int>(n.length()); indx < len; ++indx)
			{
				rem = (rem * 10) + (n[indx] - '0');
				result[indx] = static_cast<char>(rem / den) + '0';
				rem %= den;
			}
			result.resize(n.length());

			while (result[0] == '0' && result.length() != 1)
				result.erase(0, 1);

			if (result.length() == 0)
				result = "0";

			return make_pair(result, rem);
		}

		//-------------------------------------------------------------
		// converts long long to string
		std::string toString(long long n)
		{
			std::stringstream ss;
			std::string temp;

			ss << n;
			ss >> temp;

			return temp;
		}

		//-------------------------------------------------------------
		// converts string to long long
		long long toInt(std::string s)
		{
			long long sum = 0;

			for (int i = 0; i < s.length(); i++)
				sum = (sum * 10) + (s[i] - '0');

			return sum;
		}

	};

	class Trie
	{
		struct node
		{
			node* childs[26]{};
			bool word;
			node()
				: word(false)
			{
			}
		};

	public:
		Trie()
			: root(new node())
		{

		}

		~Trie()
		{
			remove_node(root);
		}

		bool add(std::string const& new_word) const
		{
			node* current_node = root;
			for (size_t i = 0; i < new_word.size(); i++)
			{
				if (current_node->childs[new_word[i]] == nullptr)
					current_node->childs[new_word[i]] = new node();

				current_node = current_node->childs[new_word[i]];
			}
			if (current_node->word == true)
				return false;
			return current_node->word = true;
		}

		bool contains(std::string const& new_word) const
		{
			node* current_node = root;
			for (size_t i = 0; i < new_word.size(); i++)
			{
				if (current_node->childs[new_word[i]] == nullptr)
					return false;
				current_node = current_node->childs[new_word[i]];
			}
			if (current_node->word == true)
				return true;
			return false;
		}

	private:
		void remove_node(node*& nd)
		{
			for (size_t i = 0; i < 26; i++)
			{
				if (nd->childs[i] != nullptr)
					remove_node(nd->childs[i]);
			}
			delete nd;
			nd = nullptr;
		}

		node* root;

	};

	class SuffixAutomaton
	{
	public:
		std::vector<std::map<char, int>> edges; // edges[i]  : the labeled edges from node i
		std::vector<int> link;            // link[i]   : the parent of i
		std::vector<int> length;          // length[i] : the length of the longest string in the ith class
		std::string cur_str;
		int last;                    // the index of the equivalence class of the whole string
		int count;

		SuffixAutomaton(std::string const& s)
			: cur_str(s)
			, last(0)
			, count(0)
		{
			// add the initial node
			edges.push_back(std::map<char, int>());
			link.push_back(-1);
			length.push_back(0);
			for (; count < s.size(); count++) {
				// construct r
				edges.emplace_back();
				length.push_back(count + 1);
				link.push_back(0);
				int r = static_cast<int>(edges.size()) - 1;

				// add edges to r and find p with link to q
				int p = last;
				while (p >= 0 && edges[p].find(s[count]) == edges[p].end()) {
					edges[p][s[count]] = r;
					p = link[p];
				}
				if (p != -1) {
					int q = edges[p][s[count]];
					if (length[p] + 1 == length[q]) {
						// we do not have to split q, just set the correct suffix link
						link[r] = q;
					}
					else {
						// we have to split, add q'
						edges.push_back(edges[q]); // copy edges of q
						length.push_back(length[p] + 1);
						link.push_back(link[q]); // copy parent of q
						int qq = static_cast<int>(edges.size()) - 1;
						// add qq as the new parent of q and r
						link[q] = qq;
						link[r] = qq;
						// move short classes pointing to q to point to q'
						while (p >= 0 && edges[p][s[count]] == q) {
							edges[p][s[count]] = qq;
							p = link[p];
						}
					}
				}
				last = r;
			}
		}

		void extend(char c)
		{
			edges.emplace_back();
			length.push_back(++count);
			link.push_back(0);
			int r = static_cast<int>(edges.size()) - 1;

			// add edges to r and find p with link to q
			int p = last;
			while (p >= 0 && edges[p].find(c) == edges[p].end()) {
				edges[p][c] = r;
				p = link[p];
			}
			if (p != -1) {
				int q = edges[p][c];
				if (length[p] + 1 == length[q]) {
					// we do not have to split q, just set the correct suffix link
					link[r] = q;
				}
				else {
					// we have to split, add q'
					edges.push_back(edges[q]); // copy edges of q
					length.push_back(length[p] + 1);
					link.push_back(link[q]); // copy parent of q
					int qq = static_cast<int>(edges.size()) - 1;
					// add qq as the new parent of q and r
					link[q] = qq;
					link[r] = qq;
					// move short classes pointing to q to point to q'
					while (p >= 0 && edges[p][c] == q) {
						edges[p][c] = qq;
						p = link[p];
					}
				}
			}
			last = r;
			cur_str.push_back(c);
		}

		std::string lcs(std::string const& str)
		{
			int v = 0, l = 0, best = 0, bestpos = 0;
			for (int i = 0; i < str.size(); i++) {
				while (v && !edges[v].count(str[i])) {
					v = link[v];
					l = length[v];
				}
				if (edges[v].count(str[i])) {
					v = edges[v][str[i]];
					l++;
				}
				if (l > best) {
					best = l;
					bestpos = i;
				}
			}
			return str.substr(bestpos - best + 1, best);
		}

		bool is_lcs(std::string const& str)
		{
			bool fail = false;
			int n = 0;
			for (int i = 0; i < str.size(); i++) {
				if (edges[n].find(str[i]) == edges[n].end()) {
					fail = true;
					break;
				}
				n = edges[n][str[i]];
			}
			return !fail;
		}
	};
}

using namespace abesse;
using namespace std;

#define LMAX = 9223372036854775807ll;
#define IMAX = 2147483647;
#define LMIN = -9223372036854775808ll;
#define IMIN = -2147483648;

typedef unsigned long long ull;
typedef long long ll;
typedef unsigned int ui;



int main(int argc, char const** argv)
{
	std::ios_base::sync_with_stdio(false);
	std::cin.tie(0);
	std::cout.tie(0);
#ifdef ABESSE
	freopen("in.txt", "r", stdin);
#endif
	std::string s;
	SuffixAutomaton sf("");
	char c;
	while (std::cin >> c)
	{
		std::cin >> s;

		if (c == 'A')
		{
			for (int i = 0; i < s.length(); i++) sf.extend(tolower(s[i]));
		}
		else
		{
			std::transform(s.begin(), s.end(), s.begin(),
				[](unsigned char c) { return std::tolower(c); });
			std::cout << (sf.is_lcs(s) ? "YES\n" : "NO\n");
		}

	}
	return 0;
}

