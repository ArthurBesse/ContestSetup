#define _CRT_SECURE_NO_WARNINGS
#define _USE_MATH_DEFINES

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
#include <cfenv>
#include <cinttypes>
#include <cstdint>
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
#include <type_traits>
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
	template<typename T, template<typename> class U>
	struct is_instantiation_of : std::false_type { };

	template<typename T, template<typename> class U>
	struct is_instantiation_of<U<T>, U> : std::true_type { };
	
	#ifdef ABESSE
	#define REPORT_TIME { auto start = std::chrono::steady_clock::now();
	#define END_REPORT_TIME_WITH_ID(report_id) std::cout << std::endl << "Report id: " << report_id << ": Elapsed(ns) = " << since(start).count() << std::endl; }
	#define END_REPORT_TIME std::cout << std::endl << "Elapsed(s) = " << static_cast<long double>(since(start).count()) / 1000000000.0 << std::endl; }
	#else
	#define REPORT_TIME
	#define END_REPORT_TIME_WITH_ID(report_id)
	#define END_REPORT_TIME
	#endif

	template <typename result_t = std::chrono::nanoseconds, typename clock_t = std::chrono::steady_clock, typename duration_t = std::chrono::nanoseconds>
	auto since(std::chrono::time_point<clock_t, duration_t> const& start)
	{
		return std::chrono::duration_cast<result_t>(clock_t::now() - start);
	}

	template<typename T>
	T gcd(T a, T b)
	{
		return b ? gcd(b, a % b) : a;
	}

	template<typename T>
	std::tuple<T, std::make_signed_t<T>, std::make_signed_t<T> > gcdex(T a, T b)
	{
		static_assert(true == std::is_signed<T>::value, "Input type for gcdex should be signed");
		if (a == 0)  return std::make_tuple(b, 0, 1);
		std::tuple<T, std::make_signed_t<T>, std::make_signed_t<T> > d = gcdex(b % a, a);
		return std::make_tuple(std::get<0>(d), std::get<2>(d) - (b / a) * std::get<1>(d), std::get<1>(d));
	}

	template<typename T>
	T lcm(T a, T b)
	{
		return (a * b) / gcd(a, b);
	}

	template<typename T>
	T fast_log2(T x)
	{
		constexpr size_t bit_count = sizeof(T) * CHAR_BIT;
#if defined(_MSC_VER)
		if constexpr (std::is_same<T, unsigned __int64>::value)
			return bit_count - 1 - __lzcnt64(x);
		else if constexpr (std::is_same<T, unsigned int>::value)
			return bit_count - 1 - __lzcnt(x);
		else if constexpr (std::is_same<T, unsigned short>::value)
			return bit_count - 1 - __lzcnt16(x);
		else
			static_assert(true == std::is_same<T, unsigned __int64>::value
				|| true == std::is_same<T, unsigned int>::value
				|| true == std::is_same<T, unsigned short>::value
				, "Invalid type has been specified for fast_log2()");
#else
		if constexpr (std::is_same<T, unsigned long long>::value)
			return bit_count - 1 - __builtin_clzll(x);
		else if constexpr (std::is_same<T, unsigned long>::value)
			return bit_count - 1 - __builtin_clzl(x);
		else if constexpr (std::is_same<T, unsigned int>::value)
			return bit_count - 1 - __builtin_clz(x);
		else
			static_assert(true == std::is_same<T, unsigned long long>::value
				|| true == std::is_same<T, unsigned long>::value
				|| true == std::is_same<T, unsigned int>::value
				, "Invalid type has been specified for fast_log2()");
#endif		
	}

	bool is_prime(unsigned long long a)
	{
		for (size_t i = 2; i * i <= a; i++)
		{
			if (a % i == 0)
				return 0;
		}
		return a != 1;
	}

	//Next larger integer with same binary weight
	unsigned int snoob(unsigned int x)
	{
		unsigned int rightOne;
		unsigned int nextHigherOneBit;
		unsigned int rightOnesPattern;

		unsigned int next = 0;

		if (x)
		{
			rightOne = x & -(signed)x;
			nextHigherOneBit = x + rightOne;
			rightOnesPattern = x ^ nextHigherOneBit;
			rightOnesPattern = (rightOnesPattern) / rightOne;
			rightOnesPattern >>= 2;
			next = nextHigherOneBit | rightOnesPattern;
		}

		return next;
	}

	/*
	* commutative_cantor_numeration(x, y) == commutative_cantor_numeration(y, x)
	* if {a, b) != {c, d} ==> commutative_cantor_numeration(a, b) != commutative_cantor_numeration(c, d)
	*/
	inline long long commutative_cantor_numeration(long long x, long long y)
	{
		return (1 + ((x + y) / 2) * (((x + y) / 2) + 1) + ((x + y) % 2) * ((x + y + 1) / 2)) + abs(x - y) / 2;
	}

	template<typename T>
	struct ABMin
	{
		static T compute(T const& first, T const& second)
		{
			return std::min(first, second);
		}
		static T DefVal()
		{
			return std::numeric_limits<T>::max();
		}
	};

	template<typename T>
	struct ABMax
	{
		static T compute(T const& first, T const& second)
		{
			return std::max(first, second);
		}
		static T DefVal()
		{
			return std::numeric_limits<T>::min();
		}
	};

	template<typename T>
	struct ABSum
	{
		static T compute(T const& first, T const& second)
		{
			return first + second;
		}

		static T DefVal()
		{
			return T();
		}
	};

	template <typename T>
	class Modular;

	template <typename T>
	class Modular
	{
	public:
		using Type = typename std::decay<decltype(T::value)>::type;

		constexpr Modular() : value() {}
		template <typename U>
		Modular(const U& x)
		{
			value = normalize(x);
		}

		template <typename U>
		static Type normalize(const U& x)
		{
			Type v;
			if (-mod() <= x && x < mod()) v = static_cast<Type>(x);
			else v = (static_cast<Type>(x)) % mod();
			if (v < 0) v += mod();
			return v;
		}


		const Type& operator()() const { return value; }
		template <typename U>
		explicit operator U() const { return static_cast<U>(value); }
		constexpr static Type mod() { return T::value; }

		Modular& operator+=(const Modular& other) { if ((value += other.value) >= mod()) value -= mod(); return *this; }
		Modular& operator-=(const Modular& other) { if ((value -= other.value) < 0) value += mod(); return *this; }
		template <typename U> Modular& operator+=(const U& other) { return *this += Modular(other); }
		template <typename U> Modular& operator-=(const U& other) { return *this -= Modular(other); }
		Modular& operator++() { return *this += 1; }
		Modular& operator--() { return *this -= 1; }
		Modular operator++(int) { Modular result(*this); *this += 1; return result; }
		Modular operator--(int) { Modular result(*this); *this -= 1; return result; }
		Modular operator-() const { return Modular(-value); }
		bool is_zero() { return value == 0; }

		template <typename U = T>
		typename std::enable_if<std::is_same<typename Modular<U>::Type, int>::value, Modular>::type& operator*=(const Modular& rhs)
		{
#ifndef _WIN32
			uint64_t x = static_cast<int64_t>(value) * static_cast<int64_t>(rhs.value);
			uint32_t xh = static_cast<uint32_t>(x >> 32), xl = static_cast<uint32_t>(x), d, m;
			asm(
				"divl %4; \n\t"
				: "=a" (d), "=d" (m)
				: "d" (xh), "a" (xl), "r" (mod()));
			value = m;
#else
			value = normalize(static_cast<int64_t>(value) * static_cast<int64_t>(rhs.value));
#endif
			return *this;
		}
		template <typename U = T>
		typename std::enable_if<std::is_same<typename Modular<U>::Type, long long>::value, Modular>::type& operator*=(const Modular& rhs)
		{
			long long q = static_cast<long long>(static_cast<long double>(value) * rhs.value / mod());
			value = normalize(value * rhs.value - q * mod());
			return *this;
		}
		template <typename U = T>
		typename std::enable_if<!std::is_integral<typename Modular<U>::Type>::value, Modular>::type& operator*=(const Modular& rhs)
		{
			value = normalize(value * rhs.value);
			return *this;
		}

		//Should be used only if mod is prime
		Modular& operator/=(const Modular& other)
		{
			auto const g = gcdex<Type>(other(), mod());
			//return *this *= Modular(std::get<1>(g));
			return this->operator*=(Modular<T>(std::get<1>(g)));
		}

		friend const Type& abs(const Modular& x) { return x.value; }

		template <typename U>
		friend bool operator==(const Modular<U>& lhs, const Modular<U>& rhs);

		template <typename U>
		friend bool operator<(const Modular<U>& lhs, const Modular<U>& rhs);

		template <typename V, typename U>
		friend V& operator>>(V& stream, Modular<U>& number);

	private:
		Type value;
	};

	template <typename T>				bool operator==(const Modular<T>& lhs, const Modular<T>& rhs) { return lhs.value == rhs.value; }
	template <typename T, typename U>	bool operator==(const Modular<T>& lhs, U rhs) { return lhs == Modular<T>(rhs); }
	template <typename T, typename U>	bool operator==(U lhs, const Modular<T>& rhs) { return Modular<T>(lhs) == rhs; }
	template <typename T>				bool operator!=(const Modular<T>& lhs, const Modular<T>& rhs) { return !(lhs == rhs); }
	template <typename T, typename U>	bool operator!=(const Modular<T>& lhs, U rhs) { return !(lhs == rhs); }
	template <typename T, typename U>	bool operator!=(U lhs, const Modular<T>& rhs) { return !(lhs == rhs); }
	template <typename T>				bool operator<(const Modular<T>& lhs, const Modular<T>& rhs) { return lhs.value < rhs.value; }
	template <typename T>				Modular<T> operator+(const Modular<T>& lhs, const Modular<T>& rhs) { return Modular<T>(lhs) += rhs; }
	template <typename T, typename U>	Modular<T> operator+(const Modular<T>& lhs, U rhs) { return Modular<T>(lhs) += rhs; }
	template <typename T, typename U>	Modular<T> operator+(U lhs, const Modular<T>& rhs) { return Modular<T>(lhs) += rhs; }
	template <typename T>				Modular<T> operator-(const Modular<T>& lhs, const Modular<T>& rhs) { return Modular<T>(lhs) -= rhs; }
	template <typename T, typename U>	Modular<T> operator-(const Modular<T>& lhs, U rhs) { return Modular<T>(lhs) -= rhs; }
	template <typename T, typename U>	Modular<T> operator-(U lhs, const Modular<T>& rhs) { return Modular<T>(lhs) -= rhs; }
	template <typename T>				Modular<T> operator*(const Modular<T>& lhs, const Modular<T>& rhs) { return Modular<T>(lhs) *= rhs; }
	template <typename T, typename U>	Modular<T> operator*(const Modular<T>& lhs, U rhs) { return Modular<T>(lhs) *= rhs; }
	template <typename T, typename U>	Modular<T> operator*(U lhs, const Modular<T>& rhs) { return Modular<T>(lhs) *= rhs; }
	template <typename T>				Modular<T> operator/(const Modular<T>& lhs, const Modular<T>& rhs) { return Modular<T>(lhs) /= rhs; }
	template <typename T, typename U>	Modular<T> operator/(const Modular<T>& lhs, U rhs) { return Modular<T>(lhs) /= rhs; }
	template <typename T, typename U>	Modular<T> operator/(U lhs, const Modular<T>& rhs) { return Modular<T>(lhs) /= rhs; }

	template<typename T, typename U>
	Modular<T> power(const Modular<T>& a, const U& b)
	{
		assert(b >= 0);
		Modular<T> x = a, res = 1;
		U p = b;
		while (p > 0) {
			if (p & 1) res *= x;
			x *= x;
			p >>= 1;
		}
		return res;
	}

	template <typename T>
	std::string to_string(const Modular<T>& number)
	{
		return std::to_string(number());
	}

	// U == std::ostream? but done this way because of fastoutput
	template <typename U, typename T>
	U& operator<<(U& stream, const Modular<T>& number)
	{
		return stream << number();
	}

	// V == std::istream? but done this way because of fastinput
	template <typename V, typename U>
	V& operator>>(V& stream, Modular<U>& number)
	{
		typename std::common_type<typename Modular<U>::Type, long long>::type x;
		stream >> x;
		number.value = Modular<U>::normalize(x);
		return stream;
	}


	template<size_t MAXN>
	class Erato
	{
		int erato[MAXN]{};
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
					if (x % i == 0) divs.push_back(i);
					while (x % i == 0) x /= i;
				}
			}
			if (x != 1) divs.push_back(x);
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
			mu_[1] = 1;
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
	class Fraction
	{
	private:

		T numerator;
		T denominator;
	public:
		Fraction(void)
		{
			this->numerator = T(0);
			this->denominator = T(1);
		}
		template<typename U>
		Fraction(U n, U d)
			: numerator(static_cast<T>(n))
			, denominator(static_cast<T>(d))
		{}
		template<typename U>
		Fraction(U n)
			: numerator(static_cast<T>(n))
			, denominator(static_cast<T>(1))
		{}
		Fraction(long double Number)
		{
			this->convert_double_to_fraction(Number);
		}
		Fraction(std::string fraction_string)
		{
			this->convert_string_to_fraction(fraction_string);
		}

		T get_numerator(void) const
		{
			return this->numerator;
		}
		T get_denominator(void) const
		{
			return this->denominator;
		}
		void set_numerator(T Numerator)
		{
			this->numerator = Numerator;
			this->normalize();
		}
		void set_denominator(T Denominator)
		{
			this->denominator = Denominator;
			this->normalize();
		}

		bool operator<(Fraction const& fraction) const
		{
			return (this->numerator * fraction.get_denominator()) < (fraction.get_numerator() * this->denominator);
		}
		bool operator<=(Fraction const& fraction) const
		{
			return (this->numerator * fraction.get_denominator()) <= (fraction.get_numerator() * this->denominator);
		}
		bool operator>(Fraction const& fraction) const
		{
			return (this->numerator * fraction.get_denominator()) > (fraction.get_numerator() * this->denominator);
		}
		bool operator>=(Fraction const& fraction) const
		{
			return (this->numerator * fraction.get_denominator()) >= (fraction.get_numerator() * this->denominator);
		}
		bool operator==(Fraction const& fraction) const
		{
			return (this->numerator * fraction.get_denominator()) == (fraction.get_numerator() * this->denominator);
		}
		bool operator!=(Fraction const& fraction) const
		{
			return (this->numerator * fraction.get_denominator()) != (fraction.get_numerator() * this->denominator);
		}
		long operator%(Fraction const& fraction) const
		{
			long result;
			result = ((this->numerator * fraction.get_denominator()) % (this->denominator * fraction.get_numerator())) / (this->denominator * fraction.get_denominator());
			return result;
		}
		explicit operator double() const
		{
			return this->convert_fraction_to_double();
		}
		explicit operator float() const
		{
			return static_cast<float>(this->convert_fraction_to_double());
		}
		explicit operator std::complex<double>() const
		{
			return std::complex<double>(this->convert_fraction_to_double());
		}
		operator std::string() const
		{
			std::stringstream output;
			output << this->get_numerator() << "/" << this->get_denominator();
			return output.str();
		}

		Fraction operator+(Fraction const& fraction) const
		{
			Fraction result = *this;
			result += fraction;
			return result;
		}
		Fraction operator+=(Fraction fraction)
		{
			if (this->denominator == fraction.get_denominator()) this->numerator += fraction.get_numerator();
			else
			{
				this->numerator = (this->numerator * fraction.get_denominator()) + (fraction.get_numerator() * this->denominator);
				this->denominator *= fraction.get_denominator();
			}
			this->normalize();
			return *this;
		}
		Fraction operator-(Fraction const& fraction) const
		{
			Fraction result = *this;
			result -= fraction;
			return result;
		}
		Fraction operator-() const
		{
			return Fraction(-this->numerator, this->denominator);
		}
		Fraction operator-=(Fraction const& fraction)
		{
			if (this->denominator == fraction.get_denominator()) this->numerator -= fraction.get_numerator();
			else
			{
				this->numerator = (this->numerator * fraction.get_denominator()) - (fraction.get_numerator() * this->denominator);
				this->denominator *= fraction.get_denominator();
			}
			this->normalize();
			return *this;
		}
		Fraction operator*(Fraction const& fraction) const
		{
			Fraction result = *this;
			result *= fraction;
			return result;
		}
		Fraction operator*=(Fraction const& fraction)
		{
			this->denominator *= fraction.get_denominator();
			this->numerator *= fraction.get_numerator();
			this->normalize();
			return *this;
		}
		Fraction operator/(Fraction const& fraction) const
		{
			Fraction result = *this;
			result /= fraction;
			return result;
		}
		Fraction operator/=(Fraction const& fraction)
		{
			this->denominator *= fraction.get_numerator();
			this->numerator *= fraction.get_denominator();
			this->normalize();
			return *this;
		}
		Fraction operator~(void) const
		{
			Fraction result_fraction;
			if (this->numerator > this->denominator) return *this;
			else
			{
				result_fraction.set_numerator(this->denominator - this->numerator);
				result_fraction.set_denominator(this->denominator);
				this->normalize();
				return result_fraction;
			}
		}
		Fraction operator++(void)
		{
			this->numerator += 1;
			this->normalize();
			return *this;
		}
		Fraction operator--(void)
		{
			this->numerator -= 1;
			this->normalize();
			return *this;
		}
	private:
		bool normalize(void)
		{
			T const greatest_common_divisor = gcd(this->numerator, this->denominator);
			if (1 < greatest_common_divisor)
			{
				this->numerator /= greatest_common_divisor;
				this->denominator /= greatest_common_divisor;

				return true;
			}
			return false;
		}
		void convert_double_to_fraction(double number)
		{
			long double const int_val = floor(number);
			long double const f = number - int_val;
			constexpr T presision = 1000000000;
			T const gcd_val = gcd(static_cast<T>(std::round(f * presision)), static_cast<T>(presision));
			T const num = std::round(f * presision) / gcd_val;
			T const deno = presision / gcd_val;
			this->numerator = (int_val * deno) + num;
			this->denominator = presision / gcd_val;
		}
		double convert_fraction_to_double(void) const
		{
			return (double)this->numerator / (double)this->denominator;
		}
		bool convert_string_to_fraction(std::string const& FractionString)
		{
			std::size_t const pos = FractionString.find("/");
			if (pos != std::string::npos)
			{
				try
				{
					this->numerator = static_cast<T>(atol(FractionString.substr(0, pos).c_str()));
					this->denominator = static_cast<T>(atol(FractionString.substr(pos + 1).c_str()));
				}
				catch (...)
				{
					return false;
				}
				return (this->denominator == 0) ? false : true;
			}
			return false;
		}
	};

	template<typename T>
	class RootOfUnity
	{
	public:
		T root;
		T inverse;
		size_t power;
		RootOfUnity(T r, T i, size_t p)
			: root(r)
			, inverse(i)
			, power(p)
		{}
	};

	template<typename T>
	class MultiplicativeInverse
	{
	public:
		template <typename U = T, std::enable_if_t<!std::is_integral<U>::value, bool> = true>
		static T compute(T a)
		{
			return T(1) / a;
		}

		template <typename U = T, std::enable_if_t<std::is_integral<U>::value, bool> = true>
		static long double compute(T a)
		{
			return (long double)(1) / a;
		}
	};

	template<typename T, bool = std::is_integral<T>::value>
	struct make_fft_compatible
	{
		using type = T;
	};

	template<typename T>
	struct make_fft_compatible<T, true>
	{
		using type = double;
	};

	template<typename T>
	class FastFourierTransform
	{
	public:
		static void compute(std::vector<T>& polynom, RootOfUnity<T> const ru, bool const inverse = false, size_t const* rev = nullptr)
		{
			size_t const n = polynom.size();

			if (rev == nullptr)
			{
				for (size_t i = 1, j = 0; i < n; ++i)
				{
					size_t bit = n >> 1;
					for (; j & bit; bit >>= 1) j ^= bit;
					j ^= bit;
					if (i < j) std::swap(polynom[i], polynom[j]);
				}
			}
			else
			{
				for (size_t i = 0; i < n; i++) if (i < rev[i]) std::swap(polynom[i], polynom[rev[i]]);
			}

			for (size_t len = 2; len <= n; len <<= 1)
			{
				T wlen(inverse ? ru.inverse : ru.root);
				for (size_t i = len; i < ru.power; i <<= 1) wlen *= wlen;

				for (size_t i = 0; i < n; i += len)
				{
					T w(1);
					for (size_t j = 0; j < len / 2; ++j)
					{
						T const u = polynom[i + j];
						T const v = polynom[i + j + len / 2] * w;
						polynom[i + j] = u + v;
						polynom[i + j + len / 2] = u - v;
						w *= wlen;
					}
				}
			}
			if (true == inverse)
			{
				T nrev = T(1) / T(n);
				for (size_t i = 0; i < n; ++i) polynom[i] *= nrev;
			}
		}

		template<class U>
		std::vector<T> multiply(const std::vector<U>& a, const std::vector<U>& b, RootOfUnity<T> const ru, size_t const* rev = nullptr)
		{
			std::vector<T> fa(a.begin(), a.end());
			std::vector<T> fb(b.begin(), b.end());
			size_t lenght = 1;
			while (lenght < a.size() + b.size()) lenght <<= 1;
			fa.resize(lenght);
			fb.resize(lenght);
			FastFourierTransform::compute(fa, ru, false, rev);
			FastFourierTransform::compute(fb, ru, false, rev);
			for (size_t i = 0; i < lenght; ++i) fa[i] *= fb[i];
			FastFourierTransform::compute(fa, ru, true, rev);
			return fa;
			//for (size_t i = 0; i < lenght; ++i) res[i] = static_cast<U>(std::round(fa[i].real()));
		}
	};

	enum class TransformationType { FFT, NTT };
	//In case of FFT root of unity will be computed in place, while in case of NTT it should be passed to ctor 
	template<typename T, TransformationType TRANSFORMATION_TYPE>
	class Polynomial
	{
		std::vector<T> coefficients;
		RootOfUnity<T> root_of_unity;
		template<typename, TransformationType> friend class Polynomial;
	public:
		template<typename U, TransformationType V = TRANSFORMATION_TYPE, std::enable_if_t<!std::is_same<T, U>::value&& V == TransformationType::NTT, bool> = true>
		Polynomial(std::vector<U> const& cfs, RootOfUnity<T> ru)
			: coefficients(cfs.cbegin(), cfs.cend())
			, root_of_unity(ru)
		{
		}

		template<typename U, TransformationType V = TRANSFORMATION_TYPE, std::enable_if_t<!std::is_same<T, U>::value&& V == TransformationType::FFT, bool> = true>
		Polynomial(std::vector<U> const& cfs)
			: coefficients(cfs.cbegin(), cfs.cend())
			, root_of_unity(T(), T(), 0)
		{
		}

		template<typename U, TransformationType V = TRANSFORMATION_TYPE, std::enable_if_t<std::is_same<T, U>::value&& V == TransformationType::NTT, bool> = true>
		Polynomial(std::vector<U> cfs, RootOfUnity<T> ru)
			: coefficients(std::move(cfs))
			, root_of_unity(ru)
		{
		}

		template<typename U, TransformationType V = TRANSFORMATION_TYPE, std::enable_if_t<std::is_same<T, U>::value&& V == TransformationType::FFT, bool> = true>
		Polynomial(std::vector<U> cfs)
			: coefficients(std::move(cfs))
			, root_of_unity(T(), T(), 0)
		{
		}

		template<TransformationType V = TRANSFORMATION_TYPE, std::enable_if_t<V == TransformationType::NTT, bool> = true>
		Polynomial(size_t size, RootOfUnity<T> ru)
			: coefficients(size)
			, root_of_unity(ru)
		{
		}

		template<TransformationType V = TRANSFORMATION_TYPE, std::enable_if_t<V == TransformationType::FFT, bool> = true>
		Polynomial(size_t size)
			: coefficients(size)
			, root_of_unity(T(), T(), 0)
		{
		}

		//Returns inverse modulo x^mod
		template <TransformationType V = TRANSFORMATION_TYPE, std::enable_if_t<V == TransformationType::NTT, bool> = true>
		Polynomial inverse(size_t mod)
		{
			size_t temp = 1;
			while (temp < mod) temp <<= 1;
			mod = temp;

			std::unique_ptr<size_t> rev;
			rev.reset(new size_t[2 * mod]);
			rev.get()[0] = 0;
			for (size_t i = 1, j = 0; i < 2 * mod; ++i)
			{
				size_t bit = (2 * mod) >> 1;
				for (; j & bit; bit >>= 1) j ^= bit;
				j ^= bit;
				rev.get()[i] = j;
			}

			Polynomial p(this->coefficients, this->root_of_unity);
			Polynomial q(std::vector<T>{T(1) / *p.cbegin()}, this->root_of_unity);
			p.coefficients.resize(mod);
			q.coefficients.resize(mod);
			Polynomial p0(2 * mod, this->root_of_unity);
			Polynomial p1(2 * mod, this->root_of_unity);

			for (size_t m = 1; m < mod; m <<= 1)
			{
				p0.coefficients.assign(2 * mod, T());
				p1.coefficients.assign(2 * mod, T());
				std::copy(p.coefficients.cbegin(), std::next(p.coefficients.cbegin(), m), p0.coefficients.begin());
				std::copy(std::next(p.coefficients.cbegin(), m), p.coefficients.cend(), p1.coefficients.begin());
				Polynomial::multiply(p0, q, 2 * mod, rev.get());
				Polynomial::multiply(p1, q, 2 * mod, rev.get());
				for (size_t i = 0; i < 2 * mod; i++) if (i < mod) p1.coefficients[i] = -(p1.coefficients[i] + p0.coefficients[i + m]); else p1.coefficients[i] = 0;
				Polynomial::multiply(p1, q, 2 * mod, rev.get());
				for (size_t i = m; i < mod; i++) q.coefficients[i] = q.coefficients[i] + p1.coefficients[i - m];
			}
			return q;
		}

		//Returns inverse modulo x^mod
		template <TransformationType V = TRANSFORMATION_TYPE, std::enable_if_t<V == TransformationType::FFT, bool> = true>
		Polynomial inverse(size_t mod)
		{
			using U = typename make_fft_compatible<T>::type;
			size_t temp = 1;
			while (temp < mod) temp <<= 1;
			mod = temp;

			std::unique_ptr<size_t> rev;
			rev.reset(new size_t[2 * mod]);
			rev.get()[0] = 0;
			for (size_t i = 1, j = 0; i < 2 * mod; ++i)
			{
				size_t bit = (2 * mod) >> 1;
				for (; j & bit; bit >>= 1) j ^= bit;
				j ^= bit;
				rev.get()[i] = j;
			}

			Polynomial<U, TRANSFORMATION_TYPE> p(this->coefficients);
			Polynomial<U, TRANSFORMATION_TYPE> q(std::vector<U>{(U(1) / U(*p.cbegin()))});
			p.coefficients.resize(mod);
			q.coefficients.resize(mod);
			Polynomial<U, TRANSFORMATION_TYPE> p0(2 * mod);
			Polynomial<U, TRANSFORMATION_TYPE> p1(2 * mod);

			for (size_t m = 1; m < mod; m <<= 1)
			{
				p0.coefficients.assign(2 * mod, U());
				p1.coefficients.assign(2 * mod, U());
				std::copy(p.coefficients.cbegin(), std::next(p.coefficients.cbegin(), m), p0.coefficients.begin());
				std::copy(std::next(p.coefficients.cbegin(), m), p.coefficients.cend(), p1.coefficients.begin());
				Polynomial<U, TRANSFORMATION_TYPE>::multiply(p0, q, 2 * mod, rev.get());
				Polynomial<U, TRANSFORMATION_TYPE>::multiply(p1, q, 2 * mod, rev.get());
				
				for (size_t i = 0; i < 2 * mod; i++) 
				{ 
					if (i < mod) 
					{ 
						p1.coefficients[i] += p0.coefficients[i + m]; 
						p1.coefficients[i] = -p1.coefficients[i];
					} 
					else p1.coefficients[i] = 0;
				}
				Polynomial<U, TRANSFORMATION_TYPE>::multiply(p1, q, 2 * mod, rev.get());
				for (size_t i = m; i < mod; i++) q.coefficients[i] += p1.coefficients[i - m];
			}

			if constexpr (std::is_same<Polynomial<U, TRANSFORMATION_TYPE>, Polynomial>::value) return q;
			else return Polynomial(q.get_coefficients());
		}

		typename std::vector<T>::iterator begin()
		{
			return coefficients.begin();
		}

		typename std::vector<T>::const_iterator cbegin() const
		{
			return coefficients.cbegin();
		}

		typename std::vector<T>::iterator end()
		{
			return coefficients.end();
		}

		typename std::vector<T>::const_iterator cend() const
		{
			return coefficients.cend();
		}

		typename std::vector<T>::size_type size() const
		{
			return this->coefficients.size();
		}

		typename std::vector<T>& get_coefficients()
		{
			return this->coefficients;
		}

		void operator +=(Polynomial const& polynomial)
		{
			size_t const max_size = std::max(this->coefficients.size(), polynomial.coefficients.size());
			size_t const min_size = std::min(this->coefficients.size(), polynomial.coefficients.size());
			this->coefficients.resize(max_size, T{});
			for (size_t i = 0; i < min_size; i++) this->coefficients[i] += polynomial.coefficients[i];
		}

		void operator -=(Polynomial const& polynomial)
		{
			size_t const max_size = std::max(this->coefficients.size(), polynomial.coefficients.size());
			size_t const min_size = std::min(this->coefficients.size(), polynomial.coefficients.size());
			this->coefficients.resize(max_size, T{});
			for (size_t i = 0; i < min_size; i++) this->coefficients[i] -= polynomial.coefficients[i];
		}

		void operator *=(Polynomial const& polynomial)
		{
			size_t temp = 1;
			while (temp < this->coefficients.size() + polynomial.coefficients.size()) temp <<= 1;
			Polynomial::multiply(*this, polynomial, temp, nullptr);
		}

		void operator /=(Polynomial const& polynomial)
		{
			Polynomial temp = polynomial;
			if (this->coefficients.size() < temp.coefficients.size())
			{
				this->coefficients.assign(1, T());
				return;
			}
			std::reverse(this->coefficients.begin(), this->coefficients.end());
			std::reverse(temp.coefficients.begin(), temp.coefficients.end());

			size_t const xmod = this->coefficients.size() + 1 - temp.coefficients.size();
			temp = temp.inverse(xmod);
			*this *= temp;
			this->coefficients.resize(xmod);
			std::reverse(this->coefficients.begin(), this->coefficients.end());
		}

		Polynomial operator +(Polynomial const& polynomial) const
		{
			Polynomial result = *this;
			result += polynomial;
			return result;
		}

		Polynomial operator -(Polynomial const& polynomial) const
		{
			Polynomial result = *this;
			result -= polynomial;
			return result;
		}

		Polynomial operator *(Polynomial const& polynomial) const
		{
			Polynomial res = *this;
			res *= polynomial;
			return res;
		}

		Polynomial operator /(Polynomial const& polynomial) const
		{
			Polynomial res = *this;
			res /= polynomial;
			return res;
		}

	private:
		template <TransformationType U = TRANSFORMATION_TYPE, std::enable_if_t<U == TransformationType::NTT, bool> = true>
		static void multiply(Polynomial& a, Polynomial const& b, size_t xmod, size_t const* rev = nullptr)
		{
			assert(a.root_of_unity.power >= xmod);
			std::vector<T> fb(b.cbegin(), b.cend());
			a.coefficients.resize(xmod);
			fb.resize(xmod);
			FastFourierTransform<T>::compute(a.coefficients, a.root_of_unity, false, rev);
			FastFourierTransform<T>::compute(fb, a.root_of_unity, false, rev);
			for (size_t i = 0; i < xmod; ++i) a.coefficients[i] *= fb[i];
			FastFourierTransform<T>::compute(a.coefficients, a.root_of_unity, true, rev);
		}

		template <TransformationType U = TRANSFORMATION_TYPE, std::enable_if_t<U == TransformationType::FFT, bool> = true>
		static void multiply(Polynomial& a, Polynomial const& b, size_t xmod, size_t const* rev = nullptr)
		{
			double const ang = 2 * M_PI / xmod;
			std::complex<double> const root(std::cos(ang), std::sin(ang));
			std::complex<double> const iroot(std::cos(-ang), std::sin(-ang));
			RootOfUnity<std::complex<double> > const ru(root, iroot, xmod);
			std::vector<std::complex<double> > fa(a.begin(), a.end());
			std::vector<std::complex<double> > fb(b.cbegin(), b.cend());
			fa.resize(xmod);
			fb.resize(xmod);
			FastFourierTransform<std::complex<double> >::compute(fa, ru, false, rev);
			FastFourierTransform<std::complex<double> >::compute(fb, ru, false, rev);
			for (size_t i = 0; i < xmod; ++i) fa[i] *= fb[i];
			FastFourierTransform<std::complex<double> >::compute(fa, ru, true, rev);
			a.coefficients.resize(xmod);
			for (size_t i = 0; i < xmod; ++i) a.coefficients[i] = static_cast<T>(std::round(fa[i].real()));
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

	template<typename T, typename Operation>
	class SegTree
	{
		std::vector<T> tree;
		int n;
	public:
		SegTree(std::vector<T> const& v)
			: tree(std::vector<T>(count_size(v.size()), Operation::DefVal())), n(tree.size() / 2)
		{
			for (int i = 0; i < v.size(); ++i)
			{
				tree[i + n] = v[i];
			}
			build();
		}

		void build()
		{
			for (std::size_t i = n - 1; i > 0; --i)
			{
				tree[i] = Operation::compute(tree[i << 1], tree[i << 1 | 1]);
			}
		}
		T query(int l, int r)
		{
			T res = Operation::DefVal();
			for (l += n, r += n; l < r; l >>= 1, r >>= 1)
			{
				if (l & 1) res = Operation::compute(res, tree[l++]);
				if (r & 1) res = Operation::compute(res, tree[--r]);
			}

			return res;
		}
		void update(int i, T const& val)
		{
			i += n;
			for (tree[i] = val; i > 1; i >>= 1)
			{
				tree[i >> 1] = Operation::compute(tree[i], tree[i ^ 1]);
			}
		}
	private:
		static unsigned long long count_size(size_t x)
		{
			return 1ull << (fast_log2(x) + 2);
		}

	};

	enum FenwickQueryType { BEGIN_QUERY, END_QUERY };
	template<typename T, typename Operation, FenwickQueryType QueryType = BEGIN_QUERY>
	class FenwickTree
	{
		std::vector<T> tree;
		int n;
	public:
		FenwickTree(size_t count)
			: tree(count, Operation::DefVal())
			, n(static_cast<int>(count))
		{
		}

		FenwickTree(std::vector<T> const& a) : FenwickTree(a.size())
		{
			for (size_t i = 0; i < a.size(); i++)
				update(static_cast<int>(i), a[i]);
		}

		//If QueryType == BEGIN_QUERY compute for range [0, r)
		//Else compute for range [r, end)
		T query(int r)
		{
			T ret = Operation::DefVal();

			if constexpr (FenwickQueryType::BEGIN_QUERY == QueryType)
			{
				--r;
				for (; r >= 0; r = (r & (r + 1)) - 1) ret = Operation::compute(tree[r], ret);
			}
			else
				for (; r < n; r = r | (r + 1)) ret = Operation::compute(tree[r], ret);
			return ret;
		}

		//In case of min/max operation, new value should be smaller/bigger than current
		void update(int idx, T const& val)
		{
			if constexpr (FenwickQueryType::BEGIN_QUERY == QueryType)
				for (; idx < n; idx = idx | (idx + 1)) tree[idx] = Operation::compute(tree[idx], val);
			else
				for (; idx >= 0; idx = (idx & (idx + 1)) - 1) tree[idx] = Operation::compute(tree[idx], val);
		}
	};

	template<typename T, typename Operation>
	class SparseTable
	{
		std::vector<std::vector<T> > st;
	public:
		SparseTable(std::vector<T> const& v)
			: st(ceil(log2(v.size())) + 1, std::vector<T>(v.size(), Operation::DefVal()))
		{
			int h = floor(log2(v.size()));

			for (int j = 0; j < v.size(); j++)
				st[0][j] = v[j];

			for (int i = 1; i <= h; i++)
				for (int j = 0; j + (1 << i) <= v.size(); j++)
					st[i][j] = Operation::compute(st[i - 1][j], st[i - 1][j + (1 << (i - 1))]);
		}

		//Compute for range [l, r)
		T query(int l, int r)
		{
			if (l == r)
				return Operation::DefVal();

			auto const p = fast_log2<unsigned int>(r - l);
			return Operation::compute(st[p][l], st[p][r - (1 << p)]);
		}

	};

	template <typename T, typename Operation>
	class DisjointSparseTable
	{
	public:
		explicit DisjointSparseTable(std::vector<T> arr)
		{
			// Find the highest cnt such that pow2 = 2^cnt >= x
			size_t const cnt = fast_log2(arr.size()) + 1;
			size_t const pow2 = 1ull << cnt;

			arr.resize(pow2, Operation::DefVal());
			st.resize(cnt, std::vector<T>(pow2));

			for (int level = 0; level < st.size(); ++level)
			{
				for (int block = 0; block < 1 << level; ++block)
				{
					const auto start = block << (st.size() - level);
					const auto end = (block + 1) << (st.size() - level);
					const auto middle = (end + start) / 2;

					auto val = arr[middle];
					st[level][middle] = val;
					for (int x = middle + 1; x < end; ++x)
					{
						val = Operation::compute(val, arr[x]);
						st[level][x] = val;
					}

					val = arr[middle - 1];
					st[level][middle - 1] = val;
					for (int x = middle - 2; x >= start; --x)
					{
						val = Operation::compute(val, arr[x]);
						st[level][x] = val;
					}
				}
			}
		}
		//Query in range [l, r)
		T query(int l, int r) const
		{
			// Convert half open interval to closed interval
			if (--r == l - 1) return Operation::DefVal();
			if (l == r) return st.back()[l];

			// Position of the leftmost different bit from the right
			auto const pos_diff = fast_log2<unsigned int>(l ^ r);
			const auto level = st.size() - 1 - pos_diff;
			return Operation::compute(st[level][l], st[level][r]);
		}
	private:
		std::vector<std::vector<T> > st;
	};

	class DSU
	{
	public:
		DSU(size_t n)
		{
			parent = new size_t[n];
			sz = new size_t[n];
			for (size_t i = 0; i < n; ++i)
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

		void union_sets(size_t u, size_t v)
		{
			u = find_parent(u);
			v = find_parent(v);
			if (sz[u] > sz[v]) std::swap(u, v);
			parent[u] = v;
			sz[v] += sz[u];
		}

		bool same_set(size_t u, size_t v)
		{
			return find_parent(u) == find_parent(v);
		}

		size_t find_parent(size_t u)
		{
			if (parent[u] == u)  return u;
			return parent[u] = find_parent(parent[u]);
		}
	private:
		size_t* parent;
		size_t* sz;
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
				if (current_node->childs[static_cast<unsigned char>(new_word[i])] == nullptr) current_node->childs[static_cast<unsigned char>(new_word[i])] = new node();
				current_node = current_node->childs[static_cast<unsigned char>(new_word[i])];
			}
			if (current_node->word == true) return false;
			return current_node->word = true;
		}

		bool contains(std::string const& new_word) const
		{
			node* current_node = root;
			for (size_t i = 0; i < new_word.size(); i++)
			{
				if (current_node->childs[static_cast<unsigned char>(new_word[i])] == nullptr) return false;
				current_node = current_node->childs[static_cast<unsigned char>(new_word[i])];
			}
			if (current_node->word == true) return true;
			return false;
		}

	private:
		void remove_node(node*& nd)
		{
			for (size_t i = 0; i < 26; i++)
			{
				if (nd->childs[i] != nullptr) remove_node(nd->childs[i]);
			}
			delete nd;
			nd = nullptr;
		}

		node* root;
	};

	class SuffixAutomaton
	{
	public:
		std::vector<std::map<char, int> > edges; // edges[i]  : the labeled edges from node i
		std::vector<std::set<int> > revedges; // edges[i]  : the labeled edges from node i
		std::vector<int> link;            // link[i]   : the parent of i
		std::vector<char> is_sep;
		std::vector<int> length;          // length[i] : the length of the longest string in the ith class
		int last;                    // the index of the equivalence class of the whole string
		int count;
		int number_of_distinct_substrings;
		std::vector<int> mask;

		SuffixAutomaton(std::string const& s)
			: last(0)
			, count(0)
			, number_of_distinct_substrings(0)
		{
			// add the initial node
			edges.push_back(std::map<char, int>());
			revedges.emplace_back();
			link.push_back(-1);
			length.push_back(0);
			is_sep.push_back(0);
			for (size_t i = 0; i < s.size(); i++)
				extend(s[i]);
		}

		void extend(char c)
		{
			edges.emplace_back();
			revedges.emplace_back();
			length.push_back(++count);
			link.push_back(0);
			is_sep.push_back(('0' <= c && c <= '9') ? 1 : 0);
			int r = static_cast<int>(edges.size()) - 1;

			// add edges to r and find p with link to q
			int p = last;
			while (p >= 0 && edges[p].find(c) == edges[p].end()) {
				edges[p][c] = r;
				revedges[r].insert(p);
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
					revedges.emplace_back();
					length.push_back(length[p] + 1);
					link.push_back(link[q]); // copy parent of q
					is_sep.push_back(0);
					int qq = static_cast<int>(edges.size()) - 1;
					for (auto const& eg : edges[q]) revedges[eg.second].insert(qq);
					// add qq as the new parent of q and r
					link[q] = qq;
					link[r] = qq;
					// move short classes pointing to q to point to q'
					while (p >= 0 && edges[p][c] == q) {
						edges[p][c] = qq;
						revedges[qq].insert(p);
						revedges[q].erase(p);
						p = link[p];
					}
				}
			}
			last = r;
			number_of_distinct_substrings += length[last] - length[link[last]];
		}

		void bfs_from_seps(int sep_count)
		{
			int sep_num = 0;
			mask.resize(edges.size());
			for (size_t i = 0; i < is_sep.size(); i++)
			{
				if (is_sep[i])
				{
					std::vector<char> vis(edges.size(), 0);

					std::queue<int> q;
					q.push(i);
					while (!q.empty())
					{
						int c = q.front();
						q.pop();
						vis[c] = 1;
						mask[c] |= (1 << sep_num);
						for (auto const& re : revedges[c])
							if (!vis[re] && !is_sep[re])
								q.push(re);
					}
					sep_num++;
				}

			}
		}

		std::string bfs(int sep_count)
		{
			this->bfs_from_seps(sep_count);
			std::queue<int> q;
			std::vector<int> candidates;
			std::vector<char> vis(edges.size(), 0);
			q.push(0);
			while (!q.empty())
			{
				int c = q.front();
				q.pop();
				vis[c] = 1;
				if (mask[c] == (1 << sep_count) - 1)
					candidates.push_back(c);
				for (auto const& re : edges[c]) if (!vis[re.second] && !is_sep[re.second]) q.push(re.second);
			}

			int v = 0;
			int len = 0;
			for (size_t i = 0; i < candidates.size(); i++)
			{
				if (length[candidates[i]] > len)
				{
					len = length[candidates[i]];
					v = candidates[i];
				}
			}
			//return len;
			return get_longest_string_from_class(v);
		}

		std::string get_longest_string_from_class(int v)
		{
			std::string res;
			int cv = v;
			int d = length[cv];
			while (cv)
			{
				for (auto p = revedges[cv].cbegin(); p != revedges[cv].cend(); ++p)
				{
					if (length[*p] == d - 1)
					{
						bool found = false;
						char c = '.';
						for (auto const& ed : edges[*p])
						{
							if (ed.second == cv)
							{
								c = ed.first;
								found = true;
								break;
							}
						}
						cv = *p;
						d = length[*p];
						res.push_back(c);
						if (found) break;
					}
				}
			}
			std::reverse(res.begin(), res.end());
			return res;
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

		int get_number_of_distinct_substrings()
		{
			return number_of_distinct_substrings;
		}
	};

	class PrefixFunction
	{
	public:
		void operator()(std::string const& s, std::vector<int>& res)
		{
			int n = static_cast<int>(s.length());
			res.assign(n, 0);
			for (int i = 1; i < n; i++) {
				int j = res[i - 1];
				while (j > 0 && s[i] != s[j])
					j = res[j - 1];
				if (s[i] == s[j])
					j++;
				res[i] = j;
			}
		}
	};

	class SuffixFunction
	{
	public:
		void operator()(std::string const& s, std::vector<int>& res)
		{
			int n = static_cast<int>(s.length());
			res.assign(n, 0);
			for (int i = n - 2; i >= 0; i--) {
				int j = res[i + 1];
				while (j > 0 && s[i] != s[n - j - 1])
					j = res[n - j];
				if (s[i] == s[n - j - 1])
					j++;
				res[i] = j;
			}
		}
	};

	class ZFunction
	{
	public:
		void operator()(std::string const& s, std::vector<int>& res)
		{
			int n = static_cast<int>(s.length());
			res.assign(n, 0);
			for (int i = 1, l = 0, r = 0; i < n; ++i)
			{
				if (i <= r)
					res[i] = std::min(r - i + 1, res[i - l]);
				while (i + res[i] < n && s[res[i]] == s[i + res[i]])
					++res[i];
				if (i + res[i] - 1 > r)
					l = i, r = i + res[i] - 1;
			}
		}
	};

	struct BipGraph final
	{
		// m and n are number of vertices on left
		// and right sides of Bipartite Graph
		std::size_t m;
		std::size_t n;

		// adj[u] stores adjacents of left side
		// vertex 'u'. The value of u ranges from 1 to m.
		// 0 is used for dummy vertex
		std::vector<std::list<int> > adj;

		// Constructor
		BipGraph(int m, int n)
			: m(m)
			, n(n)
			, adj(m + 1)

		{
		}

		// To add edge from u to v and v to u
		// 1 <= u <= m; 1 <= v <= n
		void addEdge(int u, int v)
		{
			adj[u].push_back(v); // Add u to v’s list.
		}
	};

	class HopcroftKarp final
	{
		// pairU[u] stores pair of u in matching where u
		// is a vertex on left side of Bipartite Graph.
		// If u doesn't have any pair, then pairU[u] is 0
		std::vector<int> pairU;

		// pairV[v] stores pair of v in matching. If v
		// doesn't have any pair, then pairU[v] is 0
		std::vector<int> pairV;

		// dist[u] stores distance of left side vertices
		// dist[u] is one more than dist[u'] if u is next
		// to u'in augmenting path
		std::vector<int> dist;

		BipGraph const& bg;
		int inf = 2147483647;
	public:
		HopcroftKarp(BipGraph const& bipgraph)
			: pairU(bipgraph.m + 1)
			, pairV(bipgraph.n + 1)
			, dist(bipgraph.m + 1)
			, bg(bipgraph)
		{
		}

		// Returns size of maximum matching
		int run()
		{
			// Initialize result
			int result = 0;

			// Keep updating the result while there is an
			// augmenting path.
			while (bfs())
			{
				// Find a free vertex
				for (int u = 1; u <= bg.m; u++)

					// If current vertex is free and there is
					// an augmenting path from current vertex
					if (pairU[u] == 0 && dfs(u))
						result++;
			}
			return result;
		}

		std::vector<int> const& get_pairU() const
		{
			return pairU;
		}
		std::vector<int> const& get_pairV() const
		{
			return pairV;
		}

	private:
		// Returns true if there is an augmenting path, else returns false
		bool bfs()
		{
			std::queue<int> Q; //an integer queue

			// First layer of vertices (set distance as 0)
			for (int u = 1; u <= bg.m; u++)
			{
				// If this is a free vertex, add it to queue
				if (pairU[u] == 0)
				{
					// u is not matched
					dist[u] = 0;
					Q.push(u);
				}

				// Else set distance as infinite  that this vertex
				// is considered next time
				else dist[u] = inf;
			}

			// Initialize distance to NIL as infinite
			dist[0] = inf;

			// Q is going to contain vertices of left side only.
			while (!Q.empty())
			{
				// Dequeue a vertex
				int u = Q.front();
				Q.pop();

				// If this node is not NIL and can provide a shorter path to NIL
				if (dist[u] < dist[0])
				{
					// Get all adjacent vertices of the dequeued vertex u
					std::list<int>::const_iterator i;
					for (i = bg.adj[u].begin(); i != bg.adj[u].end(); ++i)
					{
						int v = *i;

						// If pair of v is not considered so far
						// (v, pairV[V]) is not yet explored edge.
						if (dist[pairV[v]] == inf)
						{
							// Consider the pair and add it to queue
							dist[pairV[v]] = dist[u] + 1;
							Q.push(pairV[v]);
						}
					}
				}
			}

			// If we could come back to NIL using alternating path of distinct
			// vertices then there is an augmenting path
			return (dist[0] != inf);
		}

		// Returns true if there is an augmenting path beginning with free vertex u
		bool dfs(int u)
		{
			if (u != 0)
			{
				std::list<int>::const_iterator i;
				for (i = bg.adj[u].begin(); i != bg.adj[u].end(); ++i)
				{
					// Adjacent to u
					int v = *i;

					// Follow the distances set by BFS
					if (dist[pairV[v]] == dist[u] + 1)
					{
						// If dfs for pair of v also returns
						// true
						if (dfs(pairV[v]) == true)
						{
							pairV[v] = u;
							pairU[u] = v;
							return true;
						}
					}
				}

				// If there is no augmenting path beginning with u.
				dist[u] = inf;
				return false;
			}
			return true;
		}
	};

	class Kuhn final
	{
		std::vector<int> mt; //matching
		std::vector<char> used;
		BipGraph const& bg;
	public:
		Kuhn(BipGraph const& bipgraph)
			: mt(bipgraph.n + 1, 0)
			, bg(bipgraph)
		{
		}

		std::vector<int> const& run()
		{
			for (size_t i = 1; i <= bg.m; ++i)
			{
				used.assign(bg.m + 1, 0);
				attempt(i);
			}
			return mt;
		}

	private:
		bool attempt(int v)
		{
			if (used[v] == 1)
				return false;
			used[v] = 1;
			for (std::list<int>::const_iterator to = bg.adj[v].begin(); to != bg.adj[v].end(); ++to) {
				if (mt[*to] == 0 || attempt(mt[*to])) {
					mt[*to] = v;
					return true;
				}
			}
			return false;
		}
	};

	namespace persistence
	{
		template<typename T>
		class Array final
		{
			struct Node
			{
				T val;
				Node* l;
				Node* r;
				Node(T x) : val(x), l(nullptr), r(nullptr) {}
				Node(Node* ll, Node* rr) : val(), l(ll), r(rr) {}
			};

			T* data;
			size_t size;
			std::vector<Node*> roots;

			Node* build(size_t l, size_t r)
			{
				if (l + 1 == r) return new Node(data[l]);
				size_t mid = (l + r) / 2;
				return new Node(build(l, mid), build(mid, r));
			}

			Node* update_impl(Node* node, T val, size_t pos, size_t l, size_t r)
			{
				if (l + 1 == r) return new Node(val);
				size_t mid = (l + r) / 2;
				if (pos < mid) return new Node(update_impl(node->l, val, pos, l, mid), node->r);
				return new Node(node->l, update_impl(node->r, val, pos, mid, r));
			}

			T query_impl(Node* node, size_t pos, size_t l, size_t r)
			{
				if (l + 1 == r) return node->val;
				size_t mid = (l + r) / 2;
				if (pos < mid) return query_impl(node->l, pos, l, mid);
				return query_impl(node->r, pos, mid, r);
			}

			void delete_node(Node* node)
			{
				if (node == nullptr) return;
				delete_node(node->l);
				delete_node(node->r);
				delete node;
			}

		public:
			Array(T* data, size_t size, size_t max_number_of_revisions)
				: data(data)
				, size(size)
				, roots(max_number_of_revisions, nullptr)
			{
				roots[0] = build(0, size);
			}

			~Array()
			{
				//for (size_t i = 0; i < roots.size(); i++)
					//delete_node(roots[i]);
			}

			T query(size_t index, size_t revision)
			{
				// Gets the array item at a given index and time
				return query_impl(roots[revision], index, 0, size);
			}

			void update(size_t index, size_t value, size_t revision, size_t new_revision)
			{
				// Updates the array item at a given index and time
				roots[new_revision] = update_impl(roots[revision], value, index, 0, size);
			}
		};

		template<class T, class Operation>
		class SegTree
		{
			struct Node
			{
				T val;
				size_t s;
				size_t e;
				Node* l;
				Node* r;

				Node(T x, size_t start, size_t end, Node* left_child = nullptr, Node* right_child = nullptr)
					: val(x)
					, s(start)
					, e(end)
					, l(left_child)
					, r(right_child)
				{}
			};

			T* data;
			size_t size;
			std::vector<Node*> roots;

			Node* build(size_t l, size_t r)
			{
				if (l + 1 == r) return new Node(data[l], l, r);
				size_t mid = (l + r) / 2;
				Node* lc = build(l, mid);
				Node* rc = build(mid, r);
				Operation::compute(lc->val, rc->val);
				return new Node(Operation::compute(lc->val, rc->val), l, r, lc, rc);
			}

			Node* update_impl(Node* node, T val, size_t pos)
			{
				if (node->s + 1 == node->e) return new Node(val, node->s, node->e);
				size_t mid = (node->s + node->e) / 2;
				if (pos < mid) { Node* lc = update_impl(node->l, val, pos); return new Node(Operation::compute(lc->val, node->r->val), node->s, node->e, lc, node->r); }
				else { Node* rc = update_impl(node->r, val, pos); return new Node(Operation::compute(node->l->val, rc->val), node->s, node->e, node->l, rc); }
			}

			T query_impl(Node* node, size_t l, size_t r)
			{
				if (node->e <= l || r <= node->s) return Operation::DefVal();
				if (l <= node->s && node->e <= r) return node->val;
				if (r <= node->l->e) return query_impl(node->l, l, r);
				if (node->r->s <= l) return query_impl(node->r, l, r);
				size_t const mid = (node->s + node->e) / 2;
				return Operation::compute(query_impl(node->l, l, mid), query_impl(node->r, mid, r));
			}

			void delete_node(Node* node)
			{
				if (node == nullptr) return;
				delete_node(node->l);
				delete_node(node->r);
				delete node;
			}
		public:
			SegTree(T* data, size_t n, size_t max_number_of_revisions)
				: data(data)
				, size(n)
				, roots(max_number_of_revisions, nullptr)
			{
				roots[0] = build(0, size);
			}

			T query(size_t l, size_t r, size_t revision)
			{
				return query_impl(roots[revision], l, r);
			}
			void update(size_t index, T val, size_t revision, size_t new_revision)
			{
				roots[new_revision] = update_impl(roots[revision], val, index);
			}
		private:
			static unsigned long long count_size(size_t x)
			{
				return 1ull << (fast_log2(x) + 2);
			}

		};
	}
}

using namespace abesse;
using namespace std;

#define LMAX 9223372036854775807ll
#define IMAX 2147483647
#define LMIN -9223372036854775808ll
#define IMIN -2147483648
#define all(a) a.begin(), a.end()
#define read(x) for(auto &elem : x) cin >> elem;
#define forall(x) for(auto const& e : x)

typedef unsigned long long ull;
typedef long long ll;
typedef unsigned int ui;
constexpr int md = 7;
using mint = Modular<std::integral_constant<int, md>>;



void solve()
{
	int n, m;
	cin >> n;
	vector<int> pv(n + 1);
	read(pv);
	cin >> m;
	vector<int> qv(m + 1);
	read(qv);

	Polynomial<mint, TransformationType::FFT> p(pv);
	Polynomial<mint, TransformationType::FFT> q(qv);

	auto d = p / q;
	reverse(all(p));
	reverse(all(q));
	q *= d;
	p -= q;

	while (d.get_coefficients().empty() == false && d.get_coefficients().back() == 0) d.get_coefficients().pop_back();
	if (d.get_coefficients().size() == 0) d.get_coefficients().push_back(0);
	cout << d.size() - 1 << " ";
	for (auto i = d.get_coefficients().crbegin(); i != d.get_coefficients().crend(); i++) cout << *i << " ";

	cout << endl;

	while (p.get_coefficients().empty() == false && p.get_coefficients().back() == 0) p.get_coefficients().pop_back();
	if (p.get_coefficients().size() == 0) p.get_coefficients().push_back(0);
	cout << p.size() - 1 << " ";
	for (auto i = p.get_coefficients().crbegin(); i != p.get_coefficients().crend(); i++) cout << *i << " ";
}



int main(int argc, char const** argv)
{
#ifdef ABESSE
	freopen("in.txt", "r", stdin);
#endif
	ios_base::sync_with_stdio(0);
	cout.tie(0);
	cin.tie(0);
	constexpr int  mult = 0;
	int x = 1;
	if (mult)
		std::cin >> x;
	for (size_t i = 1; i <= x; i++)
	{
		REPORT_TIME
		solve();
		END_REPORT_TIME
	}


	return 0;
}

