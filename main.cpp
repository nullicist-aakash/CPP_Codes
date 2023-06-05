#include <cmath>
#include <vector>
#include <iostream>
#include <string>
#include <functional>
#include <algorithm>
#include <climits>
#include <cstring>
#include <bitset>
#include <cmath>
#include <stack>
#include <queue>
#include <cstring>
#include <set>
#include <array>
#include <cassert>
#include <map>
#include <iterator>
#include <iomanip>
#include <complex>
#include <unordered_set>
#include <unordered_map>
#include <cfloat>
#include <cstdint>
#include <numeric>
#include <type_traits>
#include <typeinfo>

using namespace std::complex_literals;

using namespace  std;

#define for_(var,elem,max) for (int var = elem; var < max; ++var)
#define mp(x, y) make_pair(x, y)
#define FAST_IO ios_base::sync_with_stdio(false); cin.tie(NULL); cout.tie(NULL)
#define REDIRECT_IO freopen("input.txt", "r", stdin); freopen("output.txt", "w", stdout)
#define REDIRECT_INPUT freopen("input.txt", "r", stdin)

using cd = complex<double>;
using ll = long long;
using ull = unsigned long long;
using pii = pair<int, int>;
using pll = pair<long long, long long>;
using vi = vector<int>;
using vb = vector<bool>;
using vll = vector<long long>;
using vd = vector<double>;
using vvi = vector<vector<int>>;
using vvb = vector<vector<bool>>;
using vvll = vector<vector<long long>>;
using vdi = vector<deque<int>>;
using vdll = vector<deque<long long>>;
using vpii = vector<pair<int, int>>;
using vpib = vector<pair<ll, bool>>;
using vvpii = vector<vpii>;
using vpll = vector<pair<long long, long long>>;
using di = deque<int>;
using sti = stack<int>;

ll binpow(ll a, ll b, ll m)
{
    ll val = a;

    ll res(1);
    while (b > 0)
    {
        if (b & 1)
            res = (res * val) % m;
        val = (val * val) % m;
        b >>= 1;
    }
    return res;
}

cd binpow(cd a, ll b)
{
    cd val = a;

    cd res(1);
    while (b > 0)
    {
        if (b & 1)
            res = (res * val);
        val = (val * val);
        b >>= 1;
    }
    return res;
}

template <const long long MOD>
class ModuloWrapper
{
private:
    long long int number;

    static inline auto Modulo(long long n)
    {
        return ((n % MOD) + MOD) % MOD;
    }

public:
    ModuloWrapper(long long int num = 0) : number(Modulo(num))
    {

    }

    [[nodiscard]] ll get() const
    {
        return number;
    }

    [[nodiscard]] ModuloWrapper inverse() const
    {
        return binpow(number, MOD - 2, MOD);
    }

    ModuloWrapper operator+(const ModuloWrapper& rhs) const
    {
        return this->number + rhs.number;
    }

    ModuloWrapper operator-(const ModuloWrapper& rhs) const
    {
        return this->number - rhs.number;
    }

    ModuloWrapper operator*(const ModuloWrapper& rhs) const
    {
        return this->number * rhs.number;
    }

    ModuloWrapper operator/(const ModuloWrapper& rhs) const
    {
        return this->number * rhs.inverse().get();
    }

    ModuloWrapper& operator +=(const ModuloWrapper& rhs)
    {
        this->number = Modulo(this->number + rhs.number);
        return *this;
    }

    ModuloWrapper& operator -=(const ModuloWrapper& rhs)
    {
        this->number = Modulo(this->number - rhs.number);
        return *this;
    }

    ModuloWrapper& operator *=(const ModuloWrapper& rhs)
    {
        this->number = Modulo(this->number * rhs.number);
        return *this;
    }

    ModuloWrapper& operator /=(const ModuloWrapper& rhs)
    {
        this->number = ModuloWrapper(*this / rhs).number;
        return *this;
    }

    bool operator==(const ModuloWrapper& rhs) const
    {
        return this->number == rhs.number;
    }

    bool operator!=(const ModuloWrapper& rhs) const
    {
        return !(*this == rhs);
    }

    static ModuloWrapper factorial(long long n)
    {
        ModuloWrapper ans = 1;
        while (n > 1)
        {
            ans *= n;
            n--;
        }
        return ans;
    }

    friend std::ostream& operator<< (std::ostream& out, const ModuloWrapper& num)
    {
        out << num.number;
        return out;
    }

    friend std::istream& operator>> (std::istream& in, ModuloWrapper& mw)
    {
        in >> mw.number;

        mw.number = Modulo(mw.number);

        return in;
    }
};

namespace FFT
{
    const double PI = acos(-1);

    long long ntt_primitive_root(int p)
    {
        int MOD = p;
        int r = 2, pw = 0, phi = --p;
        while (binpow(r, p >> 1, MOD) == 1) ++r;
        assert(binpow(r, p, MOD) == 1);         // a ^ phi(p) == 1, will be always true
        while (!(p & 1)) p >>= 1, pw++;                 // extracts the odd part of prime - 1
        return binpow(r, phi >> pw, MOD);
    }

    template <const unsigned int MOD, class T>
    void FFT(vector<T> &a, bool invert = false)
    {
        using MW = ModuloWrapper<MOD>;
        static_assert((is_same<MW, T>::value && MOD > 0) || (is_same<cd, T>::value && MOD == 0),
                      "MOD must be 0 (for complex double) or must match for modulo wrapper");

        // always work with even powers of 2
        assert((a.size() & (a.size() - 1)) == 0);
        T root, root_1;
        ll root_pw = 0;

        if constexpr (MOD > 0)
        {
            root = MW(ntt_primitive_root(MOD));
            root_1 = MW(root).inverse();
            const auto temp = MOD - 1;
            root_pw = temp & ~(temp & (temp - 1));
        }

        int n = a.size();

        for (int i = 1, j = 0; i < n; i++) {
            int bit = n >> 1;
            for (; j & bit; bit >>= 1)
                j ^= bit;
            j ^= bit;

            if (i < j)
                swap(a[i], a[j]);
        }

        for (int len = 2; len <= n; len <<= 1)
        {
            T wlen;
            if constexpr (MOD > 0)
            {
                wlen = invert ? root_1 : root;
                for (int i = len; i < root_pw; i <<= 1)
                    wlen *= wlen;
            }
            else
            {
                double ang = 2 * PI / len * (invert ? -1 : 1);
                wlen = cd(cos(ang), sin(ang));
            }


            for (int i = 0; i < n; i += len) {
                T w = 1;

                for (int j = 0; j < len / 2; j++) {
                    T u = a[i + j], v = a[i + j + len / 2] * w;
                    a[i + j] = u + v;
                    a[i + j + len / 2] = u - v;
                    w *= wlen;
                }
            }
        }

        if (!invert)
            return;

        T n_1;
        if constexpr (MOD > 0)
            n_1 = MW(n).inverse();
        else
            n_1 = 1.0 / (double)n;

        for (auto &x : a)
            x *= n_1;
    }

    template <const unsigned int MOD, class T, class U>
    vector<U> multiply(vector<T> const& a, vector<T> const& b)
    {
        vector<U> fa(a.begin(), a.end()), fb(b.begin(), b.end());
        int n = 1;
        while (n < a.size() + b.size())
            n <<= 1;
        fa.resize(n);
        fb.resize(n);

        FFT<MOD>(fa, false);
        FFT<MOD>(fb, false);
        for (int i = 0; i < n; i++)
            fa[i] *= fb[i];
        FFT<MOD>(fa, true);
        return std::move(fa);
    }

    template <const unsigned int MOD, class T>
    vector<T> multiply(vector<T> const& a, vector<T> const& b)
    {
        using MW = ModuloWrapper<MOD>;
        static_assert(
                (MOD > 0 && is_same<MW, T>::value) ||
                (MOD == 0 && is_same<cd, T>::value) ||
                is_integral<T>::value,
                "(MOD must be 0 (for complex double) or must match for modulo wrapper) or an integer");

        if constexpr (MOD > 0)
        {
            if constexpr (is_same<MW, T>::value)
                return multiply<MOD, T, MW>(a, b);
            else
            {
                auto res = multiply<MOD, T, MW>(a, b);
                vector<T> ans(res.size());
                for (int i = 0; i < res.size(); ++i)
                    ans[i] = res[i].get();
                return ans;
            }
        }
        else
        {
            auto res = multiply<MOD, T, cd>(a, b);
            if constexpr (is_same<cd, T>::value)
                return res;
            else
            {
                vector<T> result(res.size());
                for (int i = 0; i < res.size(); i++)
                    result[i] = round(res[i].real());
                return result;
            }
        }
    }
}

const ll mod = 163577857;
using MW = ModuloWrapper<mod>;
using vMW = vector<MW>;

int main()
{
    FAST_IO;
    REDIRECT_INPUT;
    int n, k;
    cin >> n >> k;
    vector<MW> arr(1 << 20);
    for (int i = 0; i < n; ++i)
    {
        int x;
        cin >> x;
        arr[x] = 1;
    }

    for (auto i : arr)
        cout << i << " ";
}