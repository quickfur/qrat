/**
 * Simple quadratic rational implementation.
 *
 * Implements exact arithmetic with numbers of the form (a + b*√r)/c where r is
 * fixed.
 *
 * Author: H. S. Teoh.
 * Copyright: H. S. Teoh, 2017-.
 * License: Boost License 1.0.
 */

module qrat;

enum isArithmeticType(T) = is(typeof(T.init + T.init) : T) &&
                           is(typeof(T.init - T.init) : T) &&
                           is(typeof(T.init * T.init) : T) &&
                           is(typeof(T.init / T.init) : T) &&
                           is(typeof(T.init == 0) : bool);

private template from(string mod)
{
    mixin("import from = " ~ mod ~ ";");
}

// This is an ultra-ugly hack to work around the Phobos bogonity that
// std.numeric.gcd has no sig constraints, yet does not compile with BigInt, so
// once we import it, we cannot even declare our own BigInt version of gcd
// without causing an overload conflict.
T gcd(T)(T a, T b)
    if (isArithmeticType!T)
in { assert(a >= 0 && b >= 0); }
body
{
    static import std.numeric;
    static if (is(typeof(std.numeric.gcd(T.init, T.init))))
    {
        return std.numeric.gcd(a, b);
    }
    else
    {
        // This is a hack to implement gcd for BigInt. Note that this is VERY
        // INEFFICIENT for BigInt; it's only a stop-gap measure until we get a
        // proper BigInt-optimized gcd algorithm into Phobos.
        while (b)
        {
            auto t = b;
            b = a % b;
            a = t;
        }
        return a;
    }
}

unittest
{
    assert(gcd(20, 15) == 5);
}

/**
 * A quadratic rational of the form (a + b*√r)/c.
 *
 * Params:
 *  r = A square-free number.  Note that since checking for square-free-ness is
 *      NP-complete, this implementation does not attempt to enforce it.
 *      However, you may get strange or wrong results if r is not square-free.
 */
struct QRat(int r, Num = long)
    if (isArithmeticType!Num)
{
    Num a, b, c=1;

    this(Num _a, Num _b, Num _c=1)
    in { assert(c != 0, "Zero denominator"); }
    body
    {
        a = _a;
        b = _b;
        c = _c;
        normalize();
    }

    // Reduce fraction to lowest terms.
    private void normalize()
    {
        auto g = gcd(a, c);
        if (g == 1) return;

        g = gcd(g, b);
        if (g == 1) return;

        a /= g;
        b /= g;
        c /= g;
    }

    /**
     * Returns: The conjugate (a - b*√r)/c of this quadratic rational.
     */
    QRat conj() { return QRat(a, -b, c); }

    /**
     * Binary operators.
     */
    QRat opBinary(string op)(QRat q)
        if (op == "+" || op == "-")
    {
        if (c == q.c)
            return QRat(mixin("a "~op~" q.a"), mixin("b "~op~" q.b"), c);

        auto g = gcd(c, q.c);
        auto k1 = q.c / g;
        auto k2 = c / g;
        auto leastMult = c*k1;
        return QRat(mixin("a*k1 "~op~" q.a*k2"), mixin("b*k1 "~op~" q.b*k2"),
                    leastMult);
    }

    static if (r==5 && is(Num == long))
    unittest
    {
        auto q1 = QRat!5(1, 1, 2);
        auto q2 = QRat!5(1, 1, 3);

        assert(q1 + q1 == QRat!5(1, 1, 1));
        assert(q1 + q2 == QRat!5(5, 5, 6));
    }

    /// ditto
    QRat opBinary(string op, N)(N n)
        if ((op == "+" || op == "-") &&
            is(typeof(Num.init * N.init) : Num))
    {
        return QRat(mixin("a "~op~" n*c"), b, c);
    }

    static if (r==5 && is(Num == long))
    unittest
    {
        auto q = QRat!5(1, 1, 2) + 1;
        assert(q == QRat!5(3, 1, 2));
        assert(q - 1 == QRat!5(1, 1, 2));
    }

    /// ditto
    QRat opBinaryRight(string op, N)(N n)
        if ((op == "+" || op == "-") &&
            is(typeof(Num.init * N.init) : Num))
    {
        return QRat(mixin("n*c "~op~" a"), b, c);
    }

    static if (r==5 && is(Num == long))
    unittest
    {
        auto q = 1 + surd!5;
        assert(q == QRat!5(1, 1, 1));
    }

    // Scalar multiplication
    /// ditto
    QRat opBinary(string op, N)(N n)
        if (op == "*" &&
            is(typeof(Num.init * N.init) : Num))
    {
        return QRat(a*n, b*n, c);
    }

    static if (r==5 && is(Num == long))
    unittest
    {
        auto q = 1 + surd!5;
        assert(q*2 == QRat!5(2, 2, 1));
    }

    /// ditto
    QRat opBinaryRight(string op, N)(N n)
        if (op == "*" &&
            is(typeof(Num.init * N.init) : Num))
    {
        return QRat(n*a, n*b, c);
    }

    static if (r==5 && is(Num == long))
    unittest
    {
        auto q = 1 + 2*surd!5;
        assert(q == QRat!5(1, 2, 1));
    }

    /// ditto
    QRat opBinary(string op, N)(N n)
        if (op == "/" &&
            is(typeof(Num.init * N.init) : Num))
    {
        return QRat(a, b, c*n);
    }

    static if (r==5 && is(Num == long))
    unittest
    {
        auto q = (1 + surd!5)/2;
        assert(q == QRat!5(1, 1, 2));
    }

    // QRat multiplication
    /// ditto
}

unittest
{
    import std.bigint : BigInt;
    QRat!(5, BigInt) big;
}

unittest
{
    auto phi = QRat!5(1, 1, 2);
    assert(phi.conj == QRat!5(1, -1, 2));
}

/**
 * Convenience function for creating quadratic rationals.
 */
auto surd(int r, Num = long)() { return QRat!(r,Num)(0, 1, 1); }

///
unittest
{
    auto phi = surd!5;
    assert(is(typeof(phi) == QRat!(5,long)));
    assert(phi == QRat!(5,long)(0, 1, 1));
}

// vim:set ai sw=4 ts=4 et:
