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

/**
 * true if T is an arithmetical type, false otherwise.
 *
 * T is considered arithmetical if it is closed under the standard field
 * operations +, -, *, and /, and furthermore supports scalar multiplication
 * and comparison with the built-in int type.
 */
enum isArithmeticType(T) = is(typeof(T.init + T.init) : T) &&
                           is(typeof(T.init - T.init) : T) &&
                           is(typeof(T.init * T.init) : T) &&
                           is(typeof(T.init / T.init) : T) &&
                           is(typeof(T.init * int.init) : T) &&
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

unittest
{
    import std.bigint : BigInt;
    assert(gcd(BigInt(20), BigInt(16)) == BigInt(4));
}

/**
 * Variadic gcd.
 */
auto gcd(T...)(T args)
    if (args.length > 2)
{
    auto g = gcd(args[0], args[1]);
    if (g == 1) return g;   // short-circuit for efficiency
    return gcd(g, args[2 .. $]);
}

unittest
{
    assert(gcd(100, 75, 25) == 25);
    assert(gcd(5, 7, 14) == 1);
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
    if (r != 0 && r != 1 && isArithmeticType!Num)
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
        if (c < 0)
        {
            a = -a;
            b = -b;
            c = -c;
        }

        import std.math : abs;
        auto g = gcd(abs(a), abs(b), c);
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
        return QRat(mixin("n*c "~op~" a"), mixin(op~" b"), c);
    }

    static if (r==5 && is(Num == long))
    unittest
    {
        auto q = 1 + surd!5;
        assert(q == QRat!5(1, 1, 1));

        auto q2 = 1 - surd!5;
        assert(q2 == QRat!5(1, -1, 1));
    }

    // Scalar multiplication
    /// ditto
    QRat opBinary(string op, N)(N n)
        if (op == "*" &&
            is(typeof(Num.init * N.init) : Num))
    {
        auto g = gcd(n, c);
        if (g == 1)
            return QRat(a*n, b*n, c);
        else
        {
            // Reduce likelihood of overflow
            auto reducedN = n / g;
            return QRat(a*reducedN, b*reducedN, c/g);
        }
    }

    static if (r==5 && is(Num == long))
    unittest
    {
        auto q = 1 + surd!5;
        assert(q*2 == QRat!5(2, 2, 1));

        auto q1 = (1 + surd!5) / 6;
        assert(q1*3 == (1 + surd!5) / 2);
    }

    /// ditto
    QRat opBinaryRight(string op, N)(N n)
        if (op == "*" &&
            is(typeof(Num.init * N.init) : Num))
    {
        return this*n;
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
    QRat opBinary(string op)(QRat q)
        if (op == "*")
    {
        return QRat(a*q.a + b*q.b*r, a*q.b + b*q.a, c * q.c);
    }

    static if (r==5 && is(Num == long))
    unittest
    {
        auto phi = (1 + surd!5)/2;
        auto inv = (surd!5 - 1)/2;
        assert(phi * inv == QRat!5(1, 0, 1));
        assert(phi * phi == phi + 1);

        // We actually don't need to worry if r<0, since the multiplication
        // actually works in that case too! So here's a Gaussian integer
        // example.
        assert(surd!(-1) * surd!(-1) == QRat!(-1)(-1, 0, 1));
        assert((1 + surd!(-1)) * (1 - surd!(-1)) == QRat!(-1)(2, 0, 1));
    }

    // QRat division
    ///
    QRat opBinary(string op)(QRat q)
        if (op == "/")
    {
        // Derivation:
        // ((a + b√r)/c) / ((a' + b'√r)/c')
        // = (c'/c) * ((a + b√r) * (a' - b'√r)) / (a'^2 - b'^2*r)
        // = (c'/c) * ((a*a' - b*b'*r) + (a'*b - a*b')√r) / (a'^2 - b'^2*r)
        import std.math : abs;

        auto aTmp = a*q.a - b*q.b*r;
        auto bTmp = q.a*b - a*q.b;
        auto cTmp = q.a*q.a - q.b*q.b*r;

        // k1/k2 = ratio of denominators
        auto g0 = gcd(abs(c), abs(q.c));
        auto k1 = q.c / g0;
        auto k2 = c / g0;

        // Cancel out common factors to reduce chances of overflow.
        auto g1 = gcd(abs(k1), abs(cTmp));
        auto g2 = gcd(abs(k2), abs(aTmp), abs(bTmp));

        if (g1 != 1)
        {
            k1 /= g1;
            cTmp /= g1;
        }

        if (g2 != 1)
        {
            k2 /= g2;
            aTmp /= g2;
            bTmp /= g2;
        }

        return QRat(k1*aTmp, k1*bTmp, k2*cTmp);
    }

    static if (r==5 && is(Num == long))
    unittest
    {
        // Golden ratio identity
        auto phi = (1 + surd!5)/2;
        auto inv = (surd!5 - 1)/2;
        assert(phi / inv == phi + 1);

        // Gaussian integer identity
        assert((1 + surd!(-1)) / (1 - surd!(-1)) == surd!(-1));
    }

    /**
     * Equality comparisons.
     */
    bool opEquals(QRat q)
    {
        assert(c > 0 && q.c > 0);
        return a == q.a && b == q.b && c == q.c;
    }

    /// ditto
    bool opEquals(Num n)
    {
        if (b != 0 || c != 1) return false;
        assert(b == 0 && c == 1);
        return a == n;
    }

    static if (r==5 && is(Num == long))
    unittest
    {
        auto q1 = 1 + surd!(-1);
        auto q2 = 1 - surd!(-1);

        assert(q1 * q2 == 2);
        assert(q1 - 2*surd!(-1) == q2);
    }
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
