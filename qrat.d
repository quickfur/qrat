/**
 * Simple quadratic rational implementation.
 *
 * Implements exact arithmetic with numbers of the form (a + b*√r)/c where r is
 * a fixed square-free integer.
 *
 * Author: H. S. Teoh.
 * Copyright: H. S. Teoh, 2017-.
 * License: Boost License 1.0.
 */
module qrat;

/// Basic usage:
pure nothrow @nogc @safe unittest
{
    // The basic type for storing quadratic rationals is QRat.
    auto phi = QRat!5(1, 1, 2); // The golden ratio, (1 + √5)/2 = 1.61803...
    auto phiInverse = QRat!5(-1, 1, 2); // The reciprocal of the golden ratio,
                                        // (-1 + √5)/2 = 0.61803...

    // Basic arithmetic (field operations) is supported, and is exact.
    assert(phi*phi == phi+1);   // Golden ratio identity
    assert(phi*phi - phi - 1 == 0);
    assert(phi * phiInverse == 1);
    assert(1/phi == phiInverse);
    assert((phi + 1)/phi == phi);
    assert(-phi == -(1 + surd!5)/2);

    // The surd() template function makes it convenient to create instances of
    // QRat in a more readable fashion.
    auto q = (1 + surd!5) / 2;
    assert(phi == q);

    // Inequalities are supported:
    assert(phi*10000 > 16180);
    assert(phi*10000 < 16181);
    assert((10 + surd!5)/20 < (surd!5 - 1)/2);
    assert((surd!5 - 1)/2 < (10 + surd!5)/19);

    // Computing the conjugate quadratic rational:
    assert(((1 + surd!5) / 2).conj == (1 - surd!5) / 2);

    // You can even create Gaussian integers.
    auto g1 = 1 + surd!(-1);
    auto g2 = 1 - surd!(-1);
    assert(g1 * g2 == 2);

    // Of course, QRat goes further and allows you to manipulate Gaussian
    // rationals as well (i.e., complex numbers with rational coefficients).
    auto g3 = g1 / (2 - surd!(-1));
    assert(g3 == (1 + 3*surd!(-1)) / 5);

    // Obviously, complex numbers cannot be linearly ordered, so trying to
    // compare them with < will fail.
    assert(!__traits(compiles, g1 < g2));

    // We're not limited, of course, to standard complex numbers. We can
    // put other negative numbers under the surd:
    auto h1 = 1 + surd!(-2);
    auto h2 = 1 - surd!(-2);
    assert(h1 * h2 == 3);

    // Including Eisenstein integers.
    auto w = (surd!(-3) - 1)/2;
    assert(w*w + w + 1 == 0);
}

/// Formatting and conversion to floating-point:
unittest
{
    // You can print out QRat quantities in a nice formatting
    import std.format : format;
    auto s = format("%s", (7 - 2*surd!11)/3);
    assert(s == "(7-2*√11)/3");

    // You can convert non-complex quadratic rationals into floating-point, for
    // interfacing with other code that doesn't understand QRat quantities.
    double fval = cast(double)((1 + surd!5)/2);
    assert(format("%.5f", fval) == "1.61803");
}

/// BigInt support:
pure unittest
{
    // QRat supports BigInt coefficients for when you need insurance against
    // integer overflow:
    import std.bigint : BigInt;
    auto qBig1 = (BigInt(1_000_000) + BigInt(1_000_011)*surd!(127031, BigInt)) /
        BigInt(127431);
    auto qBig2 = (BigInt(1_000_000) - BigInt(1_000_099)*surd!(127031, BigInt)) /
        BigInt(139201);
    auto bigResult = qBig1 / qBig2;
    assert(bigResult == (BigInt("-2526418080557432169937") -
                         BigInt("39773901730000000")*surd!(127031, BigInt)) /
                         BigInt("2312966464393285975023"));
}

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

// This is an ultra-ugly hack to work around the Phobos bogonity that
// std.numeric.gcd has no sig constraints, yet does not compile with BigInt, so
// once we import it, we cannot even declare our own BigInt version of gcd
// without causing an overload conflict.
T gcd(T)(T a, T b)
    if (isArithmeticType!T)
    in (a >= 0 && b >= 0)
{
    static import std.numeric;
    // This is a hack to work around BigInt causing std.numeric.gcd to assert.
    static if (is(isIntegral!T))
    {
        return std.numeric.gcd(a, b);
    }
    else
    {
        // This is a hack to implement gcd for BigInt. Note that this is VERY
        // INEFFICIENT for BigInt; it's only a stop-gap measure until we get a
        // proper BigInt-optimized gcd algorithm into Phobos.
        import std.traits : Unqual;

        Unqual!T ua = a;
        Unqual!T ub = b;
        while (ub)
        {
            auto t = ub;
            ub = ua % ub;
            ua = t;
        }
        return ua;
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

///
unittest
{
    assert(gcd(100, 75, 25) == 25);
    assert(gcd(5, 7, 14) == 1);
}

/**
 * Returns: false if n is not a perfect square. If n is a perfect square, true,
 * and square root is stored in result.
 */
private bool isSquare(Num)(Num n, ref Num result)
    if (is(Num : long))
{
    if (n < 0)
        return false;

    import std.math : sqrt;
    result = cast(Num) sqrt(cast(double) n);
    return result * result == n;
}

unittest
{
    long root;
    assert( isSquare(0, root) && root == 0);
    assert( isSquare(1, root) && root == 1);
    assert(!isSquare(2, root));
    assert(!isSquare(3, root));
    assert( isSquare(4, root) && root == 2);
    assert(!isSquare(5, root));
    assert(!isSquare(6, root));
    assert(!isSquare(7, root));
    assert(!isSquare(8, root));
    assert( isSquare(9, root) && root == 3);
    assert(!isSquare(10, root));

    assert(!isSquare(-1, root));
    assert(!isSquare(-2, root));
    assert(!isSquare(-3, root));
    assert(!isSquare(-4, root));
    assert(!isSquare(-5, root));
    assert(!isSquare(-6, root));
    assert(!isSquare(-7, root));
    assert(!isSquare(-8, root));
    assert(!isSquare(-9, root));
    assert(!isSquare(-10, root));
}

/**
 * A quadratic rational of the form (a + b*√r)/c.
 *
 * Params:
 *  r = A non-zero square-free number.  Note that since checking for
 *      square-free-ness is NP-complete, this implementation does not attempt
 *      to enforce it.  However, you may get strange or wrong results if r is
 *      not square-free.
 *  Num = The base integer type. This should be signed. BigInt is supported.
 */
struct QRat(int r, Num = long)
    if (r != 0 && r != 1 && isArithmeticType!Num)
{
    Num a, b, c = Num(1);

    /**
     * Constructor.
     *
     * Creates a QRat instance representing the quadratic rational (a+b*√r)/c.
     *
     * See also the `surd` template, that allows a friendlier syntax for
     * creating instances of QRat.
     *
     * Params:
     *  a = The integral part of the numerator.
     *  b = The coefficient of √r.
     *  c = The denominator.
     */
    this(N)(N _a, N _b=0, N _c=1)
        if (is(typeof(Num(N.init))))
        in (c != 0, "Zero denominator")
    {
        a = Num(_a);
        b = Num(_b);
        c = Num(_c);
        normalize();
    }

    static if (r==5 && is(Num == long))
    ///
    unittest
    {
        import std.format : format;
        auto q = QRat!5(3, 1, 2); // (3 + 1*sqrt(5)) / 2
        assert(format("%.5f", cast(double) q) == "2.61803");
    }

    static if (r==5)
    this(string s)
    {
        if (s == "phi")
        {
            a = Num(1);
            b = Num(1);
            c = Num(2);
        }
        else
            throw new Exception("Unknown constant '" ~ s ~ "'");
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
        auto g = gcd(abs(a), c, abs(b));
        if (g == 1) return;

        a /= g;
        b /= g;
        c /= g;
    }

    /**
     * Unary operators.
     */
    QRat opUnary(string op)() const
        if (op == "+" || op == "-")
    {
        // Note: any negative denominator that results will get normalized by
        // the ctor.
        return QRat(a, b, mixin(op ~ "c"));
    }

    static if (r==5 && is(Num == long))
    /// Unary + and -:
    unittest
    {
        auto w = (surd!(-3) - 1)/2;
        assert(-w == (1 - surd!(-3)) / 2);
        assert(+w == w);
    }

    /// ditto
    ref QRat opUnary(string op)()
        if (op == "++" || op == "--")
    {
        mixin("a " ~ op[0] ~ "= c;");
        normalize();
        return this;
    }

    static if (r==5 && is(Num == long))
    /// Increment and decrement:
    unittest
    {
        auto x = surd!7 / 2;
        x++;
        assert(x == 1 + (surd!7 / 2));

        auto y = (1 + surd!3) / 2;
        --y;
        assert(y == (surd!3 - 1) / 2);
    }

    /**
     * Binary operators.
     *
     * Field operations between QRats and integral types are supported, and are
     * exact.  Integral types should be compatible with the base number type
     * Num.
     */
    QRat opBinary(string op)(in QRat q) const
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

    static if (r==5 && is(Num == long))
    /// Addition and subtraction:
    unittest
    {
        auto q1 = (1 + surd!5) / 2;
        auto q2 = (1 + surd!5) / 3;

        assert(q1 + q1 == 1 + surd!5);
        assert(q1 + q2 == (5 + 5*surd!5) / 6);
        assert(q1 - q1 == 0);
        assert(q1 - q2 == (1 + surd!5) / 6);
    }

    /// ditto
    QRat opBinary(string op, N)(in N n) const
        if ((op == "+" || op == "-") &&
            is(typeof(Num.init * N.init) : Num))
    {
        return QRat(mixin("a "~op~" n*c"), b, c);
    }

    static if (r==5 && is(Num == long))
    /// Addition and subtraction of integers:
    unittest
    {
        auto q = QRat!5(1, 1, 2) + 1;
        assert(q == QRat!5(3, 1, 2));
        assert(q - 1 == QRat!5(1, 1, 2));
    }

    /// ditto
    QRat opBinaryRight(string op, N)(in N n) const
        if ((op == "+" || op == "-") &&
            is(typeof(Num.init * N.init) : Num))
    {
        return QRat(mixin("n*c "~op~" a"), mixin(op~" b"), c);
    }

    static if (r==5 && is(Num == long))
    ///
    unittest
    {
        auto q = 1 + surd!5;
        assert(q == QRat!5(1, 1, 1));

        auto q2 = 1 - surd!5;
        assert(q2 == QRat!5(1, -1, 1));
    }

    // Scalar multiplication
    /// ditto
    QRat opBinary(string op, N)(in N n) const
        if (op == "*" &&
            is(typeof(Num.init * N.init) : Num))
    {
        import std.math : abs;
        auto g = gcd(abs(n), abs(c));
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
    /// Scalar multiplication:
    unittest
    {
        auto q = 1 + surd!5;
        assert(q*2 == QRat!5(2, 2, 1));

        auto q1 = (1 + surd!5) / 6;
        assert(q1*3 == (1 + surd!5) / 2);
    }

    /// ditto
    QRat opBinaryRight(string op, N)(in N n) const
        if (op == "*" &&
            is(typeof(Num.init * N.init) : Num))
    {
        return this*n;
    }

    static if (r==5 && is(Num == long))
    ///
    unittest
    {
        auto q = 1 + 2*surd!5;
        assert(q == QRat!5(1, 2, 1));
    }

    /// ditto
    QRat opBinary(string op, N)(in N n) const
        if (op == "/" &&
            is(typeof(Num.init * N.init) : Num))
        in (n != 0, "Division by zero")
    {
        return QRat(a, b, c*n);
    }

    static if (r==5 && is(Num == long))
    /// Division by integer:
    unittest
    {
        auto q = (1 + surd!5)/2;
        assert(q == QRat!5(1, 1, 2));
    }

    // QRat multiplication
    /// ditto
    QRat opBinary(string op)(in QRat q) const
        if (op == "*")
    {
        return QRat(a*q.a + b*q.b*r, a*q.b + b*q.a, c * q.c);
    }

    static if (r==5 && is(Num == long))
    /// Multiplication between QRats:
    unittest
    {
        auto phi = (1 + surd!5)/2;
        auto inv = (surd!5 - 1)/2;
        assert(phi * inv == QRat!5(1, 0, 1));
        assert(phi * phi == phi + 1);

        // Gaussian integer example:
        assert(surd!(-1) * surd!(-1) == QRat!(-1)(-1, 0, 1));
        assert((1 + surd!(-1)) * (1 - surd!(-1)) == QRat!(-1)(2, 0, 1));
    }

    // QRat division
    /// ditto
    QRat opBinary(string op)(in QRat q) const
        if (op == "/")
        in (q.a != 0 || q.b != 0, "Division by zero")
    {
        // Derivation:
        // ((a + b√r)/c) / ((a' + b'√r)/c')
        // = (c'/c) * ((a + b√r) * (a' - b'√r)) / (a'^2 - b'^2*r)
        // = (c'/c) * ((a*a' - b*b'*r) + (a'*b - a*b')√r) / (a'^2 - b'^2*r)
        import std.math : abs;

        Num aTmp = a*q.a - b*q.b*r;
        Num bTmp = q.a*b - a*q.b;
        Num cTmp = q.a*q.a - q.b*q.b*r;

        // k1/k2 = ratio of denominators
        auto g0 = gcd(abs(c), abs(q.c));
        Num k1 = q.c / g0;
        Num k2 = c / g0;

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
    /// Division of QRats.
    unittest
    {
        // Golden ratio identity
        auto phi = (1 + surd!5)/2;
        auto inv = (surd!5 - 1)/2;
        assert(phi / inv == phi + 1);

        // Gaussian integer identity
        assert((1 + surd!(-1)) / (1 - surd!(-1)) == surd!(-1));

        // Use case with lots of common factors
        auto q1 = (2 + 2*surd!3) / 3;
        auto q2 = (3 - 3*surd!3) / 2;
        assert(q1 / q2 == (-8 - 4*surd!3)/9);
    }

    /// Division by zero causes a runtime assertion.
    unittest
    {
        import core.exception : AssertError;
        import std.exception : assertThrown;

        auto q = 0*surd!5;
        assertThrown!AssertError(1/q);
        assertThrown!AssertError(q/0);
    }

    /// ditto
    QRat opBinaryRight(string op, N)(in N n) const
        if (op == "/" &&
            is(typeof(N.init / Num.init) : Num))
    {
        // FIXME: optimize this.
        return QRat(n, 0, 1) / this;
    }

    static if (r==5 && is(Num == long))
    /// Reciprocation:
    unittest
    {
        assert(1 / ((1 + surd!5)/2) == (surd!5 - 1)/2);
    }

    /// ditto
    QRat opBinary(string op, N)(in N n) const
        if (op == "^^" && is(typeof((N n) => n >>= 1)) &&
            is(typeof(N.init & 1)))
    {
        return pow(this, n);
    }

    /// ditto
    QRat opBinary(string op)(in QRat q) const
        if (op == "^^")
        in (q.b == 0 && q.c == 1, "Non-integral exponent not supported")
    {
        return pow(this, q.a);
    }

    static if (r==5 && is(Num == long))
    /**
     * Exponentiation by non-negative integers is supported.
     *
     * The cost of exponentiation is O(log(n)).
     */
    unittest
    {
        auto phi = (1 + surd!5) / 2;
        assert(phi^^2 == phi + 1);
        assert(phi^^6 == 8*phi + 5);
        assert(phi^^12 == 144*phi + 89);

        assert(phi^^(-2) == 2 - phi);
        assert(phi^^(-10) == 89 - 55*phi);
    }

    /**
     * Exponentiation by QRat is also supported, but only if the irrational
     * part is 0 and the denominator is 1.
     */
    unittest
    {
        auto phi = (1 + surd!5) / 2;
        auto two = (2 + 0*surd!5) / 1;
        assert(phi ^^ two == (3 + surd!5) / 2);
    }

    /**
     * Assignment operators.
     */
    ref QRat opOpAssign(string op, T)(T arg)
        if (op == "+" || op == "-" || op == "*" || op == "/" || op == "^^")
    {
        auto result = mixin("this "~op~" arg");
        this = result;
        return this;
    }

    static if (r==5 && is(Num == long))
    ///
    unittest
    {
        auto q = surd!3 / 3;
        q += 2;
        assert(q == 2 + (surd!3 / 3));

        q *= surd!3;
        assert(q == 2*surd!3 + 1);

        q -= 1;
        assert(q == 2*surd!3);

        q /= surd!3;
        assert(q == 2);

        q ^^= 5;
        assert(q == 32);
    }

    /**
     * Equality comparisons.
     *
     * Equality with integers is supported. Equality with floating-point is not
     * supported, however, because floating-point is inexact. For comparisons
     * with floating-point, use `cast(double)` and compare the result with the
     * usual approximate floating-point comparisons.
     */
    bool opEquals()(QRat q) const
    {
        assert(c > 0 && q.c > 0);
        return a == q.a && b == q.b && c == q.c;
    }

    /// ditto
    bool opEquals()(Num n) const
    {
        if (b != 0 || c != 1) return false;
        assert(b == 0 && c == 1);
        return a == n;
    }

    static if (r==5 && is(Num == long))
    ///
    unittest
    {
        auto q1 = 1 + surd!(-1);
        auto q2 = 1 - surd!(-1);

        assert(q1 * q2 == 2);
        assert(q1 - 2*surd!(-1) == q2);
    }

    /**
     * Convert this quadratic rational to (imprecise) floating-point
     * representation.
     *
     * If r is negative, returns NaN.
     *
     * Note that for custom base number types that may overflow upon
     * conversion to double, this operation may not return the correct
     * result.
     */
    auto opCast(T : double)() const
        if (is(typeof(cast(double) Num.init)))
    {
        import std.math : sqrt;
        return (cast(double) a + b*sqrt(cast(double)r)) / c;
    }

    static if (r==5 && is(Num == long))
    ///
    unittest
    {
        import std.math : abs, isNaN;
        auto q = cast(double) (1 + surd!5)/2;
        assert(abs(q - 1.61803398874989) < 1e-13);

        // Complex numbers produce NaN.
        assert(isNaN(cast(double) (1 + surd!(-1))));
    }

    /**
     * Compute the sign of this quadratic rational.
     *
     * Obviously, this only works if r is non-negative. A compile error is
     * issued if this is attempted with negative r.
     *
     * Returns: -1 if this quadratic rational is negative; 0 if it is zero, or
     * 1 if it is positive.
     */
    int sgn()() const
    {
        static assert(r >= 0, "Cannot compute sign for square root of "~
                              "negative number");

        // Simple cases.
        import std.math : abs, sgn;
        assert(c > 0);
        if (a==0)
            return cast(int) sgn(b);
        if (b==0)
            return cast(int) sgn(a);

        // Cases of obvious sign
        assert(a != 0 && b != 0);
        if (a < 0 && b < 0) return -1;
        if (a > 0 && b > 0) return 1;

        // Complicated cases: when the rational and irrational components are
        // of opposite signs.
        auto g = gcd(abs(a), abs(b));   // minimize chances of overflow
        auto aTmp = a/g;
        auto bTmp = b/g;

        if (a < 0 && b > 0)
        {
            // In this case, (b*√r - a) is positive, so sgn(this) ==
            // sgn(this*(b*√r - a)) == sgn(b^2*r - a^2).
            return cast(int) sgn(bTmp*bTmp*r - aTmp*aTmp);
        }

        assert(a > 0 && b < 0);
        // In this case, (a - b*√r) is positive, so sgn(this) ==
        // sgn(this*(a - b*√r)) == sgn(a^2 - b^2*r).
        return cast(int) sgn(aTmp*aTmp - bTmp*bTmp*r);
    }

    static if (r==5 && is(Num == long))
    ///
    unittest
    {
        auto q1 = 0*surd!5;
        assert(q1.sgn() == 0);

        auto q2 = 5*surd!5;
        assert(q2.sgn() == 1);

        auto q3 = -5*surd!5;
        assert(q3.sgn() == -1);

        auto q4 = 1 + 0*surd!5;
        assert(q4.sgn() == 1);

        auto q5 = -2 + 0*surd!5;
        assert(q5.sgn() == -1);

        assert(((1 + surd!5)/2).sgn() == 1);
        assert(((-1 - surd!5)/2).sgn() == -1);

        auto q6 = (1 - surd!5)/2;
        assert(q6.sgn() == -1);
        assert((q6 * -1).sgn() == 1);

        assert((3 - surd!5).sgn() == 1);
        assert((2 - surd!5).sgn() == -1);
    }

    /**
     * Compare two quadratic rationals according to numerical order.
     *
     * Obviously, this only works if r is non-negative. A compile error is
     * issued if this is attempted with negative r.
     */
    int opCmp(T)(T q) const
        if (r > 0 && (is(T == QRat) || is(T : Num)))
    {
        return (this - q).sgn();
    }

    static if (r==5 && is(Num == long))
    ///
    unittest
    {
        assert(6 + surd!5 < 4 + 2*surd!5);
        assert(1 + surd!5 < 2 + 2*(surd!5)/3);
        assert((10 + surd!5)/20 < (surd!5 - 1)/2);
        assert((surd!5 - 1)/2 < (10 + surd!5)/19);

        auto phi = (1 + surd!5)/2;
        assert(100*phi / 162 < 1);
        assert(100*phi / 161 > 1);
    }

    /**
     * Convert this quadratic rational to a string representation.
     */
    void toString()(scope void delegate(const(char)[]) sink) const
    {
        import std.format : formattedWrite;

        if (a == 0 && b == 0)
        {
            sink("0");
            return;
        }

        bool needParens = (a != 0 && b != 0 && c != 1);
        if (needParens) sink("(");
        if (a != 0)
        {
            sink.formattedWrite("%d", a);
            if (b > 0) sink("+");
        }
        if (b != 0)
        {
            if (b == -1)
                sink("-");
            else if (b != 1)
                sink.formattedWrite("%d*", b);

            if (r < 0)
                sink.formattedWrite("√(%d)", r);
            else
                sink.formattedWrite("√%d", r);
        }
        if (needParens) sink(")");
        if (c != 1)
            sink.formattedWrite("/%d", c);
    }

    static if (r==5 && is(Num == long))
    ///
    unittest
    {
        import std.format : format;
        assert(format("%s", 0*surd!5) == "0");
        assert(format("%s", 1 + 0*surd!5) == "1");
        assert(format("%s", surd!5) == "√5");
        assert(format("%s", 2*surd!5) == "2*√5");
        assert(format("%s", -2*surd!5) == "-2*√5");
        assert(format("%s", 1 + surd!5) == "1+√5");
        assert(format("%s", 1 + 2*surd!5) == "1+2*√5");
        assert(format("%s", (1 + 2*surd!5)/2) == "(1+2*√5)/2");

        assert(format("%s", (surd!5)/2) == "√5/2");
        assert(format("%s", 3*(surd!5)/2) == "3*√5/2");
        assert(format("%s", (1 + 0*surd!5)/2) == "1/2");

        assert(format("%s", 0*surd!(-1)) == "0");
        assert(format("%s", 1 + 0*surd!(-1)) == "1");
        assert(format("%s", 1*surd!(-1)) == "√(-1)");
        assert(format("%s", 2*surd!(-1)) == "2*√(-1)");
        assert(format("%s", (1 + 2*surd!(-1))/2) == "(1+2*√(-1))/2");
        assert(format("%s", (1 + 2*surd!(11))/2) == "(1+2*√11)/2");
        assert(format("%s", (1 - 2*surd!(11))/2) == "(1-2*√11)/2");
        assert(format("%s", (1 - surd!(11))/2) == "(1-√11)/2");
    }

    /**
     * Returns: The square root of this quadratic rational, if it exists in the
     *  corresponding extension field.
     *
     * Throws: Exception if this quadratic rational is not a perfect square.
     */
    @property QRat sqrt()() const
    {
        import std.format : format;
        typeof(*null) noRoot() // Convenience function for aborting
        {
            throw new Exception("%s has no square root in Q[√%d]"
                                .format(this, r));
        }

        if (a == r && b == 0 && c == 1)
            return QRat(0, 1, 1);

        static if (is(Num : long) /* BigInt currently has no .sqrt */)
        {
            static if (r > 0)
            {
                // Early exit optimizations for r > 0.
                if (a < Num(0) || (a == Num(0) && b != Num(0)))
                    noRoot();
            }

            // Degenerate case: irrational part is zero.
            if (b == 0)
            {
                // Either c = √a, d = 0, or c = 0, d = √(a/r).
                Num denom;
                if (!c.isSquare(denom) || denom == 0)
                    noRoot();

                Num root;
                if (a.isSquare(root))
                    return QRat(root, 0, denom);
                if ((a % r) == 0 && (a/r).isSquare(root))
                    return QRat(0, root, denom);
                noRoot();
            }

            // General case: both rational and irrational parts are non-zero.
            Num m;
            if (!isSquare(a*a - b*b*r, m))
                noRoot();

            // Compute coefficient of √r.
            // Equal to ±sqrt((a ± √(a^2 - b^2*r)) / (2*c*r)).
            import std.math : abs, sgn;
            Num dn, dd;
            auto root = a + m;
            auto rootdenom = 2*c*r;
            auto g = gcd(root.abs, rootdenom.abs) * sgn(rootdenom);
            auto reducedRoot = root / g;
            auto reducedDenom = rootdenom / g;

            // Generally we need to test both roots in the inner √ to find the
            // one that's a perfect square.
            if (!isSquare(reducedRoot, dn) || !isSquare(reducedDenom, dd))
            {
                // Positive root didn't work, try negative root.
                root = a - m;
                g = gcd(root.abs, rootdenom.abs) * sgn(rootdenom);
                reducedRoot = root / g;
                reducedDenom = rootdenom / g;

                if (!isSquare(reducedRoot, dn) || !isSquare(reducedDenom, dd))
                    noRoot();
            }

            // Compute scalar coefficient.
            // Equal to sqrt((b^2*r)/(2*c*(a ± √(a^2 - b^2r)))).
            // The inner √ should use the same root used to compute d above.
            Num cn, cd;
            auto c2num = b*b*r;
            auto c2denom = 2*c*root;
            g = gcd(c2num.abs, c2denom.abs) * sgn(c2denom);
            c2num /= g;
            c2denom /= g;

            if (!isSquare(c2num, cn) || !isSquare(c2denom, cd))
                noRoot();

            // Compute result.
            auto result = QRat(cn*dd, (b < 0) ? -dn*cd : dn*cd, cd*dd);
            static if (r > 0)
                return (result.sgn < 0) ? -result : result;
            else
                return result;
        }
        throw new Exception("Don't know how to compute square root of %s"
                            .format(this));
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

unittest
{
    // Test assignment operator
    QRat!5 q;
    q = 1 + surd!5;
    q = surd!5 / 5;
    assert(q == 1 / surd!5);
}

/**
 * Convenience function for creating quadratic rationals.
 *
 * Params:
 *  r = The number under the radical.
 *  Num = The base number type for the coefficients of the resulting QRat.
 * Returns: The QRat representing √r.
 */
auto surd(int r, Num = long)() { return QRat!(r,Num)(Num(0), Num(1), Num(1)); }

///
unittest
{
    auto phi = (1 + surd!5)/2;
    assert(is(typeof(phi) == QRat!(5,long)));
    assert(phi == QRat!(5,long)(1, 1, 2));
}

/**
 * Computes the conjugate of a quadratic rational.
 *
 * Params:
 *  Q = An instantiation of QRat.
 *  q = A quadratic rational.
 *
 * Returns: The conjugate (a - b*√r)/c of the given quadratic rational.
 */
Q conj(Q : QRat!(r,Num), int r, Num)(Q q)
{
    return Q(q.a, -q.b, q.c);
}

///
unittest
{
    auto phi = (1 + surd!5)/2;
    assert(phi.conj == (1 - surd!5)/2);
}

/**
 * Computes the absolute value of the given quadratic rational.
 *
 * A compile error is raised if the radical is complex.
 *
 * Params:
 *  Q = An instantiation of QRat.
 *  q = A quadratic rational.
 *
 * Returns: The positive form of the quadratic rational.
 */
Q abs(Q : QRat!(r,Num), int r, Num)(Q q)
{
    static assert(is(typeof(q.sgn())), "Cannot compute absolute value of "~
                                       "complex radical");
    return (q.sgn() < 0) ? -q : q;
}

///
unittest
{
    auto q1 = (1 + surd!5)/2;
    assert(q1.abs == q1);

    auto q2 = (1 - surd!5)/2;
    assert(q2.abs == (surd!5 - 1)/2);
}

///
pure nothrow @nogc @safe unittest
{
    assert(pow(surd!17, 3) == 17*surd!17);
    assert(pow(surd!3, -3) == 1 / (3 * surd!3));
}

unittest
{
    // Ensure QRat!(n, BigInt) is usable with pow().
    import std.bigint : BigInt;
    assert(pow(surd!(5, BigInt), 3) == BigInt(5)*surd!(5, BigInt));
}

unittest
{
    auto q = 5 + 0*surd!5;
    assert(q.sqrt == surd!5);
}

/**
 * Square roots of perfect squares.
 */
unittest
{
    import std.exception : assertThrown;
    assertThrown((1 + surd!2).sqrt);
    assertThrown((0 + 2*surd!2).sqrt);
    assertThrown((0 + 4*surd!2).sqrt);

    assert((3 + 2*surd!2).sqrt == 1 + surd!2);
    assert((3 - 2*surd!2).sqrt == surd!2 - 1);
    assert((6 - 4*surd!2).sqrt == 2 - surd!2);
    assert((6 + 4*surd!2).sqrt == 2 + surd!2);
    assert((9 + 4*surd!2).sqrt == 1 + 2*surd!2);
    assert((9 - 4*surd!2).sqrt == 2*surd!2 - 1);
    assert((19 - 6*surd!2).sqrt == 3*surd!2 - 1);

    assert((4 + 0*surd!2).sqrt == 2);
    assert((8 + 0*surd!2).sqrt == 2*surd!2);
    assert((18 + 0*surd!2).sqrt == 3*surd!2);

    assert((6 + 2*surd!5).sqrt == surd!5 + 1);
    assert((6 - 2*surd!5).sqrt == surd!5 - 1);

    assert(((9 - 4*surd!5) / 4).sqrt == (surd!5 - 2) / 2);
    assertThrown(((9 - 4*surd!5) / 8).sqrt);

    assert(((7 - 3*surd!5) / 2).sqrt == (3 - surd!5) / 2);
    assert(((9 + 4*surd!5) / 5).sqrt == (5 + 2*surd!5) / 5);

    // Gaussian integers
    assert((2*surd!(-1)).sqrt == 1 + surd!(-1));
    assert((-2*surd!(-1)).sqrt == 1 - surd!(-1));
    assert((3 - 4*surd!(-1)).sqrt == 2 - surd!(-1));
    assert((-3 + 4*surd!(-1)).sqrt == 1 + 2*surd!(-1));
}

/**
 * Exponentiate a numeric type by an integral exponent.
 *
 * This function computes t raised to the power of n in O(log n) time. Negative
 * exponents are accepted as long as the base type supports division and `t` is
 * non-zero.
 *
 * Preconditions: If n < 0, then T must support division, and t must not be
 * equal to 0.
 */
T pow(T,N)(in T t, in N n)
    if (is(typeof(T(1)) : T) &&
        is(typeof((T t) => t *= T.init)) &&
        is(typeof((N n) => n >>= 1)) &&
        is(typeof(N.init & 1)))
    in (t != T(0) || n >= 0, "Cannot take negative exponents of zero")
{
    T result = T(1);
    T mult = void;
    N m = void;

    if (n >= 0)
    {
        mult = t;
        m = n;
    }
    else
    {
        static if (is(typeof(T.init / T.init)))
        {
            mult = T(1) / t;
            m = -n;
        }
        else
            assert(0, "Don't know how to compute negative exponents for " ~
                      T.stringof);
    }
    while (m)
    {
        if (m & 1) result *= mult;
        m >>= 1;
        mult *= mult;
    }
    return result;
}

///
pure nothrow @nogc @safe unittest
{
    assert(pow(0, 0) == 1);
    assert(pow(2, 20) == 1048576);
}

// vim:set ai sw=4 ts=4 et:
