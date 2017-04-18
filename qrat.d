/**
 * Simple quadratic rational implementation.
 *
 * Implements exact arithmetic with numbers of the form (a + b*√r)/c where r is
 * fixed.
 */

module qrat;

enum isArithmeticType(T) = is(typeof(T.init + T.init) : T) &&
                           is(typeof(T.init - T.init) : T) &&
                           is(typeof(T.init * T.init) : T) &&
                           is(typeof(T.init / T.init) : T) &&
                           is(typeof(T.init == 0) : bool);

/**
 * A quadratic rational of the form (a + b*√r)/c.
 *
 * Params:
 *  r = A square-free number.
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
    }

    /**
     * Returns: The conjugate (a - b*√r)/c of this quadratic rational.
     */
    QRat conj() { return QRat(a, -b, c); }
}

unittest
{
    import std.bigint : BigInt;
    static assert(is(QRat!(5, BigInt)));
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
