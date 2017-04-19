QRat: Exact arithmetic for quadratic rationals.

A quadratic rational is a number of the form:

	(a + b*√r) / c

where a, b, c are arbitrary integers with c != 0, and r is a fixed square-free
integer that is not 0 or 1.  Numbers of this form are closed under the
operations +, -, *, and / (where the divisor is non-zero), and thus form a
field.  In fact, it is precisely the set of rational numbers adjoined with the
radical √r.

Since r is square-free, √r is irrational and therefore cannot be represented
exactly in floating-point format; thus, arithmetic on these numbers in
floating-point representation is inexact and vulnerable to roundoff errors.

This module implements the QRat type that can represent the exact values of
these numbers, and provides exact arithmetic on them. It allows exact
computations with numbers of this form.  BigInt coefficients are also supported
where integer overflow is a concern. Exact arithmetic is also supported by
symbolic algebra software like Mathcad, but general symbolic algebra has poorer
performance due to the complexity of handling arbitrary algebraic expressions,
whereas a native implementation of quadratic rationals as provided by this
module can perform better.

Among the applications of quadratic rationals are the computation of
coordinates of certain geometric objects, such as equilateral triangles
(involving ratios of √3 and 1/√3), regular octagons (involving combinations of
√2), and regular pentagons (involving the Golden Ratio (1+√5)/2); Gaussian
integers and Gaussian rationals (a + b*√-1, where a, b are integers or
rationals, respectively).

