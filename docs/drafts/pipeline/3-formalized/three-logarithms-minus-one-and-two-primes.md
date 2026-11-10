# Three logarithms: minus one and two primes

- **Stage:** 3-formalized
- **Source:** review-0911 §11.4 and §11.6.

## Exact statement

For distinct primes `p,q`, some `c,C>0` satisfy
`‖m log(-1)+a log p+b log q‖ ≥ c(2+|m|+|a|+|b|)^(-C)`
for every nonzero integer triple `(m,a,b)`, using principal complex logs.

## Proof

If `m≠0`, the imaginary part is `mπ`, so the norm is at least `π`.
If `m=0`, the effective two-prime Baker bound applies. Shrink its constant
to at most `π`; enlarging the coefficient height weakens the lower bound.

This proves the particular three-logarithm bound named in the report.
It does not estimate `m+a log p+b log q`: the constant frequency is real,
whereas `log(-1)=iπ`. The cubic upper-side construction still needs its
own inhomogeneous estimate.

Lean: `ArithmeticOfSquareRootPrecision/MinusOneAndTwoPrimeLogarithms.lean`,
`exists_minusOne_primeLog_separation`. Direct audit passed without warnings;
transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.
