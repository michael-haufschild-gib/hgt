# Route E: integer quantization of complete multiplicative cells

- **ID:** E-INTEGER-CUBE-APERTURE-001
- **Stage:** 1-in-progress
- **Target:** test the proposed near-unit escape for complete growing-dimensional physical cells.
- **Status:** paper three-axis inequality; corpus and Lean audit in progress.
- **Parent:** [Route E frontier](rh-current-frontier-map.md).

## Conjecture and paper proof

Let `a_i,b_i` be positive integers with `a_i<b_i`, for three independent
factor coordinates. Let `c>=1` be an integer spectator, put
`X=c*a_1*a_2*a_3`, and let the complete corner span be
`H=c*(b_1*b_2*b_3-a_1*a_2*a_3)`. Then

```
H^3 >= 27*c*X^2 >= 27*X^2.
```

Indeed `b_i>=a_i+1`, so
`H>=c*(a_1*a_2+a_1*a_3+a_2*a_3)`.
The three-term arithmetic/geometric mean inequality gives
`(a_1*a_2+a_1*a_3+a_2*a_3)^3>=27*(a_1*a_2*a_3)^2`.
This retains the integer minimum increment; small relative increments do
not remove it. The same result applies with either orientation on each
axis by taking its smaller and larger endpoint.

For any finite number of axes, select three changing coordinates and hold
all others at their lower endpoint. Their product is the spectator `c`.
The selected upper corner cannot exceed the full upper corner, so the same
bound persists whenever at least three coordinates change. More precisely,
if all corners lie in `[L,L+W]` with `L>=0` and `W^3<27*L^2`, at most
two coordinates can change. This statement allows either orientation on
every axis and any number of constant coordinates.

## Landing on the actual Route E histogram cell

In the complete singleton binary histogram cell, each component has one
active slot and all remaining slots inactive. Independently permuting the
slots for each component puts any desired binary corner in slot zero,
without changing any component histogram. Consequently, for positive
integer component values, the slot receiver contains both the product of
the componentwise minima and the product of the componentwise maxima.

If every receiver lies in `[X-H,X+H]`, where `0<=H<=X`, the condition
`(2*H)^3<27*(X-H)^2` therefore forces at most two nonconstant components.
This strengthens the earlier factor-two activation obstruction for integer
components. It is not an assertion about arbitrary positive real component
values.

The corpus's actual growing window `H(X)=sqrt(X)*exp(log(X)/log(log(X)))`
satisfies `log(H(X))/log(X)->1/2`. Eventually that ratio is below `2/3`,
so `H(X)^3<X^2`. For `X>27`, this also gives `3*H(X)<X`. Hence
`(2*H(X))^3<8*X^2<12*X^2<=27*(X-H(X))^2`.
Thus this precise source-predeclared window eventually excludes three
nonconstant positive integer components in a complete histogram cell.

## Sharp positive survivor

For equal lower endpoints `a_1=a_2=a_3=a`, upper endpoints `a+1`, and
`c=1`, the span is `3*a^2+3*a+1`. Its cube divided by `X^2=a^6`
tends to `27`. Thus the exponent and leading constant are sharp for the
general integer-factor geometry. This does not assert that these equal-axis
examples are admissible Möbius sign-reversing cells.

## Scope and remaining source problem

This tests complete Cartesian products of integer factor choices. It does
not forbid incomplete product-conditioned cells, additive transports, or
arbitrary abstract activation systems without this integer factorization.
No signed covariance bound follows. If the candidate closes, the survivor
is an exact arithmetic aperture bound and a sharper specification of the
incomplete-cell boundary that the growing-prime construction must control.

Do not create a general cubature receiver in place of this source-geometry
test. The prime-anchor Hall matching was already proved in the corpus.
