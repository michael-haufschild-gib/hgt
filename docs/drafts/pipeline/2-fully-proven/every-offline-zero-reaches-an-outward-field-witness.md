# Every off-line zero reaches an outward-field witness

- **ID:** offline-outward-field-witness
- **Stage:** 2-fully-proven; Lean formalization pending
- **Type:** THEOREM (paper)
- **Source:** B3.28; `ArithmeticCorrespondencePositivity/TheRankinSelbergSquareSeesTheFieldOfTheOtherZeros.lean`.

## Exact statement [PROVED HERE]

There are absolute constants `C,c > 0` such that, for every Xi zero
`rho = 1/2 + a + i gamma` with `a > 0`, there is an Xi zero
`rho' = 1/2 + a' + i gamma'` of multiplicity `m >= 1` with

1. `a' >= a` and `|gamma'-gamma| <= C log(|gamma|+3)`;
2. for every Xi zero `z = 1/2 + b + i eta`,
   `b^2 <= (a')^2 + (eta-gamma')^2`;
3. the absolutely convergent transverse field obeys

   `E(rho') := sum_(z != rho') m(z) (Re rho' - Re z) / |rho'-z|^2`
   `>= m/(2a') + c a' log(|gamma'|+4)`.

In (2), zeros on either side of the line are included; multiplicities are
counted in (3). No claim of an off-line zero is made, and the supremal depth
need not be attained.

For a zero left of the line, first reflect it across the line while preserving
its ordinate. The resulting right-hand terminal has depth at least the
original absolute depth and satisfies the same ordinate bound.

Let `A(s) = s(s-1) pi^(-s/2) Gamma(s/2)/2`, so `xi = A zeta` in the strip.
The same constants give the actual-source inequality, for every
`0 < h < 1/2-a'`,

`Re (zeta'/zeta)(rho'+h) + Re (A'/A)(rho'+h)`
`>= m/h + m/(2a'+h) + c a' log(|gamma'|+4)`.

This point is zero-free. If `B(rho')` is the regular part of `zeta'/zeta`
at `rho'`, then the coefficient of `(s-rho')^(-1)` in `(zeta'/zeta)^2` is
`2m B(rho')`, and

`Re(2m B(rho')) + 2m Re(A'/A)(rho')`
`>= m^2/a' + 2m c a' log(|gamma'|+4)`.

The last form retains the Gamma and pole correction. It is a local identity
for the analytic continuation of the actual Rankin–Selberg square, whose
Dirichlet coefficients on `Re s > 1` are `Lambda * Lambda`. It does not
assert a positive uncorrected zeta field or prove RH.

## Proof [PROVED HERE]

**Pair sign and cone.** Reflection sends a zero of depth `b` and ordinate
`eta` to one of depth `-b` at the same ordinate, with the same multiplicity.
At a point of depth `x > 0`, ordinate `t`, the sum of their real reciprocal
terms is

`P(x,b,y) = (x-b)/((x-b)^2+y^2) + (x+b)/((x+b)^2+y^2)`
`= 2x(x^2-b^2+y^2) / (((x-b)^2+y^2)((x+b)^2+y^2))`,

where `y=t-eta`, whenever the denominators are nonzero. Thus a negative
pair requires `b^2 > x^2+y^2`. Every Xi depth has magnitude `< 1/2`.

**Uniform local counting.** The unconditional corpus theorem
`ncard_xiOrdinateWindow_one_le_log` bounds the number of multiplicity copies
in every unit window by `16(K0+log(|t|+4))`. Cover `[t-R,t+R]` by at most
`2 ceil(R)+1` such windows. With `d=1+|K0|`, for `R >= 1` the number in the
window is at most

`80 R (d+log(|t|+R+5))`.

Put `L=d+log(|t|+5) >= 1`. Since
`|t|+R+5 <= (|t|+5)(1+R)` and `log(1+R) <= 2 sqrt(R)`, this is at most
`80 R (L+2 sqrt(R))`. Choose a fixed `K >= 1` so that
`4 K^2 > 80 K (1+2 sqrt(K)) + 2`; such a K exists. At `R=K L` the count
`N` therefore satisfies `N+1 < 4 R^2`. Finally `L <= C0 log(|t|+3)` for a
fixed positive `C0`, giving `R <= C log(|t|+3)` with `C=K C0`.

**Finite ascent.** Start at `rho` and consider all zero copies in the
window of radius `R` around its ordinate; let their number be `N`. If no
point reachable there satisfies (2), at each step choose a zero of positive
depth `a_(j+1)` and ordinate `gamma_(j+1)` with

`a_(j+1)^2 > a_j^2 + (gamma_(j+1)-gamma_j)^2`.

This follows from failure of (2), reflecting a left-side zero when needed.
Depths strictly increase, so all visited copies are distinct. Telescoping
gives `sum_(j<n) (gamma_(j+1)-gamma_j)^2 < 1/4`. Cauchy–Schwarz gives
`|gamma_n-gamma|^2 < n/4`. Since `N+1 < 4R^2`, the first `N+1` visited
copies all remain in the original window. They are distinct, contradicting
its cardinality. Hence a terminal copy exists and has the stated depth and
distance. This also covers repeated zeros: the count includes all copies,
and increasing depth prevents revisiting a support point.

**A positive logarithmic reserve.** The unconditional theorem
`exists_xiZeroCount_window_ge_log` supplies `h0 > 0`, `T0 >= 4`, such that
the number of positive-ordinate copies in `(T-h0,T+h0]` is at least `log T`
for `T >= T0`. Set `T=|gamma'|+T0+h0+1` and reflect this band across the
real axis when `gamma' < 0`. Its copies have the same sign of ordinate as
`gamma'`, ordinate distance between `1` and `H=T0+2h0+1`, and number at
least `log T >= log(|gamma'|+4)`. None lies in either copy fibre above
`rho'` and its line reflection.

For `a' <= x < 1/2`, every selected pair has
`x^2-b^2+y^2 >= 3/4` and each denominator at most `1+H^2`. Hence
`P(x,b,y) >= k a'`, with `k = (3/2)/(1+H^2)^2 > 0`.
The entire paired sum counts each copy twice, so the selected band supplies
at least `c a' log(|gamma'|+4)`, where `c=k/2`. All remaining pairs outside
the two fibres are nonnegative by (2). The two fibres each have `m` copies.

**Actual log derivatives.** The centered Hadamard partial-fraction theorem
gives, off the Xi divisor,

`xi'/xi(s) = sum_q ((z_q-1/2)^(-1) + (s-z_q)^(-1))`.

The real parts of the first terms form an absolutely convergent series,
whose sum is zero by line reflection. The real reciprocal series also
converges absolutely, by the corpus inverse-square sum and local finiteness.
At `s=rho'+h`, (2) excludes any zero on the ray, and the pair estimate with
`x=a'+h` yields

`Re xi'/xi(s) >= m/h + m/(2a'+h) + c a' log(|gamma'|+4)`.

The actual completion factor `A` is holomorphic and nonzero in the open
strip. The corpus identity `logDeriv_xi_eq_archFactor_add_of_strip` then
gives the displayed zeta inequality.

For `h` near zero, remove all `m` copies of `rho'` from the real reciprocal
sum. Its remaining terms converge uniformly near `rho'`: finitely many
nearby zeros stay a positive distance away, and the tail is dominated by a
constant times the summable inverse-square ordinate weights. Letting
`h downarrow 0` gives (3). Analytic factorization
`zeta(s)=(s-rho')^m u(s)` with `u(rho') != 0` gives
`zeta'/zeta(s)=m/(s-rho')+u'(s)/u(s)` and the stated coefficient and corrected
inequality. The same factorization identifies the Xi regular part with `E`.

## Formalization gates

- [x] Finite ascent and uniform logarithmic localization: the Xi terminal,
  logarithmic window, and right-hand reflection are Lean-checked and use
  only standard axioms.
- [x] Actual Xi paired-resolvent bound, including the positive logarithmic
  reserve: zero-freeness, nonnegative pairs on the ray, and the
  multiplicity-counted logarithmic band and their Xi-ray combination are
  Lean-checked and use only standard axioms. The Gamma-corrected zeta-ray
  consequence is also Lean-checked with only standard axioms.
- [ ] Regular field, multiplicity, and Gamma/pole-corrected Rankin–Selberg coefficient.
- The unconditional Λ∗Λ Dirichlet-series identity is Lean-checked and uses
  only standard axioms in `TheVonMangoldtSquareIsTheZetaSource.lean`.
  `WeilSingularArithmetic.LSeries_sourceSquareCoeff` assumes Weil positivity
  and is not used as an input.
- [ ] Final leaf checks, standard-axiom audits, and umbrella imports.
- [ ] Significance assessment and contribution count.
