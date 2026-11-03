# Complete first-fold coercivity away from the first moment

- **ID:** F1-FM
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Two-moment form](../5-failed/f1-primitive-variance-joint-payment.md)
- **Statement:** Every real odd C² unit-window test satisfies
  `Q(F)+(5123/320)(∫xF)²≥∫F²/1000`.

The proof below reduces the complete first-fold sign problem from two low moments to one.

## Proof

For `supp F⊆[−1/2,1/2]`, put `G(u)=F(u/2)`. Oddness gives
`∫₀¹G²=∫F²` and `∫₀¹uG=2∫xF`.
Write `b=log2`, `w=b/√2`, `c=γ+logπ+1/192+1/(96π²)+97/483840`, `a=137/60−c`, and
`V(u)=u²/2+u⁴/4+u⁶/6+u⁸/8≤−½log(1−u²)`.
Let `B` be multiplication by `a+V`, with the signed reflection `wG(2b−u)`
on `[2b−1,1]`. The bounds established below are

`(19/50)I≤B≤(37/20)I`, `⟨P₃,BP₃⟩≥12/125`, `‖P₃‖²=1/7`.

The inverse chord on `[m,M]`, `1/t≤(m+M−t)/(mM)`, gives
`⟨P₃,B⁻¹P₃⟩≤1558/4921`. Weighted Cauchy–Schwarz pays the third moment:

`⟨G,BG⟩−(63/20)⟨P₃,G⟩²≥(133/49210)⟨G,BG⟩≥‖G‖²/1000`.

Combining with the audited `D≤P+E/64≤Q` leaves precisely the first-moment charge.
Its coefficient is `4(77/20+39/256)=5123/320` in the original variable.
No sign of the remaining first-moment form is assumed.

## Spectral bounds

The existing Euler-constant, `log3` and π bounds give `11/20≤a≤14/25`.
The derivative of `−½log(1−u²)−V(u)` is `u⁹/(1−u²)≥0` on `[0,1)`.

For `k=a−19/50≥17/100`, put `f=k+V` and `v=u²`. Direct differentiation gives

`ff″−(f′)² = k+(3k−1/2)v+(5k−1/4)v²+(7k+5/12)v³
              +11v⁴/8−v⁵/24−5v⁶/24−v⁷/8`.

For `0≤v≤1`, the last four terms are at least `v⁴`; all remaining coefficients
are nonnegative. Thus `log f` is convex. Midpoint convexity gives
`f(u)f(2b−u)≥f(b)²≥w²`; the last inequality uses `b≥693/1000` and `w≤4902/10000`.
This proves the lower bound on each reflected pair; off the strip it follows from `a≥11/20`.

For the upper bound, convexity of `V` bounds each pair matrix by the convex interpolation
of its endpoint matrices. At the endpoints, `a+V(1)≤961/600` and
`a+V(2b−1)≤13/20`, since `2b−1≤2/5`.
Subtracting from `(37/20)I` leaves positive diagonal entries at least `149/600` and
`6/5`, with product `149/500>1/4≥w²`.

## Third-moment pairing

With `s=2−2b`, direct polynomial integration gives the reflection pairing
`R=s−6s²+11s³−35s⁴/4+27s⁵/8−5s⁶/8+5s⁷/112`.
The bounds `6137/10000≤s≤6138/10000`, applied separately to its positive and
negative coefficients, give `R≥−19/200`.

The multiplication pairing is at least
`11/140+23/630+13/924+7/858+19/3432`.
Consequently
`⟨P₃,BP₃⟩≥11/140+23/630+13/924+7/858+19/3432−(4902/10000)(19/200)>12/125`.

## Inverse chord without a spectral assumption

For a positive symmetric pair matrix `T` with `mI≤T≤MI`, let `δ=det T`.
The numerator of the inverse-chord difference on a vector `z` is
`[(m+M)δ−mM tr T]‖z‖²+(mM−δ)⟨z,Tz⟩`.
If `δ≤mM`, the lower bound on `T` makes this at least `M det(T−mI)‖z‖²`;
if `δ≥mM`, its upper bound makes it at least `m det(MI−T)‖z‖²`.
Both are nonnegative. The scalar version applies off the strip.
Integrating the resulting completed-square inequality and taking its discriminant gives
the stated weighted Cauchy–Schwarz bound. All pairings are integrable on the compact interval.

## Lean

- WTZ `TheFirstFoldHasAPolynomialSpectralBracket`:
  `firstFoldLogPolynomial_le_log`, `firstFoldPolynomial_pair_bounds`.
- WTZ `TheThirdOddMomentIsPaidByTheFirstFold`:
  `firstFoldPolynomialEnergy_sub_third_moment`,
  `firstFoldTwoMomentForm_add_first_moment_ge_mass`, `weilQuad_add_first_moment_ge_mass`.

Individual Lean checks and transitive axiom audits pass using only
`propext`, `Classical.choice`, `Quot.sound`. No positivity input is assumed.
