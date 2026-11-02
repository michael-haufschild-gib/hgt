# Interior jumps of odd prime-free cycles

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Π11h: interior-jump count on the prime-free window.
- **Statement:** For every odd real compact `C²` test supported in `[-a,a]`,
  `a>0`, with mass `M=∫f²` and autocorrelation `A`,
  `∫_0^(2a) (M−A(t))/t dt ≥ (log 2+7/5)M`.
  Consequently, the interior and exterior Gamma jump count gives
  `W(f,f)≥M/1000` and `h¹_prim≥M/2000` whenever `2a≤log 2`.

Odd Weil positivity through radius `181/500` was already formalized. The new
content is the scale-invariant logarithmic jump gap and its count derivation
of positivity throughout the prime-free odd window.

## Proof

Scale to `a=1`. Put `h(x)=x(1−4x²/5)` and
`k(x,y)=1/(2|x−y|)−1/(2(x+y))` on `(0,1)²`. Then `h≥x/5>0`
and `k≥0` off the diagonal. Symmetry and

`(u−v)²−u²(1−q/p)−v²(1−p/q)=(uq−vp)²/(pq)≥0`

give `∫∫k(f(x)−f(y))²≥2∫f² h⁻¹∫k(h(x)−h(y))dy`.
Direct integration gives

`h⁻¹∫k(h(x)−h(y))dy=7/5−(26/75)x²/(1−4x²/5)−log((1+x)/x)`.

For `0≤v<1`,

`−½log(1−v) ≥ (26/75)v/(1−4v/5)`.

To verify this scalar bound, split at `1/4,1/2,3/4,7/8,15/16`.
Lower tangents to `−½log(1−v)` have respective affine lower bounds
`v/2`, `3v/4−1/20`, `3v/2−91/200`, `20v/7−1041/700`,
`16v/3−274/75`, `8v−153/25`. After multiplication by `1−4v/5`,
each required inequality is a concave quadratic with nonnegative endpoints.
The tangent constants follow from rational bounds for `log 2`, `log 3`
and `log(40/7)=3log 2−log(7/5)`.

The exact jump identity, obtained by Fubini and reflection, is

`∫₀²(M−A(t))/t dt = ∫₀¹∫₀¹k(x,y)(f(x)−f(y))² dxdy + 2∫₀¹f(x)²V(x)dx`,

where `V=log 2−½log(1−x²)+log((1+x)/x)`.
Same-side and crossing pairs give the first term and the last logarithm;
jumps leaving `[-1,1]` give `log 2−½log(1−x²)`.
The scalar bound therefore gives `V+h⁻¹∫k(h(x)−h(y))≥log 2+7/5`.
Since `M=2∫₀¹f²`, this proves the statement.

All uses of Fubini are absolute: Lipschitz differences cancel the diagonal
singularity; oddness gives `f(x)=O(x)` and `h(x)≥x/5` at the origin;
compact support gives `f(x)=O(1−x)` at the other endpoint.

## Gamma count and pole cost

Oddness gives `∫₀²ᵃA=0`. Centering at `a` and using `|A|≤M` gives
`∫₀²ᵃtA=∫₀²ᵃ(t−a)A≥−M∫₀²ᵃ|t−a|=−a²M`, hence
`∫₀²ᵃt(M−A)≤3a²M`. On `0<t≤3/4`, the second-order Gamma bound gives
`w(t)≥1/t+1/2−t/10`. Thus the complete jump count satisfies

`J≥[log 2+7/5+a−3a²/10+2Ω(2a)]M`.

The tail bound is `2Ω(2a)≥log(2/a)+π/2−a+a²/12`.
Cauchy–Schwarz on `[-a,a]`, with
`|sinh(x/2)|≤|x|cosh(a/2)/2`, bounds the exact odd pole
`−2(∫f sinh(x/2))²` below by `−(a³/3)cosh²(a/2)M`.
Combining the count with the archimedean constant yields the Weil floor

`[7/5−γ−log(2πa)−13a²/60−(a³/3)cosh²(a/2)]M`.

The coefficient is at least `1/1000` for `0<a≤(log 2)/2`.

The scalar bounds `γ≤289/500`, `log(π log 2)≤779/1000`, `a²≤121/1000`
and `(a³/3)cosh²(a/2)≤3/200` leave `107/60000>1/1000`.
The logarithmic bound follows from the exponential Taylor lower sum of degree
six; the pole bound follows from `(1−z²/2)cosh z≤1`, `z=a/2`, and
`cosh²(a/2)≤16/15`. Prime autocorrelations vanish also at `2a=log 2`.

## Lean proof

Namespace: `GaloisForLFunctions.LatticeSectionTheory`.

- `WindowJumpCounts/OddLogarithmicPairGap.lean`:
  `odd_cubic_log_barrier`, `folded_logarithmic_jump_gap`.
- `WindowJumpCounts/OddLogarithmicLagGap.lean`:
  `odd_interior_jump_poincare` (also proved for globally Lipschitz tests).
- `WindowJumpCounts/OddPrimeFreeGammaJumpCount.lean`:
  `odd_gamma_jump_count_ge`, `odd_weil_count_floor`,
  `odd_primefree_Weil_from_jump_count`, `odd_primefree_primitiveH1_from_jump_count`.

All three modules pass direct Lean source checks. The capstones depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Imported by `LatticeSectionTheory.lean`.

## Remaining

Even tests on the whole prime-free window, prime jumps at larger apertures,
and counts on lattices of growing rank remain open.
