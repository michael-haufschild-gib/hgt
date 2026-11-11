# Exceptional contact heights

- **ID:** A104
- **Stage:** 3-formalized
- **Lean:** `SelectiveArithmetic/TheContactPolynomialHasFewLargeHeights.lean`;
  `SelectiveArithmetic/TheContactMomentGivesAPowerSaving.lean`

## Second moment

Write `D_N(t)=Σ₂≤n≤N Λ(n)n^(−1/2)cos(t log n)` and
`M_N=Σ₂≤n≤N Λ(n)n^(−1/2)`.
Mertens' first theorem gives

`Σ₂≤n≤N Λ(n)²/n ≤ log N (log N+log 4+4)`.

Indeed, `Λ(n)≤log N` and `ΣΛ(n)/n≤log N+log 4+4`.
The existing mean-square inequality and Markov then give

`measure{|D_N|≥V} ≤ [T log N(log N+log 4+4)+4NM_N²]/V²`

on `(T,2T]`. For `N=⌊exp(2a)⌋`, `a≥1`, and
`4exp(4a)(2+2a)^4≤T`, this yields the stronger bound

`measure{|D_N|≥c log T} ≤ (13+2 log 4)Ta²/(c log T)²`.

## Growing moments

The prime-supported Dirichlet polynomial has variance at most
`W_N=log N(log N+log 4+4)`. The remaining prime powers contribute at most
`H_N=2 log N+4 log 4+16`, pointwise. Thus, for every integer `k≥1` with
`8N^k(1+log N^k)≤T`,

`measure{|D_N|≥V+H_N} ≤ 2e sqrt(k) T [kW_N/(eV²)]^k`.

For `N≈(log T)^(2κ)` and fixed positive threshold fraction, choosing
`k≈(1−δ)log T/(2κ log log T)` gives exponent
`1−1/(2κ)+O(δ)+o(1)`.

Keeping the full mean-value error permits the exact order
`k=⌊log T/log N⌋`: then `N^k≤T`, and the interval factor is at most
`9T(1+log T)`. If `0<θ≤1` and
`log T(log N+log 4+4)≤θV²`, factorial domination gives

`measure{|D_N|≥V+H_N} ≤ 9T(1+log T) θ⁻¹ T^(log θ/log N)`.

For `V≈log T`, take `θ≈log log T/log T`; its exponent tends to
`−1/(2κ)`. This avoids a separate asymptotic estimate of the integer moment order.

## Lean statements

Both modules pass direct Lean checks. The second proves
`eventually_measureReal_contactPoly_rung_le_rpow` and
`eventually_boundedShape_rung_exceptions_sharp`: for every `κ,c,ε>0`, the
scalar exceptional measure is eventually at most `T^(1−1/(2κ)+ε)`;
the same exponent controls the sign simultaneously over the stated bounded-shape class.

## Uniform packet transfer

`ArithmeticCastelnuovoSeveri/MostHeightsAreWeilPositiveAtSmallAperture.lean`
already supplies a frequency average independent of the test:

`primeField(N,R,γ)=∫ |D_N(γ+t)|/(1+R²t²) dt`.

Its `abs_integral_mul_primeCosine_le` bounds the prime contribution by
`shapeNorm(R,f)²·primeField`, and `fullZeroForm_quadrature_ge` supplies the
archimedean lower bound with the pole error. Normalize the averaging weight
to mass one. Jensen followed by the shift-uniform high-moment bound gives
the same moment estimate for `(R/π)primeField`, with the explicit proper
prime-power error retained. This controls all packets satisfying
`shapeNorm(R,f)²≤M²R∫f²` at once. A pointwise bound at one frequency alone
does not supply this transfer.

`ArithmeticCastelnuovoSeveri/TheBadHeightsOfTheLocalSignHaveGaussianTails.lean`
already supplies `primeField_le_primePartField`, the shift-uniform prime moments,
moment-field averaging, and uniform bounded-shape sign estimates. Its existing
log-log bound has saving `1/(64κ)`. The sharper optimization gives saving `1/(2κ)` in that uniform estimate.

For aperture `A=κ log u`, `u=log T`, set `δ=64M²A/u` and take any `κ'>κ`.
Choose `N=⌈exp(2A)⌉` and `k=⌊u/(2κ' log u)⌋`. Eventually
`log N≤2A+1≤2κ' log u`, hence `N^k≤T`. Apply `exists_bad_heights_moment`
directly: its deterministic sign proof does not require the stronger auxiliary
condition `kδ≤8M²` used in `weilPositive_quadrature_moment_of_le`.
Its exceptional measure is at most `209T(4kδ²)^k`, and

`4kδ² ≤ (8192 M⁴κ²/κ') log u/u`.

The right side is bounded by `rungMomentRatio(κ', κ'/(64M²κ), u)`.
The existing scalar envelope therefore gives every exponent above `1−1/(2κ')`.
Letting `κ'↓κ` gives `1−1/(2κ)+ε`. All shape and pole terms use the existing
`field_term_le`, `pole_term_le`, and `closing_inequality`.
