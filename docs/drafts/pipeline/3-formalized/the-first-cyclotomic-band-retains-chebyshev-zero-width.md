# The first cyclotomic band retains the zero width

- **Stage:** 3-formalized.
- **Type:** THEOREM [L].
- **Wall:** Π10.
- **Statement:** Among energy exponents `r≥1`, the fixed first cyclotomic band has infimum `2Θ`; consequently every eventually positive integer bandwidth does too.

## Frontier

`ChebyshevThinBandAbscissa` proves this for every positive-power bandwidth. The first-band theorem removes all bandwidth growth: fixed and arbitrarily slowly growing positive bands retain `2Θ`. Their `N^(1+ε)` energy bounds for every `ε>0` are equivalent to RH. Localization is solved; the arithmetic upper bound remains open.

## Paper proof

Put `a_j=(ψ(j−1)−(j−1))/(j√(j−1))` for `j≥3`, zero otherwise. For each fixed integer `k≥1`, set

`B_k(x)=Σ_(j≤x) a_j(1−exp(2πikj/x))`.

Let `E_1(N)=chebyshevCyclotomicNear N 1`, and suppose `E_1(N)=O(N^r)`, `r≥1`. Put `b=(r−1)/2≥0`. With `Q=N+1`, the cyclic difference identity gives `B_1(Q)=(1−ζ_1)P_Q(ζ_1)`. For `Q≥8`, `|1−ζ_1|≤2π/Q≤1` and `|1+ζ_1|≥1`. Since the first mode is a nonnegative summand of the near energy,

`|B_1(Q)|²≤(2π)²E_1(Q−1)/Q=O(Q^(r−1))`.

For `Q≤x<Q+1`, `Q≥1`, the bounds `|a_j|≤6` and `|j/x−j/Q|≤1/Q` for `1≤j≤Q` give

`|B_1(x)−B_1(Q)|≤Σ_(1≤j≤Q)6·2π/Q=12π`.

The endpoint term vanishes because `exp(2πi)=1`. Hence `B_1(x)=O(x^b)` for real horizons.

Put `E(t)=ψ(t)−t`, `w(v)=1−exp(2πiv)`, and replace the packet by

`C(x)=∫_1^x E(t)t^(−3/2)w(t/x)dt`.

For `x≥2`, `|C(x)−B_1(x)|≤80π`. Put `g_x(t)=t^(−3/2)w(t/x)`. On `[n,n+1]`, `n≥1`, linear vanishing of `w` gives

`|g_x(t)|≤2π/x`, `|g_x′(t)|≤(5π/x)t^(−3/2)≤5π/(xn)`.

Since `E(t)=E(n)−(t−n)` inside a cell and `|E(n)|≤6n`, replacing `E(t)g_x(t)` by `E(n)g_x(n)` costs at most `32π/x`. For `n≥2`, the denominator shift from `E(n)/(n√n)` to `a_(n+1)` and the phase shift from `n/x` to `(n+1)/x` cost at most `12π/x` each, using `|a_(n+1)|≤6`. Thus each complete cell costs `56π/x`; there are at most `x` cells. The first cell and final partial cell each cost at most `12π`, since `|E(t)g_x(t)|≤12π` for `1≤t≤x`. Since `b≥0`, `C(x)=O(x^b)`.

Consequently `F(s)=∫_1^∞C(x)x^(−s−1)dx` is holomorphic on `Re s>b`; its power bound dominates every logarithmic factor needed for differentiation on compact subsets. On `Re s>1/2`, absolute Fubini and substitution `v=t/x` give

`F(s)=J_1(s)∫_1^∞E(t)t^(−s−3/2)dt`,

where `J_1(s)=∫_0^1 v^(s−1)w(v)dv`. Absolute convergence follows from `E(t)=O(t)` and `|w|≤2`. With `u=s+1/2`, the corpus Chebyshev Mellin identity identifies the second factor as `−(Z′(u)/Z(u)+1)/u`, where `Z(u)=(u−1)ζ(u)`.

## Noncancellation

Write `I_a(s)=∫_0^1 t^s exp(iat)dt`, with `a>0`, `Re s>0`, `Im s=τ>a`. Integration by parts gives

`(s+1)I_a(s)+ia I_a(s+1)=exp(ia)`.

For a positive lower endpoint, divide the oscillatory integrand by its phase derivative `τ/t+a`. The resulting amplitude `g(t)=t^(Re s+2)/(τ+at)` has nonnegative derivative. Boundary terms and its total variation give

`|I_a(s+1)|≤2/(τ+a)`.

The lower-endpoint limit exists by absolute integrability. If `I_a(s)=0`, the recurrence would give `1≤2a/(τ+a)<1`. Therefore `I_a(s)≠0`. At `a=2π`, another integration by parts gives `s J_1(s)=2πi I_(2π)(s)`.

The corpus theorem `xiWard_offlinePair_abs_im_gt_eight` puts every upper right zero above height `8>2π`. Hence `J_1` cannot annihilate any right zero.

## Zero-width conclusion

On the connected domain `U={Re s>b, Im s>2π}`, `J_1` is holomorphic and nonzero. The cleared initial identity continues analytically to `U` and reads

`Z′(s+1/2)+[(s+1/2)F(s)/J_1(s)+1]Z(s+1/2)=0`.

A nonzero analytic solution of this first-order equation has no zero. It is nonzero at any point with `Re(s+1/2)>1`, by the Euler product. Thus no upper right zero can have `Re ρ>r/2`; conjugation covers lower zeros. Therefore `2Θ≤r`.

Conversely, the corpus bound `chebyshevPowerBand_subpower 0 ε` gives `E_1(N)=O(N^(2Θ+ε))` for every `ε>0`. Together these prove the claimed infimum `2Θ` and the corresponding subpower equivalence. Monotonicity in bandwidth and the full-energy upper bound extend the result to every eventually positive bandwidth. Bandwidth zero has identically zero energy.

## Lean certificate

Main leaf: `CompletedArithmeticForms/FirstCyclotomicBandAbscissa.lean`.

- `chebyshevFirstCyclotomicBand_exponent_inf`: fixed-band exponent infimum `2Θ`, among `r≥1`.
- `chebyshevCyclotomicBand_exponent_inf`, `chebyshevCyclotomicBand_subpower_iff`: every eventually positive integer bandwidth retains the same exponent and subpower bounds.
- `riemannHypothesis_iff_chebyshevFirstCyclotomicBand`, `riemannHypothesis_iff_chebyshevCyclotomicBand`: exact RH energy criteria.
- `chebyshevCyclotomicNear_zero`: bandwidth zero has zero energy.

The seven supporting leaves prove Mellin noncancellation, holomorphy, packet interpolation, absolute factorization, uniform comparison, growth transfer and zero exclusion. All eight leaves passed canonical `lake --old env lean` checks and are imported by `CompletedArithmeticForms.lean`. Main theorem audits use only `propext`, `Classical.choice`, `Quot.sound`.
