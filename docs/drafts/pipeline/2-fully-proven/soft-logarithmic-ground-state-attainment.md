# Attainment of the closed soft logarithmic ground energy

- **Stage:** 2-fully-proven; Lean assembly incomplete, not counted.
- **Target:** Review-1311 A158; closed-domain attainment of the universal confinement limit.
- **Connection:** First-moment Fourier nonconcentration, physical/Fourier compactness, and the literal logarithmic jump form.

## Statement

Let `D` consist of real `L²(ℝ)` profiles supported in `(-∞,0)` with
`M(v)=∫|u||v(u)|²<∞` and `∫|log|ξ|||Fourier(v)(ξ)|²<∞`. Set
`Q(v)=8M(v)+∫log|ξ||Fourier(v)(ξ)|²`. The trial infimum `μ` from
`softLogarithmicHalfLineGroundEnergy` is the minimum of `Q` on the unit
sphere of `D`. No exponential moment or absolute integrability of the
minimizer is asserted.

## Proof

Choose unit trial profiles with energies tending to `μ`, all at most
`μ+1`. The verified coercivity bound `L₊+4M≤Q+16` bounds their first and
positive logarithmic moments. The verified physical/Fourier cutoff
compactness gives a strong `L²` subsequence with unit limit `v`. Reality
and half-line support pass through an almost-everywhere subsequence.

Write `X(ξ)=max(-log|ξ|,0)`. The verified uniform bound
`∫_{X>T}X|Fourier(f)|²≤(8+2M)(T+2)exp(-T/2)` transfers to the limit by
Fatou. For each fixed cap, multiplication by `sqrt(min(X,T))` is bounded
on Fourier `L²`, so its squared norm is continuous. Removing the caps
proves convergence of the full negative logarithmic energies. Apply Fatou
to the sum of the nonnegative physical and positive Fourier densities,
using a common almost-everywhere subsequence. This gives `v∈D` and
`Q(v)≤μ`.

For the reverse inequality take any unit `v∈D`. Choose real cutoffs `χ_N`
equal to one on `[-N,0]`, vanishing below `-2N`, bounded between zero and
one, with Lipschitz constants at most one and `χ_N→1` pointwise. The
existing endpoint cutoffs have these properties for `N≥2`. Put
`g_N=(1-χ_N)v`. Dominated convergence gives `g_N→0` in `L²` and convergence
of the physical first moments of `χ_Nv`.

The reference weight `1+½log(1+4π²ξ²)` is comparable to `1+max(log|ξ|,0)`:
the lower bound follows from `2π≥1`; the upper bound follows by splitting
`|ξ|≤1` and `|ξ|≥1` in
`1+4π²ξ²≤(1+4π²)max(1,ξ²)`. Thus `v` has finite reference jump energy.
For each fixed shift `t`, the translation defect of `g_N` tends to zero.
The cutoff commutator bound gives
`‖T_tg_N-g_N‖²≤2‖T_tv-v‖²+2t²‖v‖²`.
Both terms are integrable against `exp(-t)/(2t)` on `(0,∞)`.
Dominated convergence and the verified literal jump/Fourier identity show
that the positive logarithmic Fourier energy of `g_N` tends to zero.
Consequently the positive logarithmic energies of `χ_Nv` converge to
that of `v`.

Normalize `χ_Nv` once its norm is nonzero. These profiles are compactly
supported, hence in `L¹`, have all positive exponential square moments,
and have finite positive logarithmic energy. The first-moment
negative-logarithm estimate supplies their remaining logarithmic
integrability, so they belong to the original trial domain. Their first
moments remain uniformly bounded. The preceding capped-multiplier
argument therefore also gives convergence of their negative logarithmic
energies. Their full energies converge to `Q(v)`. The trial inequality
`μ≤Q` passes to this limit. Apply it to the previously constructed `v` to
obtain `Q(v)=μ`.

## Lean status

Coercivity, compactness of every unit trial Rayleigh sublevel, and a
strongly convergent unit minimizing sequence are verified and integrated.
The entire sufficiently confined rescaled minimizing family also has
compact closure. `SoftLogarithmicCompactProfiles` passes its final plain
source audit with exactly the standard three axioms. Weighted Fatou,
continuity under uniform tails, closed-domain identification, and cutoff
recovery are being formalized. Attainment remains unverified.
Uniqueness and sign rigidity are separate open statements in
[the profile card](../1-in-progress/soft-logarithmic-profile-compactness-and-sign.md).
