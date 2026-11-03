# F2 — the literal core has its global completed-period identity

- **Stage:** 3-formalized
- **Result:** Throughout `0<Re s<1/2`, `Im s>0`, the actual Cauchy-integral core is real analytic on `(0,∞)` and equals the completed Lewis period minus both explicit boundary channels there.
- **Scope:** No resonance assumption, replacement core, or unproved regularity input. Corrected Hecke transport is a separate consequence under formalization.

## One field boundary coordinate supplies global analyticity

Put `F_w=fieldCore w`, `σ=Re w`, `β=1−σ`, and `Z₀=ζ(w)`. The exact existing tail decomposition is

`F_w(a)=tail_w(a)−Z₀ a^(−w)−c_w a⁻¹`,

with `|tail_w(a)|≤T_w a^(−σ/2−1)` for `a≥1`. Hence `F_w(a)=O(a^(−σ))` there, while

`F_w(a)+Z₀ a^(−w)=O(a⁻¹)`.

Actual inversion transports the second estimate to

`F_w(a)+Z₀=O(a^β)` for `0<a≤1`.

Therefore the literal logarithmic remainder

`h_s(x)=Γ_R(w)[F_w(e^(−x))+Z₀ 1_(0,∞)(x)]`

has an exponential bound at both ends: `|h_s(x)|≤C_s exp(−ε_s|x|)`, where `ε_s=min(σ,β)>0`. It belongs to both `L¹(ℝ)` and `L²(ℝ)`.

Let `k_s` be the existing normalized logarithmic Cauchy kernel. It is continuous, bounded and integrable. These facts follow directly from its formula and the existing bounds `|cauchyWeight_w(t)|≤min(1,t^(−σ−2))`. It is real analytic, since its positive real base never meets the complex-power branch cut.

The literal change of variable `t=e^(−u)` identifies the physical core in logarithmic coordinates with

`core_s(e^(−x))=(k_s*h_s)(x)−Γ_R(w)Z₀ K_s(x)`,

where `K_s(x)=∫_(−∞)^x k_s(u)du`.

The first convolution is continuous because its kernel is bounded and continuous and `h_s∈L¹`. Its existing Cauchy-operator representative is holomorphic in a strip because `h_s∈L²`; continuity upgrades the almost-everywhere representative equality to pointwise equality. The second term is real analytic: locally it is a constant plus a primitive of the real-analytic kernel. The existing analytic-primitive theorem applies to its real and imaginary parts after translation. Thus the literal core is real analytic on the entire positive axis, for every stated parameter, including nonresonant parameters.

## Global period identity

The existing local scattering identity gives, on the interior of `periodSegment`,

`core_s(a)=E_s(a)−ζ(w)A_w(a)−b_sP_w(a)`,

where `A_w(a)=1+a^(−w)`, `P_w(a)=a⁻¹+a^(1−w)`, and `b_s=2ζ(w−1)/(w−1)`.

All functions in this identity are now real analytic on `(0,∞)`. Connected analytic continuation gives the same equality for every positive `a`. This retains the actual Cauchy integral rather than defining a replacement core.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/CoreCauchyAnalyticContinuation`:

- `mayerFieldLogRemainder_exponential_bound`
- `mayerFieldLogRemainder_integrable_memLp`
- `mayerFieldLogRemainder_cauchy_analytic`
- `mayerPeriodCore_log_boundary_decomposition`
- `mayerPeriodCore_real_analytic`
- `mayerPeriodCore_eq_eisenstein_sub_boundary`

Individual final `lake --old env lean` audit passed without warnings. All six declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Umbrella import wired.
