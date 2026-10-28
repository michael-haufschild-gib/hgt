# Exact Gamma loss from interval averaging

- **ID:** acs-gamma-interval-averaging-loss
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [coarse Gamma recovery](../1-in-progress/acs-coarse-gamma-recovery.md)
- **Statement:** Replacing the actual Gamma kernel along an interval by its far-end charge loses exactly twice the first kernel moment below the interval width, hence at most `exp(1/2)` times that width when the width is at most one.

## Exact result

Let `I=(a,b)`, `w=b-a>0`, `E=(-∞,a)∪(b,∞)`, `k=archLevyDensity`, and `F(y)=gammaFarCharge(a,b,y)`. For each `x∈I`, Lean proves `F(y)≤k(|y-x|)` in nonnegative extended form. Define

`D(x,y)=ofReal(k(|y-x|))-F(y)`.

Then

`∫_I∫_E D(x,y) = 2*∫_(0,w) t*k(t)`.

For `w≤1`, this is at most `exp(1/2)*w`. These are nonnegative extended integrals; the bound proves finiteness.

Writing `T(s)=∫_(s,∞) k(t) dt` for positive `s`, the actual interval kernel satisfies

`∫_I∫_E k(|y-x|) = 2*w*T(w) + 2*∫_(0,w) t*k(t)`

and, for `w≤1`, is at most `w*(2*T(w)+exp(1/2))`.

The same module proves exact left and right half-line rows. If `δ>0`, `T₀+δ≤a`, and `b+δ≤U₀`, then

`∫_I∫_((-∞,T₀)∪(U₀,∞)) k(|y-x|) ≤ 2*w*T(δ)`.

All integrals retain the original Gamma density. No analytic estimate is supplied as a hypothesis.

## Matched proof

Translate a right half-line row and reflect a left row to the actual Gamma tail. The existing positive-tail integrability theorem makes tail subtraction legitimate. For interior `x`, subtracting the far-end row leaves the kernel window from `b-x` to `w` on the right, and from `x-a` to `w` on the left.

Tonelli on the triangle `0<x<t<w` gives `∫_(0,w)∫_(x,w) k(t)=∫_(0,w) t*k(t)`. Translation and reflection make both interval losses equal this triangle. For `t≤1`, the checked density bound `k(t)≤exp(1/2)/(2t)` cancels the factor `t`, proving the uniform width bound. Adding the far-end charge back gives the exact actual-kernel decomposition. Restricting translated half-line tails gives the separated-row estimate.

## Lean evidence

[GammaIntervalRemainder.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/GammaIntervalRemainder.lean) includes:

- `gamma_interval_row_defect_eq`, `gamma_interval_row_defect_le`
- `gamma_interval_exterior_kernel_eq`, `gamma_interval_exterior_kernel_le`
- `gamma_separated_interval_rows_le`
- exact half-line rows, the triangular first-moment identity, and `gammaFarCharge_le_actual`.

Exact project check passed with no warnings: `lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/GammaIntervalRemainder.lean`. All twelve transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Log: `/tmp/acs-gamma-interval-remainder-final.log`. Umbrella import is wired; umbrella was not compiled.

## Actual pair kernels

[GammaPairRemainder.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/GammaPairRemainder.lean) also passes its exact project check and nine clean transitive audits, without warnings. Log: `/tmp/acs-gamma-pair-remainder-final.log`.

For ordered disjoint intervals `I=(a,b)`, `J=(c,d)`, the actual interaction is exactly its integrated source-row defect plus `|I|*∫_J gammaFarCharge_I`. Even when they touch, it is bounded by that same defect plus `|I|*|J|*k(|I|)`. With a positive gap, the farthest-endpoint replacement loss is at most `|I|*|J|*[k(c-b)-k(d-a)]`. Monotonicity proves these pointwise bounds before integration. Both the interaction and endpoint loss are symmetric and invariant under common translation.

The exact decomposition holds against any set, including the full exterior (`gamma_interval_set_kernel_eq_defect_add_far`). `gammaIntervalPairDefect_le_endpoints` connects the checked discrete rows directly to integrated kernels; `gammaIntervalKernel_le_defect_add_width` retains the entire touching loss. Together, both modules have twenty-one clean axiom audits.

## Finite symmetric error

[GammaFiniteError.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/GammaFiniteError.lean) passes its exact project check and four clean transitive audits, without warnings. Log: `/tmp/acs-gamma-finite-error-final.log`.

Set `Rᵢᵢ=0` and let `Rᵢⱼ` be the actual integrated farthest-endpoint replacement error off the diagonal. For every finite interval family and arbitrary real coefficients,

`Σᵢⱼ (qᵢ-qⱼ)² Rᵢⱼ ≤ 4*Σᵢ qᵢ²*Σⱼ Rᵢⱼ`.

Symmetry and `(u-v)²≤2(u²+v²)` prove this directly in nonnegative extended integrals. Diagonal coefficient differences vanish. `gammaFinitePairDefect_weighted_kernel_le` also proves that each actual weighted kernel is at most its retained mean edge plus this explicit error, without assuming a row bound. All three modules now have twenty-five clean axiom audits.

## Exterior subsets and finite boundary charges

[GammaExteriorSubsets.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/GammaExteriorSubsets.lean) passes its exact project check and four clean transitive audits, without warnings. Log: `/tmp/acs-gamma-exterior-subsets-final.log`.

For any `F⊆Iᶜ`, with `0<w=|I|≤1`, `gamma_interval_exterior_subset_defect_le` bounds `∫_I∫_F D` by `exp(1/2)*w`. `gamma_interval_exterior_subset_kernel_le` bounds the actual kernel by `w*(2*T(w)+exp(1/2))`. The two endpoints are null, so restriction to any exterior subset preserves the checked full-exterior estimates.

`gamma_interval_far_charge_le` bounds `∫_F ofReal(w*q²)*gammaFarCharge_I` by `ofReal(q²*w*(2*T(w)+exp(1/2)))`. The exact kernel decomposition first bounds the far charge by the actual interaction, and the finite kernel estimate then gives this bound. Thus finiteness is proved before any real conversion. `gammaIntervalPairDefect_le_boundary` also bounds a touching replacement error by the full source-row loss plus `ofReal(w*|J|*k(w))`. All four modules have twenty-nine clean axiom audits.

## Remaining parent obligation

The interval averaging loss, separated tails, symmetric finite-error estimate, and [actual coarse-source accounting](acs-coarse-gamma-accounting.md) are formalized. Recovering the entire coarse Gamma energy still requires uniform complete logarithmic-cell row bounds and the final real comparison. Full mixed Weil positivity remains open.

## Log

- 2026-10-28 — Exact project and transitive audits passed; recorded directly in stage 3.
