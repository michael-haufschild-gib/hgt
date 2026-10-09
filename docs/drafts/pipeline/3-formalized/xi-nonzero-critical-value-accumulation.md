# Actual Xi: nonzero critical values accumulate at zero

- **ID:** XI-CRITICAL-ACCUMULATION-20261008
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/RHTower/XiCriticalValueAccumulation.lean`
- **Parent:** `../1-in-progress/xi-single-mark-infinite-cover-exclusion.md`

## Exact unconditional result

For every real T and ε>0, there exists s with Re(s)=1/2, Im(s)>T, xi'(s)=0, and 0<|xi(s)|<ε. Xi therefore has infinitely many nonzero critical values. In centered coordinates, every real tail yields infinitely many distinct nonzero critical values.

This proves a source-specific ingredient for the active infinite-cover attack. It neither proves marked monodromy surjectivity nor discharges RH. External novelty remains unverified under the user's no-web instruction. No claim about absence from literature or training data.

## Dependency-closed paper proof

For t≥2 put s=1/2+it. Exact factorization gives
|XiC(t)|=|s(s−1)/2| pi^(-1/4) |Gamma(s/2)| |zeta(s)|.
The triangle inequality gives |s(s−1)/2|≤2t², and the corpus's elementary strip bound gives |zeta(s)|≤2+4t≤5t. Hence
|XiC(t)|≤80 pi^(-1/4) |(t/2)^3 Gamma(1/4+it/2)|.
The right side tends to zero by the Gamma integral bound and recurrence (`Gamma_vertical_tendsto_zero_mul_pow`), without a Fourier step.

Given T and ε>0, choose U beyond which |XiC(t)|<ε. The unconditional high-simple-critical-line-zero theorem supplies a>max(T,U) and b>a with XiC(a)=XiC(b)=0. Compact zero finiteness selects a consecutive pair p,q with a≤p<q≤b. Rolle's theorem gives c∈(p,q) with XiC'(c)=0. The zero-free gap implies XiC(c)≠0, and c>U gives its small norm.

If a tail supplied only finitely many nonzero critical values, their positive norms would have a positive minimum. Apply the result with ε equal to that minimum to contradict it. The affine coordinate map s=1/2+it has derivative i≠0, so critical points and values transfer to xi.

## Formal details

- `norm_XiC_ofReal_le_gamma_cubic`
- `tendsto_XiC_ofReal_atTop_via_gamma`
- `exists_high_nonzero_small_XiC_critical_value`
- `infinite_XiC_nonzero_real_critical_values_above`
- `exists_high_nonzero_small_xi_critical_value`
- `infinite_xi_nonzero_critical_values`

`SuzukiCharacteristicEntireLimitNoGo.lean` now exports the existing internal lower bound a≤p through `exists_positive_real_XiC_zero_gap_ge_of_two_zeros`. Its previous theorem remains as a compatible corollary.

The scratch proof of all six declarations compiled with zero warnings and no placeholders. Production leaf build, axiom audit and final source check are recorded below. Full formal lint currently has unrelated reachability/index failures; do not infer a clean global gate.

## Log

- 2026-10-08: Complete paper proof and all six scratch declarations checked. Source promoted and wired into RHTower. Active infinite-cover conjecture retained; no route retired.

## Formalized consequence

Xi cannot equal F∘P for any polynomial P and any entire F with finitely many critical values. Paper proof: if P is constant, its composite is constant. Otherwise P' has finitely many zeros, and the chain rule puts every critical value of F∘P in CV(F) union F(P(zeros(P'))), a finite set. This contradicts the proved infinitude for Xi. This exact consequence addresses the polynomial-inner branch of the covering attack; it does not assume the missing outer-function growth theorem.

### Validation update

- Production leaf build `lake build --old +GaloisForLFunctions.RHTower.XiCriticalValueAccumulation`: PASS, including new helper `HTGeometry/PolynomialCriticalValues.lean` and `xi_ne_comp_polynomial_of_finite_critical_values`.
- Ten-declaration axiom audit: PASS, only `propext`, `Classical.choice`, `Quot.sound`; `/tmp/hgt-xi-critical-axioms.log`.
- Previous six-declaration scratch: PASS, warning-free. Final seven-declaration source check: PASS, exit 0 and empty `/tmp/hgt-xi-critical-final.log`.
- Formal index regenerated. Global lint rerun: FAIL on seven unrelated unreachable modules: RHTower.CCMFullGroundZeroSideEigen, RHTower.ChronologicalBoseDilateCompleteness; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No forbidden-declaration or own-module reachability failure. Log: `/tmp/hgt-xi-critical-lint.log`. No global-clean claim.
