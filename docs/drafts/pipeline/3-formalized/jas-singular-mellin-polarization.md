# JAS singular Mellin polarization and closed anomaly shadow

- **ID:** JAS-SMP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** read-only `rh-current-frontier-map.md` · JAS `ORIENT COMP`; corpus Gamma-sewn
  synchronized lcm cocycle, BV--Wold graded determinant-two anomaly, additive Mellin translation,
  `L²` reflection, and maximal real `L²` multiplication
- **Statement:** Every positive Gamma-sewn or BV--Wold scalar anomaly has a zero-independent
  unitary logarithmic-translation lift on one fixed positive `L²(ℝ)` carrier.  Multiplication by
  `exp(x)` gives a dense closed self-adjoint scalar (`ℂ`-linear) shadow recovering the anomaly;
  multiplication by `exp(-x)` is its reflected closed partner.  Gamma compound faces agree with
  the original lcm weights and commute on every two-prime square, while the graded BV--Wold
  anomaly makes each curved transport triangle exactly flat.

## Goal

Test whether the actual finite-support/valuation anomaly diagram admits a zero-independent
positive polarization with a closed, single-valued scalar shadow.  Then audit whether that shadow
meets JAS's stronger `C(PrimeTorus)`-source-linearity gate, rather than conflating the two notions.

## Gates

- [x] 0 → 1 in-progress: mandatory corpus search, source-derived conjecture, hostile falsifier loop,
  current primary-literature search
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact Lean source check/build, scoped axiom audit, forbidden-declaration
  scan, umbrella wiring
- [ ] 3 → 4 publication-ready: standalone paper and independent novelty review

## Conjecture loop and result

1. **C1 — positive anomalies can be represented without a gain-dependent metric.**  Finite
   positive invariant metrics are terminal in the corpus.  Replacing scalar dilation by the left
   regular representation gives `g ↦ T_{-log g}` on one fixed `L²(ℝ)` carrier.  Each transport is
   unitary, preserves the Hilbert inner product exactly, multiplies correctly, and reflection sends
   `g` to `g⁻¹`. **[PROVED HERE]**
2. **C2 — a scalar exponential reporter may close the JAS shadow.**  Failed: the scalar functional
   `f ↦ ∫ exp(x)f(x) dx` has the correct eigencharacter but cannot be the required ordinary bounded
   `L²` reporter.  This is the precise singularity predicted by the corpus.
3. **C3 — promote reporter to a maximal unbounded operator.**  Multiplication by `exp(x)` on its
   maximal `L²` domain is dense and self-adjoint, hence closed.  Its exact covariance is
   `M_exp T_t = exp(-t) T_t M_exp`; at `t=-log g` the closed shadow recovers `g` exactly.
   **[PROVED HERE]**
4. **C4 — reflection may destroy the maximal domain.**  Failed as a falsifier.  Multiplication by
   `exp(-x)` is also dense, self-adjoint, and closed.  Spatial reflection maps the positive maximal
   domain into the negative one and intertwines both operators exactly. **[PROVED HERE]**
5. **C5 — state-dependent Gamma compound gains may break positivity or path independence.**
   Failed as a falsifier.  Every synchronized lcm insertion gain is strictly positive.  The closed
   shadow agrees with the exact inserted lcm weight, and both orders around every admissible
   two-prime square give the same unitary transport. **[PROVED HERE]**
6. **C6 — the BV--Wold graded anomaly may remain curved after lifting.**  Failed as a falsifier.
   Its unitary lift is translation by the exact consecutive-increment area, its closed shadow is
   the original determinant-two anomaly, and insertion into the two source transports makes the
   triangle exactly flat. **[PROVED HERE]**

## Hard-frontier significance and exact remaining burden

This is not a bound improvement or a renamed RH receiver.  It constructs the missing kind of
object excluded by the finite and bounded scalar no-go results: one fixed positive carrier together
with a genuinely unbounded but closed scalar anomaly detector.  It simultaneously handles all
Gamma compound faces and the independent BV--Wold valuation-depth curvature on the same carrier.

It closes only a **scalar analytic existence / closed-shadow / finite-face compatibility** subgate.
It does not close JAS or prove RH.  In particular,
`primePoisson_reflection_nonzeroClosedSourceLinearSewing_iff` proves that ordinary reflected
prime-Poisson multiplication sectors admit a nonzero closed densely defined single-valued
`C(PrimeTorus)`-source-linear sewing iff `σ = 1/2`; this module's multiplication operator is merely
`ℂ`-linear and does not evade that theorem.  Remaining hard theorem is therefore a different
arithmetic comparison mechanism retaining prime support/history, followed by completed-theta/Xi
identification.  Until then this is a scalar ingredient, not a JAS closure or RH proof.

## Lean artifact

- Module: `GaloisForLFunctions.RHTower.JointAncestrySingularMellinPolarization`
- Positive carrier and closed shadow:
  - `jointAncestryPositiveMellinLift_inner`
  - `jointAncestrySingularMellinOperator_dense`
  - `jointAncestrySingularMellinOperator_selfAdjoint`
  - `jointAncestrySingularMellinOperator_closed`
  - `jointAncestrySingularMellinOperator_covariance`
  - `jointAncestrySingularMellinOperator_mellinLiftCovariance`
- Reflection:
  - `jointAncestryPositiveMellinLift_inv_reflection`
  - `jointAncestrySingularMellinReflectedOperator_closed`
  - `jointAncestrySingularMellinOperator_reflection_mem`
  - `jointAncestrySingularMellinOperator_reflection_covariance`
- Gamma all-compound finite faces:
  - `jointAncestry_gammaSewnSynchronizedLcmInsertionGain_pos`
  - `jointAncestry_gammaSewnMellinLift_closedShadow_weightInsert`
  - `jointAncestry_gammaSewnMellinLift_cocycle`
- BV--Wold valuation-depth curvature:
  - `jointAncestry_primeDepthBVWoldAnomaly_mellinLift_eq_translation`
  - `jointAncestry_primeDepthBVWold_mellinLift_flat`
  - `jointAncestry_primeDepthBVWoldAnomaly_mellinLift_closedShadow`
- Verification:
  - `lake env lean GaloisForLFunctions/RHTower/JointAncestrySingularMellinPolarization.lean` — PASS
  - `lake build GaloisForLFunctions.RHTower.JointAncestrySingularMellinPolarization` — PASS
    (`Built ...`, 39s)
  - scoped `#print axioms` — only `propext`, `Classical.choice`, `Quot.sound`
  - forbidden-declaration scan and scoped `git diff --check` — PASS
  - leaf wired into `GaloisForLFunctions.RHTower`
  - global `scripts/formal_tools.py lint` currently reports unrelated concurrent un-wired modules;
    this new module is reachable and is not among reported failures

## Literature audit (as of 2026-08-28)

- Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*
  (arXiv:math/9811068), interprets zeta zeros through scaling on adelic quotient spaces, not a
  Gamma-lcm/BV--Wold common closed anomaly shadow.
- Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*
  (arXiv:math/0203120), develops co-Poisson, Sonine, and distributional structures, not this
  reflected maximal-exponential operator lift of finite-support/valuation cocycles.
- Sierra, *H = xp with interaction and the Riemann zeros* (arXiv:math-ph/0702034), studies
  dilation Hamiltonians and Jost functions, not state-dependent arithmetic compound cocycles.
- Connes--Consani, *Weil positivity and Trace formula, the archimedean place*
  (arXiv:2006.13771), studies compressed scaling actions and Weil positivity, not the exact
  all-compound finite-face and BV--Wold flatness laws proved here.
- Hansen--Tong, *Complex Moments, Gamma and Riemann Zeta Functions unified by the Parabolic Mellin
  Transform* (arXiv:2602.17007), develops a 2026 Fourier--Laplace/Mellin framework, not a closed
  self-adjoint anomaly reporter for these corpus-native source diagrams.
- Logarithmic translation, maximal multiplication, and reflection are individually classical.
  Targeted searches found no source combining them with the exact Gamma-sewn lcm insertion
  cocycle, its finite-face weights, and the BV--Wold graded anomaly. **Novelty status:**
  `[NOVELTY UNVERIFIED]` pending independent expert review.

## Door passport

- **Unconditional source:** explicit positive Gamma-sewn gains, exact lcm weight insertion and
  cocycle, exact BV--Wold transport/anomaly identity, Haar translation/reflection, maximal real
  `L²` multiplication.
- **No RH leakage:** no Xi zero, RH premise, zero enumeration, numerical computation, new axiom,
  or target-fitted choice enters any declaration.
- **Burden removed:** existence of a zero-independent fixed positive carrier with closed
  single-valued scalar shadows compatible with all synchronized compound faces and the independent
  valuation-depth anomaly.
- **Burden not removed:** `C(PrimeTorus)`-source-linear sewing (terminal off wall for the ordinary
  multiplication model), completed theta tomography/prime-Poisson first-jet comparison by any
  surviving mechanism, infinite provenance-continuous arithmetic assembly, and Xi landing.

## Log

- 2026-08-28 — created from mandatory Lean-corpus research; frontier map remained read-only.
- 2026-08-28 — scalar reporter failed the closedness audit; pivoted to maximal self-adjoint
  multiplication rather than abandoning the hard JAS core.
- 2026-08-28 — reflected closed pair, Gamma finite-face/cocycle lift, BV--Wold flat lift, source
  check, leaf build, and axiom audit completed.
- 2026-08-28 — hostile corpus audit found
  `primePoisson_reflection_nonzeroClosedSourceLinearSewing_iff`; corrected the initial
  source-linearity overclaim.  The construction is `ℂ`-linear only and does not close JAS's
  prime-Poisson sewing gate.
