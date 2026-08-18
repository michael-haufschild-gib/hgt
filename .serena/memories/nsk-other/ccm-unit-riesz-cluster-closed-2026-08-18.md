# CCM unit-Riesz cluster — closed at stage 3 (2026-08-18)

All seven `ccm-*` cards that were in
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other` are now at
`3-formalized/new_scientific_knowledge/other`.  That folder no longer contains any `ccm-*` card;
the earlier ledger note "the six ccm-* cards belong to a concurrently running CCM agent" is stale.

## What was already done vs. what was new

Already complete (only audited, no new Lean):
`ccm-unit-riesz-exponential-coherent-trace`, `ccm-unit-riesz-hankel-boundary-pulse`,
`ccm-unit-riesz-suzuki-green-producer-classification`.

New modules (all wired into `GaloisForLFunctions.RHTower`, all unconditional):

```text
RHTower/CCMUnitRieszCoherentGeneratorSampling.lean         (13) in generator-energy form
RHTower/CCMUnitRieszApertureResolventEpsilonTransfer.lean  §4 all-epsilon order transfer
RHTower/CCMUnitRieszCesaroFiniteApertureReporter.lean      (9),(10),(12)-(17), iff (20)-(21)
RHTower/CCMUnitRieszVolterraLaplace.lean                   the reusable convolution law
RHTower/CCMUnitRieszStirlingLaplace.lean                   L[a](z) = zeta(1+z)/(1+z)^2 - 1/z - 1/(z+1)
RHTower/CCMUnitRieszCompletedCurrentLaplace.lean           L[W](z) = 2/z - 2/(z+1) - LSeries Λ (1+z)/(z+1/2)
RHTower/CCMUnitRieszCompletedSourceLaplaceWeld.lean        (25)-(28)
```

## Reusable assets — check these before building anything Laplace-shaped

- `integral_Ioi_expVolterra_laplace {b} (hb : 0 ≤ b) {z} (hz : 0 < z.re) {φ C}
  (hφ : Measurable φ) (hbnd : ∀ h > 0, |φ h| ≤ C(1+h))`:
  `∫_{Ioi 0} e^{-zt} (∫_{Ioc 0 t} e^{-b(t-h)} φ(h) dh) dt = (z+b)⁻¹ ∫_{Ioi 0} e^{-zh} φ(h) dh`.
  Companion `integrableOn_Ioi_cexp_mul_expVolterra` (same hypotheses) gives integrability of the
  outer integrand, which is what lets you split a two-exponential kernel.
  **This removes the need for Stieltjes–Laplace measure theory whenever the kernel is a finite
  combination of pure decaying exponentials.**
- `integral_Ioi_cexp_neg_mul_linear` (`∫_0^∞ u e^{-wu} du = 1/w²`) and its shifted complex/real
  forms `integral_Ioi_cexp_neg_mul_linear_shift`, `integral_Ioi_rexp_neg_mul_linear_shift`.
- `setIntegral_Ioi_of_vanishing_lt`, `integrableOn_Ioc_of_vanishing_Ioo`
  (in `CCMUnitRieszCompletedCurrentLaplace`): the half-line split for arithmetic atoms whose
  switch-on point is **closed**, i.e. the atom does not vanish at `h = log n`.  The corpus's
  `setIntegral_Ioi_of_vanishing` needs vanishing on the closed ray and does not apply there.
- `unitRieszStirlingHead_laplace`, `unitRieszCompletedCurrent_laplace`,
  `unitRieszPrimeCurrent_laplace` — the three arithmetic Laplace transforms.
- `measurable_criticalMellinPrimeMass`, `measurable_criticalMellinCompletedError`,
  `measurable_unitRieszStirlingCorrection`: floor-staircase measurability, done by
  `measurable_from_top.comp (Nat.measurable_floor.comp Real.measurable_exp)` after rewriting the
  function as `g ∘ (fun h => ⌊exp h⌋₊)` with a `rfl` `have`.
- `abs_criticalMellinCompletedError_le_log_sqrt` (corpus, `XiMassCriticalErrorFlux`) gives
  `|E(h)| ≤ 2(h+1)exp(h/2)`, hence the critically weighted current `exp(-h/2)E(h)` is bounded by
  `2(1+h)` — exactly the linear-growth hypothesis the convolution law wants.

## Lean traps hit on this pass

- `HasDerivAt.mul` / `.add` / `.pow` produce **Pi**-algebra functions (`c * d`, `f + g`), not
  lambdas.  `convert ... using 1` then descends into instance arguments and leaves goals like
  `Real.instAddCommGroup = Real.normedAddCommGroup.toAddCommGroup`.  Fix: `simp only [Pi.mul_def,
  Pi.add_def] at h` and finish with `exact h.congr_deriv (by ring)` — never `convert`.
- `hlin : HasDerivAt (fun x => t - x) (-1) s` must be built as
  `simpa using (hasDerivAt_id s).const_sub t`; the `(hasDerivAt_const s t).sub (hasDerivAt_id s)`
  route lands in the wrong instance path.
- `field_simp` in this toolchain does **not** clear `(3 + z*2)⁻¹` even when
  `(3 : ℂ) + z*2 ≠ 0` is in context (it arises from normalizing `z + 3/2`).  Fix: let `field_simp`
  run, then close with `linear_combination` against `mul_inv_cancel₀` facts.
- `Integrable.const_mul` / `.sub` conclusions must be given an explicit `IntegrableOn (fun t => …)`
  type ascription, otherwise `integral_sub` will not match the goal's lambda.
- `IntegrableOn.congr_fun` needs `EqOn f g s` in the direction `source = target`, and the goal is
  beta-unreduced: open with `show` spelling out the reduced equation.
