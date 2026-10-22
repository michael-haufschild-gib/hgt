# Hedenmalm critical-feature Ward--Green Plancherel fracture

- **ID:** `P-G151`
- **Stage:** `1-in-progress`
- **Type:** FALSIFIED producer; THEOREM (Lean) positive survivor
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [CORPUS-NEW SPECIALIZATION] [NOT RH]`
- **Parent:** `P-G150`
- **Module:** `formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureWardGreenPlancherelFracture.lean`
- **Statement:** Full continuous critical-feature Plancherel reconstructs Ward Hermitian mass exactly,
  but erases height and cannot supply the missing arithmetic same-copy trace.

## Goal

Test whether integrating P-G150 over every real critical-feature center converts its Hermitian
trace into a source-evaluable Plancherel quantity. Extract the strongest exact survivor if the
positive-frame completion loses the RH-bearing information.

## Heavy conjecture loop

1. `[CONJECTURE]` Continuous critical features may create a new arithmetic evaluation of the
   same-copy Hermitian row.
2. `[FAILED AS NOVELTY]` The general source-profile Plancherel law already exists in
   `HedenmalmThetaResolventMetricPlancherel.lean`; restating it would be research theatre.
3. `[PIVOT]` Specialize both Hermitian and holomorphic polarizations to the exact critical-feature
   source profile and measure their discrepancy before claiming a producer.
4. `[PROVED]` For `|Im(z)|<1/2`, real-centered critical evaluation is the angular Fourier transform
   of

   ```text
   f_z(x)=exp(-|x|) sourceChar(z,x).
   ```

   Consequently

   ```text
   integral_t |ell_z(k_t)|^2 = 2 pi / (1-Im(z)^2).
   ```

5. `[PROVED]` Polarized Plancherel pairs `f_conj(z)` with `f_z`. Source-character factors cancel
   pointwise, leaving `exp(-2|x|)`, so

   ```text
   integral_t ell_z(k_t)^2 = 2 pi
   ```

   throughout the strip. This is independent of transverse displacement.
6. `[PROVED]` The exact Hermitian--holomorphic fracture is therefore

   ```text
   E(z)=2 pi Im(z)^2/(1-Im(z)^2).
   ```

   Off the Ward kernel, `G_W(z)=Im(z)^(-2)` gives

   ```text
   G_W(z) E(z)=2 pi/(1-Im(z)^2),
   ```

   exactly the original Hermitian frame mass. Green inversion reconstructs an already
   nonholomorphic quantity; it does not turn it into independently arithmetic data.
7. `[PROVED: SINGULAR KERNEL LAW]` On `Im(z)=0`, Hermitian mass remains `2 pi`, whereas both
   `E(z)` and totalized `G_W(z)E(z)` equal zero. The Green reconstruction is discontinuous at the
   RH locus and cannot itself detect membership there.
8. `[PIVOT]` Integrate one complete P-G150 copy anyway to test whether a counting invariant
   survives. Lean proves

   ```text
   integral_t current_t(q)
     = renormalizedKreinDefect(q) * 2 pi/(1-Im(z_q)^2).
   ```

   Every strict-right multiplicity copy contributes at least `2 pi/81`.
9. `[FAIL AS RH PRODUCER]` Full-orbit integration removes `Re(z_q)`, hence all height-local phase
   needed by prime--Gamma arithmetic. An upper bound could at most control total off-line copy
   count; no source theorem in the corpus supplies the required global integral, and the identity
   does not compare same-copy Hermitian energy with holomorphic Weil polarization.

## No-go closure

- **Exact killing mechanism:** Holomorphic polarization is flat (`2 pi`). All transverse data are
  precisely its Hermitian excess. Ward Green multiplication merely divides that excess by its
  quadratic zero and reconstructs the Hermitian mass. Complete-frame integration additionally
  erases height.
- **Strongest positive survivor:** Exact whole-strip fracture, singular kernel law, Ward
  reconstruction identity, height-erased one-copy density, and strict-right lower charge
  `2 pi/81`.
- **New insight:** Route P's missing producer must act before Hermitianization or before complete
  Plancherel averaging. Any positive Gram completion over the full critical-feature orbit is an
  information-loss/reconstruction identity. A viable successor must retain signed source phase or
  a genuinely bivariate arithmetic coupling through the diagonal limit.
- **Status:** Dependency-closed and formalized. Producer retired; positive survivor remains active
  as a constraint on the next conjecture.

## Lean certificate

Headline theorems:

- `integral_normSq_criticalEvaluation_realCriticalFeature_eq`
- `integral_criticalEvaluation_realCriticalFeature_sq`
- `criticalFeatureContinuousFrameHermitianExcess_eq`
- `wardGreen_mul_criticalFeatureContinuousFrameHermitianExcess_eq`
- `wardGreen_kernel_continuousFrame_fracture`
- `integral_fiveShiftCriticalFeatureWardGreenCurrent_eq_density`
- `fiveShiftWardGreenContinuousFrameDensity_right_ge`

## Gates

- [x] existing Plancherel prior-art/corpus audit
- [x] exact Hermitian frame law
- [x] exact holomorphic polarization law
- [x] whole-strip fracture and kernel classification
- [x] Ward reconstruction no-go
- [x] integrated one-copy law and strict-right lower charge
- [x] direct Lean check
- [x] exact module build
- [x] axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)
- [ ] umbrella build
- [ ] signed or bivariate arithmetic successor
- [ ] unconditional RH

## Log

- 2026-08-13 -- P-G151 opened, continuous-frame producer falsified, strongest survivor formalized.
