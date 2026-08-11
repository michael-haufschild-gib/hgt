# Adaptive canonical singular source and rank-fill law

- **ID:** adaptive-canonical-singular-source-rank-fill-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 exact open core
- **Statement:** At first singular Hankel face, actual inverse-Hankel `P^sharp` remains finite; its division-free norm flux lands on completed adaptive arithmetic packet, whose sign exactly classifies next PSD rank-one extension.

## Gates

- [x] 0 → 1: hostile conjecture/failure loop recorded
- [x] 1 → 2: dependency-closed paper proof `[PROVED HERE]`
- [x] 2 → 3: unconditional Lean proofs; direct check, targeted build, axiom audit green
- [ ] 3 → 4: specialist novelty review and standalone exposition

## Exact theorem `[PROVED HERE]`

Let `H_n(y)` be shifted-Xi Hankel block, `P_n^sharp` canonical monic admission built from
`H_n⁻¹`,

`N_n=L_y((P_n^sharp)²)`, `B_n=L_y(P_n^sharp X P_n^sharp)`,

`a_n=[X^(n-1)]P_n^sharp`, `Φ_n=2a_nN_n-(2n+1)B_n`.

Whenever `det H_n≠0`, actual admission motion obeys division-free law

`N_n'=Φ_n`.

At flat face `H_(n+1)c_n=0`, `N_n=0`, `B_n=R_n`, where
`R_n=Δ_(2n+1)` is canonical first-unseen monic remainder.  Hence

`N_n'=-(2n+1)R_n`.

Two exhaustive branches follow:

1. `R_n≠0`: `H_(n+2)` is not positive semidefinite.
2. `R_n=0`: actual coefficient velocity is tangent to null flag, so

   `B_n'=-2Σ_n`,

   `Φ_n'=2(2n+1)Σ_n=(2n+1)A_completed^sharp`,

   `A_completed^sharp=2(n+1)Δ_(2n+2)`.

Rank-one boundary decomposition gives exact equivalence

`H_(n+2)⪰0 ↔ Δ_(2n+2)≥0 ↔ A_completed^sharp≥0`.

Producer is admission-sensitive and source-first: select odd `P_n^sharp`, form even bilinear shear,
then complete aggregate.  No orientation map or fixed linear reporter.

## Proof-or-fail loop

1. **Conjecture:** first face can destroy inverse-Hankel admission.  **FAIL.** Degree-`n` admission
   denominator is `H_n`, still positive definite when `H_(n+1)` first becomes singular.  Only
   quotient `B_n/N_n` becomes undefined.
2. **Conjecture:** ordinary Jacobi norm ODE can be taken to face.  **FAIL.** It divides by `N_n=0`.
   Positive survivor is raw flux `Φ_n`.
3. **Conjecture:** monic coefficient motion adds uncontrolled singular connection.  **FAIL.** At
   flat face its degree-lower velocity pairs to zero by null-kernel orthogonality.
4. **Conjecture:** completed source is merely orientation witness.  **FAIL.** Adjacent-defect
   theorem identifies it exactly with first even Padé coordinate; rank-one decomposition makes its
   sign equivalent to PSD extension.
5. **Conjecture:** lower finite face signs completed source.  **FAIL.** First even successor is free
   while every lower defect is held fixed.  Positive survivor is exact boundary classifier; missing
   RH input must be cofinal across parity lifts.

## Lean certificate

- `HTGeometry.MonicMomentAdmissionNormTransport`
  - `momentInner_monicMomentAdmission_lower_eq_zero`
  - `momentFunctional_X_shiftedEuler_one_sq_monicMomentAdmission`
- `RHTower.XiShiftedCanonicalAdmissionConnection`
  - `hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det`
  - `hasDerivAt_xiShiftedCanonicalAdmissionNorm_of_flatFace`
  - `hasDerivAt_xiShiftedCanonicalAdmissionOddCurrent_eq_adaptiveShear_of_flatFace`
  - `hasDerivAt_xiShiftedCanonicalAdmissionNormFlux_eq_completedAggregate_of_flatTangent`
  - `xiShiftedCanonicalAdmission_firstFace_preemption_or_completedSource`
- `RHTower.XiShiftedCanonicalAdmissionSingularSourceLaw`
  - `xiShiftedCompletedMomentAggregate_canonicalFlatTangent_eq_evenPadeDefect`
  - `xiShiftedMomentHankelMatrix_succ_posSemidef_iff_evenPadeDefect_nonneg_of_flatTangent`
  - `xiShiftedCanonicalAdmission_succ_posSemidef_iff_completedSource_nonneg_of_flatTangent`
  - `hasDerivAt_xiShiftedCanonicalAdmissionNormFlux_eq_evenPadeDefect_of_flatTangent`

## Remaining boundary

First face is closed.  Positive even defect rank-fills next block; zero even defect prolongs flat
plateau.  Existing odd-contact parity theorem proves first later nonzero odd defect preempts its
successor.  Exact open core is now cofinal arithmetic exclusion of unbounded plateau/degree escape.
Finite face data cannot supply it.  RH is not yet proved.

## Log

- 2026-08-11 — paper proof and unconditional Lean formalization completed without computation.
- 2026-08-11 — direct Lean check and targeted module build PASS.  Axiom audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
