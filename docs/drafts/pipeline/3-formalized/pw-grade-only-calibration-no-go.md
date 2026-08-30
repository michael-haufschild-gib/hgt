# Parikh--Wilczek grade-only diagonal calibration no-go

- **ID:** PW-B-GRADE-ONLY-CALIBRATION-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `ThetaCuspHawkingParikhWilczekSignedMatrixThreeMomentClassification.lean` · `ThetaCuspHawkingParikhWilczekCalibratedRecoilEndpointTomography.lean` · route PW-B
- **Statement:** Two distinct PW recoil grades cannot be aligned at two distinct off-wall spectral coordinates by fixed nonzero grade scalars; consequently no spectrally independent nondegenerate diagonal grade calibration can supply the common wall channel used by PW-B endpoint tomography.

## Goal

Kill proof chain

`fixed grade-only recoil coupling → common oriented wall channel → countable endpoint winding tomography → Xi-flatness → RH`.

This separates source mechanism from receiver normalization. Existing calibrated endpoint tomography divides by the full residual at the observed spectral parameter. Proposed branch asked whether fixed physical couplings, chosen before spectral observation and depending only on grade, could produce same common channel.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Corpus factorization gives

`Im H_k(s) = W(s) (X(s) + λ_k)`,

where `W(s)` is common reflection-wall orientation and `λ_k = 4k(k+1)`. Test fixed grade scalars against two off-wall spectral probes. Affine dependence on `X` makes two probes enough to classify all such calibrations.

## Paper proof

**[PROVED HERE]** Let grades `i,j` satisfy `λ_i ≠ λ_j`, and let spectral points `s,t` satisfy `W(s)W(t) ≠ 0` and `X(s) ≠ X(t)`. Suppose fixed real scalars `a,b` align raw recoil orientations at both probes:

`a Im H_i(s) = b Im H_j(s)`,

`a Im H_i(t) = b Im H_j(t)`.

Cancel nonzero wall factors independently. Then

`a(X(s)+λ_i) = b(X(s)+λ_j)`,

`a(X(t)+λ_i) = b(X(t)+λ_j)`.

Subtract equations. This gives `(a-b)(X(s)-X(t))=0`, so `a=b`. Substitute into either equation: `a(λ_i-λ_j)=0`. Distinct shifts force `a=0`, hence `b=0`.

For closed branch kill take `i=0`, `j=1`, `s=1/4+I`, and `t=1/4+2I`. Direct identities are

`W(s)=1`, `W(t)=2`, `X(s)=35/16`, `X(t)=83/16`, `λ_0=0`, and `λ_1=8`.

Thus any fixed scale family aligning every pair of grades throughout open strip has zero scales at grades zero and one, contradicting nondegeneracy.

Positive classification is exact. At one off-wall strip point, if scalar `a` recovers wall itself,

`a Im H_k(s)=W(s)`,

then cancellation and strict positivity of residual give

`a=(X(s)+λ_k)⁻¹`.

Therefore calibrated endpoint normalization is uniquely forced and spectrally dependent.

## Hostile audit

- The theorem does not attack existing receiver theorem; it explains why its division by `schwarzschildParikhWilczekBorelGradeResidual s k` cannot be replaced by fixed grade-only source weights.
- Allowing a different common output does not evade no-go: two-point theorem assumes only equality between calibrated grades, not equality to canonical wall.
- Degenerate zero calibration is classified, not silently excluded.
- Surviving mechanisms remain spectral feedback, non-diagonal grade mixing, and nonlocal coupling. The result does not claim those impossible.
- August 2026 literature audit found PW tunneling law and its energy-conserving nonthermal correction, plus work on emission correlations and limits of PW nonthermality, but no Borel-grade calibration theorem or this affine two-probe rigidity. Exact objects and proof burden originate in Lean corpus.

## No-go closure

- **Exact killing theorem/mechanism:** affine grade residuals at two distinct spectral coordinates force any fixed two-grade alignment scalars to coincide; distinct grade shifts then force both to vanish.
- **Strongest positive survivor:** exact single-point uniqueness `a=(X(s)+4k(k+1))⁻¹`. Common diagonal wall recovery necessarily reads spectral parameter.
- **New insight:** current PW-B endpoint calibration is an exact receiver normalization, not a spectrally independent grade-only producer. Missing producer must contain spectral feedback or genuinely non-diagonal/nonlocal grade dynamics.
- **Status:** dependency-closed paper proof and Lean formalization complete in `ThetaCuspHawkingParikhWilczekGradeOnlyCalibrationNoGo.lean`.

## Lean certificate

- Unique normalization: `schwarzschildParikhWilczekWallCalibration_unique`.
- General two-point rigidity: `schwarzschildParikhWilczekGradeOnlyCalibration_twoPoint_rigidity`.
- Calibration property: `SchwarzschildParikhWilczekGradeOnlyDiagonalCalibration`.
- Closed route kill: `no_schwarzschildParikhWilczekGradeOnlyDiagonalCalibration`.
- Direct `lake env lean` check: PASS.
- Targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGradeOnlyCalibrationNoGo`: PASS (`11570/11570`; shared worktree required stale dependency replay).
- Axiom audit for all named theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- Wired into `GaloisForLFunctions.RHTower` umbrella. Global lint reaches new module and remains red only on unrelated concurrently unwired modules; no lint error names this module.

## Log

- 2026-08-29 — corpus audit identified spectral dependence in existing calibrated endpoint and found no grade-only rigidity theorem.
- 2026-08-29 — paper proof completed after two weaker FZZ conjectures were falsified or found already solved in corpus.
- 2026-08-29 — Lean formalization, targeted build, axiom audit, umbrella wiring, and lint reachability audit completed; moved to 3-formalized.
