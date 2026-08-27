# Finite Schur quartic spectral split tightness

- **ID:** GTA-PQ4-SC1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean; stage-3 lint promotion pending unrelated umbrella repair)
- **Source:** `rh-current-frontier-map.md` · route GTA (`COF + ORIENT`)
- **Statement:** A Schur packet whose eigenvalues above squared-modulus threshold `δ` have squared imaginary part at most `η` has total positive quartic charge at most `2300 (δ + η)` times matrix Hilbert--Schmidt energy.

## Goal
Supply dimension-free spectral tightness needed to turn compact zero localization for finite theta
determinants into decay of the actual Schur quartic charge.  The bound is finite, source-side, and
does not assume RH or normality.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, exact build green, axiom audit and lint pass
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
**[PROVED HERE]** Corpus search exposes two exact ingredients: the local charge polynomial
`100 y^2 (6 x^2 + 23 y^2)` and Schur diagonal energy bounded by matrix Hilbert--Schmidt energy.
For `x^2+y^2 ≤ δ`, local charge is at most `2300 δ (x^2+y^2)`.  For a complementary diagonal
with `y^2 ≤ η`, it is at most `2300 η (x^2+y^2)`.  Split the finite diagonal and sum, avoiding
any eigenvalue-count or dimension factor.

## Conjecturing loop
- `[GTA-PQ4-SC1.1]` Bound tail by number of small eigenvalues times `δ^2`. Rejected: dimension loss
  prevents passage to growing theta stages.
- `[GTA-PQ4-SC1.2]` Use Schur Hilbert--Schmidt energy to weight each local charge by eigenvalue
  squared norm. Scratch proof closed the small-spectrum half.
- `[GTA-PQ4-SC1.3]` Split at `δ`; compact localization supplies `Im(λ)^2 ≤ η` on the large half.
  The dimension-free total bound is proved.

## Novelty audit
- Internal corpus search on 2026-08-27 found Schur diagonal Hilbert--Schmidt control and the local
  positive quartic polynomial, but no dimension-free small/large spectral split for this charge.
- External exact-term and concept searches through 2026-08-27 found finite-section determinant
  convergence and unrelated non-self-adjoint real-axis localization, but no Schur quartic charge or
  this `2300(δ+η)·HS²` inequality. Bornemann's arXiv:0804.2543 is numerical Fredholm-determinant
  approximation; Sierra's arXiv:1601.01797 is a tuned spectral model. Novelty remains
  **UNVERIFIED**, not a priority claim.

## Lean certificate
- Module: `GaloisForLFunctions.HTGeometry.FiniteMatrixSchurPositiveQuarticSpectralSplit`.
- Main theorem: `finiteMatrixSchurPositiveQuarticCharge_le_of_large_im_sq_le`.
- Small-tail theorem: `finiteMatrixSchurPositiveQuarticSmallSpectrumCharge_le`.
- `lake env lean` and exact `lake build` pass. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Global lint reaches only an unrelated unwired concurrent module:
  `GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBlockConvolution`.

## Log
- 2026-08-27 — frozen after corpus search and successful Lean scratch proof of small-spectrum tail.
- 2026-08-27 — `.1 → .2 → .3` loop closed; paper proof and unconditional Lean theorem completed.
- 2026-08-27 — moved to 2-fully-proven pending clean global lint rerun.
