# D2 boundary-to-interior no-go

- **ID:** D2-BOUNDARY-INTERIOR-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED / THEOREM (Lean)
- **Statement:** For the actual prime--archimedean log-height defect, “every admissible rational-window frontier lower bound forces a Gaussian-rational interior lower bound” is equivalent to RH.

## Closed chain

False RH supplies an off-line Xi zero. A rational rectangle isolates it while staying in D2's admissible strip. Actual defect is continuous and bounded below on the compact zero-free frontier, but its Gaussian-rational interior values are unbounded below by the exact negative-residue pole-escape theorem. Hence

`frontier floor → interior floor → D2 criterion → RH`

cannot start from frontier-size estimates: its first implication already carries RH.

## No-go closure

- **Killing theorem:** `primeArchLogHeightDefectFrontierLowerForcesGaussianRatInteriorLower_iff_rh`.
- **Actual counterwindow:** `primeArchLogHeightDefectBoundaryBlindWindow_iff_not_rh`.
- **Positive survivor:** contour D2 must first establish zero/residue exclusion inside every window; boundary bounds alone are insufficient.
- **Lean:** `RHTower/PrimeArchLogHeightDefectBoundaryInteriorNoGo.lean`; source check and targeted build pass; no project axioms.
- **Novelty audit through 2026-08:** no exact corpus or literature collision found. Nearby work treats mean/omega or edge-of-strip bounds for `ζ'/ζ`, not this actual-defect boundary/interior equivalence: [Ge 2023](https://arxiv.org/abs/2211.08571), [Li--Zhao 2024](https://arxiv.org/abs/2404.17250), [Chirre--Molero Ravines 2026](https://arxiv.org/abs/2602.06199), [Leong 2026](https://arxiv.org/abs/2405.04869). External priority remains unverified.

## Gates

- [x] paper proof dependency-closed
- [x] Lean source check
- [x] targeted module build
- [x] axiom audit
- [x] umbrella wiring
