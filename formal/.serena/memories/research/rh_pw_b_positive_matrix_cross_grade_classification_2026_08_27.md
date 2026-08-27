# PW-B positive matrix cross-grade classification (2026-08-27)

Formalized:
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekPositiveMatrixCrossGradeClassification.lean
- wired into formal/GaloisForLFunctions/RHTower.lean
- card docs/drafts/pipeline/3-formalized/pw-b-positive-matrix-cross-grade-classification.md
- frontier map read only

Exact results:
- Every Borel-grade recoil phase factors as W(s) R_k(s), with W=-2 Im(s)(2 Re(s)-1) and R_k strictly positive in open strip.
- Every finite real matrix cross-grade energy factors as W(s)^2 times residual matrix energy.
- If matrix is entrywise nonnegative and has a positive entry, residual energy is strictly positive throughout strip.
- At nonreal strip points, energy zero iff Re(s)=1/2.
- Universal zero on Xi divisor support is exactly RH for every such matrix.

Route closure:
Every finite entrywise-nonnegative matrix-valued cross-Borel interaction is a receiver, not producer. Viable PW-B dynamics must use signed/complex orientation-sensitive coefficients, infinite/singular interaction, or additional channels not sharing common wall factor.

Verification:
- direct lake env lean passed
- targeted lake build module passed
- six exported theorem axiom audit only propext, Classical.choice, Quot.sound
- scratch removed

Novelty audit:
Corpus had scalar histories and gradewise formulas but no matrix factorization. Literature compared original PW arXiv:hep-th/9907001 and opposite correlation claims arXiv:1305.6341 / arXiv:1406.3635. No exact Borel-grade matrix/RH law found; priority provisional.