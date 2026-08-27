# PW-B positive matrix cross-grade classification

- **ID:** PW-B-MCG
- **Stage:** 3-formalized
- **Type:** MATRIX-HISTORY CLASSIFICATION / NO-GO SURVIVOR
- **Parent:** PW-B
- **Frontier-map policy:** read only; no edit made

## Exact result

Every Borel-grade recoil phase splits as

`phase_k(s)=W(s)R_k(s)`,

where `W(s)=-2 Im(s)(2 Re(s)-1)` is common wall factor and

`R_k(s)=(2k+Re(s)+1/2)(2k+3/2-Re(s))+Im(s)^2+1/4`

is strictly positive throughout open critical strip.

For arbitrary finite real matrix `M`, cross-grade interaction

`Q_M(s)=Σᵢⱼ Mᵢⱼ phase_i(s)phase_j(s)`

therefore factors exactly as

`Q_M(s)=W(s)^2 Σᵢⱼ Mᵢⱼ R_i(s)R_j(s)`.

If `M` is entrywise nonnegative and has at least one positive entry, residual
double sum is strictly positive. At nonreal strip points,

`Q_M(s)=0 ↔ Re(s)=1/2`.

Universal vanishing on actual Xi divisor support is therefore exactly RH for
every such matrix.

## Paper proof

Insert corpus recoil identity into every matrix entry and extract common factor
`W(s)^2`.  Strip inequalities make both linear factors in every `R_k` positive;
remaining square and quarter terms are nonnegative/positive.  Entrywise
nonnegative matrix gives nonnegative summands, and one positive entry gives one
strictly positive summand.  Thus matrix residual cannot vanish.  Since
`Im(s)≠0`, vanishing of `W(s)^2` is equivalent to `2 Re(s)-1=0`.  Xi-support
result follows from standard divisor-support/RH bridge.

## No-go closure and positive survivor

This closes not only scalar histories but every finite entrywise-nonnegative
matrix interaction across Borel grades. Positive covariance, positive shell
correlation, and positive finite channel mixing preserve exact wall detector;
they cannot supply unconditional flatness.

Strongest positive survivor: viable PW-B interaction must use at least one of:

- signed or complex orientation-sensitive matrix coefficients;
- a genuinely infinite cross-grade interaction whose completion is not finite
  positive summation;
- singular/nonlocal memory or additional channel data not sharing common wall
  factor.

Such extension still needs literal source derivation before divisor selection.

## Hostile review

- Entrywise nonnegative is stronger/different from positive semidefinite; theorem
  does not claim all PSD matrices have positive residual on this vector.
- Matrix may be nonsymmetric; proof uses only entrywise signs.
- Finite dimension is explicit.
- Result diagnoses receiver structure; it does not assert physical PW correlation
  matrix has these signs.
- Universal flatness remains RH-equivalent, not proved.

## Novelty audit (2026-08-27)

Corpus search found scalar shell histories, two-copy reflection aggregates, and
gradewise PW growth/holonomy laws, but no finite matrix cross-grade factorization
or positivity classification.  Primary literature derives nonthermal PW emission
and debates correlations/information carried by successive emissions, but search
found no Borel-grade common-wall matrix theorem or RH application. Priority is
provisional pending expert review.

Primary comparison sources:

- arXiv:hep-th/9907001, *Hawking Radiation as Tunneling*
- arXiv:1305.6341, *Information conservation is fundamental: recovering the lost
  information in Hawking radiation*
- arXiv:1406.3635, *Tunneling across the quantum horizon does not resolve the
  information paradox*

## Lean realization

Module:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekPositiveMatrixCrossGradeClassification`

Theorems:

- `schwarzschildParikhWilczekBorelRecoilHolonomy_im_factorization`
- `schwarzschildParikhWilczekBorelGradeResidual_pos`
- `schwarzschildParikhWilczekMatrixCrossGradeEnergy_factorization`
- `schwarzschildParikhWilczekMatrixResidualEnergy_pos`
- `schwarzschildParikhWilczekMatrixCrossGradeEnergy_eq_zero_iff`
- `riemannHypothesis_iff_schwarzschildParikhWilczekMatrixCrossGradeEnergy_zero`

Verification:

- direct `lake env lean` passed
- targeted module `lake build` passed
- exported theorem axiom audit passed: only standard Mathlib axioms
- imported by `GaloisForLFunctions.RHTower`
