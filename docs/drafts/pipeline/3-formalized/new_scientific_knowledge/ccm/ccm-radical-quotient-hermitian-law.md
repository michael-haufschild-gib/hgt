# CCM radical-quotient Hermitian law — formal certificate

- **ID:** `ccm-radical-quotient-hermitian-law-formal`
- **Stage:** 3-formalized
- **Parent route:** `../../1-in-progress/ccm-radical-quotient-hermitian-law.md`
- **Module:** `formal/GaloisForLFunctions/RHTower/CCMRadicalQuotientHermitian.lean`
- **Manuscript:** `docs/drafts/manuscripts/ccm-radical-quotient-hermitian/main.tex`
- **Status:** `[UNCONDITIONALLY FORMALIZED] [NOT AN RH PROOF]`

## Certified theorem

For a surjective Gram frame `B` with right inverse `R`, every operator `A` satisfying

```text
(B* B) A=A* (B* B)
```

has Hermitian quotient compression `C=B A R`. If `A` preserves `ker B`, then `C B=B A`.
Consequently the characteristic polynomial of `C` has only real zeros.

The real theorem is connected to the existing boundary-channel completion for every finite
reflection-graded CCM divided-difference scalar shift. Given a full-row-rank Gram factor of that
shift, the module produces a symmetric quotient clock and proves the exact quotient intertwiner,
without a simple or parity-pure radical.

For cofinal families, locally uniform convergence of nowhere-zero normalized quotient
characteristic polynomials to `XiC` implies RH.

## Main declarations

- `semimetricQuotientCompression_isHermitian`
- `semimetricQuotientCompression_charpoly_zero_im_eq_zero`
- `semimetricQuotientCompression_intertwines`
- `realSemimetricQuotientCompression_transpose`
- `realSemimetricQuotientCompression_intertwines`
- `realSymmetric_complexification_charpoly_zero_im_eq_zero`
- `riemannHypothesis_of_normalizedRealSemimetricQuotientCharpoly_tendstoLocallyUniformly`
- `ccmBoundaryChannelCompletion_realSemimetricQuotient_exists`
- `ccmDividedDifferenceShift_realSemimetricQuotient_exists`

## Novelty boundary

Universal semidefinite quotient self-adjointness is classical; see Bovdi et al., arXiv:2003.06919,
Lemma 3. Candidate novelty is the arbitrary-radical CCM boundary completion and quotient-determinant
application. The open RH-bearing theorem is locally uniform convergence of actual cofinal CCM
quotient determinants to `Xi`; it is not asserted here.

## Audit

- [x] leaf file passes `lake env lean`
- [x] imported by `RHTower.lean`
- [x] final cached `lake build GaloisForLFunctions.RHTower.CCMRadicalQuotientHermitian`
- [x] axiom print audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] module reachable from `RHTower.lean`; repository-wide lint is blocked only by unrelated
  concurrent unreachable modules, none involving this module
