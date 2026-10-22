# Deninger--Hazewinkel corrected multiplication descent

- **Stage:** 3-formalized
- **Route:** L — rational-Witt source foundation
- **Status:** dependency-closed results below; general all-stage Hazewinkel primeness remains on
  parent literature-parity card
- **Primary sources:** Hazewinkel, *Operations in the K-theory of endomorphisms* (1983), appendix;
  Deninger, *Rational Witt vectors and associated sheaves*, arXiv:2508.05329v1, §2

## Formalized statements

The published stage estimate `(n,m) ↦ n+m` is false. The replacement development proves:

1. A normalized rational presentation in stages `n,m` has product stage at most
   `(n-1)(m-1)+nm+1` over every commutative ring, including rings with nilpotents.
2. Over a field, Hankel rank `< n` is equivalent to existence of a normalized rational
   presentation of stage `n` (full Kronecker converse), hence the corrected product rank bound.
3. Over an arbitrary commutative ring, every corrected-size product Hankel minor is nilpotent.
   It therefore vanishes over every reduced ring.
4. The two-block universal coordinate quotient carries the input rank relations and descends an
   exact corrected product bound to arbitrary target rings once that universal quotient is reduced.
5. Explicit generator maps identify the universal quotient canonically with the integer tensor
   product of the individual Hazewinkel stage quotients:

   `ℤ[X,Y]/(J_n(X)+J_m(Y)) ≃+* (ℤ[X]/J_n) ⊗_ℤ (ℤ[Y]/J_m)`.

   Reducedness is proved equivalent across this ring equivalence.
6. Tensor reducedness is no longer an input: tensor products of arbitrary field extensions over a
   perfect field are reduced, and integer tensor products of arbitrary characteristic-zero domains
   are reduced.
7. Therefore individual primeness of `J_n,J_m` implies universal pair-quotient reducedness and the
   corrected multiplication theorem over every commutative target ring, including nilpotents.
8. `J₁` is prime by the exact kernel presentation `X_j ↦ T^(j+1)`. Consequently two vectors of
   Hankel rank `<2` have product of Hankel rank `<3` over every commutative ring.
9. For every `n>0`, an explicit rational `n`-atomic moment evaluation kills `J_n` while sending
   leading determinant `D_n` to a nonzero Vandermonde-diagonal product. Thus `D_n mod J_n ≠ 0`.
10. After inverting `D_n`, the universal stage quotient is canonically isomorphic to the
    localization of the polynomial ring in the first `2n-1` coefficients. Both coordinate-map
    composites are identities, so this localized stage is an integral domain for every `n>0`.
    General primeness is now reduced only to integral Sylvester saturation/regularity; it is not
    imported as an assumption in a claimed capstone.
11. Hazewinkel Appendix A.1 is formalized over arbitrary commutative rings by a Cramer/adjugate
    determinant-exchange identity. For the universal Hankel matrix this constructs the fixed-row
    ideal and special `m_s` ideal, proves `K_n ≤ J_n^fixed ≤ J_n`, and proves the exact exchange
    containment `D_n J_n^fixed ≤ K_n`.

All statements are theorem-kernel proofs. No `sorry`, `admit`, new axiom, ghost-coordinate
injectivity, target reducedness shortcut, or computation is used in the arbitrary-ring results.

## Lean modules

- `GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelCorrectedRationalStage`
- `GaloisForLFunctions.RHTower.Deninger.DeningerKroneckerFieldStage`
- `GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelReducedMultiplication`
- `GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelUniversalQuotient`
- `GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelUniversalMultiplicationDescent`
- `GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelPairTensorEquiv`
- `GaloisForLFunctions.RHTower.Deninger.DeningerCharacteristicZeroTensorReduced`
- `GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelPrimeReduction`
- `GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelStageOnePrime`
- `GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelLeadingLocalization`
- `GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelLocalizedCoordinates`
- `GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelLocalizedRetraction`
- `GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelLocalizedEquivalence`
- `GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelSylvesterExchange`
- `GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelSylvesterContainment`

## Exact remaining source theorem

The tensor theorem is closed. General corrected ind-ring closure for nonreduced targets now reduces
only to Hazewinkel's integral theorem that `J_n` is prime for every positive `n`. Stage `n=1` is
closed. For arbitrary `n`, nonvanishing of leading determinant is closed, as is formal implication
from regularity plus localized integrality to primeness. Localized integrality itself is now closed
by an explicit two-sided coordinate equivalence. Exact missing source proof is only
`(J_n : D_n)=J_n`. Its determinant-exchange containment is closed; remaining Appendix A.2 work is
fixed-row generation of the full Hankel ideal and integral saturation of the fixed-row ideal. These
are recorded as open, not hidden as hypotheses in any claimed unconditional all-stage theorem.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerHazewinkelPairTensorEquiv.lean`
- `lake build GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelPairTensorEquiv`
- `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerHazewinkelLeadingLocalization.lean`
- `lake build GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelLeadingLocalization`
- `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerHazewinkelStageOnePrime.lean`
- `lake build GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelStageOnePrime`
- `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerHazewinkelLocalizedEquivalence.lean`
- `lake build GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelLocalizedEquivalence`

All passed on 2026-08-13. Modules are wired into `GaloisForLFunctions.RHTower`. Axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.
