# Möbius-contact Gamma scale/covariant-residue joint freeness universality law

- **ID:** mobius-contact-gamma-scale-covariant-residue-joint-freeness-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of `MobiusGammaContactTransgression` and
  `GammaPoleReciprocalBellGrading`
- **Statement:** After the canonical one-step pole-index shift, the negative finite Möbius contact
  defect is the reciprocal signed-factorial germ. This observable germ is jointly algebraically
  independent over `ℂ` with the complete countable family of Gamma simple-zero covariant-residue
  germs.

## Goal

Test whether arithmetic contact normalization remains free only order-by-order or jointly with the
entire intrinsic simple-zero residue tower.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `mobiusGammaContactPartialCharge_eq`
- `reciprocalSignedFactorialSequence_succ_eq_neg_scale`
- `gammaPoleScaleAndCovariantResidueFamily`
- `algebraicIndependent_gammaPoleScaleAndCovariantResidueFamily`

## Proof

**[PROVED HERE]** Set
`c_n=(-2-mobiusGammaContactPartialCharge n)/2`. Exact contact transgression gives
`c_n=reciprocalGammaFactorialScale n`. The signed-factorial recursion gives
`reciprocalSignedFactorialSequence (n+1)=-reciprocalGammaFactorialScale n=-c_n`.
Hence the pole-index germ `N ↦ -c_(N-1)` equals `reciprocalSignedFactorialGerm`; the possible
depth-zero discrepancy is irrelevant in the germ at infinity. Replace the scale coordinate of
the established family
`none ↦ reciprocalSignedFactorialGerm`,
`some j ↦ gammaSimpleZeroCovariantResidueGerm j`
by this equal contact germ. Algebraic independence is invariant under equality of the indexed
family, proving joint freeness of the contact observable and every residue grade. No computation
is used. ∎

## Strict gain over corpus endpoints

Contact transgression supplied one scalar boundary observable but no independence theorem. The
reciprocal-Bell grading proved joint freeness for an internal signed-factorial germ but did not
identify an arithmetic boundary source. Their closure proves that the observable contact defect
cannot satisfy any nonzero finite polynomial relation jointly with any finite selection of
intrinsic simple-zero covariant residues.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.MobiusContactGammaScaleCovariantResidueJointFreenessUniversalityLaw`
- Main theorem:
  `algebraicIndependent_mobiusContactGammaScaleAndCovariantResidueFamily`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/MobiusContactGammaScaleCovariantResidueJointFreenessUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for algebraic independence of reciprocal-Gamma coefficient/residue germs, signed factorial
sequences, and Möbius contact observables found no exact collision. Closest primary sources:

- R. Vidunas, *Expressions for values of the gamma function*,
  <https://arxiv.org/abs/math/0403510>, discusses relations and open algebraic-independence
  questions for isolated Gamma values, not moving-pole coefficient germs.
- L. Fekih-Ahmed, *On the Power Series Expansion of the Reciprocal Gamma Function*,
  <https://arxiv.org/abs/1407.5983>, derives reciprocal-Gamma coefficient asymptotics but no joint
  algebraic-independence theorem with factorial scale or covariant residues.
- D. P. H. Ulgenes, *Series and Product Representations of Gamma, Pseudogamma and Inverse Gamma
  Functions*, <https://arxiv.org/abs/2301.09699>, gives coefficient formulas and interpolation,
  not a contact-generated countably free residue family.

## Log

- 2026-07-23 — complete common-scale scan exposed joint contact/residue germ family.
- 2026-07-23 — dependency-closed proof completed.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
