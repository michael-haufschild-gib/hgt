# Generic affine HT carriers have exactly the collision differential matroid — formalized

- **ID:** `affine-jet-packet-collision-completeness-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `affine-jet-packet-collision-completeness.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

Pre-existing parents used unchanged: `MultivariateEntireCompactOpen`,
`MultivariateEntireFrechetRegularity`, `MultivariateEntireFrechetJet`,
`MultivariateEntireDirectionalJet`, `MultivariateEntireAffinePullback`,
`MultivariateEntirePolarizedJet`, `MultivariatePolynomialJetCoefficient`,
`MultivariateMultiIndexJet`, `MultivariateEntireVanishingPower`, `MultivariateHermiteCRT`,
`MultivariateCoefficientPatternDeterminant`, `CountableMultivariateAffineJetPattern`,
`ContinuousPolynomialDefect`, `BaireGenericAvoidance`, `PolynomialEvaluationLemma`,
`AffineCollisionMatroid`, `AffineJetPacketCollisionCompletion`, `AffineIteratedFDeriv`.

| New module | Content |
|---|---|
| `HTGeometry/AffineJetVanishingTransfer.lean` | flatness transfer through an affine frame |
| `HTGeometry/AffineJetPacketPrescription.lean` | affine substitution on polynomials; affine jet-packet surjectivity |
| `HTGeometry/AffineFramePacketSeparation.lean` | generic base separating a packet |
| `HTGeometry/AffineJetPacketWitness.lean` | an escaping witness for every finite decorated pattern |
| `HTGeometry/AffineJetPacketResidual.lean` | the unconditional dense residual generic set |
| `HTGeometry/AffineJetDifferentialIndependence.lean` | determinant avoidance is differential independence |
| `HTGeometry/MultivariateEntirePartialDeriv.lean` | directional derivatives of entire sources |
| `HTGeometry/MultivariateJetCompositionLaw.lean` | jet word symmetry and `∂^γ ∘ ∂^β = ∂^{β+γ}` |
| `HTGeometry/LinearFormSubstitution.lean` | substituting independent linear forms is injective |
| `HTGeometry/AffineOperatorRankLaw.lean` | constant-coefficient operator rows and their jets |
| `HTGeometry/AffineOperatorRankBridge.lean` | operator rank as independence over `ℂ[∂]` |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- **`(15)`–`(16)`** `affineJetPacketGenericSet_dense_residual` — for `d ≥ 1`, a countable family of
  pairwise distinct affine automorphisms of `ℂᵈ`, the sources on which every finite decorated jet
  determinant is nonzero form a dense residual subset of the compact-open space of multivariate
  entire functions.  Its input, `nonempty_multivariateAffinePatternWitness`, is the card's step 2:
  a separating base from `exists_base_separating_and_eval_ne_zero` plus a polynomial source from
  `exists_mvPolynomial_affine_packet_prescribed`.
- **`(10)`–`(14)`** `multivariateFullPatternDeterminant_ne_zero`, `exists_coordDiffPoly_ne_zero`,
  `exists_mvPolynomial_affineMultiIndexJetEvalCLM_eq`,
  `affineMultiIndexJetEvalCLM_congr_of_orderedPartialJetEvalCLM_eq`.
- **`(5)`–`(6)`** `exists_affineJetRelationValue_ne_zero` — for any source in the generic set and
  any injective labelling, every nonzero differential polynomial with polynomial coefficients has a
  point where its value at the pullbacks along distinct frames is nonzero.  Rational coefficients
  are the same statement after clearing denominators.
- **`(7)`** `affineJetPacketCollision_orbitRank_eq_collisionMatroid_eRk` against
  `affineCollisionMatroid`.
- **`(17)`–`(18)`** `exists_jetRelationValue_operatorRowSource_ne_zero_of_linearIndependent` and
  `exists_nonzero_jetRelation_of_not_linearIndependent_operator` — the differential matroid of the
  outputs of constant-coefficient operator rows is the linear matroid of the operator matrix over
  `ℂ[∂]`, via `linearIndependent_operatorJetSubstVector_iff`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/AffineJetPacketResidual.lean
lake env lean GaloisForLFunctions/HTGeometry/AffineJetDifferentialIndependence.lean
lake build GaloisForLFunctions.HTGeometry.AffineOperatorRankBridge
```

## What closed last

Three pieces mathlib does not have.  **Affine jet-packet surjectivity**: polynomial jets depend only
on word multiplicity, so pulling a one-point Taylor polynomial back through `σ⁻¹` and matching
Hermite data at the distinct image points already prescribes the whole pulled-back observation — no
symmetric-tensor inverse and no Leibniz rule.  **Packet separation**: each coincidence
`σ_i(x_a) = σ_j(x_b)` is a nontrivial degree-one condition, so one base makes the pattern
determinant nonzero and separates the packet at once.  **The jet composition law**: two words with
equal multiplicity differ by a permutation of the slots (glued from fibre equivalences), which turns
`iteratedFDeriv_succ_apply_right` into `∂^γ ∘ ∂^β = ∂^{β+γ}` for the continuous jet observations and
makes the operator rows differentiable objects rather than formal ones.

## Boundary

The remaining gates on the paper card — an independent specialist proof audit and an
exact-formulation primary-literature audit — are external literature obligations, not formalization
obligations.  The RH content is a necessity statement about what an RH-bearing carrier must supply
(a stable arithmetic packet defect); it is not a proof of RH.
