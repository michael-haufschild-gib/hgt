# Card: observer-visible-local-time-dimension-obstruction — Lean formalization

Card: `docs/drafts/pipeline/2-fully-proven/observer-visible-local-time-dimension-obstruction.md`

## Already existing before this work
`HTGeometry/ObserverVisibleLocalTimeDimension.lean` (namespace `QuantumAlg`):
QFI Gram factorization, `qfim_rank_eq_centeredRealification_rank`,
`centeredRealification_mulVec_eq_zero_iff_eigenvector`, observer-channel
rank-nullity laws.

## Done in this pass (all unconditional, axioms = propext/Classical.choice/Quot.sound)

### Chunk A — eq. (4) ray preservation
`HTGeometry/ObserverInvisibleRayPreservation.lean` (namespace `QuantumAlg`)
- `pow_mulVec_of_eigenvector`, `mulVecHom`, `continuous_mulVecHom`
- `exp_mulVec_of_eigenvector` : `NormedSpace.exp A *ᵥ ψ = Complex.exp c • ψ`
  (norm hidden in proof via `open scoped Matrix.Norms.Operator`)
- `unitaryEvolution_mulVec_of_eigenvector` (phase form)
- `generatorCombination_conjTranspose`, `expval_generatorCombination_ofReal_re`
- `unitaryEvolution_generatorCombination_mulVec_of_invisible` — eq. (4)
- `exists_unit_phase_unitaryEvolution_of_invisible` (projective form)
- `finrank_ker_centeredRealification_add_rank` — eq. (3)
- `centeredLinear` : ℂ-linear `A ↦ centered ψ A`

### Chunk B — eqs. (12)–(18) fixed-locality product-state rank (general qudit)
- `HTGeometry/FiniteSupportCounting.lean` — generic support-size counting:
  `card_configSupport_card_eq`, `card_configSupport_pos_le`
- `HTGeometry/FiniteQuditHermitianUnit.lean` — local Hermitian basis
  `quditHermUnit : Fin D × Fin D → Matrix (Fin D) (Fin D) ℂ`
  ((0,0)=identity, all others traceless Hermitian), `single_eq_sum_quditUnitCoeff`
- `HTGeometry/FiniteQuditHermitianStringBasis.lean` — `quditString`,
  Hermiticity, `span_quditString_eq_top`, `linearIndependent_quditString`,
  `linearIndependent_real_quditString`, `QLocalStringLabel`,
  `card_QLocalStringLabel = ∑_{k=1}^q C(n,k)(D²−1)^k`
- `HTGeometry/ProductStateObserverVisibleRank.lean` —
  `quditString_mulVec_vacuum`, `centered_quditString_vacuum`,
  `map_qLocalDictionary` (visible image = span of excitation directions),
  `finrank_map_qLocalDictionary = 2·∑_{k=1}^q C(n,k)(D−1)^k`  ← eq. (16) v_Φ
  `finrank_qLocalDictionary = ∑_{k=1}^q C(n,k)(D²−1)^k`       ← eq. (13) m
  `finrank_ker_add_finrank_map_qLocalDictionary`               ← eq. (16) dim F_Φ
  qubit corollaries `..._qubit`                                ← eq. (17)

## Remaining (Chunk C)
- eq. (6) annular volume law of the kernel tube (needs Haar volume of
  annulus × ball under an orthogonal splitting)
- eq. (7) Gaussian small-ball lower bound `≥ c' t^{-v_Φ}`
- eq. (8) `κ ≤ v_Φ` exponent comparison (elementary; do first)
- eq. (10) Duhamel/Lipschitz tube bound — corpus already has
  `norm_unitaryEvolution_sub_le` in `ObserverProfileStability.lean`

All four new modules are wired into `GaloisForLFunctions/HTGeometry.lean`.
