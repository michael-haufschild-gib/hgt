# Card observer-visible-local-time-dimension-obstruction — FULLY FORMALIZED

Card moved to `docs/drafts/pipeline/3-formalized/observer-visible-local-time-dimension-obstruction.md`,
status `[LEAN-PROVED]`.  Every displayed equation of the card is closed
unconditionally (axioms = propext / Classical.choice / Quot.sound only).

## Modules (all wired into `GaloisForLFunctions/HTGeometry.lean`)

| Module | Content |
|---|---|
| `ObserverInvisibleRayPreservation.lean` | eq (3),(4): `exp_mulVec_of_eigenvector`, `unitaryEvolution_mulVec_of_eigenvector`, `unitaryEvolution_generatorCombination_mulVec_of_invisible`, `exists_unit_phase_unitaryEvolution_of_centered_eq_zero`, `finrank_ker_centeredRealification_add_rank`, `centeredLinear` |
| `FiniteSupportCounting.lean` | `card_configSupport_card_eq`, `card_configSupport_pos_le` (generic support-size counting) |
| `FiniteQuditHermitianUnit.lean` | local Hermitian basis `quditHermUnit` of `Mat_D(ℂ)` ((0,0)=identity, rest traceless), `single_eq_sum_quditUnitCoeff`, `span_quditHermUnit_eq_top`, `linearIndependent_quditHermUnit`, `trace_quditHermUnit`, `exists_real_repr_ground_zero_of_traceless` |
| `FiniteQuditHermitianStringBasis.lean` | `quditStringOf`, `quditString`, `quditStringOf_sum/mul/conjTranspose/one`, `span_quditString_eq_top`, `linearIndependent_(real_)quditString`, `QLocalStringLabel`, `card_QLocalStringLabel` |
| `ProductStateObserverVisibleRank.lean` | eqs (13)–(17): `quditString_mulVec_vacuum`, `centered_quditString_vacuum`, `map_qLocalDictionary`, `finrank_map_qLocalDictionary` (=2N), `finrank_qLocalDictionary` (=m), `finrank_ker_add_finrank_map_qLocalDictionary`, qubit corollaries |
| `ProductStateLocalUnitaryInvariance.lean` | local-unitary invariance: `conj_quditString_mem_span_sameSupport`, `map_conj_qLocalDictionary_le`, `centered_conj`, `map_qLocalDictionary_productState`, `finrank_map_qLocalDictionary_productState`, `exists_unitary_col_zero`, `finrank_map_qLocalDictionary_productVector` |
| `ObserverKernelTubeVolume.lean` | eq (8) machinery: `exponent_le_of_forall_rpow_le`, `exponent_le_natCast_of_forall_le`; eq (6) volume: `measure_annulus`, `measure_annulusTube`, `measure_annulusTube_pos` |
| `GaussianSmallBallLowerBound.lean` | eq (7): `gaussianDensityFloor`, `measure_pi_gaussian_closedBall_lower`, `measure_pi_gaussian_transverse_ball_lower` |
| `ObserverInvisibleTubeShortcut.lean` | eqs (6),(7),(8),(10) capstones: `norm_unitaryEvolution_mulVec_sub_le`, `RayClose`, `rayClose_of_transverse_small`, `measure_rayClose_ge_annulusTube`, `measure_rayClose_ge_gaussian_smallBall`, `exponent_le_visible_of_upper_law` |

## Modelling conventions (documented in the card)
- shortcut membership = `RayClose` (endpoint within ε of the initial ray); the
  zero-gate identity witness is exactly what the paper proof uses.
- the splitting `V = F_Φ ⊕ F_Φ^⊥` is the product coefficient space `E × F`; the
  standard Gaussian on the visible coordinates is `Measure.pi (gaussianReal 0 1)`.

## Reusable assets created
Local Hermitian unit basis + operator-string basis for arbitrary local dimension
`D` and arbitrary finite site set (`quditHermUnit`, `quditString`) — the
qudit generalisation of `FiniteQubitPauliBasisLaw.lean`.  Support-size counting
for finite configuration spaces.  Annular Haar tube volume.  Multivariate
Gaussian small-ball lower bound.
