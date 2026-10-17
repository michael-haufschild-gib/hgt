import GaloisForLFunctions.RHTower.CHMDNodalCrossPrimeShiftAndPrimitiveRayleighClosure
import GaloisForLFunctions.RHTower.CHMDStationaryStrictContractionAndSecondResolventIdentity

/-!
# Prime-Generator Beurling–Deny Contraction, Nodal Lobe Cauchy–Schwarz, and Diagonal Potential Balance

This module establishes the Beurling–Deny nodal contraction law for `primeGenerator`, the exact
orthogonal nodal-lobe edge pairings and Cauchy–Schwarz inequalities on `SourceGraph`,
`stationaryGroundGraph`, and `PrimeGraph`, and the pure jump vs. local diagonal potential balance
on `SourceGraph` and for `resolvent` eigenvectors:

1. **Beurling–Deny Nodal Contraction and Cross-Jump Identity for `primeGenerator`**:
   - `inner_primeGenerator_eq_primeDiagonal_sub_primeShift`:
     `⟪primeGenerator u, v⟫_ℝ = ⟪primeDiagonalOperator u, v⟫_ℝ - ⟪primeShiftOperator u, v⟫_ℝ`.
   - `inner_primeGenerator_posGraph_negGraph`: because `primeDiagonalOperator` vanishes between
     `posGraph p` and `negGraph p`,
     `⟪primeGenerator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ = -⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ≤ 0`.
   - `inner_primeGenerator_absGraph_eq`:
     `⟪primeGenerator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ = ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ - 4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`.
   - `four_inner_primeShift_posGraph_negGraph_le_primeGenerator`:
     `0 ≤ 4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ≤ ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ`.
   - `inner_primeShift_posGraph_negGraph_sq_le_primeGenerator_mul`:
     `⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ^ 2 ≤ ⟪primeGenerator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ * ⟪primeGenerator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`.

2. **Orthogonal Nodal-Lobe Edge Pairings, Cauchy–Schwarz, and Strict Stationary Dominance**:
   - `sourcePair_posGraph_negGraph_eq_inner_snd` and `sourcePair_posGraph_negGraph_eq_inner_graph`:
     `sourcePair (posGraph p) (negGraph p) = ⟪(posGraph p).val.snd, (negGraph p).val.snd⟫_ℝ = ⟪posGraph p, negGraph p⟫_ℝ`.
   - `sourcePair_posGraph_negGraph_sq_le_norm_snd_sq_mul` and
     `inner_fullGroundEquiv_posGraph_negGraph_snd_sq_le_stationaryEnergy_mul`.
   - `neg_four_inner_fullGroundEquiv_posGraph_negGraph_snd_lt_stationaryEnergy_of_ne_zero`:
     because `stationaryGroundGraph` has no constant zero mode, for every `p ≠ 0`,
     `-4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ < stationaryEnergy (thetaProduct p.val.fst)`.

3. **Pure Jump Energy (`stationaryEnergy + primeGenerator`) vs. Local Diagonal Potential Balance**:
   - `sourceEnergy_eq_stationary_add_primeGenerator_sub_diagonals`:
     `sourceEnergy p = stationaryEnergy (thetaProduct p.val.fst) + ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ - archGroundConstant * ‖thetaToVolume p.val.fst‖ ^ 2 - ⟪primeDiagonalOperator p.val.fst, p.val.fst⟫_ℝ`.
   - `norm_snd_sq_eq_stationary_add_primeGenerator_add_groundPotential`:
     `‖p.val.snd‖ ^ 2 = stationaryEnergy (thetaProduct p.val.fst) + ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ + ⟪groundPotentialOperator p.val.fst, p.val.fst⟫_ℝ`.
   - `eigenvector_stationary_add_primeGenerator_add_groundPotential` and
     `eigenvector_stationary_add_primeGenerator_eq_diagonals`:
     for every eigenvector `resolvent u = μ • u` (`μ ≠ 0`),
     `stationaryEnergy (thetaProduct u) + ⟪primeGenerator u, u⟫_ℝ + ⟪groundPotentialOperator u, u⟫_ℝ = ((1 - μ) / μ) * ‖u‖ ^ 2`
     and
     `stationaryEnergy (thetaProduct u) + ⟪primeGenerator u, u⟫_ℝ + ((2 * μ - 1) / μ) * ‖u‖ ^ 2 = archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeDiagonalOperator u, u⟫_ℝ`.
   - `neg_four_sourcePair_posGraph_negGraph_lt_stationary_add_primeGenerator_of_ne_zero`:
     for every `p ≠ 0`,
     `-4 * sourcePair (posGraph p) (negGraph p) < stationaryEnergy (thetaProduct p.val.fst) + ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ`.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation ThetaSourceWard

/-! ## Section 1: Beurling–Deny Nodal Contraction and Cross-Jump Identity for `primeGenerator` -/

/-- Symmetry of `primeGenerator` on `MassSpace`. -/
theorem primeGenerator_symmetric (u v : MassSpace) :
    ⟪primeGenerator u, v⟫_ℝ = ⟪u, primeGenerator v⟫_ℝ :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp primeGenerator_isSelfAdjoint u v

/-- Nonnegativity of the prime jump Dirichlet energy `0 ≤ ⟪primeGenerator u, u⟫_ℝ`. -/
theorem inner_primeGenerator_self_nonneg (u : MassSpace) :
    0 ≤ ⟪primeGenerator u, u⟫_ℝ := by
  rw [inner_primeGenerator_self]
  exact sq_nonneg _

/-- For all `u, v : MassSpace`,
`⟪primeGenerator u, v⟫_ℝ = ⟪primeDiagonalOperator u, v⟫_ℝ - ⟪primeShiftOperator u, v⟫_ℝ`. -/
theorem inner_primeGenerator_eq_primeDiagonal_sub_primeShift (u v : MassSpace) :
    ⟪primeGenerator u, v⟫_ℝ =
      ⟪primeDiagonalOperator u, v⟫_ℝ - ⟪primeShiftOperator u, v⟫_ℝ := by
  change ⟪primeGenerator u, v⟫_ℝ =
    ⟪primeDiagonalOperator u, v⟫_ℝ - ⟪primeDiagonalOperator u - primeGenerator u, v⟫_ℝ
  rw [inner_sub_left]
  ring

/-- Because `primeDiagonalOperator` is a local diagonal multiplication operator, its pairing between
`posGraph p` and `negGraph p` vanishes, so the `primeGenerator` cross-lobe pairing is the exact
negative of the `primeShiftOperator` cross-lobe pairing:
`⟪primeGenerator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ = -⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`. -/
theorem inner_primeGenerator_posGraph_negGraph (p : SourceGraph) :
    ⟪primeGenerator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ =
      -⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  rw [inner_primeGenerator_eq_primeDiagonal_sub_primeShift,
    inner_primeDiagonalOperator_posGraph_negGraph, zero_sub]

/-- On `allPrimeMeasure`, the prime edge difference pairing between `posGraph p` and `negGraph p`
equals `-⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ≤ 0`. -/
theorem inner_primeDifference_posGraph_negGraph (p : SourceGraph) :
    ⟪primeDifference (posGraph p).val.fst, primeDifference (negGraph p).val.fst⟫_ℝ =
      -⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  rw [← inner_primeGenerator, inner_primeGenerator_posGraph_negGraph]

/-- **Nodal Lobe Decomposition of `primeGenerator`**:
for every `p : SourceGraph`,
`⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ = ⟪primeGenerator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ + ⟪primeGenerator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ + 2 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`. -/
theorem inner_primeGenerator_eq_posGraph_add_negGraph_add_two_primeShift (p : SourceGraph) :
    ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ =
      ⟪primeGenerator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
        ⟪primeGenerator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ +
        2 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  have hsub : p.val.fst = (posGraph p).val.fst - (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_sub_negGraph p).symm
  conv_lhs => rw [hsub]
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    primeGenerator_symmetric (negGraph p).val.fst (posGraph p).val.fst,
    real_inner_comm _ (negGraph p).val.fst, inner_primeGenerator_posGraph_negGraph]
  ring

/-- **Exact Beurling–Deny Cross-Jump Formula for `primeGenerator` on `absGraph p`**:
for every `p : SourceGraph`,
`⟪primeGenerator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ = ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ - 4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`. -/
theorem inner_primeGenerator_absGraph_eq (p : SourceGraph) :
    ⟪primeGenerator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ =
      ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ -
        4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  rw [inner_primeGenerator_eq_primeDiagonal_sub_primeShift,
    inner_primeGenerator_eq_primeDiagonal_sub_primeShift,
    inner_primeDiagonalOperator_absGraph_self]
  have h := inner_primeShiftOperator_absGraph_self_eq p
  linarith

/-- **Beurling–Deny Markov Contraction and Upper Bound for `primeGenerator`**:
for every `p : SourceGraph`,
`⟪primeGenerator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ ≤ ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ`
and
`4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ≤ ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ`. -/
theorem four_inner_primeShift_posGraph_negGraph_le_primeGenerator (p : SourceGraph) :
    ⟪primeGenerator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ ≤
        ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ ∧
      4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ≤
        ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ := by
  have h1 := inner_primeGenerator_absGraph_eq p
  have h2 := inner_primeShiftOperator_posGraph_negGraph_nonneg p
  have h3 := inner_primeGenerator_self_nonneg (absGraph p).val.fst
  exact ⟨by linarith, by linarith⟩

/-- **Prime-Difference Cauchy–Schwarz Inequality for the Prime-Shift Cross-Lobe Pairing**:
for every `p : SourceGraph`,
`⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ^ 2 ≤ ⟪primeGenerator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ * ⟪primeGenerator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`. -/
theorem inner_primeShift_posGraph_negGraph_sq_le_primeGenerator_mul (p : SourceGraph) :
    ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ^ 2 ≤
      ⟪primeGenerator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ *
        ⟪primeGenerator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  have h1 : ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ =
      -⟪primeDifference (posGraph p).val.fst, primeDifference (negGraph p).val.fst⟫_ℝ := by
    rw [inner_primeDifference_posGraph_negGraph, neg_neg]
  have hnn := inner_primeShiftOperator_posGraph_negGraph_nonneg p
  have hcs : -⟪primeDifference (posGraph p).val.fst, primeDifference (negGraph p).val.fst⟫_ℝ ≤
      ‖primeDifference (posGraph p).val.fst‖ * ‖primeDifference (negGraph p).val.fst‖ := by
    have h2 := neg_le_abs
      ⟪primeDifference (posGraph p).val.fst, primeDifference (negGraph p).val.fst⟫_ℝ
    exact h2.trans (abs_real_inner_le_norm _ _)
  rw [← h1] at hcs
  have hsq := pow_le_pow_left₀ hnn hcs 2
  rw [mul_pow, ← inner_primeGenerator_self, ← inner_primeGenerator_self] at hsq
  exact hsq

/-! ## Section 2: Orthogonal Nodal-Lobe Edge Pairings, Cauchy–Schwarz, and Strict Stationary Dominance -/

/-- Because `(posGraph p).val.fst` and `(negGraph p).val.fst` are orthogonal in `MassSpace`,
`sourcePair (posGraph p) (negGraph p) = ⟪posGraph p, negGraph p⟫_ℝ`. -/
theorem sourcePair_posGraph_negGraph_eq_inner_graph (p : SourceGraph) :
    sourcePair (posGraph p) (negGraph p) = ⟪posGraph p, negGraph p⟫_ℝ := by
  rw [graph_inner, inner_posGraph_negGraph_fst, zero_add,
    sourcePair_posGraph_negGraph_eq_inner_snd]

/-- In `stationaryGroundGraph`,
`⟪fullGroundEquiv (posGraph p), fullGroundEquiv (negGraph p)⟫_ℝ = ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ`. -/
theorem inner_fullGroundEquiv_posGraph_negGraph_eq_snd (p : SourceGraph) :
    ⟪fullGroundEquiv (posGraph p), fullGroundEquiv (negGraph p)⟫_ℝ =
      ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ := by
  rw [Submodule.coe_inner, WithLp.prod_inner_apply]
  change ⟪(fullGroundEquiv (posGraph p)).val.fst, (fullGroundEquiv (negGraph p)).val.fst⟫_ℝ +
    ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ = _
  have hp : (fullGroundEquiv (posGraph p)).val.fst = (posGraph p).val.fst :=
    fullGroundEquiv_source (posGraph p)
  have hn : (fullGroundEquiv (negGraph p)).val.fst = (negGraph p).val.fst :=
    fullGroundEquiv_source (negGraph p)
  rw [hp, hn, inner_posGraph_negGraph_fst, zero_add]

/-- **Edge-Space Cauchy–Schwarz Inequality for `sourcePair (posGraph p) (negGraph p)`**:
for every `p : SourceGraph`,
`sourcePair (posGraph p) (negGraph p) ^ 2 ≤ ‖(posGraph p).val.snd‖ ^ 2 * ‖(negGraph p).val.snd‖ ^ 2`. -/
theorem sourcePair_posGraph_negGraph_sq_le_norm_snd_sq_mul (p : SourceGraph) :
    sourcePair (posGraph p) (negGraph p) ^ 2 ≤
      ‖(posGraph p).val.snd‖ ^ 2 * ‖(negGraph p).val.snd‖ ^ 2 := by
  have hnn : 0 ≤ -sourcePair (posGraph p) (negGraph p) :=
    neg_nonneg.mpr (sourcePair_posGraph_negGraph_nonpos p)
  have hcs : -sourcePair (posGraph p) (negGraph p) ≤
      ‖(posGraph p).val.snd‖ * ‖(negGraph p).val.snd‖ := by
    rw [sourcePair_posGraph_negGraph_eq_inner_snd]
    exact (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have hsq := pow_le_pow_left₀ hnn hcs 2
  rwa [neg_sq, mul_pow] at hsq

/-- **Stationary Edge Cauchy–Schwarz Inequality for the Nodal Cross-Jump Pairing**:
for every `p : SourceGraph`,
`⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ ^ 2 ≤ stationaryEnergy (thetaProduct (posGraph p).val.fst) * stationaryEnergy (thetaProduct (negGraph p).val.fst)`. -/
theorem inner_fullGroundEquiv_posGraph_negGraph_snd_sq_le_stationaryEnergy_mul (p : SourceGraph) :
    ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ ^ 2 ≤
      stationaryEnergy (thetaProduct (posGraph p).val.fst) *
        stationaryEnergy (thetaProduct (negGraph p).val.fst) := by
  have hnn : 0 ≤ -⟪(fullGroundEquiv (posGraph p)).val.snd,
      (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ :=
    neg_nonneg.mpr (inner_fullGroundEquiv_posGraph_negGraph_snd_nonpos p)
  have hcs : -⟪(fullGroundEquiv (posGraph p)).val.snd,
      (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ ≤
      ‖(fullGroundEquiv (posGraph p)).val.snd‖ * ‖(fullGroundEquiv (negGraph p)).val.snd‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have hsq := pow_le_pow_left₀ hnn hcs 2
  have hp : (fullGroundEquiv (posGraph p)).val.fst = (posGraph p).val.fst :=
    fullGroundEquiv_source (posGraph p)
  have hn : (fullGroundEquiv (negGraph p)).val.fst = (negGraph p).val.fst :=
    fullGroundEquiv_source (negGraph p)
  rw [neg_sq, mul_pow, stationaryGround_edge_energy, stationaryGround_edge_energy, hp, hn] at hsq
  exact hsq

/-- For every nonzero `p : SourceGraph` (`p ≠ 0`),
`0 < stationaryEnergy (thetaProduct p.val.fst)`. -/
theorem stationaryEnergy_pos_of_ne_zero {p : SourceGraph} (hp : p ≠ 0) :
    0 < stationaryEnergy (thetaProduct p.val.fst) := by
  have hsrc : (fullGroundEquiv p).val.fst = p.val.fst := fullGroundEquiv_source p
  rw [← hsrc, ← stationaryGround_edge_energy]
  have hne : fullGroundEquiv p ≠ 0 := by
    intro h0
    exact hp (fullGroundEquiv.injective (h0.trans (map_zero _).symm))
  have hsnd : (fullGroundEquiv p).val.snd ≠ 0 :=
    fun h => hne ((stationaryGround_edge_zero_iff _).mp h)
  exact sq_pos_of_pos (norm_pos_iff.mpr hsnd)

/-- For every nonzero `p : SourceGraph` (`p ≠ 0`), `absGraph p ≠ 0`, so
`0 < stationaryEnergy (thetaProduct (absGraph p).val.fst)` and therefore
`-4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ < stationaryEnergy (thetaProduct p.val.fst)`. -/
theorem neg_four_inner_fullGroundEquiv_posGraph_negGraph_snd_lt_stationaryEnergy_of_ne_zero
    {p : SourceGraph} (hp : p ≠ 0) :
    -4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ <
      stationaryEnergy (thetaProduct p.val.fst) := by
  have habs_ne : absGraph p ≠ 0 := by
    intro h0
    apply hp
    apply source_projection_injective
    change p.val.fst = 0
    have hnorm : ‖p.val.fst‖ ^ 2 = 0 := by
      rw [← norm_absGraph_fst_sq, h0]
      simp
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  have hpos := stationaryEnergy_pos_of_ne_zero habs_ne
  have heq := stationaryEnergy_absGraph_eq p
  linarith

/-! ## Section 3: Pure Jump Energy (`stationaryEnergy + primeGenerator`) vs. Local Diagonal Potential Balance -/

/-- **Pure Jump Energy vs. Local Diagonal Potential Decomposition of `sourceEnergy`**:
for every `p : SourceGraph`,
`sourceEnergy p = stationaryEnergy (thetaProduct p.val.fst) + ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ - archGroundConstant * ‖thetaToVolume p.val.fst‖ ^ 2 - ⟪primeDiagonalOperator p.val.fst, p.val.fst⟫_ℝ`. -/
theorem sourceEnergy_eq_stationary_add_primeGenerator_sub_diagonals (p : SourceGraph) :
    sourceEnergy p =
      stationaryEnergy (thetaProduct p.val.fst) +
        ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ -
        archGroundConstant * ‖thetaToVolume p.val.fst‖ ^ 2 -
        ⟪primeDiagonalOperator p.val.fst, p.val.fst⟫_ℝ := by
  have h1 := sourceEnergy_eq_stationary_sub_arch_sub_primeShift p
  have h2 := inner_primeGenerator_eq_primeDiagonal_sub_primeShift p.val.fst p.val.fst
  linarith

/-- **Edge Norm-Squared Decomposition into Pure Jump Energy + `groundPotentialOperator`**:
for every `p : SourceGraph`,
`‖p.val.snd‖ ^ 2 = stationaryEnergy (thetaProduct p.val.fst) + ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ + ⟪groundPotentialOperator p.val.fst, p.val.fst⟫_ℝ`. -/
theorem norm_snd_sq_eq_stationary_add_primeGenerator_add_groundPotential (p : SourceGraph) :
    ‖p.val.snd‖ ^ 2 =
      stationaryEnergy (thetaProduct p.val.fst) +
        ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ +
        ⟪groundPotentialOperator p.val.fst, p.val.fst⟫_ℝ := by
  have hE : sourceEnergy p = ‖p.val.snd‖ ^ 2 - ‖p.val.fst‖ ^ 2 := rfl
  have h1 := sourceEnergy_eq_stationary_add_primeGenerator_sub_diagonals p
  have hsub := congrArg (fun T : MassSpace →L[ℝ] MassSpace => ⟪T p.val.fst, p.val.fst⟫_ℝ)
    sub_groundPotentialOperator_eq
  change ⟪p.val.fst - groundPotentialOperator p.val.fst, p.val.fst⟫_ℝ =
    ⟪primeDiagonalOperator p.val.fst + archDiagonalOperator p.val.fst, p.val.fst⟫_ℝ at hsub
  rw [inner_sub_left, real_inner_self_eq_norm_sq, inner_add_left,
    inner_archDiagonalOperator_self] at hsub
  linarith

/-- **Strict Total Jump Dominance over the Cross-Jump Penalty**:
for every nonzero `p : SourceGraph` (`p ≠ 0`),
`-4 * sourcePair (posGraph p) (negGraph p) < stationaryEnergy (thetaProduct p.val.fst) + ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ`. -/
theorem neg_four_sourcePair_posGraph_negGraph_lt_stationary_add_primeGenerator_of_ne_zero
    {p : SourceGraph} (hp : p ≠ 0) :
    -4 * sourcePair (posGraph p) (negGraph p) <
      stationaryEnergy (thetaProduct p.val.fst) + ⟪primeGenerator p.val.fst, p.val.fst⟫_ℝ := by
  have h1 := neg_four_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift p
  have h2 := neg_four_inner_fullGroundEquiv_posGraph_negGraph_snd_lt_stationaryEnergy_of_ne_zero hp
  have h3 := (four_inner_primeShift_posGraph_negGraph_le_primeGenerator p).2
  linarith

/-- **Pure Jump + Ground Potential Balance for Any `resolvent` Eigenvector**:
for every eigenvector `resolvent u = μ • u` (`μ ≠ 0`),
`stationaryEnergy (thetaProduct u) + ⟪primeGenerator u, u⟫_ℝ + ⟪groundPotentialOperator u, u⟫_ℝ = ((1 - μ) / μ) * ‖u‖ ^ 2`
and
`stationaryEnergy (thetaProduct u) + ⟪primeGenerator u, u⟫_ℝ + ((2 * μ - 1) / μ) * ‖u‖ ^ 2 = archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeDiagonalOperator u, u⟫_ℝ`. -/
theorem eigenvector_stationary_add_primeGenerator_balance {μ : ℝ} (hμ : μ ≠ 0) {u : MassSpace}
    (heig : resolvent u = μ • u) :
    stationaryEnergy (thetaProduct u) +
        ⟪primeGenerator u, u⟫_ℝ +
        ⟪groundPotentialOperator u, u⟫_ℝ =
      ((1 - μ) / μ) * ‖u‖ ^ 2 ∧
    stationaryEnergy (thetaProduct u) +
        ⟪primeGenerator u, u⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖u‖ ^ 2 =
      archGroundConstant * ‖thetaToVolume u‖ ^ 2 +
        ⟪primeDiagonalOperator u, u⟫_ℝ := by
  have hstat := stationaryEnergy_of_resolvent_eigenvector hμ heig
  have hprime := inner_primeGenerator_eq_primeDiagonal_sub_primeShift u u
  have hsub := congrArg (fun T : MassSpace →L[ℝ] MassSpace => ⟪T u, u⟫_ℝ)
    sub_groundPotentialOperator_eq
  change ⟪u - groundPotentialOperator u, u⟫_ℝ =
    ⟪primeDiagonalOperator u + archDiagonalOperator u, u⟫_ℝ at hsub
  rw [inner_sub_left, real_inner_self_eq_norm_sq, inner_add_left,
    inner_archDiagonalOperator_self] at hsub
  have hid1 : ((1 - 2 * μ) / μ) * ‖u‖ ^ 2 + ‖u‖ ^ 2 = ((1 - μ) / μ) * ‖u‖ ^ 2 := by
    field_simp [hμ]
    ring
  have hid2 : ((1 - 2 * μ) / μ) * ‖u‖ ^ 2 + ((2 * μ - 1) / μ) * ‖u‖ ^ 2 = 0 := by
    field_simp [hμ]
    ring
  exact ⟨by linarith, by linarith⟩

end RHTower.CHMDPolar
