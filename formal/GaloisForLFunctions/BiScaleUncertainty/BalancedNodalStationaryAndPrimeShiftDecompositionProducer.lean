import GaloisForLFunctions.BiScaleUncertainty.PrimeGraphClockOffDiagonalSynthesisAndStationaryEnergyProducer
import GaloisForLFunctions.RHTower.CHMDResolventNodalCrossPositivityAndBalancedRayleighExcess

/-!
# Balanced-Nodal Stationary and Prime-Shift Decomposition, Five-Term Nonnegative Balance, and Off-Diagonal Clock Synthesis

This module develops **Pillar XLII** of the `BiScaleUncertainty` framework, connecting the
doubly-orthogonal balanced nonnegative nodal graph
`balancedNodalGraph p = ‖(negGraph p).val.fst‖ ^ 2 • posGraph p + ‖(posGraph p).val.fst‖ ^ 2 • negGraph p`
to the stationary and prime-shift decompositions on `SourceGraph`, the five-term nonnegative
jump-vs.-diagonal potential balance for `resolvent` eigenvectors, the `stationaryResolvent`
Cauchy–Schwarz inequality, and the off-diagonal prime-clock realization of Pillar XLI:

1. **Disjoint-Support Diagonal Additivity and Odd-Sector Identity on `balancedNodalGraph p`**:
   - `norm_thetaToVolume_balancedNodalGraph_sq`:
     `‖thetaToVolume (balancedNodalGraph p).val.fst‖ ^ 2 = ‖(negGraph p).val.fst‖ ^ 4 * ‖thetaToVolume (posGraph p).val.fst‖ ^ 2 + ‖(posGraph p).val.fst‖ ^ 4 * ‖thetaToVolume (negGraph p).val.fst‖ ^ 2`.
   - `inner_archDiagonalOperator_balancedNodalGraph_self`,
     `inner_primeDiagonalOperator_balancedNodalGraph_self`, and
     `inner_groundPotentialOperator_balancedNodalGraph_self`:
     because `posGraph p` and `negGraph p` have disjoint supports, all three local diagonal
     quadratic forms (`archDiagonalOperator`, `primeDiagonalOperator`, `groundPotentialOperator`)
     are identically additive across the two weighted lobes of `balancedNodalGraph p` with zero
     cross term.
   - `balancedNodalGraph_eq_half_norm_sq_smul_absGraph_of_odd`:
     for every odd graph vector `p` (`reflectGraph p = -p`),
     `balancedNodalGraph p = ((1 / 2) * ‖p.val.fst‖ ^ 2) • absGraph p` and
     `primGraph (balancedNodalGraph p) = ((1 / 2) * ‖p.val.fst‖ ^ 2) • primGraph (absGraph p)`.

2. **Nonnegativity and Three-Term Decompositions of `primeShiftOperator`, `primeGenerator`, and
   `stationaryEnergy` on `balancedNodalGraph p`**:
   - `balancedNodalGraph_fst_ae_nonneg` and `inner_primeShiftOperator_balancedNodalGraph_self_nonneg`:
     `0 ≤ᵐ[massMeasure] (balancedNodalGraph p).val.fst` and
     `0 ≤ ⟪primeShiftOperator (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ`.
   - `inner_primeShiftOperator_balancedNodalGraph_self_eq`:
     expands `⟪primeShiftOperator (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ`
     into the sum of three nonnegative terms (`posGraph`-`posGraph`, `negGraph`-`negGraph`, and
     `2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`).
   - `inner_primeGenerator_balancedNodalGraph_self_eq` and
     `two_mul_lobe_prod_inner_primeShift_le_primeGenerator`:
     weighted Beurling–Deny cross-jump bound for `primeGenerator` on `balancedNodalGraph p`.
   - `stationaryEnergy_balancedNodalGraph_eq` and
     `two_mul_lobe_prod_neg_stationary_cross_le_stationaryEnergy`:
     weighted Beurling–Deny cross-jump bound for `stationaryEnergy` on `balancedNodalGraph p`.

3. **Three-Term Edge Norm and Five-Term Nonnegative Jump-vs.-Diagonal Balance for `balancedNodalGraph q`**:
   - `balancedNodalGraph_three_term_nonneg_snd_sq_of_eigenvector`:
     for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
     `‖(balancedNodalGraph q).val.snd‖ ^ 2 - ‖q.val.fst‖ ^ 4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + ‖q.val.fst‖ ^ 4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ = ((1 - μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2`.
   - `balancedNodalGraph_five_term_jump_eq_diagonals_of_eigenvector`:
     `stationaryEnergy (thetaProduct (balancedNodalGraph q).val.fst) + ⟪primeGenerator (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ - ‖q.val.fst‖ ^ 4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + ‖q.val.fst‖ ^ 4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ + ((2 * μ - 1) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 = archGroundConstant * ‖thetaToVolume (balancedNodalGraph q).val.fst‖ ^ 2 + ⟪primeDiagonalOperator (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ`.

4. **`stationaryResolvent` Cauchy–Schwarz Bound and Off-Diagonal Prime-Clock Synthesis on `balancedNodalGraph`**:
   - `norm_balancedNodalGraph_fst_pow_four_le_stationaryResolvent_mul_of_eigenvector` and
     `stationary_balancedNodalGraph_nodal_cross_le_of_rayleigh_le`:
     zero-mode-free `stationaryResolvent` Cauchy–Schwarz and Rayleigh-to-energy nodal bounds on
     `balancedNodalGraph q`.
   - `exists_cutoff_eventually_offDiag_primeClock_primGraph_balancedNodalGraph_of_eigenvector`:
     synthesizes the doubly-orthogonal balanced nodal vector `primGraph (balancedNodalGraph q)` via
     the off-diagonal (`p ≠ p'`) distinct-prime clock sum with arbitrarily small diagonal cost.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators
noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

open _root_.RHTower
open _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.CHMDClosedJump
open _root_.RHTower.CHMDTranslation
open _root_.RHTower.ThetaSourceWard
open _root_.RHTower.CHMDPolar

/-! ## Section 1: Disjoint-Support Diagonal Additivity and Odd-Sector Identity on `balancedNodalGraph p` -/

/-- Because `thetaToVolume (posGraph p).val.fst` and `thetaToVolume (negGraph p).val.fst` are
orthogonal in `L^2(volume)`, the `thetaToVolume` norm-squared of `balancedNodalGraph p` is the
fourth-power weighted sum of the individual lobe `thetaToVolume` norms-squared:
`‖thetaToVolume (balancedNodalGraph p).val.fst‖ ^ 2 = ‖(negGraph p).val.fst‖ ^ 4 * ‖thetaToVolume (posGraph p).val.fst‖ ^ 2 + ‖(posGraph p).val.fst‖ ^ 4 * ‖thetaToVolume (negGraph p).val.fst‖ ^ 2`. -/
theorem norm_thetaToVolume_balancedNodalGraph_sq (p : SourceGraph) :
    ‖thetaToVolume (balancedNodalGraph p).val.fst‖ ^ 2 =
      ‖(negGraph p).val.fst‖ ^ 4 * ‖thetaToVolume (posGraph p).val.fst‖ ^ 2 +
        ‖(posGraph p).val.fst‖ ^ 4 * ‖thetaToVolume (negGraph p).val.fst‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, balancedNodalGraph_fst, map_add, map_smul, map_smul,
    inner_add_left, inner_add_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm (thetaToVolume (posGraph p).val.fst) (thetaToVolume (negGraph p).val.fst),
    inner_thetaToVolume_posGraph_negGraph]
  ring

/-- Disjoint-support additivity of `archDiagonalOperator` on `balancedNodalGraph p`. -/
theorem inner_archDiagonalOperator_balancedNodalGraph_self (p : SourceGraph) :
    ⟪archDiagonalOperator (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ =
      ‖(negGraph p).val.fst‖ ^ 4 *
          ⟪archDiagonalOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
        ‖(posGraph p).val.fst‖ ^ 4 *
          ⟪archDiagonalOperator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  rw [inner_archDiagonalOperator_self, inner_archDiagonalOperator_self,
    inner_archDiagonalOperator_self, norm_thetaToVolume_balancedNodalGraph_sq]
  ring

/-- Disjoint-support additivity of `primeDiagonalOperator` on `balancedNodalGraph p`. -/
theorem inner_primeDiagonalOperator_balancedNodalGraph_self (p : SourceGraph) :
    ⟪primeDiagonalOperator (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ =
      ‖(negGraph p).val.fst‖ ^ 4 *
          ⟪primeDiagonalOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
        ‖(posGraph p).val.fst‖ ^ 4 *
          ⟪primeDiagonalOperator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  rw [balancedNodalGraph_fst, map_add, map_smul, map_smul,
    inner_add_left, inner_add_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    primeDiagonalOperator_symmetric (negGraph p).val.fst (posGraph p).val.fst,
    real_inner_comm (primeDiagonalOperator (posGraph p).val.fst) (negGraph p).val.fst,
    inner_primeDiagonalOperator_posGraph_negGraph]
  ring

/-- Disjoint-support additivity of `groundPotentialOperator` on `balancedNodalGraph p`. -/
theorem inner_groundPotentialOperator_balancedNodalGraph_self (p : SourceGraph) :
    ⟪groundPotentialOperator (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ =
      ‖(negGraph p).val.fst‖ ^ 4 *
          ⟪groundPotentialOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
        ‖(posGraph p).val.fst‖ ^ 4 *
          ⟪groundPotentialOperator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  rw [balancedNodalGraph_fst, map_add, map_smul, map_smul,
    inner_add_left, inner_add_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    groundPotentialOperator_symmetric (negGraph p).val.fst (posGraph p).val.fst,
    real_inner_comm (groundPotentialOperator (posGraph p).val.fst) (negGraph p).val.fst,
    inner_groundPotentialOperator_posGraph_negGraph]
  ring

/-- **Odd-Sector Coincidence of `balancedNodalGraph` and `absGraph`**:
for every odd graph vector `p : SourceGraph` (`reflectGraph p = -p`), its positive and negative
lobes have equal `MassSpace` norm-squared `(1 / 2) * ‖p.val.fst‖ ^ 2`, so
`balancedNodalGraph p = ((1 / 2) * ‖p.val.fst‖ ^ 2) • absGraph p` and
`primGraph (balancedNodalGraph p) = ((1 / 2) * ‖p.val.fst‖ ^ 2) • primGraph (absGraph p)`. -/
theorem balancedNodalGraph_eq_half_norm_sq_smul_absGraph_of_odd {p : SourceGraph}
    (hp : reflectGraph p = -p) :
    balancedNodalGraph p = ((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • absGraph p ∧
      primGraph (balancedNodalGraph p) =
        ((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • primGraph (absGraph p) := by
  obtain ⟨hpos, hneg⟩ := norm_posGraph_and_negGraph_fst_sq_eq_half_of_odd hp
  have h1 : balancedNodalGraph p = ((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • absGraph p := by
    unfold balancedNodalGraph
    rw [hpos, hneg, ← smul_add, posGraph_add_negGraph]
  have h2 : primGraph (balancedNodalGraph p) =
      ((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • primGraph (absGraph p) := by
    apply source_projection_injective
    change (primGraph (balancedNodalGraph p)).val.fst =
      ((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • (primGraph (absGraph p)).val.fst
    rw [h1, primGraph_fst, primGraph_fst]
    change (((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • (absGraph p).val.fst) -
        (2 * ⟪((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) • (absGraph p).val.fst, oneL⟫_ℝ) • oneL =
      ((1 / 2 : ℝ) * ‖p.val.fst‖ ^ 2) •
        ((absGraph p).val.fst - (2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ) • oneL)
    rw [real_inner_smul_left, smul_sub, smul_smul]
    congr 2
    ring
  exact ⟨h1, h2⟩

/-! ## Section 2: Nonnegativity and Three-Term Decompositions of `primeShiftOperator`,
`primeGenerator`, and `stationaryEnergy` on `balancedNodalGraph p` -/

/-- Almost-everywhere nonnegativity of `(balancedNodalGraph p).val.fst` on `massMeasure`. -/
theorem balancedNodalGraph_fst_ae_nonneg (p : SourceGraph) :
    0 ≤ᵐ[massMeasure] ((balancedNodalGraph p).val.fst : ℝ → ℝ) := by
  rw [balancedNodalGraph_fst]
  have h1 := Lp.coeFn_add (‖(negGraph p).val.fst‖ ^ 2 • (posGraph p).val.fst)
    (‖(posGraph p).val.fst‖ ^ 2 • (negGraph p).val.fst)
  have h2 := Lp.coeFn_smul (‖(negGraph p).val.fst‖ ^ 2) (posGraph p).val.fst
  have h3 := Lp.coeFn_smul (‖(posGraph p).val.fst‖ ^ 2) (negGraph p).val.fst
  filter_upwards [h1, h2, h3, posGraph_fst_ae p, negGraph_fst_ae p] with x hx1 hx2 hx3 hp hn
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx1 hx2 hx3
  rw [hx1, hx2, hx3, hp, hn]
  exact add_nonneg (mul_nonneg (sq_nonneg _) (posFun_nonneg _))
    (mul_nonneg (sq_nonneg _) (negFun_nonneg _))

/-- Exact three-term nonnegative expansion of `⟪primeShiftOperator (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ`. -/
theorem inner_primeShiftOperator_balancedNodalGraph_self_eq (p : SourceGraph) :
    ⟪primeShiftOperator (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ =
      ‖(negGraph p).val.fst‖ ^ 4 *
          ⟪primeShiftOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
        ‖(posGraph p).val.fst‖ ^ 4 *
          ⟪primeShiftOperator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ +
        2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) *
          ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  rw [balancedNodalGraph_fst, map_add, map_smul, map_smul,
    inner_add_left, inner_add_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    primeShiftOperator_symmetric (negGraph p).val.fst (posGraph p).val.fst,
    real_inner_comm (primeShiftOperator (posGraph p).val.fst) (negGraph p).val.fst]
  ring

/-- Nonnegativity of `⟪primeShiftOperator (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ`
and lower bound by the weighted cross-lobe prime-shift term. -/
theorem inner_primeShiftOperator_balancedNodalGraph_self_nonneg (p : SourceGraph) :
    0 ≤ ⟪primeShiftOperator (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ ∧
      2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) *
          ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ≤
        ⟪primeShiftOperator (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ := by
  have heq := inner_primeShiftOperator_balancedNodalGraph_self_eq p
  have hp : 0 ≤ ‖(negGraph p).val.fst‖ ^ 4 *
      ⟪primeShiftOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ :=
    mul_nonneg (by positivity) (inner_primeShiftOperator_posGraph_self_nonneg p)
  have hn : 0 ≤ ‖(posGraph p).val.fst‖ ^ 4 *
      ⟪primeShiftOperator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ :=
    mul_nonneg (by positivity) (inner_primeShiftOperator_negGraph_self_nonneg p)
  have hc : 0 ≤ 2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) *
      ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ :=
    mul_nonneg (by positivity) (inner_primeShiftOperator_posGraph_negGraph_nonneg p)
  exact ⟨by linarith, by linarith⟩

/-- Exact expansion of `⟪primeGenerator (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ`
and weighted Beurling–Deny cross-jump inequality for `primeGenerator`. -/
theorem inner_primeGenerator_balancedNodalGraph_self_eq (p : SourceGraph) :
    ⟪primeGenerator (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ =
      ‖(negGraph p).val.fst‖ ^ 4 *
          ⟪primeGenerator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
        ‖(posGraph p).val.fst‖ ^ 4 *
          ⟪primeGenerator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ -
        2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) *
          ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ∧
    2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) *
        ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ≤
      ‖(negGraph p).val.fst‖ ^ 4 *
          ⟪primeGenerator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
        ‖(posGraph p).val.fst‖ ^ 4 *
          ⟪primeGenerator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  have h1 : ⟪primeGenerator (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ =
      ‖(negGraph p).val.fst‖ ^ 4 *
          ⟪primeGenerator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
        ‖(posGraph p).val.fst‖ ^ 4 *
          ⟪primeGenerator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ -
        2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) *
          ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
    have hd := inner_primeDiagonalOperator_balancedNodalGraph_self p
    have hs := inner_primeShiftOperator_balancedNodalGraph_self_eq p
    have hbal := inner_primeGenerator_eq_primeDiagonal_sub_primeShift
      (balancedNodalGraph p).val.fst (balancedNodalGraph p).val.fst
    have hp := inner_primeGenerator_eq_primeDiagonal_sub_primeShift
      (posGraph p).val.fst (posGraph p).val.fst
    have hn := inner_primeGenerator_eq_primeDiagonal_sub_primeShift
      (negGraph p).val.fst (negGraph p).val.fst
    linear_combination hbal + hd - hs - ‖(negGraph p).val.fst‖ ^ 4 * hp -
      ‖(posGraph p).val.fst‖ ^ 4 * hn
  have hnn := inner_primeGenerator_self_nonneg (balancedNodalGraph p).val.fst
  exact ⟨h1, by linarith⟩

/-- **Exact Expansion of `stationaryEnergy` on `balancedNodalGraph p` and Weighted Stationary
Beurling–Deny Cross-Jump Bound**:
for every `p : SourceGraph`,
`stationaryEnergy (thetaProduct (balancedNodalGraph p).val.fst) = ‖(negGraph p).val.fst‖ ^ 4 * stationaryEnergy (thetaProduct (posGraph p).val.fst) + ‖(posGraph p).val.fst‖ ^ 4 * stationaryEnergy (thetaProduct (negGraph p).val.fst) + 2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ`
and
`-2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ ≤ ‖(negGraph p).val.fst‖ ^ 4 * stationaryEnergy (thetaProduct (posGraph p).val.fst) + ‖(posGraph p).val.fst‖ ^ 4 * stationaryEnergy (thetaProduct (negGraph p).val.fst)`. -/
theorem stationaryEnergy_balancedNodalGraph_eq (p : SourceGraph) :
    stationaryEnergy (thetaProduct (balancedNodalGraph p).val.fst) =
      ‖(negGraph p).val.fst‖ ^ 4 * stationaryEnergy (thetaProduct (posGraph p).val.fst) +
        ‖(posGraph p).val.fst‖ ^ 4 * stationaryEnergy (thetaProduct (negGraph p).val.fst) +
        2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) *
          ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ ∧
    -2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) *
        ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ ≤
      ‖(negGraph p).val.fst‖ ^ 4 * stationaryEnergy (thetaProduct (posGraph p).val.fst) +
        ‖(posGraph p).val.fst‖ ^ 4 * stationaryEnergy (thetaProduct (negGraph p).val.fst) := by
  have hmap : fullGroundEquiv (balancedNodalGraph p) =
      ‖(negGraph p).val.fst‖ ^ 2 • fullGroundEquiv (posGraph p) +
        ‖(posGraph p).val.fst‖ ^ 2 • fullGroundEquiv (negGraph p) := by
    unfold balancedNodalGraph
    rw [map_add, map_smul, map_smul]
  have hnorm_eq : ‖fullGroundEquiv (balancedNodalGraph p)‖ ^ 2 =
      ‖(negGraph p).val.fst‖ ^ 4 * ‖fullGroundEquiv (posGraph p)‖ ^ 2 +
        ‖(posGraph p).val.fst‖ ^ 4 * ‖fullGroundEquiv (negGraph p)‖ ^ 2 +
        2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) *
          ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ := by
    rw [hmap, norm_add_sq_real, norm_smul, norm_smul,
      Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _),
      Submodule.coe_inner, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower,
      real_inner_smul_left, real_inner_smul_right, ← Submodule.coe_inner,
      inner_fullGroundEquiv_posGraph_negGraph_eq_snd]
    ring
  rw [norm_fullGroundEquiv_sq, norm_fullGroundEquiv_sq, norm_fullGroundEquiv_sq,
    norm_balancedNodalGraph_fst_sq, ← norm_posGraph_fst_sq_add_negGraph_fst_sq p] at hnorm_eq
  have h1 : stationaryEnergy (thetaProduct (balancedNodalGraph p).val.fst) =
      ‖(negGraph p).val.fst‖ ^ 4 * stationaryEnergy (thetaProduct (posGraph p).val.fst) +
        ‖(posGraph p).val.fst‖ ^ 4 * stationaryEnergy (thetaProduct (negGraph p).val.fst) +
        2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) *
          ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ := by
    linarith
  have hnn := (stationaryEnergy_nonneg_and_le_norm_sq (balancedNodalGraph p)).1
  exact ⟨h1, by linarith⟩

/-! ## Section 3: Three-Term Edge Norm and Five-Term Nonnegative Balanced-Nodal Balance for Eigenvectors -/

/-- **Three-Term Nonnegative Edge-Norm Decomposition of `balancedNodalGraph q` for Any Eigenvector**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`‖(balancedNodalGraph q).val.snd‖ ^ 2 - ‖q.val.fst‖ ^ 4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + ‖q.val.fst‖ ^ 4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ = ((1 - μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2`,
where all three summands on the left-hand side are nonnegative. -/
theorem balancedNodalGraph_three_term_nonneg_snd_sq_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    ‖(balancedNodalGraph q).val.snd‖ ^ 2 -
        ‖q.val.fst‖ ^ 4 *
          ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ‖q.val.fst‖ ^ 4 *
          ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ =
      ((1 - μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 := by
  intro q
  have h1 := norm_balancedNodalGraph_snd_sq_of_eigenvector hμ heig
  have h2 := norm_balancedNodalGraph_fst_sq q
  have h3 := sourcePair_posGraph_negGraph_eq_stationary_sub_primeShift q
  change ‖(balancedNodalGraph q).val.snd‖ ^ 2 = _ at h1
  rw [h3] at h1
  calc ‖(balancedNodalGraph q).val.snd‖ ^ 2 -
        ‖q.val.fst‖ ^ 4 *
          ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ‖q.val.fst‖ ^ 4 *
          ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ
      = ((1 - μ) / μ) *
          (‖q.val.fst‖ ^ 2 * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2)) := by
        rw [h1]
        ring
    _ = ((1 - μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 := by
        rw [← h2]

/-- **Product Bounds on the Stationary and Prime-Shift Cross-Jump Pairings for Any Eigenvector**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`-‖q.val.fst‖ ^ 4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ ≤ ((1 - μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2`
and
`‖q.val.fst‖ ^ 4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤ ((1 - μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2`. -/
theorem stationary_and_primeShift_mul_pow_four_le_balancedNodalGraph_fst_sq_of_eigenvector
    {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w;
    -‖q.val.fst‖ ^ 4 *
        ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ ≤
      ((1 - μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 ∧
    ‖q.val.fst‖ ^ 4 *
        ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤
      ((1 - μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 := by
  intro q
  have h1 := balancedNodalGraph_three_term_nonneg_snd_sq_of_eigenvector hμ heig
  have hsnd_nn : 0 ≤ ‖(balancedNodalGraph q).val.snd‖ ^ 2 := sq_nonneg _
  have hstat_nn : 0 ≤ -‖q.val.fst‖ ^ 4 *
      ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ := by
    have hst := neg_nonneg.mpr (inner_fullGroundEquiv_posGraph_negGraph_snd_nonpos q)
    nlinarith [show 0 ≤ ‖q.val.fst‖ ^ 4 by positivity]
  have hprime_nn : 0 ≤ ‖q.val.fst‖ ^ 4 *
      ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ :=
    mul_nonneg (by positivity) (inner_primeShiftOperator_posGraph_negGraph_nonneg q)
  exact ⟨by linarith, by linarith⟩

/-- **Five-Term Nonnegative Balanced-Nodal Jump-vs.-Diagonal Balance for Any Eigenvector**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`stationaryEnergy (thetaProduct (balancedNodalGraph q).val.fst) + ⟪primeGenerator (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ - ‖q.val.fst‖ ^ 4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + ‖q.val.fst‖ ^ 4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ + ((2 * μ - 1) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2`
equals both
`archGroundConstant * ‖thetaToVolume (balancedNodalGraph q).val.fst‖ ^ 2 + ⟪primeDiagonalOperator (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ`
and
`‖(balancedNodalGraph q).val.fst‖ ^ 2 - ⟪groundPotentialOperator (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ`,
where all five left-hand summands are nonnegative whenever `1 / 2 ≤ μ`. -/
theorem balancedNodalGraph_five_term_jump_eq_diagonals_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    stationaryEnergy (thetaProduct (balancedNodalGraph q).val.fst) +
        ⟪primeGenerator (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ -
        ‖q.val.fst‖ ^ 4 *
          ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ‖q.val.fst‖ ^ 4 *
          ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 =
      archGroundConstant * ‖thetaToVolume (balancedNodalGraph q).val.fst‖ ^ 2 +
        ⟪primeDiagonalOperator (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ ∧
    stationaryEnergy (thetaProduct (balancedNodalGraph q).val.fst) +
        ⟪primeGenerator (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ -
        ‖q.val.fst‖ ^ 4 *
          ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ‖q.val.fst‖ ^ 4 *
          ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 =
      ‖(balancedNodalGraph q).val.fst‖ ^ 2 -
        ⟪groundPotentialOperator (balancedNodalGraph q).val.fst,
          (balancedNodalGraph q).val.fst⟫_ℝ := by
  intro q
  have h1 := balancedNodalGraph_three_term_nonneg_snd_sq_of_eigenvector hμ heig
  have h2 := norm_snd_sq_eq_stationary_add_primeGenerator_add_groundPotential
    (balancedNodalGraph q)
  have h3 := arch_add_primeDiagonal_eq_norm_sq_sub_groundPotential
    (balancedNodalGraph q).val.fst
  have hid : ((1 - μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 +
      ((2 * μ - 1) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 =
      ‖(balancedNodalGraph q).val.fst‖ ^ 2 := by
    field_simp [hμ]
    ring
  exact ⟨by linarith, by linarith⟩

/-- Uniform potential upper bound `(1 + thetaGroundPotentialBound) * ‖(balancedNodalGraph q).val.fst‖ ^ 2`
on the five-term nonnegative balanced-nodal sum of any `resolvent` eigenvector. -/
theorem balancedNodalGraph_five_term_jump_le_potential_bound_of_eigenvector
    {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    stationaryEnergy (thetaProduct (balancedNodalGraph q).val.fst) +
        ⟪primeGenerator (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ -
        ‖q.val.fst‖ ^ 4 *
          ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ‖q.val.fst‖ ^ 4 *
          ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ +
        ((2 * μ - 1) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 ≤
      (1 + thetaGroundPotentialBound) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 := by
  intro q
  have h1 := (balancedNodalGraph_five_term_jump_eq_diagonals_of_eigenvector hμ heig).1
  have h2 := (arch_add_primeDiagonal_nonneg_and_le (balancedNodalGraph q).val.fst).2
  linarith

/-! ## Section 4: `stationaryResolvent` Cauchy–Schwarz Bound and Off-Diagonal Prime-Clock Synthesis
on `balancedNodalGraph q` and `primGraph (balancedNodalGraph q)` -/

/-- **Zero-Mode-Free `stationaryResolvent` Cauchy–Schwarz Inequality on `balancedNodalGraph q`**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`‖(balancedNodalGraph q).val.fst‖ ^ 4 ≤ ⟪stationaryResolvent (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ * (((1 - μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 + ‖q.val.fst‖ ^ 4 * sourcePair (posGraph q) (negGraph q) + archGroundConstant * ‖thetaToVolume (balancedNodalGraph q).val.fst‖ ^ 2 + ⟪primeShiftOperator (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ)`. -/
theorem norm_balancedNodalGraph_fst_pow_four_le_stationaryResolvent_mul_of_eigenvector
    {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    ‖(balancedNodalGraph q).val.fst‖ ^ 4 ≤
      ⟪stationaryResolvent (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ *
        (((1 - μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 +
          ‖q.val.fst‖ ^ 4 * sourcePair (posGraph q) (negGraph q) +
          archGroundConstant * ‖thetaToVolume (balancedNodalGraph q).val.fst‖ ^ 2 +
          ⟪primeShiftOperator (balancedNodalGraph q).val.fst,
            (balancedNodalGraph q).val.fst⟫_ℝ) := by
  intro q
  have hcs := norm_fst_pow_four_le_inner_stationaryResolvent_mul (balancedNodalGraph q)
  have hstat := sourceEnergy_eq_stationary_sub_arch_sub_primeShift (balancedNodalGraph q)
  have hE := sourceEnergy_balancedNodalGraph_of_eigenvector hμ heig
  have hnorm := norm_balancedNodalGraph_fst_sq q
  change sourceEnergy (balancedNodalGraph q) = _ at hE
  have hE' : sourceEnergy (balancedNodalGraph q) =
      ((1 - 2 * μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 +
        ‖q.val.fst‖ ^ 4 * sourcePair (posGraph q) (negGraph q) := by
    rw [hE, hnorm]
    ring
  have hid : ((1 - 2 * μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 +
      ‖(balancedNodalGraph q).val.fst‖ ^ 2 =
      ((1 - μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 := by
    field_simp [hμ]
    ring
  have hsum : stationaryEnergy (thetaProduct (balancedNodalGraph q).val.fst) +
      ‖(balancedNodalGraph q).val.fst‖ ^ 2 =
      ((1 - μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 +
        ‖q.val.fst‖ ^ 4 * sourcePair (posGraph q) (negGraph q) +
        archGroundConstant * ‖thetaToVolume (balancedNodalGraph q).val.fst‖ ^ 2 +
        ⟪primeShiftOperator (balancedNodalGraph q).val.fst,
          (balancedNodalGraph q).val.fst⟫_ℝ := by
    linarith
  rwa [hsum] at hcs

/-- **Zero-Mode-Free `stationaryResolvent` Rayleigh Nodal Bound on `balancedNodalGraph q`**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w` and any `0 < σ_max`,
if `⟪stationaryResolvent (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ ≤ σ_max * ‖(balancedNodalGraph q).val.fst‖ ^ 2`,
then
`(((1 - σ_max) / σ_max) - ((1 - 2 * μ) / μ)) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 - ‖q.val.fst‖ ^ 4 * sourcePair (posGraph q) (negGraph q) ≤ archGroundConstant * ‖thetaToVolume (balancedNodalGraph q).val.fst‖ ^ 2 + ⟪primeShiftOperator (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ`. -/
theorem stationary_balancedNodalGraph_nodal_cross_le_of_rayleigh_le
    {μ σ_max : ℝ} (hμ : μ ≠ 0) (hσ : 0 < σ_max) {w : MassSpace} (heig : resolvent w = μ • w)
    (hray : ⟪stationaryResolvent (balancedNodalGraph (rieszLift w)).val.fst,
        (balancedNodalGraph (rieszLift w)).val.fst⟫_ℝ ≤
      σ_max * ‖(balancedNodalGraph (rieszLift w)).val.fst‖ ^ 2) :
    let q := rieszLift w
    (((1 - σ_max) / σ_max) - ((1 - 2 * μ) / μ)) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 -
        ‖q.val.fst‖ ^ 4 * sourcePair (posGraph q) (negGraph q) ≤
      archGroundConstant * ‖thetaToVolume (balancedNodalGraph q).val.fst‖ ^ 2 +
        ⟪primeShiftOperator (balancedNodalGraph q).val.fst,
          (balancedNodalGraph q).val.fst⟫_ℝ := by
  intro q
  have h1 := stationaryEnergy_ge_of_inner_stationaryResolvent_le hσ hray
  have h2 := sourceEnergy_eq_stationary_sub_arch_sub_primeShift (balancedNodalGraph q)
  have hE := sourceEnergy_balancedNodalGraph_of_eigenvector hμ heig
  have hnorm := norm_balancedNodalGraph_fst_sq q
  change sourceEnergy (balancedNodalGraph q) = _ at hE
  have hE' : sourceEnergy (balancedNodalGraph q) =
      ((1 - 2 * μ) / μ) * ‖(balancedNodalGraph q).val.fst‖ ^ 2 +
        ‖q.val.fst‖ ^ 4 * sourcePair (posGraph q) (negGraph q) := by
    rw [hE, hnorm]
    ring
  linarith

/-- **Off-Diagonal Prime-Clock Synthesis of the Doubly-Orthogonal Balanced Nodal Graph
`primGraph (balancedNodalGraph q)`**:
for every primitive eigenvector `resolvent w = μ • w` (`μ ≠ 0`, `⟪w, oneL⟫_ℝ = 0`) with
`q = rieszLift w` and `u_bal = primGraph (balancedNodalGraph q)` (which is simultaneously
orthogonal to `oneL` and to `q.val.fst`), every depth threshold `T₀ : ℝ`, and every `0 < ε`,
there exists a smooth cutoff `k : ℕ` such that for all sufficiently large `N : ℕ`, there exists
a finite set `S` of distinct primes `p > √N` with `log(N / p) > T₀` such that:
1. the packet `P = ∑ p ∈ S, canonicalPrimeGraphClockAtom k N p` approximates `u_bal` in
   `SourceGraph` with `‖P - u_bal‖ < ε`,
2. the diagonal graph norm-squared sum satisfies
   `∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ ^ 2 < ε`,
3. the off-diagonal (`p ≠ p'`) distinct-prime clock sum approximates the exact doubly-orthogonal
   balanced nodal energy:
   `|offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N) - (((1 - 2 * μ) / μ) * ‖u_bal.val.fst‖ ^ 2 + ‖q.val.fst‖ ^ 4 * (sourcePair (posGraph q) (negGraph q) + ((1 - μ) / (2 * μ)) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2))| ≤ ε + ε ^ 2 + 2 * ε * ‖u_bal‖`. -/
theorem exists_cutoff_eventually_offDiag_primeClock_primGraph_balancedNodalGraph_of_eigenvector
    {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace} (hprim : ⟪w, oneL⟫_ℝ = 0)
    (heig : resolvent w = μ • w) (T₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    let q := rieszLift w
    let u_bal := primGraph (balancedNodalGraph q)
    ∃ k : ℕ, ∀ᶠ N : ℕ in atTop,
      ∃ S : Finset ℕ,
        (∀ p ∈ S, Nat.Prime p ∧ Real.sqrt (N : ℝ) < (p : ℝ) ∧ T₀ < Real.log ((N : ℝ) / p)) ∧
        ‖(∑ p ∈ S, canonicalPrimeGraphClockAtom k N p) - u_bal‖ < ε ∧
        (∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ ^ 2) < ε ∧
        |offDiagSourcePairSum S (canonicalPrimeGraphClockAtom k N) -
          (((1 - 2 * μ) / μ) * ‖u_bal.val.fst‖ ^ 2 +
            ‖q.val.fst‖ ^ 4 *
              (sourcePair (posGraph q) (negGraph q) +
                ((1 - μ) / (2 * μ)) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2))| ≤
          ε + ε ^ 2 + 2 * ε * ‖u_bal‖ := by
  intro q u_bal
  have hE : sourceEnergy u_bal =
      ((1 - 2 * μ) / μ) * ‖u_bal.val.fst‖ ^ 2 +
        ‖q.val.fst‖ ^ 4 *
          (sourcePair (posGraph q) (negGraph q) +
            ((1 - μ) / (2 * μ)) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2) :=
    (primGraph_balancedNodalGraph_orthogonal_and_energy_of_primitive_eigenvector
      hμ hprim heig).2.2.2
  obtain ⟨k, hk⟩ := exists_cutoff_eventually_offDiag_primeClock_realization
    u_bal (ContinuousLinearMap.id ℝ MassSpace) T₀ hε
  refine ⟨k, hk.mono fun N hN => ?_⟩
  rcases hN with ⟨S, hS, happrox, hdiag, hoffE, _⟩
  rw [hE] at hoffE
  exact ⟨S, hS, happrox, hdiag, hoffE⟩

end GaloisForLFunctions.BiScaleUncertainty
