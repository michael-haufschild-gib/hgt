import GaloisForLFunctions.HTGeometry.GammaCommonInverseCollar

/-!
# Contracting inverse-Gamma sheets on a common exterior

The common pole-microscope collar produces genuine inverse branches of `Gamma` after undoing the
factorial normalization.  Every sufficiently late branch acts on the same exterior
`{y : ℂ | 4 ≤ ‖y‖}`, maps it back into that exterior, is localized in a disjoint disk around one
negative integer, and has Lipschitz constant at most `2 / n!`.

All data in this file are defined from `gammaCommonInverseCollar`; there are no branch-existence or
contraction hypotheses.
-/

namespace GaloisForLFunctions

open Complex Function Metric Set
open scoped NNReal

noncomputable section

/-- The common closed exterior on which all selected inverse-Gamma branches act. -/
def gammaExterior : Set ℂ := {y : ℂ | 4 ≤ ‖y‖}

theorem gammaExterior_ne_zero {y : ℂ} (hy : y ∈ gammaExterior) : y ≠ 0 := by
  intro h
  subst y
  norm_num [gammaExterior] at hy

/-- Reciprocal inversion sends the common exterior into the common microscope target disk. -/
theorem neg_inv_mem_gammaMicroscopeTarget {y : ℂ} (hy : y ∈ gammaExterior) :
    -y⁻¹ ∈ Metric.closedBall (0 : ℂ) (1 / 4) := by
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr (gammaExterior_ne_zero hy)
  rw [Metric.mem_closedBall, dist_zero_right, norm_neg, norm_inv]
  apply (inv_le_comm₀ hypos (by norm_num : (0 : ℝ) < 1 / 4)).2
  norm_num [gammaExterior] at hy ⊢
  exact hy

/-- The actual inverse-Gamma sheet based at the pole `-n`. -/
def gammaExteriorInverseBranch (n : ℕ) (y : ℂ) : ℂ :=
  -(n : ℂ) + reciprocalGammaFactorialScale n *
    gammaCommonInverseCollar.branch n (-y⁻¹)

/-- Every selected exterior sheet is a genuine right inverse of the Euler Gamma function. -/
theorem Gamma_gammaExteriorInverseBranch
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {y : ℂ} (hy : y ∈ gammaExterior) :
    Complex.Gamma (gammaExteriorInverseBranch n y) = y := by
  have ht := neg_inv_mem_gammaMicroscopeTarget hy
  have hright := gammaCommonInverseCollar_rightInverse hn ht
  have hrec : reciprocalGammaEntire (gammaExteriorInverseBranch n y) = y⁻¹ := by
    exact neg_inj.mp (by simpa [gammaPoleMicroscope, gammaExteriorInverseBranch] using hright)
  have hinv : (Complex.Gamma (gammaExteriorInverseBranch n y))⁻¹ = y⁻¹ := by
    simpa [reciprocalGammaEntire] using hrec
  simpa using congrArg Inv.inv hinv

private theorem norm_reciprocalGammaFactorialScale_le_one (n : ℕ) :
    ‖reciprocalGammaFactorialScale n‖ ≤ 1 := by
  rw [norm_reciprocalGammaFactorialScale]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).2
  simpa using (show (1 : ℝ) ≤ n.factorial by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)))

/-- The displacement of an inverse sheet from its pole center is strictly smaller than its
factorial scale. -/
theorem norm_gammaExteriorInverseBranch_add_nat_lt
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {y : ℂ} (hy : y ∈ gammaExterior) :
    ‖gammaExteriorInverseBranch n y + (n : ℂ)‖ <
      ‖reciprocalGammaFactorialScale n‖ := by
  have ht := neg_inv_mem_gammaMicroscopeTarget hy
  have hb := gammaCommonInverseCollar_branch_mem hn ht
  rw [Metric.mem_ball, dist_zero_right] at hb
  rw [gammaExteriorInverseBranch]
  ring_nf
  rw [norm_mul]
  have hspos : 0 < ‖reciprocalGammaFactorialScale n‖ :=
    norm_pos_iff.mpr (by
      apply div_ne_zero
      · exact pow_ne_zero _ (by norm_num)
      · exact_mod_cast Nat.factorial_ne_zero n)
  simpa using mul_lt_mul_of_pos_left hb hspos

/-- All sufficiently late inverse sheets preserve the same exterior collar. -/
theorem gammaExteriorInverseBranch_mem
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {y : ℂ} (hy : y ∈ gammaExterior) :
    gammaExteriorInverseBranch n y ∈ gammaExterior := by
  have hn5 : 5 ≤ n := gammaCommonInverseCollar_threshold_ge_five.trans hn
  have hdisp := norm_gammaExteriorInverseBranch_add_nat_lt hn hy
  have hscale := norm_reciprocalGammaFactorialScale_le_one n
  have hnorm : (n : ℝ) -
      ‖reciprocalGammaFactorialScale n *
        gammaCommonInverseCollar.branch n (-y⁻¹)‖ ≤
      ‖gammaExteriorInverseBranch n y‖ := by
    have htriangle := norm_sub_norm_le (-(n : ℂ))
      (-(reciprocalGammaFactorialScale n *
        gammaCommonInverseCollar.branch n (-y⁻¹)))
    simpa [gammaExteriorInverseBranch, norm_neg] using htriangle
  have hpert : ‖reciprocalGammaFactorialScale n *
      gammaCommonInverseCollar.branch n (-y⁻¹)‖ < 1 := by
    simpa [gammaExteriorInverseBranch] using hdisp.trans_le hscale
  rw [gammaExterior]
  have hnreal : (5 : ℝ) ≤ n := by exact_mod_cast hn5
  exact le_trans (by linarith : (4 : ℝ) ≤ n - 1) <|
    le_trans (sub_lt_sub_left hpert (n : ℝ)).le hnorm

/-- Reciprocal inversion is `1`-Lipschitz on the common exterior.  The much stronger constant
`1/16` is available, but this sharpness is unnecessary for the factorial horizon. -/
theorem lipschitzOn_neg_inv_gammaExterior :
    LipschitzOnWith 1 (fun y : ℂ => -y⁻¹) gammaExterior := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  have hx0 := gammaExterior_ne_zero hx
  have hy0 := gammaExterior_ne_zero hy
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have hden : 1 ≤ ‖x‖ * ‖y‖ := by
    have hx4 : 4 ≤ ‖x‖ := hx
    have hy4 : 4 ≤ ‖y‖ := hy
    nlinarith [norm_nonneg x, norm_nonneg y]
  calc
    ‖-x⁻¹ - -y⁻¹‖ = ‖x⁻¹ - y⁻¹‖ := by
      rw [show -x⁻¹ - -y⁻¹ = -(x⁻¹ - y⁻¹) by ring, norm_neg]
    _ = ‖y - x‖ / (‖x‖ * ‖y‖) := by
      rw [inv_sub_inv hx0 hy0, norm_div, norm_mul]
    _ ≤ ‖y - x‖ := div_le_self (norm_nonneg _) hden
    _ = ‖x - y‖ := norm_sub_rev _ _

/-- The exact factorial Lipschitz constant used by the horizon construction. -/
def gammaExteriorContraction (n : ℕ) : ℝ≥0 :=
  2 * ‖reciprocalGammaFactorialScale n‖₊

theorem gammaExteriorContraction_eq (n : ℕ) :
    (gammaExteriorContraction n : ℝ) = 2 / (n.factorial : ℝ) := by
  simp [gammaExteriorContraction, norm_reciprocalGammaFactorialScale, div_eq_mul_inv]

/-- Each actual inverse-Gamma sheet contracts on the common exterior by its factorial constant. -/
theorem lipschitzOn_gammaExteriorInverseBranch
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n) :
    LipschitzOnWith (gammaExteriorContraction n)
      (gammaExteriorInverseBranch n) gammaExterior := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  have htx := neg_inv_mem_gammaMicroscopeTarget hx
  have hty := neg_inv_mem_gammaMicroscopeTarget hy
  have hB := gammaCommonInverseCollar.lipschitzOn hn
  have hQ := lipschitzOn_neg_inv_gammaExterior.dist_le_mul x hx y hy
  have hbranch := hB.dist_le_mul (-x⁻¹) htx (-y⁻¹) hty
  rw [gammaExteriorInverseBranch, gammaExteriorInverseBranch, dist_eq_norm]
  simp only [add_sub_add_left_eq_sub, ← mul_sub, norm_mul]
  calc
    ‖reciprocalGammaFactorialScale n‖ *
        ‖gammaCommonInverseCollar.branch n (-x⁻¹) -
          gammaCommonInverseCollar.branch n (-y⁻¹)‖
        ≤ ‖reciprocalGammaFactorialScale n‖ * (2 * dist (-x⁻¹) (-y⁻¹)) := by
          gcongr
          simpa only [dist_eq_norm, NNReal.coe_ofNat] using hbranch
    _ ≤ ‖reciprocalGammaFactorialScale n‖ * (2 * dist x y) := by
          gcongr
          simpa using hQ
    _ = (gammaExteriorContraction n : ℝ) * dist x y := by
          simp [gammaExteriorContraction]
          ring

/-- Every late branch is a strict contraction. -/
theorem gammaExteriorContraction_lt_one
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n) :
    gammaExteriorContraction n < 1 := by
  have hn5 : 5 ≤ n := gammaCommonInverseCollar_threshold_ge_five.trans hn
  rw [← NNReal.coe_lt_coe, gammaExteriorContraction_eq]
  have hfacNat : 2 < n.factorial :=
    lt_of_lt_of_le (by norm_num : 2 < (5 : ℕ).factorial)
      (Nat.factorial_le hn5)
  have hfac : (2 : ℝ) < n.factorial := by exact_mod_cast hfacNat
  exact (div_lt_iff₀ (by positivity : (0 : ℝ) < n.factorial)).2 (by simpa using hfac)

/-- Late sheets lie in pairwise disjoint radius-`1/4` pole disks. -/
theorem gammaExteriorInverseBranch_mem_poleBall
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {y : ℂ} (hy : y ∈ gammaExterior) :
    gammaExteriorInverseBranch n y ∈ Metric.ball (-(n : ℂ)) (1 / 4) := by
  rw [Metric.mem_ball, dist_eq_norm]
  have hdisp := norm_gammaExteriorInverseBranch_add_nat_lt hn hy
  have hn5 : 5 ≤ n := gammaCommonInverseCollar_threshold_ge_five.trans hn
  have hfacNat : 4 < n.factorial :=
    lt_of_lt_of_le (by norm_num : 4 < (5 : ℕ).factorial)
      (Nat.factorial_le hn5)
  have hfac : (4 : ℝ) < n.factorial := by exact_mod_cast hfacNat
  have hscale : ‖reciprocalGammaFactorialScale n‖ < 1 / 4 := by
    rw [norm_reciprocalGammaFactorialScale]
    exact (div_lt_div_iff₀ (by positivity : (0 : ℝ) < n.factorial)
      (by norm_num : (0 : ℝ) < 4)).2 (by simpa using hfac)
  simpa [sub_neg_eq_add] using hdisp.trans hscale

theorem gammaExteriorInverseBranch_images_disjoint
    {n m : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    (hm : gammaCommonInverseCollar.threshold ≤ m) (hnm : n ≠ m) :
    Disjoint (gammaExteriorInverseBranch n '' gammaExterior)
      (gammaExteriorInverseBranch m '' gammaExterior) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have hnx := gammaExteriorInverseBranch_mem_poleBall hn hx
  have hmy := gammaExteriorInverseBranch_mem_poleBall hm hy
  rw [Metric.mem_ball] at hnx hmy
  have hcenters : dist (-(n : ℂ)) (-(m : ℂ)) < 1 / 2 := by
    calc
      dist (-(n : ℂ)) (-(m : ℂ))
          ≤ dist (-(n : ℂ)) (gammaExteriorInverseBranch n x) +
              dist (gammaExteriorInverseBranch n x) (-(m : ℂ)) := dist_triangle _ _ _
      _ = dist (-(n : ℂ)) (gammaExteriorInverseBranch n x) +
              dist (gammaExteriorInverseBranch m y) (-(m : ℂ)) := by rw [heq]
      _ < 1 / 4 + 1 / 4 := add_lt_add (by simpa [dist_comm] using hnx) hmy
      _ = 1 / 2 := by norm_num
  have hnat : (1 : ℝ) ≤ dist (-(n : ℂ)) (-(m : ℂ)) := by
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · have hnm1 : n + 1 ≤ m := hlt
      rw [dist_eq_norm]
      have hltR : (n : ℝ) < m := by exact_mod_cast hlt
      have hnm1R : ((n + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hnm1
      have hnonneg : (0 : ℝ) ≤ (m : ℝ) - n := by linarith
      have hone : (1 : ℝ) ≤ (m : ℝ) - n := by
        push_cast at hnm1R
        linarith
      have hcenter : (-(n : ℂ)) - -(m : ℂ) =
          (((m : ℝ) - (n : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcenter]
      exact hone.trans_eq (Complex.norm_of_nonneg hnonneg).symm
    · have hmn1 : m + 1 ≤ n := hgt
      rw [dist_eq_norm]
      have hgtR : (m : ℝ) < n := by exact_mod_cast hgt
      have hmn1R : ((m + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hmn1
      have hnonneg : (0 : ℝ) ≤ (n : ℝ) - m := by linarith
      have hone : (1 : ℝ) ≤ (n : ℝ) - m := by
        push_cast at hmn1R
        linarith
      have hcenter : (-(n : ℂ)) - -(m : ℂ) =
          -(((n : ℝ) - (m : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcenter, norm_neg]
      exact hone.trans_eq (Complex.norm_of_nonneg hnonneg).symm
  linarith

end

end GaloisForLFunctions
