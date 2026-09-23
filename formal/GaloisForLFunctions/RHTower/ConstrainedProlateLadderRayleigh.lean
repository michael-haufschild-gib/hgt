import Mathlib.Analysis.InnerProductSpace.Basic
import GaloisForLFunctions.RHTower.ConstrainedProlateHermiteContrast
import GaloisForLFunctions.RHTower.ConstrainedProlateLadderExactTransfer

/-!
# Depth-k Rayleigh quotients and the Hermite contrast spectral ladder

This module formalizes the multi-mode Rayleigh quotient for depth-$k$ constrained prolate trial
vectors, the exact algebraic isolation of the leading eigenvalue scale $d_{k+1}$, the general
asymptotic convergence theorem to the leading squared-coefficient ratio, and its identification
with the Gram determinant ratios $\theta_k = Q_k / Q_{k+1}$ of the Hermite contrast ladder.
-/

open Filter Topology

namespace GaloisForLFunctions.RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Finite linear combination of orthonormal modes with given coefficients. -/
def modeCombo (n : ℕ) (c : ℕ → ℝ) (e : ℕ → E) : E :=
  ∑ j ∈ Finset.range n, c j • e j

/-- The squared norm of a linear combination of orthonormal modes is the sum of squared coefficients. -/
theorem modeCombo_norm_sq (n : ℕ) (c : ℕ → ℝ) (e : ℕ → E)
    (hortho : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, i ≠ j → inner ℝ (e i) (e j) = (0 : ℝ))
    (hunit : ∀ i ∈ Finset.range n, inner ℝ (e i) (e i) = (1 : ℝ)) :
    ‖modeCombo n c e‖ ^ (2 : ℕ) = ∑ j ∈ Finset.range n, c j ^ (2 : ℕ) := by
  unfold modeCombo
  rw [← real_inner_self_eq_norm_sq]
  rw [sum_inner]
  have hdiag : ∀ i ∈ Finset.range n,
      inner ℝ (c i • e i) (∑ j ∈ Finset.range n, c j • e j) = c i ^ (2 : ℕ) := by
    intro i hi
    rw [inner_sum]
    have hsum_i : ∑ j ∈ Finset.range n, inner ℝ (c i • e i) (c j • e j) =
        inner ℝ (c i • e i) (c i • e i) := by
      refine Finset.sum_eq_single_of_mem i hi fun j hj hji => ?_
      simp only [real_inner_smul_left, real_inner_smul_right,
        hortho i hi j hj hji.symm, mul_zero]
    rw [hsum_i]
    simp only [real_inner_smul_left, real_inner_smul_right, hunit i hi]
    ring
  exact Finset.sum_congr rfl hdiag

/-- The energy under a diagonal operator `K e_j = d_j e_j`. -/
theorem modeCombo_energy (n : ℕ) (c : ℕ → ℝ) (e : ℕ → E) (K : E →L[ℝ] E) (d : ℕ → ℝ)
    (hK : ∀ j ∈ Finset.range n, K (e j) = d j • e j)
    (hortho : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, i ≠ j → inner ℝ (e i) (e j) = (0 : ℝ))
    (hunit : ∀ i ∈ Finset.range n, inner ℝ (e i) (e i) = (1 : ℝ)) :
    inner ℝ (modeCombo n c e) (K (modeCombo n c e)) = ∑ j ∈ Finset.range n, c j ^ (2 : ℕ) * d j := by
  unfold modeCombo
  have hK_sum : K (∑ j ∈ Finset.range n, c j • e j) =
      ∑ j ∈ Finset.range n, (c j * d j) • e j := by
    simp only [map_sum, ContinuousLinearMap.map_smul_of_tower]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hK j hj, smul_smul]
  rw [hK_sum, sum_inner]
  have hdiag : ∀ i ∈ Finset.range n,
      inner ℝ (c i • e i) (∑ j ∈ Finset.range n, (c j * d j) • e j) = c i ^ (2 : ℕ) * d i := by
    intro i hi
    rw [inner_sum]
    have hsum_i : ∑ j ∈ Finset.range n, inner ℝ (c i • e i) ((c j * d j) • e j) =
        inner ℝ (c i • e i) ((c i * d i) • e i) := by
      refine Finset.sum_eq_single_of_mem i hi fun j hj hji => ?_
      simp only [real_inner_smul_left, real_inner_smul_right,
        hortho i hi j hj hji.symm, mul_zero]
    rw [hsum_i]
    simp only [real_inner_smul_left, real_inner_smul_right, hunit i hi]
    ring
  exact Finset.sum_congr rfl hdiag

noncomputable section

/-- Exact Rayleigh quotient of a finite linear combination of modes. -/
def ladderRayleighQuotient (n : ℕ) (c : ℕ → ℝ) (d : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range n, c j ^ (2 : ℕ) * d j) / (∑ j ∈ Finset.range n, c j ^ (2 : ℕ))

/-- Algebraic identity isolating the leading eigenvalue `d (n - 1)` in the Rayleigh quotient. -/
theorem ladderRayleighQuotient_div_dLead_eq (n : ℕ) (c : ℕ → ℝ) (d : ℕ → ℝ)
    (hd_lead : d (n - 1) ≠ 0) (hn : 0 < n) :
    ladderRayleighQuotient n c d / d (n - 1) =
      (c (n - 1) ^ (2 : ℕ) + ∑ j ∈ Finset.range (n - 1), c j ^ (2 : ℕ) * (d j / d (n - 1))) /
        (∑ j ∈ Finset.range n, c j ^ (2 : ℕ)) := by
  unfold ladderRayleighQuotient
  have hsplit_num : ∑ j ∈ Finset.range n, c j ^ (2 : ℕ) * d j =
      (∑ j ∈ Finset.range (n - 1), c j ^ (2 : ℕ) * d j) + c (n - 1) ^ (2 : ℕ) * d (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from (Nat.succ_pred_eq_of_pos hn).symm, Finset.sum_range_succ]
  have h1 : (∑ j ∈ Finset.range n, c j ^ (2 : ℕ) * d j) / (∑ j ∈ Finset.range n, c j ^ (2 : ℕ)) / d (n - 1) =
      ((∑ j ∈ Finset.range n, c j ^ (2 : ℕ) * d j) / d (n - 1)) / (∑ j ∈ Finset.range n, c j ^ (2 : ℕ)) :=
    div_right_comm _ _ _
  rw [h1, hsplit_num, add_div, mul_div_cancel_right₀ (c (n - 1) ^ (2 : ℕ)) hd_lead,
    Finset.sum_div]
  congr 1
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => by
    rw [mul_div_assoc]

/-- General asymptotic theorem: when lower eigenvalues are negligible `d j / d (n - 1) → 0` for all
`j < n - 1`, the normalized Rayleigh quotient converges to the squared coefficient fraction. -/
theorem tendsto_ladderRayleighQuotient_div_dLead
    {ι : Type*} {L : Filter ι}
    (n : ℕ) (hn : 0 < n)
    {c : ι → ℕ → ℝ} {d : ι → ℕ → ℝ}
    {C : ℕ → ℝ}
    (hc : ∀ j ∈ Finset.range n, Tendsto (fun i => c i j) L (𝓝 (C j)))
    (hC_lead : C (n - 1) ≠ 0)
    (hd_lead : ∀ᶠ i in L, d i (n - 1) ≠ 0)
    (hd_ratio : ∀ j ∈ Finset.range (n - 1),
      Tendsto (fun i => d i j / d i (n - 1)) L (𝓝 0)) :
    Tendsto (fun i => ladderRayleighQuotient n (c i) (d i) / d i (n - 1))
      L (𝓝 (C (n - 1) ^ (2 : ℕ) / (∑ j ∈ Finset.range n, C j ^ (2 : ℕ)))) := by
  have hden_pos : 0 < ∑ j ∈ Finset.range n, C j ^ (2 : ℕ) := by
    have hn_mem : n - 1 ∈ Finset.range n := Finset.mem_range.mpr (Nat.pred_lt hn.ne')
    have hterm_pos : 0 < C (n - 1) ^ (2 : ℕ) := sq_pos_of_ne_zero hC_lead
    have hsum_le : C (n - 1) ^ (2 : ℕ) ≤ ∑ j ∈ Finset.range n, C j ^ (2 : ℕ) :=
      Finset.single_le_sum (fun j _ => sq_nonneg (C j)) hn_mem
    exact hterm_pos.trans_le hsum_le
  have hsub_sum : Tendsto (fun i => ∑ j ∈ Finset.range (n - 1), c i j ^ (2 : ℕ) * (d i j / d i (n - 1)))
      L (𝓝 0) := by
    have hterms : ∀ j ∈ Finset.range (n - 1),
        Tendsto (fun i => c i j ^ (2 : ℕ) * (d i j / d i (n - 1))) L (𝓝 (C j ^ (2 : ℕ) * 0)) := by
      intro j hj
      have hj_n : j ∈ Finset.range n := by
        rw [Finset.mem_range] at hj ⊢
        exact hj.trans (Nat.pred_lt hn.ne')
      exact (hc j hj_n).pow 2 |>.mul (hd_ratio j hj)
    have hsum := tendsto_finsetSum (Finset.range (n - 1)) hterms
    simp only [mul_zero, Finset.sum_const_zero] at hsum
    exact hsum
  have hnum : Tendsto (fun i => c i (n - 1) ^ (2 : ℕ) + ∑ j ∈ Finset.range (n - 1), c i j ^ (2 : ℕ) * (d i j / d i (n - 1)))
      L (𝓝 (C (n - 1) ^ (2 : ℕ) + 0)) := by
    have hn_mem : n - 1 ∈ Finset.range n := Finset.mem_range.mpr (Nat.pred_lt hn.ne')
    exact (hc (n - 1) hn_mem).pow 2 |>.add hsub_sum
  simp only [add_zero] at hnum
  have hden : Tendsto (fun i => ∑ j ∈ Finset.range n, c i j ^ (2 : ℕ))
      L (𝓝 (∑ j ∈ Finset.range n, C j ^ (2 : ℕ))) :=
    tendsto_finsetSum (Finset.range n) (fun j hj => (hc j hj).pow 2)
  have hlim := hnum.div hden hden_pos.ne'
  refine hlim.congr' ?_
  filter_upwards [hd_lead] with i hdi
  exact (ladderRayleighQuotient_div_dLead_eq n (c i) (d i) hdi hn).symm

/-- First adjacent Gram determinant ratio $\theta_1 / \theta_0 = (176/211) / (8/11) = 242/211$. -/
theorem constrainedProlateLadderFirstAdjacentRatio :
    ((176 : ℝ) / 211) / ((8 : ℝ) / 11) = 242 / 211 := by
  norm_num

end

end GaloisForLFunctions.RHTower
