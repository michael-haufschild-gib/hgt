import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Finite dual vectors turn response bounds into weighted and uniform leakage bounds. -/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

theorem finiteWeil_extend_norm {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι → κ) (he : Function.Injective e) (c : ι → ℝ) :
    ‖Function.extend e c (fun _ => 0)‖ = ‖c‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg c)).mpr
    intro j
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [he.extend_apply]
      exact norm_le_pi_norm c i
    · rw [Function.extend_apply' c (fun _ => 0) j hj, norm_zero]
      exact norm_nonneg c
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [← he.extend_apply c (fun _ => 0) i]
    exact norm_le_pi_norm _ (e i)

theorem finiteWeil_extend_abs_sum {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι → κ) (he : Function.Injective e) (c : ι → ℝ) :
    ∑ j : κ, |Function.extend e c (fun _ => 0) j| = ∑ i : ι, |c i| := by
  symm
  apply Fintype.sum_of_injective e he
  · intro j hj
    rw [Function.extend_apply' c (fun _ => 0) j hj, abs_zero]
  · intro i
    rw [he.extend_apply]

/-- Zero extension transports every finite pairing, not only its norm. -/
theorem finiteWeil_extend_pairing {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι → κ) (he : Function.Injective e) (c : ι → ℝ) (f : κ → ℝ) :
    ∑ j, Function.extend e c (fun _ => 0) j * f j = ∑ i, c i * f (e i) := by
  symm
  apply Fintype.sum_of_injective e he
  · intro j hj
    rw [Function.extend_apply' c (fun _ => 0) j hj, zero_mul]
  · intro i
    rw [he.extend_apply]

/-- Moment-annihilating pairings ignore every background in the same finite span. -/
theorem finiteWeil_pairing_sub_background {ι κ : Type} [Fintype ι] [Fintype κ]
    (d y h : ι → ℝ) (b : κ → ℝ) (p : κ → ℕ)
    (hm : ∀ k, ∑ i, d i * h i ^ p k = 0) :
    ∑ i, (y i - ∑ k, b k * h i ^ p k) * d i = ∑ i, y i * d i := by
  have hz : (∑ i, (∑ k, b k * h i ^ p k) * d i) = 0 := by
    calc
      _ = ∑ k, b k * ∑ i, d i * h i ^ p k := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by simp only [hm, mul_zero, Finset.sum_const_zero]
  simp only [sub_mul, Finset.sum_sub_distrib, hz, sub_zero]

theorem finiteWeil_coordinate_le_pairing_add_off {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : ι) (d y : ι → ℝ) (hi : |d i| = 1) :
    |y i| ≤ |∑ j, y j * d j| + ∑ j ∈ Finset.univ.erase i, |d j| * |y j| := by
  have hsum := Finset.sum_erase_add Finset.univ (fun j => y j * d j) (Finset.mem_univ i)
  have hterm : y i * d i = (∑ j, y j * d j) -
      ∑ j ∈ Finset.univ.erase i, y j * d j := by linarith only [hsum]
  calc
    |y i| = |y i * d i| := by rw [abs_mul, hi, mul_one]
    _ ≤ |∑ j, y j * d j| + |∑ j ∈ Finset.univ.erase i, y j * d j| := by
      rw [hterm]
      exact abs_sub _ _
    _ ≤ |∑ j, y j * d j| + ∑ j ∈ Finset.univ.erase i, |d j| * |y j| := by
      apply add_le_add le_rfl
      simpa only [abs_mul, mul_comm] using
        Finset.abs_sum_le_sum_abs (fun j => y j * d j) (Finset.univ.erase i)

theorem finiteWeil_offweight_le_norm {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : ι) (d y : ι → ℝ) :
    (∑ j ∈ Finset.univ.erase i, |d j| * |y j|) ≤
      (∑ j ∈ Finset.univ.erase i, |d j|) * ‖y - Pi.single i (y i)‖ := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  have hz : ((y - Pi.single i (y i)) : ι → ℝ) j = y j := by simp [hji]
  have hy : |y j| ≤ ‖y - Pi.single i (y i)‖ := by
    calc
      |y j| = ‖((y - Pi.single i (y i)) : ι → ℝ) j‖ := by rw [hz, Real.norm_eq_abs]
      _ ≤ ‖y - Pi.single i (y i)‖ := norm_le_pi_norm (y - Pi.single i (y i) : ι → ℝ) j
  exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)

/-- A bounded dual response controls one coordinate modulo all other coordinates. -/
theorem finiteWeil_cost_leakage_of_pairing {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : ι) (d y : ι → ℝ) (E M C : ℝ) (hE : 0 ≤ E) (hdi : |d i| = 1)
    (hoff : (∑ j ∈ Finset.univ.erase i, |d j|) ≤ M)
    (hpair : E * |∑ j, y j * d j| ≤ C) :
    (E * |y i| ≤ C + E * ∑ j ∈ Finset.univ.erase i, |d j| * |y j|) ∧
    (E * |y i| ≤ C + E * M * ‖y - Pi.single i (y i)‖) := by
  have hweighted : E * |y i| ≤ C + E * ∑ j ∈ Finset.univ.erase i, |d j| * |y j| := by
    calc
      _ ≤ E * (|∑ j, y j * d j| + ∑ j ∈ Finset.univ.erase i, |d j| * |y j|) :=
        mul_le_mul_of_nonneg_left (finiteWeil_coordinate_le_pairing_add_off i d y hdi) hE
      _ ≤ _ := by rw [mul_add]; exact add_le_add hpair le_rfl
  refine ⟨hweighted, hweighted.trans ?_⟩
  have hnorm : (∑ j ∈ Finset.univ.erase i, |d j| * |y j|) ≤
      M * ‖y - Pi.single i (y i)‖ :=
    (finiteWeil_offweight_le_norm i d y).trans
      (mul_le_mul_of_nonneg_right hoff (norm_nonneg _))
  simpa only [mul_assoc] using
    add_le_add (le_refl C) (mul_le_mul_of_nonneg_left hnorm hE)

theorem finiteWeil_leakage_half_budget (E B m C δ : ℝ)
    (hE : 0 < E) (hB : 0 < B) (hm : 0 < m)
    (h : E ≤ B * C + E * m * δ) :
    (C ≤ E / (2 * B) → 1 / (2 * m) ≤ δ) ∧
      (δ ≤ 1 / (2 * m) → E / (2 * B) ≤ C) := by
  have h2B : 0 < 2 * B := by positivity
  have h2m : 0 < 2 * m := by positivity
  constructor
  · intro hC
    have hC' := (le_div_iff₀ h2B).mp hC
    have hmul : E * 1 ≤ E * (2 * m * δ) := by nlinarith only [h, hC']
    have hδ := (mul_le_mul_iff_of_pos_left hE).mp hmul
    apply (div_le_iff₀ h2m).mpr
    nlinarith only [hδ]
  · intro hδ
    have hδ' := (le_div_iff₀ h2m).mp hδ
    have hscaled := mul_le_mul_of_nonneg_left hδ' hE.le
    apply (div_le_iff₀ h2B).mpr
    nlinarith only [h, hscaled]

end RHTower
