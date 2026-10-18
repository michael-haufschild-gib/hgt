import GaloisForLFunctions.RHTower.ZetaFiniteMeanSquare
import Mathlib.Analysis.PSeries

/-!
# Sharp mean squares after removing a fixed Dirichlet head

All coefficient cutoffs are literal finite sums. The diagonal is the square
coefficient mass of the retained band.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

def zetaDirichletBand (M N : ℕ) (σ t : ℝ) : ℂ :=
  edPoly (fun n => if n ≤ M then 0 else 1) (Finset.Icc 1 N)
    ((σ : ℂ) + (t : ℂ) * I)

def zetaBandDiagonal (M N : ℕ) (σ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, if n ≤ M then 0 else (n : ℝ) ^ (-2 * σ)

def zetaCoefficientTailMass (M : ℕ) (σ : ℝ) : ℝ :=
  ∑' n : ℕ, if n ≤ M then 0 else (n : ℝ) ^ (-2 * σ)

private theorem edPoly_Icc_vertical_eq_dirPoly (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ) :
    edPoly a (Finset.Icc 1 N) ((σ : ℂ) + (t : ℂ) * I) =
      Sieve.dirPoly N (fun n => a (n + 1) * ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ)) (-t) := by
  classical
  rw [edPoly_line _ (fun n hn => (Finset.mem_Icc.mp hn).1)]
  unfold cdpoly cdterm Sieve.dirPoly
  rw [← Sieve.image_succ_univ N, Finset.sum_image (Sieve.succ_injOn N)]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Nat.cast_add, Nat.cast_one]
  congr 2
  push_cast
  ring

theorem zetaDirichletBand_eq_dirPoly (M N : ℕ) (σ t : ℝ) :
    zetaDirichletBand M N σ t = Sieve.dirPoly N
      (fun n => if (n : ℕ) + 1 ≤ M then 0 else ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ)) (-t) := by
  rw [zetaDirichletBand, edPoly_Icc_vertical_eq_dirPoly]
  congr 1
  funext n
  split_ifs <;> simp

theorem zetaDirichletBand_eq_sub {M N : ℕ} (hMN : M ≤ N) (σ t : ℝ) :
    zetaDirichletBand M N σ t = zetaDirichletHead N σ t - zetaDirichletHead M σ t := by
  classical
  let f : ℕ → ℂ := fun n => ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))
  have hsub : Finset.Icc 1 M ⊆ Finset.Icc 1 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hMN⟩
  have hlow : (∑ n ∈ Finset.Icc 1 N, if n ≤ M then f n else 0) =
      ∑ n ∈ Finset.Icc 1 M, f n := by
    symm
    calc
      (∑ n ∈ Finset.Icc 1 M, f n) = ∑ n ∈ Finset.Icc 1 M, if n ≤ M then f n else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [(Finset.mem_Icc.mp hn).2]
      _ = _ := Finset.sum_subset hsub (by
        intro n hn hnm
        have h : ¬n ≤ M := fun h => hnm (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, h⟩)
        simp [h])
  change (∑ n ∈ Finset.Icc 1 N, (if n ≤ M then (0 : ℂ) else 1) * f n) =
    (∑ n ∈ Finset.Icc 1 N, 1 * f n) - ∑ n ∈ Finset.Icc 1 M, 1 * f n
  simp only [one_mul]
  rw [← hlow, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp

theorem continuous_zetaDirichletHead (N : ℕ) (σ : ℝ) : Continuous (zetaDirichletHead N σ) :=
  (differentiable_edPoly (fun _ => 1) (fun _n hn => (Finset.mem_Icc.mp hn).1)).continuous.comp
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))

theorem continuous_zetaDirichletBand (M N : ℕ) (σ : ℝ) : Continuous (zetaDirichletBand M N σ) :=
  (differentiable_edPoly (fun n => if n ≤ M then 0 else 1)
    (fun _n hn => (Finset.mem_Icc.mp hn).1)).continuous.comp
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))

private theorem norm_bandCoeff_sq (M : ℕ) (σ : ℝ) (n : ℕ) :
    ‖(if n + 1 ≤ M then (0 : ℂ) else ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ))‖ ^ 2 =
      if n + 1 ≤ M then 0 else ((n : ℝ) + 1) ^ (-2 * σ) := by
  split_ifs
  · simp
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      pow_two, ← Real.rpow_add (by positivity)]
    congr 1
    ring

theorem zetaDirichletBand_meanSquare_error (M N : ℕ) (σ T₁ T₂ : ℝ) :
    |(∫ t in T₁..T₂, ‖zetaDirichletBand M N σ t‖ ^ 2) -
        (T₂ - T₁) * zetaBandDiagonal M N σ| ≤
      208 * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (1 - 2 * σ) := by
  have h := Sieve.dirichlet_meanValue_sharp_window_neg N
    (fun n => if (n : ℕ) + 1 ≤ M then 0 else ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ)) T₁ T₂
  have hdiag : (∑ n : Fin N,
      ‖(if (n : ℕ) + 1 ≤ M then (0 : ℂ) else ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ))‖ ^ 2) =
      zetaBandDiagonal M N σ := by
    simp_rw [norm_bandCoeff_sq]
    simpa only [zetaBandDiagonal, Nat.cast_add, Nat.cast_one] using
      Sieve.sum_fin_eq_sum_Icc N (fun n => if n ≤ M then 0 else (n : ℝ) ^ (-2 * σ))
  have hw : (∑ n : Fin N, ((n : ℝ) + 1) *
      ‖(if (n : ℕ) + 1 ≤ M then (0 : ℂ) else ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ))‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (1 - 2 * σ) := by
    rw [← Sieve.sum_fin_eq_sum_Icc N (fun n => (n : ℝ) ^ (1 - 2 * σ))]
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_bandCoeff_sq]
    by_cases hnM : (n : ℕ) + 1 ≤ M
    · simp only [hnM, if_true, mul_zero]
      positivity
    · simp only [hnM, if_false, Nat.cast_add, Nat.cast_one]
      apply le_of_eq
      calc
        ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-2 * σ) =
            ((n : ℝ) + 1) ^ (1 : ℝ) * ((n : ℝ) + 1) ^ (-2 * σ) := by rw [Real.rpow_one]
        _ = ((n : ℝ) + 1) ^ (1 - 2 * σ) := by
          rw [← Real.rpow_add (by positivity)]
          congr 1
          ring
  simp_rw [← zetaDirichletBand_eq_dirPoly] at h
  rw [hdiag] at h
  exact h.trans (mul_le_mul_of_nonneg_left hw (by norm_num))

theorem zetaDirichletBand_meanSquare_error_subcritical (M N : ℕ) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (T₁ T₂ : ℝ) :
    |(∫ t in T₁..T₂, ‖zetaDirichletBand M N σ t‖ ^ 2) -
        (T₂ - T₁) * zetaBandDiagonal M N σ| ≤
      208 * ((N : ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ) + 1) := by
  apply (zetaDirichletBand_meanSquare_error M N σ T₁ T₂).trans
  have h := Sieve.sum_rpow_neg_subcritical_le (c := 2 * σ - 1) (by linarith) (by linarith) N
  rw [show -(2 * σ - 1) = 1 - 2 * σ by ring,
    show 1 - (2 * σ - 1) = 2 - 2 * σ by ring] at h
  exact mul_le_mul_of_nonneg_left h (by norm_num)

theorem summable_zetaCoefficientTail (M : ℕ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun n : ℕ => if n ≤ M then (0 : ℝ) else (n : ℝ) ^ (-2 * σ)) := by
  apply Summable.of_norm_bounded (Real.summable_nat_rpow.mpr (by linarith : -2 * σ < -1))
  intro n
  split_ifs
  · simp only [norm_zero]
    positivity
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem tendsto_zetaBandDiagonal (M : ℕ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (fun N => zetaBandDiagonal M N σ) atTop (𝓝 (zetaCoefficientTailMass M σ)) := by
  have h := (summable_zetaCoefficientTail M hσ).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  apply h.congr
  intro N
  have hset : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  simp only [Function.comp_apply, zetaBandDiagonal, hset,
    Finset.sum_Ico_eq_sub _ (show 1 ≤ N + 1 by omega), Finset.sum_range_one,
    Nat.zero_le, if_true, sub_zero]

end RHTower
