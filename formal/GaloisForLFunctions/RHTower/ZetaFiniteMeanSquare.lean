import GaloisForLFunctions.RHTower.EntireDirichletPolynomial
import GaloisForLFunctions.RHTower.Sieve.DirichletMeanValueSharp
import GaloisForLFunctions.RHTower.Sieve.DirichletMVTNegativeWindow
import GaloisForLFunctions.RHTower.Sieve.SubCriticalPowerSum

/-!
# Sharp finite mean squares for the zeta Dirichlet heads

The error retains the weight `n` on each squared coefficient. Replacing that
weight by the full length loses the estimate needed near the critical line.
-/

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

namespace Sieve

theorem dirichlet_meanValue_sharp_window (N : ℕ) (a : Fin N → ℂ) (T₁ T₂ : ℝ) :
    |(∫ t in T₁..T₂, ‖dirPoly N a t‖ ^ 2) -
        (T₂ - T₁) * ∑ n : Fin N, ‖a n‖ ^ 2| ≤
      208 * ∑ n : Fin N, ((n : ℝ) + 1) * ‖a n‖ ^ 2 := by
  have h₁ := dirichlet_meanValue_sharp N a T₁
  have h₂ := dirichlet_meanValue_sharp N a T₂
  have hsplit : (∫ t in T₁..T₂, ‖dirPoly N a t‖ ^ 2) =
      (∫ t in (0 : ℝ)..T₂, ‖dirPoly N a t‖ ^ 2) -
        (∫ t in (0 : ℝ)..T₁, ‖dirPoly N a t‖ ^ 2) := by
    rw [← intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_normSq_dirPoly N a 0 T₂)
      (intervalIntegrable_normSq_dirPoly N a 0 T₁)]
  rw [hsplit]
  have hid : (∫ t in (0 : ℝ)..T₂, ‖dirPoly N a t‖ ^ 2) -
        (∫ t in (0 : ℝ)..T₁, ‖dirPoly N a t‖ ^ 2) -
        (T₂ - T₁) * ∑ n : Fin N, ‖a n‖ ^ 2 =
      ((∫ t in (0 : ℝ)..T₂, ‖dirPoly N a t‖ ^ 2) - T₂ * ∑ n : Fin N, ‖a n‖ ^ 2) -
        ((∫ t in (0 : ℝ)..T₁, ‖dirPoly N a t‖ ^ 2) - T₁ * ∑ n : Fin N, ‖a n‖ ^ 2) := by ring
  rw [hid]
  exact (abs_sub _ _).trans (by linarith)

theorem dirichlet_meanValue_sharp_window_neg (N : ℕ) (a : Fin N → ℂ) (T₁ T₂ : ℝ) :
    |(∫ t in T₁..T₂, ‖dirPoly N a (-t)‖ ^ 2) -
        (T₂ - T₁) * ∑ n : Fin N, ‖a n‖ ^ 2| ≤
      208 * ∑ n : Fin N, ((n : ℝ) + 1) * ‖a n‖ ^ 2 := by
  have h := dirichlet_meanValue_sharp_window N (fun n => (starRingEnd ℂ) (a n)) T₁ T₂
  simpa only [dirPoly_conj_neg, RCLike.norm_conj] using h

end Sieve

/-- Literal unsmoothed zeta head on a vertical line. -/
def zetaDirichletHead (N : ℕ) (σ t : ℝ) : ℂ :=
  edPoly (fun _ => 1) (Finset.Icc 1 N) ((σ : ℂ) + (t : ℂ) * I)

theorem zetaDirichletHead_eq_dirPoly (N : ℕ) (σ t : ℝ) :
    zetaDirichletHead N σ t =
      Sieve.dirPoly N (fun n => (((n : ℝ) + 1) ^ (-σ) : ℝ)) (-t) := by
  classical
  rw [zetaDirichletHead, edPoly_line _ (fun n hn => (Finset.mem_Icc.mp hn).1)]
  unfold cdpoly cdterm Sieve.dirPoly
  rw [← Sieve.image_succ_univ N, Finset.sum_image (Sieve.succ_injOn N)]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [one_mul, Nat.cast_add, Nat.cast_one]
  congr 2
  push_cast
  ring

private theorem norm_real_rpow_sq (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖((x ^ (-σ) : ℝ) : ℂ)‖ ^ 2 = x ^ (-2 * σ) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    pow_two, ← Real.rpow_add hx]
  congr 1
  ring

/-- Exact diagonal, with the sharp weighted off-diagonal bound, on every window. -/
theorem zetaDirichletHead_meanSquare_error (N : ℕ) (σ T₁ T₂ : ℝ) :
    |(∫ t in T₁..T₂, ‖zetaDirichletHead N σ t‖ ^ 2) -
        (T₂ - T₁) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ)| ≤
      208 * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (1 - 2 * σ) := by
  have h := Sieve.dirichlet_meanValue_sharp_window_neg N
    (fun n => (((n : ℝ) + 1) ^ (-σ) : ℝ)) T₁ T₂
  have hdiag : (∑ n : Fin N, ‖((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ)‖ ^ 2) =
      ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ) := by
    have hterm (n : Fin N) : ‖((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ)‖ ^ 2 =
        ((n : ℝ) + 1) ^ (-2 * σ) := norm_real_rpow_sq σ (by positivity)
    simp_rw [hterm]
    simpa only [Nat.cast_add, Nat.cast_one] using
      Sieve.sum_fin_eq_sum_Icc N (fun n => (n : ℝ) ^ (-2 * σ))
  have hweight :
      (∑ n : Fin N, ((n : ℝ) + 1) * ‖((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ)‖ ^ 2) =
        ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (1 - 2 * σ) := by
    rw [← Sieve.sum_fin_eq_sum_Icc N (fun n => (n : ℝ) ^ (1 - 2 * σ))]
    apply Finset.sum_congr rfl
    intro n hn
    rw [norm_real_rpow_sq σ (by positivity)]
    push_cast
    calc
      ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-2 * σ) =
          ((n : ℝ) + 1) ^ (1 : ℝ) * ((n : ℝ) + 1) ^ (-2 * σ) := by rw [Real.rpow_one]
      _ = ((n : ℝ) + 1) ^ (1 - 2 * σ) := by
        rw [← Real.rpow_add (by positivity)]
        congr 1
        ring
  simp_rw [← zetaDirichletHead_eq_dirPoly] at h
  rwa [hdiag, hweight] at h

theorem zetaDirichletHead_meanSquare_error_subcritical (N : ℕ) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (T₁ T₂ : ℝ) :
    |(∫ t in T₁..T₂, ‖zetaDirichletHead N σ t‖ ^ 2) -
        (T₂ - T₁) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ)| ≤
      208 * ((N : ℝ) ^ (2 - 2 * σ) / (2 - 2 * σ) + 1) := by
  apply (zetaDirichletHead_meanSquare_error N σ T₁ T₂).trans
  have h := Sieve.sum_rpow_neg_subcritical_le (c := 2 * σ - 1) (by linarith) (by linarith) N
  rw [show -(2 * σ - 1) = 1 - 2 * σ by ring,
    show 1 - (2 * σ - 1) = 2 - 2 * σ by ring] at h
  exact mul_le_mul_of_nonneg_left h (by norm_num)

end RHTower
