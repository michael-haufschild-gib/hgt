import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticMeanComparison
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSquareSummability

/-!
# Actual vertical mean square of the literal reciprocal

The source tail estimate compares the actual reciprocal with a polynomial
of length `floor(sqrt(T))`. Its coefficient energy converges, and the sharp
finite mean-value error tends to zero after division by `T`.
This is a fixed-line mean identity; it gives no bound at exceptional heights.
-/

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
open RHTower.Sieve

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem mean_value_negative (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖dirPoly N a (-t)‖ ^ 2) -
      T * ∑ m : Fin N, ‖a m‖ ^ 2| ≤
        104 * ∑ m : Fin N, ((m : ℕ) + 1 : ℝ) * ‖a m‖ ^ 2 := by
  have h := dirichlet_meanValue_sharp N a (-T)
  have hi : (∫ t in (0 : ℝ)..T, ‖dirPoly N a (-t)‖ ^ 2) =
      -(∫ t in (0 : ℝ)..(-T), ‖dirPoly N a t‖ ^ 2) := by
    rw [intervalIntegral.integral_comp_neg (fun t => ‖dirPoly N a t‖ ^ 2),
      neg_zero, intervalIntegral.integral_symm]
  rw [hi]
  have heq : -(∫ t in (0 : ℝ)..(-T), ‖dirPoly N a t‖ ^ 2) -
      T * ∑ m : Fin N, ‖a m‖ ^ 2 =
      -((∫ t in (0 : ℝ)..(-T), ‖dirPoly N a t‖ ^ 2) -
        (-T) * ∑ m : Fin N, ‖a m‖ ^ 2) := by ring
  rw [heq, abs_neg]
  exact h

private theorem tendsto_growing_polynomial_mean (b : ℕ → ℂ)
    (hb : Summable (fun n => ‖b n‖ ^ 2)) :
    Tendsto (fun T : ℝ =>
      (∫ t in (0 : ℝ)..T,
        ‖dirPoly ⌊T ^ (1 / 2 : ℝ)⌋₊ (fun m => b m) (-t)‖ ^ 2) / T)
      atTop (𝓝 (∑' n : ℕ, ‖b n‖ ^ 2)) := by
  let S : ℝ := ∑' n : ℕ, ‖b n‖ ^ 2
  let A : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, ‖b n‖ ^ 2
  let N : ℝ → ℕ := fun T => ⌊T ^ (1 / 2 : ℝ)⌋₊
  let M : ℝ → ℝ := fun T =>
    (∫ t in (0 : ℝ)..T, ‖dirPoly (N T) (fun m => b m) (-t)‖ ^ 2) / T
  have hS : 0 ≤ S := tsum_nonneg fun _ => sq_nonneg _
  have hfinite : ∀ (L : ℕ) (T : ℝ), 0 < T →
      |(∫ t in (0 : ℝ)..T, ‖dirPoly L (fun m => b m) (-t)‖ ^ 2) / T - A L| ≤
        104 * ((L : ℝ) / T) * S := by
    intro L T hT
    have hsum : (∑ m : Fin L, ‖b (m : ℕ)‖ ^ 2) = A L :=
      Fin.sum_univ_eq_sum_range (fun n => ‖b n‖ ^ 2) L
    have hAle : A L ≤ S := hb.sum_le_tsum _ fun _ _ => sq_nonneg _
    have hweight : ∑ m : Fin L, ((m : ℕ) + 1 : ℝ) * ‖b (m : ℕ)‖ ^ 2 ≤ (L : ℝ) * S := by
      calc
        _ ≤ (L : ℝ) * ∑ m : Fin L, ‖b (m : ℕ)‖ ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro m _
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact_mod_cast m.isLt
        _ ≤ _ := by rw [hsum]; exact mul_le_mul_of_nonneg_left hAle (Nat.cast_nonneg L)
    have hmv := mean_value_negative L (fun m => b m) T
    rw [hsum] at hmv
    have heq : (∫ t in (0 : ℝ)..T, ‖dirPoly L (fun m => b m) (-t)‖ ^ 2) / T - A L =
        ((∫ t in (0 : ℝ)..T, ‖dirPoly L (fun m => b m) (-t)‖ ^ 2) - T * A L) / T := by
      field_simp
    rw [heq, abs_div, abs_of_pos hT]
    calc
      _ ≤ (104 * ∑ m : Fin L, ((m : ℕ) + 1 : ℝ) * ‖b (m : ℕ)‖ ^ 2) / T :=
        div_le_div_of_nonneg_right hmv hT.le
      _ ≤ (104 * ((L : ℝ) * S)) / T :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hweight (by norm_num)) hT.le
      _ = _ := by ring
  have hdec : Tendsto (fun T : ℝ => 104 * S * T ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : ℝ))).const_mul
      (104 * S)
  have hdiff : Tendsto (fun T => M T - A (N T)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hdec
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hT0 : 0 < T := by linarith
    have hN : (N T : ℝ) ≤ T ^ (1 / 2 : ℝ) := Nat.floor_le (by positivity)
    have hratio : (N T : ℝ) / T ≤ T ^ (-(1 / 2 : ℝ)) := by
      calc
        _ ≤ T ^ (1 / 2 : ℝ) / T := div_le_div_of_nonneg_right hN hT0.le
        _ = _ := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hT0]
          congr 1
          norm_num
    rw [Real.norm_eq_abs]
    exact (hfinite (N T) T hT0).trans (by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 104)) hS
      simpa only [mul_right_comm] using h)
  have hNtop : Tendsto N atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ)))
  have henergy : Tendsto (fun T => A (N T)) atTop (𝓝 S) :=
    hb.hasSum.tendsto_sum_nat.comp hNtop
  have h := hdiff.add henergy
  simpa only [sub_add_cancel, zero_add] using h

private theorem partial_series_eq_polynomial (b : ℕ → ℂ) (σ t : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, LSeries.term b ((σ : ℂ) + t * I) n) =
      dirPoly N (fun m => LSeries.term b (σ : ℂ) ((m : ℕ) + 1)) (-t) := by
  rw [← dirichletPartialSum_eq_sum_term, dirichletPartialSum, dirPoly,
    Fin.sum_univ_eq_sum_range
      (fun n => LSeries.term b (σ : ℂ) (n + 1) *
        cexp (((-t * Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * I)) N]
  apply Finset.sum_congr rfl
  intro n _
  rw [term_succ_eq, mul_assoc]
  congr 1
  have hn : ((((n : ℝ) + 1 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  rw [Complex.cpow_def_of_ne_zero hn, Complex.cpow_def_of_ne_zero hn, ← Complex.exp_add,
    ← Complex.ofReal_log (by positivity)]
  congr 1
  push_cast
  ring

/-- For every fixed line right of one half, the actual literal reciprocal
has mean square equal to its finite coefficient energy. Full positivity is
the only arithmetic assumption. -/
theorem exists_reciprocal_mean_square {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        G s = cexp (-LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s)) ∧
      ∀ σ : ℝ, 1 / 2 < σ →
        Summable (fun n : ℕ =>
          ‖LSeries.term (producerMobius (fun n => if 2 ≤ n then lam n else 0))
            (σ : ℂ) (n + 1)‖ ^ 2) ∧
        Tendsto (fun T : ℝ =>
          (∫ t in (0 : ℝ)..T, ‖G ((σ : ℂ) + t * I)‖ ^ 2) / T) atTop
          (𝓝 (∑' n : ℕ,
            ‖LSeries.term (producerMobius (fun n => if 2 ≤ n then lam n else 0))
              (σ : ℂ) (n + 1)‖ ^ 2)) := by
  obtain ⟨G, hGd, hGL, happrox⟩ := exists_reciprocal_mean_approximation hW
  refine ⟨G, hGd, hGL, fun σ hσ => ?_⟩
  let b : ℕ → ℂ := producerMobius (fun n => if 2 ≤ n then lam n else 0)
  let c : ℕ → ℂ := fun n => LSeries.term b (σ : ℂ) (n + 1)
  have hc : Summable (fun n => ‖c n‖ ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr (summable_reciprocal_square_weight hW hσ)
    refine h.congr fun n => ?_
    have hpow : (((n : ℝ) + 1) ^ (-σ)) ^ (2 : ℕ) =
        ((n : ℝ) + 1) ^ (-2 * σ) := by
      rw [← Real.rpow_two (((n : ℝ) + 1) ^ (-σ)), ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    dsimp [c]
    rw [term_succ_eq, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
      Complex.neg_re, Complex.ofReal_re, mul_pow, hpow]
    push_cast
    rfl
  refine ⟨hc, ?_⟩
  have hp := tendsto_growing_polynomial_mean c hc
  have hid : ∀ T : ℝ,
      (∫ t in (0 : ℝ)..T, ‖∑ n ∈ Finset.Icc 1 ⌊T ^ (1 / 2 : ℝ)⌋₊,
        LSeries.term b ((σ : ℂ) + t * I) n‖ ^ 2) / T =
      (∫ t in (0 : ℝ)..T,
        ‖dirPoly ⌊T ^ (1 / 2 : ℝ)⌋₊ (fun m => c m) (-t)‖ ^ 2) / T := by
    intro T
    simp only [partial_series_eq_polynomial, c]
  have hp' := hp.congr fun T => (hid T).symm
  have h := (happrox σ hσ).add hp'
  simpa only [b, c, sub_add_cancel, zero_add] using h

end RHTower.WeilSingularArithmetic
