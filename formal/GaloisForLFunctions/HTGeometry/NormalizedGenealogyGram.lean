import GaloisForLFunctions.HTGeometry.FiniteGenealogyGramMatrix
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.LiminfLimsup

/-! # The exact energy threshold for normalized genealogy Gram determinants

Removing the coefficient-free factor `2^N` leaves a monotone positive sequence.
Its finite partial sums have two-sided energy bounds; boundedness, finite positive
convergence and square-summability of the coefficients are equivalent.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology

def normalizedGenealogyGram (w : ℕ → ℂ) (N : ℕ) : ℝ :=
  finiteGenealogyGramValue w N / 2 ^ N

@[simp] theorem normalizedGenealogyGram_zero (w : ℕ → ℂ) :
    normalizedGenealogyGram w 0 = 1 := by simp [normalizedGenealogyGram]

@[simp] theorem normalizedGenealogyGram_one (w : ℕ → ℂ) :
    normalizedGenealogyGram w 1 = 1 := by norm_num [normalizedGenealogyGram]

theorem one_le_normalizedGenealogyGram (w : ℕ → ℂ) (N : ℕ) :
    1 ≤ normalizedGenealogyGram w N := by
  rw [normalizedGenealogyGram, le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ N), one_mul]
  exact two_pow_le_finiteGenealogyGramValue w N

theorem normalizedGenealogyGram_monotone (w : ℕ → ℂ) : Monotone (normalizedGenealogyGram w) := by
  apply monotone_nat_of_le_succ
  intro N
  calc
    normalizedGenealogyGram w N = (2 * finiteGenealogyGramValue w N) / 2 ^ (N + 1) := by
      simp only [normalizedGenealogyGram, pow_succ]
      field_simp
    _ ≤ normalizedGenealogyGram w (N + 1) :=
      div_le_div_of_nonneg_right (finiteGenealogyGramValue_two_mul_le_succ w N) (by positivity)

theorem normalizedGenealogyGram_recurrence (w : ℕ → ℂ) (N : ℕ) :
    normalizedGenealogyGram w (N + 2) = normalizedGenealogyGram w (N + 1) +
      ‖w N‖ ^ 2 / 2 * (normalizedGenealogyGram w (N + 1) - normalizedGenealogyGram w N / 2) := by
  simp only [normalizedGenealogyGram, finiteGenealogyGramValue_succ_succ, pow_succ]
  field_simp

theorem normalizedGenealogyGram_increment_lower (w : ℕ → ℂ) (N : ℕ) :
    ‖w N‖ ^ 2 / 4 ≤ normalizedGenealogyGram w (N + 2) - normalizedGenealogyGram w (N + 1) := by
  have hm := normalizedGenealogyGram_monotone w (Nat.le_succ N)
  have h1 := one_le_normalizedGenealogyGram w (N + 1)
  have hp := mul_nonneg (sq_nonneg ‖w N‖)
    (show 0 ≤ normalizedGenealogyGram w (N + 1) - normalizedGenealogyGram w N / 2 - 1 / 2 by
      linarith)
  rw [normalizedGenealogyGram_recurrence]
  nlinarith

theorem normalizedGenealogyGram_increment_upper (w : ℕ → ℂ) (N : ℕ) :
    normalizedGenealogyGram w (N + 2) ≤
      (1 + ‖w N‖ ^ 2 / 2) * normalizedGenealogyGram w (N + 1) := by
  have h0 : 0 ≤ normalizedGenealogyGram w N := le_trans zero_le_one (one_le_normalizedGenealogyGram w N)
  have hp := mul_nonneg (sq_nonneg ‖w N‖) h0
  rw [normalizedGenealogyGram_recurrence]
  nlinarith

theorem normalizedGenealogyGram_energy_lower (w : ℕ → ℂ) (N : ℕ) :
    1 + (∑ n ∈ Finset.range N, ‖w n‖ ^ 2) / 4 ≤ normalizedGenealogyGram w (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hs := normalizedGenealogyGram_increment_lower w N
      rw [Finset.sum_range_succ]
      linarith

theorem normalizedGenealogyGram_energy_upper (w : ℕ → ℂ) (N : ℕ) :
    normalizedGenealogyGram w (N + 1) ≤ Real.exp ((∑ n ∈ Finset.range N, ‖w n‖ ^ 2) / 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        normalizedGenealogyGram w (N + 1 + 1) ≤
            (1 + ‖w N‖ ^ 2 / 2) * normalizedGenealogyGram w (N + 1) :=
          normalizedGenealogyGram_increment_upper w N
        _ ≤ Real.exp (‖w N‖ ^ 2 / 2) * Real.exp ((∑ n ∈ Finset.range N, ‖w n‖ ^ 2) / 2) :=
          mul_le_mul (by linarith [Real.add_one_le_exp (‖w N‖ ^ 2 / 2)]) ih
            (le_trans zero_le_one (one_le_normalizedGenealogyGram w (N + 1))) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add, Finset.sum_range_succ]; congr 1; ring

theorem normalizedGenealogyGram_bddAbove_iff (w : ℕ → ℂ) :
    BddAbove (Set.range (normalizedGenealogyGram w)) ↔ Summable (fun n => ‖w n‖ ^ 2) := by
  constructor
  · rintro ⟨B, hB⟩
    apply summable_of_sum_range_le (c := 4 * (B - 1)) (fun n => sq_nonneg ‖w n‖)
    intro N
    have hl := normalizedGenealogyGram_energy_lower w N
    have hu := hB (Set.mem_range_self (N + 1))
    linarith
  · intro hs
    refine ⟨Real.exp ((∑' n, ‖w n‖ ^ 2) / 2), ?_⟩
    rintro _ ⟨N, rfl⟩
    cases N with
    | zero =>
        rw [normalizedGenealogyGram_zero]
        exact Real.one_le_exp (by positivity)
    | succ N =>
        apply (normalizedGenealogyGram_energy_upper w N).trans
        apply Real.exp_le_exp.mpr
        exact div_le_div_of_nonneg_right
          (hs.sum_le_tsum (Finset.range N) (fun n _ => sq_nonneg ‖w n‖)) (by norm_num)

theorem normalizedGenealogyGram_finite_limit_iff (w : ℕ → ℂ) :
    (∃ L : ℝ, 1 ≤ L ∧ Tendsto (normalizedGenealogyGram w) atTop (𝓝 L)) ↔
      Summable (fun n => ‖w n‖ ^ 2) := by
  constructor
  · rintro ⟨L, _, hL⟩
    exact (normalizedGenealogyGram_bddAbove_iff w).mp hL.bddAbove_range
  · intro hs
    have hb := (normalizedGenealogyGram_bddAbove_iff w).mpr hs
    refine ⟨⨆ N, normalizedGenealogyGram w N, ?_,
      tendsto_atTop_ciSup (normalizedGenealogyGram_monotone w) hb⟩
    simpa only [normalizedGenealogyGram_zero] using le_ciSup hb 0

theorem normalizedGenealogyGram_tendsto_atTop_iff (w : ℕ → ℂ) :
    Tendsto (normalizedGenealogyGram w) atTop atTop ↔ ¬ Summable (fun n => ‖w n‖ ^ 2) := by
  constructor
  · intro hi hs
    obtain ⟨L, _, hL⟩ := (normalizedGenealogyGram_finite_limit_iff w).mpr hs
    exact not_tendsto_nhds_of_tendsto_atTop hi L hL
  · intro hs
    apply tendsto_atTop_atTop_of_monotone' (normalizedGenealogyGram_monotone w)
    exact fun hb => hs ((normalizedGenealogyGram_bddAbove_iff w).mp hb)

end
end GaloisForLFunctions.HTGeometry
