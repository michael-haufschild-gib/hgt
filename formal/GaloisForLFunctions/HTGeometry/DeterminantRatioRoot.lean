import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Ratio collapse forces geometric-root collapse

The extended Szegő limit theorem is naturally stated for consecutive Toeplitz-determinant ratios,
whereas the cofinal Cholesky geometry uses normalized determinant roots.  This module proves the
entire passage between those two statements.  Thus the literature interface can remain the exact
ratio theorem; normalized Gram collapse is not smuggled into the external input.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Finset
open scoped Topology

/-- A real sequence tending to negative infinity still tends to negative infinity after taking
the sum of its first `n` terms and dividing by `n+1`. -/
theorem cesaro_range_div_succ_atBot {u : ℕ → ℝ} (hu : Tendsto u atTop atBot) :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ range n, u i)
      atTop atBot := by
  rw [tendsto_atTop_atBot]
  intro b
  obtain ⟨N, hN⟩ := (tendsto_atTop_atBot.mp hu) (b - 1)
  let A : ℝ := ∑ i ∈ range N, u i
  let E : ℝ := A - (N : ℝ) * (b - 1)
  let E' : ℝ := E - (b - 1)
  have hE : Tendsto (fun n : ℕ => E' / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat E').comp (tendsto_add_atTop_nat 1)
  have hEle : ∀ᶠ n : ℕ in atTop, E' / ((n + 1 : ℕ) : ℝ) ≤ 1 :=
    ((tendsto_order.1 hE).2 1 zero_lt_one).mono fun _ h => h.le
  have hevent : ∀ᶠ n : ℕ in atTop,
      (((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ range n, u i ≤ b := by
    filter_upwards [hEle, Ici_mem_atTop N] with n hEn hn
    have htail : (∑ i ∈ Ico N n, u i) ≤
        ∑ _i ∈ Ico N n, (b - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hN i (Finset.mem_Ico.mp hi).1
    have hsplit : (∑ i ∈ range n, u i) = A + ∑ i ∈ Ico N n, u i := by
      simpa [A] using (sum_range_add_sum_Ico u hn).symm
    have hcard : ((Ico N n).card : ℝ) = (n : ℝ) - N := by
      rw [Nat.card_Ico, Nat.cast_sub hn]
    have hsum : (∑ i ∈ range n, u i) ≤ (n : ℝ) * (b - 1) + E := by
      rw [hsplit]
      calc
        A + ∑ i ∈ Ico N n, u i ≤ A + ∑ _i ∈ Ico N n, (b - 1) := by linarith
        _ = (n : ℝ) * (b - 1) + E := by
          rw [sum_const, nsmul_eq_mul, hcard]
          dsimp [E]
          ring
    have hnpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    calc
      (((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ range n, u i ≤
          (((n + 1 : ℕ) : ℝ))⁻¹ * ((n : ℝ) * (b - 1) + E) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hnpos.le)
      _ = (b - 1) + E' / ((n + 1 : ℕ) : ℝ) := by
        dsimp [E']
        field_simp
        push_cast
        ring
      _ ≤ b := by linarith
  simpa only [eventually_atTop] using hevent

/-- **Ratio-to-root collapse law.**  For a strictly positive sequence, convergence of consecutive
ratios to zero forces convergence of the `(n+1)`st geometric roots to zero. -/
theorem tendsto_rpow_inv_succ_zero_of_ratio_zero
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hratio : Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 0)) :
    Tendsto (fun n => a n ^ (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
  have hratioPos : ∀ n, 0 < a (n + 1) / a n := fun n => div_pos (ha _) (ha _)
  have hratioGT : Tendsto (fun n => a (n + 1) / a n) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hratio, Filter.Eventually.of_forall hratioPos⟩
  have hlogRatio : Tendsto (fun n => Real.log (a (n + 1) / a n)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hratioGT
  have havg : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹ *
        ∑ i ∈ range n, Real.log (a (i + 1) / a i)) atTop atBot :=
    cesaro_range_div_succ_atBot hlogRatio
  have htel : ∀ n : ℕ,
      ∑ i ∈ range n, Real.log (a (i + 1) / a i) =
        Real.log (a n) - Real.log (a 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [sum_range_succ, ih, Real.log_div (ha (n + 1)).ne' (ha n).ne']
        ring
  have hconst : Tendsto
      (fun n : ℕ => Real.log (a 0) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log (a 0))).comp
        (tendsto_add_atTop_nat 1)
  have hlogRoot : Tendsto
      (fun n : ℕ => Real.log (a n) * (((n + 1 : ℕ) : ℝ))⁻¹) atTop atBot := by
    rw [tendsto_atTop_atBot]
    intro b
    obtain ⟨N, hN⟩ := (tendsto_atTop_atBot.mp havg) (b - 1)
    have hconstLe : ∀ᶠ n : ℕ in atTop,
        Real.log (a 0) / ((n + 1 : ℕ) : ℝ) ≤ 1 :=
      ((tendsto_order.1 hconst).2 1 zero_lt_one).mono fun _ h => h.le
    have hevent : ∀ᶠ n : ℕ in atTop,
        Real.log (a n) * (((n + 1 : ℕ) : ℝ))⁻¹ ≤ b := by
      filter_upwards [hconstLe, Ici_mem_atTop N] with n hcn hn
      have havgN : (((n + 1 : ℕ) : ℝ))⁻¹ *
          ∑ i ∈ range n, Real.log (a (i + 1) / a i) ≤ b - 1 := hN n hn
      rw [htel n] at havgN
      have hnpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      have hid : Real.log (a n) * (((n + 1 : ℕ) : ℝ))⁻¹ =
          (((n + 1 : ℕ) : ℝ))⁻¹ *
              (Real.log (a n) - Real.log (a 0)) +
            Real.log (a 0) / ((n + 1 : ℕ) : ℝ) := by
        field_simp
        ring
      rw [hid]
      linarith
    simpa only [eventually_atTop] using hevent
  apply (Real.tendsto_exp_atBot.comp hlogRoot).congr'
  filter_upwards with n
  simp [Real.rpow_def_of_pos (ha n)]

end GaloisForLFunctions.HTGeometry
