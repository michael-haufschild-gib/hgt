import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticAbelEnergy
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# A radial residue cannot exceed logarithmic coefficient energy

Only an Abelian implication is used. In particular, no ordinary or
logarithmic first mean is inferred from a radial pole.
-/

open Complex Filter Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic

private theorem norm_term_real {f : ℕ → ℂ} {s : ℝ} (hs : 1 < s) (n : ℕ) :
    ‖LSeries.term f (s : ℂ) n‖ = ‖f n‖ / (n : ℝ) ^ s := by
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow (by linarith : s ≠ 0)]
  · simp [hn]

/-- Weighted Cauchy--Schwarz on the literal Dirichlet series. -/
theorem norm_LSeries_sq_le_energy {f : ℕ → ℂ} {s : ℝ} (hs : 1 < s)
    (hf : LSeriesSummable f (s : ℂ))
    (he : Summable (fun n : ℕ => ‖f n‖ ^ 2 / (n : ℝ) ^ s)) :
    ‖LSeries f (s : ℂ)‖ ^ 2 ≤
      (∑' n : ℕ, ‖f n‖ ^ 2 / (n : ℝ) ^ s) * ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
  have hz := Real.summable_one_div_nat_rpow.mpr hs
  have hfinite (N : ℕ) :
      ‖∑ n ∈ Finset.range N, LSeries.term f (s : ℂ) n‖ ^ 2 ≤
        (∑ n ∈ Finset.range N, ‖f n‖ ^ 2 / (n : ℝ) ^ s) *
          ∑ n ∈ Finset.range N, 1 / (n : ℝ) ^ s := by
    have hnorm := norm_sum_le (Finset.range N) (fun n => LSeries.term f (s : ℂ) n)
    simp only [norm_term_real hs] at hnorm
    have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range N)
      (r := fun n : ℕ => ‖f n‖ / (n : ℝ) ^ s)
      (f := fun n : ℕ => ‖f n‖ ^ 2 / (n : ℝ) ^ s)
      (g := fun n : ℕ => 1 / (n : ℝ) ^ s)
      (fun n _ => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (fun n _ => div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (fun n _ => by ring_nf; exact le_rfl)
    have hnn : 0 ≤ ∑ n ∈ Finset.range N, ‖f n‖ / (n : ℝ) ^ s :=
      Finset.sum_nonneg fun n _ => div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    nlinarith [norm_nonneg (∑ n ∈ Finset.range N, LSeries.term f (s : ℂ) n)]
  exact le_of_tendsto_of_tendsto ((hf.hasSum.tendsto_sum_nat).norm.pow 2)
    (he.hasSum.tendsto_sum_nat.mul hz.hasSum.tendsto_sum_nat)
    (Filter.Eventually.of_forall hfinite)

private theorem energy_term_damping (f : ℕ → ℂ) {s : ℝ} (hs : 1 < s) (n : ℕ) :
    (‖f n‖ ^ 2 / n) * (n : ℝ) ^ (-(s - 1)) = ‖f n‖ ^ 2 / (n : ℝ) ^ s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by linarith : s ≠ 0)]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show -(s - 1) = 1 - s by ring, Real.rpow_sub hn0, Real.rpow_one]
    field_simp

/-- A radial Dirichlet residue is controlled by the exact logarithmic energy
constant, even when no first-mean Tauberian conclusion is available. -/
theorem norm_residue_sq_le_log_energy {f : ℕ → ℂ} {V : ℝ} (hV0 : 0 ≤ V)
    (hV : Tendsto (fun N : ℕ =>
      weightPartialSum (fun n => ‖f n‖ ^ 2 / n) N / Real.log N) atTop (𝓝 V))
    (hf : ∀ s : ℝ, 1 < s → LSeriesSummable f (s : ℂ)) {R : ℂ}
    (hR : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * LSeries f (s : ℂ))
      (𝓝[>] 1) (𝓝 R)) : ‖R‖ ^ 2 ≤ V := by
  apply le_of_forall_pos_le_add
  intro e he
  obtain ⟨A, _, hA⟩ := exists_abel_energy_majorant (w := fun n => ‖f n‖ ^ 2 / n)
    (by simp) (fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hV0 hV he
  have hbound : ∀ᶠ s : ℝ in 𝓝[>] 1,
      ‖((s : ℂ) - 1) * LSeries f (s : ℂ)‖ ^ 2 ≤
        ((s - 1) * A + (V + e) * s) * ((s - 1) * ∑' n : ℕ, 1 / (n : ℝ) ^ s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 1 < s := hs
    obtain ⟨hes, heb⟩ := hA (s - 1) (by linarith)
    simp only [energy_term_damping f hs'] at hes heb
    have hc := norm_LSeries_sq_le_energy hs' (hf s hs') hes
    have hz0 : 0 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s :=
      tsum_nonneg fun n => div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hn : ‖(s : ℂ) - 1‖ = s - 1 := by
      rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [norm_mul, hn, mul_pow]
    have h1 := mul_le_mul_of_nonneg_left hc (sq_nonneg (s - 1))
    have h2 := mul_le_mul_of_nonneg_right heb (mul_nonneg (by linarith : 0 ≤ s - 1) hz0)
    nlinarith
  have hid : Tendsto (fun s : ℝ => s) (𝓝[>] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hright := (((hid.sub_const 1).mul_const A).add (hid.const_mul (V + e))).mul
    tendsto_sub_mul_tsum_nat_rpow
  simp only [sub_self, zero_mul, mul_one, zero_add] at hright
  exact le_of_tendsto_of_tendsto (hR.norm.pow 2) hright hbound

end RHTower.WeilSingularArithmetic
