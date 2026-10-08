import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticAbelEnergy

/-!
# Coefficient masks retain their own density in the residue bound

Weighted Cauchy--Schwarz uses the square energy of both factors. Passing
to the radial limit retains the mask density instead of replacing it by one.
No first-mean Tauberian implication is used.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem norm_term_mul_real {f g : ℕ → ℂ} {s : ℝ} (hs : 1 < s) (n : ℕ) :
    ‖LSeries.term (fun n => f n * g n) (s : ℂ) n‖ =
      ‖f n‖ * ‖g n‖ / (n : ℝ) ^ s := by
  rw [LSeries.norm_term_eq, norm_mul]
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow (by linarith : s ≠ 0)]
  · simp [hn]

/-- The mask contributes its actual square mass to weighted Cauchy--Schwarz. -/
theorem norm_LSeries_mul_sq_le_energy {f g : ℕ → ℂ} {s : ℝ} (hs : 1 < s)
    (hfg : LSeriesSummable (fun n => f n * g n) (s : ℂ))
    (hf : Summable (fun n : ℕ => ‖f n‖ ^ 2 / (n : ℝ) ^ s))
    (hg : Summable (fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ s)) :
    ‖LSeries (fun n => f n * g n) (s : ℂ)‖ ^ 2 ≤
      (∑' n : ℕ, ‖f n‖ ^ 2 / (n : ℝ) ^ s) *
        ∑' n : ℕ, ‖g n‖ ^ 2 / (n : ℝ) ^ s := by
  have hfinite (N : ℕ) :
      ‖∑ n ∈ Finset.range N, LSeries.term (fun n => f n * g n) (s : ℂ) n‖ ^ 2 ≤
        (∑ n ∈ Finset.range N, ‖f n‖ ^ 2 / (n : ℝ) ^ s) *
          ∑ n ∈ Finset.range N, ‖g n‖ ^ 2 / (n : ℝ) ^ s := by
    have hn := norm_sum_le (Finset.range N)
      (fun n => LSeries.term (fun n => f n * g n) (s : ℂ) n)
    simp only [norm_term_mul_real hs] at hn
    have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range N)
      (r := fun n : ℕ => ‖f n‖ * ‖g n‖ / (n : ℝ) ^ s)
      (f := fun n : ℕ => ‖f n‖ ^ 2 / (n : ℝ) ^ s)
      (g := fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ s)
      (fun n _ => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (fun n _ => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (fun n _ => by ring_nf; exact le_rfl)
    have hnn : 0 ≤ ∑ n ∈ Finset.range N, ‖f n‖ * ‖g n‖ / (n : ℝ) ^ s :=
      Finset.sum_nonneg fun n _ => div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact ((sq_le_sq₀ (norm_nonneg _) hnn).mpr hn).trans hc
  exact le_of_tendsto_of_tendsto ((hfg.hasSum.tendsto_sum_nat).norm.pow 2)
    (hf.hasSum.tendsto_sum_nat.mul hg.hasSum.tendsto_sum_nat)
    (Eventually.of_forall hfinite)

private theorem energy_damping (f : ℕ → ℂ) {s : ℝ} (hs : 1 < s) (n : ℕ) :
    (‖f n‖ ^ 2 / n) * (n : ℝ) ^ (-(s - 1)) = ‖f n‖ ^ 2 / (n : ℝ) ^ s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by linarith : s ≠ 0)]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show -(s - 1) = 1 - s by ring, Real.rpow_sub hn0, Real.rpow_one]
    field_simp

/-- A masked radial residue is at most the source log energy times the
mask's radial square density. -/
theorem norm_masked_residue_sq_le_log_energy {f g : ℕ → ℂ} {V D : ℝ}
    (hV0 : 0 ≤ V)
    (hV : Tendsto (fun N : ℕ =>
      weightPartialSum (fun n => ‖f n‖ ^ 2 / n) N / Real.log N) atTop (𝓝 V))
    (hfg : ∀ s : ℝ, 1 < s → LSeriesSummable (fun n => f n * g n) (s : ℂ))
    (hg : ∀ s : ℝ, 1 < s → Summable (fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ s))
    (hD : Tendsto (fun s : ℝ =>
      (s - 1) * ∑' n : ℕ, ‖g n‖ ^ 2 / (n : ℝ) ^ s) (𝓝[>] 1) (𝓝 D))
    {R : ℂ} (hR : Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      LSeries (fun n => f n * g n) (s : ℂ)) (𝓝[>] 1) (𝓝 R)) :
    ‖R‖ ^ 2 ≤ V * D := by
  have hbound (e : ℝ) (he : 0 < e) : ‖R‖ ^ 2 ≤ (V + e) * D := by
    obtain ⟨A, _, hA⟩ := exists_abel_energy_majorant (w := fun n => ‖f n‖ ^ 2 / n)
      (by simp) (fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hV0 hV he
    have hb : ∀ᶠ s : ℝ in 𝓝[>] 1,
        ‖((s : ℂ) - 1) * LSeries (fun n => f n * g n) (s : ℂ)‖ ^ 2 ≤
          ((s - 1) * A + (V + e) * s) *
            ((s - 1) * ∑' n : ℕ, ‖g n‖ ^ 2 / (n : ℝ) ^ s) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : 1 < s := hs
      obtain ⟨hes, heb⟩ := hA (s - 1) (by linarith)
      simp only [energy_damping f hs'] at hes heb
      rw [show 1 + (s - 1) = s by ring] at heb
      have hc := norm_LSeries_mul_sq_le_energy hs' (hfg s hs') hes (hg s hs')
      have hz0 : 0 ≤ ∑' n : ℕ, ‖g n‖ ^ 2 / (n : ℝ) ^ s :=
        tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have hn : ‖(s : ℂ) - 1‖ = s - 1 := by
        rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      rw [norm_mul, hn, mul_pow]
      calc
        _ ≤ (s - 1) ^ 2 *
            ((∑' n : ℕ, ‖f n‖ ^ 2 / (n : ℝ) ^ s) *
              ∑' n : ℕ, ‖g n‖ ^ 2 / (n : ℝ) ^ s) :=
          mul_le_mul_of_nonneg_left hc (sq_nonneg (s - 1))
        _ = ((s - 1) * ∑' n : ℕ, ‖f n‖ ^ 2 / (n : ℝ) ^ s) *
            ((s - 1) * ∑' n : ℕ, ‖g n‖ ^ 2 / (n : ℝ) ^ s) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right heb
          (mul_nonneg (by linarith : 0 ≤ s - 1) hz0)
    have hid : Tendsto (fun s : ℝ => s) (𝓝[>] 1) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have ht := (((hid.sub_const 1).mul_const A).add (hid.const_mul (V + e))).mul hD
    simp only [sub_self, zero_mul, mul_one, zero_add] at ht
    exact le_of_tendsto_of_tendsto (hR.norm.pow 2) ht hb
  have ht : Tendsto (fun e : ℝ => (V + e) * D) (𝓝[>] 0) (𝓝 (V * D)) := by
    have hi : Tendsto (fun e : ℝ => e) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (hi.const_add V).mul_const D
  exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with e he; exact hbound e he)

end RHTower.WeilSingularArithmetic
