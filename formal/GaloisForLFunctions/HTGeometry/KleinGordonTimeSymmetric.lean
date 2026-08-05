import GaloisForLFunctions.HTGeometry.KleinGordonFloquetExponent

/-!
# A time-symmetric background pairs its multipliers

Statement 363 says that reversing time inverts the Floquet multipliers. When the background is even in
time — `W(−r) = W(r)`, the case of a driving that looks the same run backwards — reversing time changes
nothing, so the spectrum is **invariant under inversion**:

`σ(M) = σ(M)⁻¹`,   equivalently   `k ∈ σ(M) ↔ k⁻¹ ∈ σ(M)`.

The multipliers of such a clock therefore come in reciprocal pairs, and the consequence is sharp: a
multiplier of modulus greater than one is accompanied by one of modulus less than one, so a
time-symmetric clock is stable only if **all** of its multipliers lie on the unit circle. There is no
partial stability for a driving that is symmetric in time.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section TimeSymmetric

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **A time-symmetric background has an inversion-invariant spectrum.** -/
theorem spectrum_kgMonodromy_inv_eq (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hsym : ∀ r : ℝ, W (-r) = W r) :
    (spectrum ℂ (kgMonodromy W b hb0 hWb hWs T))⁻¹
      = spectrum ℂ (kgMonodromy W b hb0 hWb hWs T) := by
  have hfun : (fun r : ℝ => W (-r)) = W := funext hsym
  have hrefl := spectrum_kgMonodromy_reflected hb0 hWb hWs hper
  rw [kgMonodromy_congr hfun hb0 (norm_neg_background_le hWb)
    (continuous_neg_background_apply hWs) hWb hWs T] at hrefl
  exact hrefl.symm

/-- **The multipliers of a time-symmetric clock come in reciprocal pairs.** -/
theorem mem_spectrum_kgMonodromy_inv_iff (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hsym : ∀ r : ℝ, W (-r) = W r) (k : ℂ) :
    k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)
      ↔ k⁻¹ ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T) := by
  constructor
  · intro hk
    rw [← spectrum_kgMonodromy_inv_eq hb0 hWb hWs hper hsym, Set.mem_inv, inv_inv]
    exact hk
  · intro hk
    have h : k⁻¹ ∈ (spectrum ℂ (kgMonodromy W b hb0 hWb hWs T))⁻¹ := by
      rw [spectrum_kgMonodromy_inv_eq hb0 hWb hWs hper hsym]
      exact hk
    rw [Set.mem_inv, inv_inv] at h
    exact h

set_option maxHeartbeats 1000000 in
/-- **A stable time-symmetric clock has all of its multipliers on the unit circle.** There is no
partial stability for a driving that is symmetric in time. -/
theorem norm_eq_one_of_mem_spectrum_of_time_symmetric (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hsym : ∀ r : ℝ, W (-r) = W r) {C : ℝ}
    (hC : ∀ n : ℕ, ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ≤ C) {k : ℂ}
    (hk : k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)) : ‖k‖ = 1 := by
  have hle : ‖k‖ ≤ 1 := norm_le_one_of_mem_spectrum_of_pow_bound hb0 hWb hWs hC hk
  have hinv : k⁻¹ ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T) :=
    (mem_spectrum_kgMonodromy_inv_iff hb0 hWb hWs hper hsym k).mp hk
  have hle' : ‖k⁻¹‖ ≤ 1 := norm_le_one_of_mem_spectrum_of_pow_bound hb0 hWb hWs hC hinv
  have hpos : 0 < ‖k‖ := by
    have hge := exp_neg_le_norm_of_mem_spectrum_kgMonodromy hb0 hWb hWs hper hk
    exact lt_of_lt_of_le (Real.exp_pos _) hge
  rw [norm_inv] at hle'
  have hmul := mul_le_mul_of_nonneg_left hle' hpos.le
  rw [mul_inv_cancel₀ hpos.ne', mul_one] at hmul
  exact le_antisymm hle hmul

end TimeSymmetric

end GaloisForLFunctions.HTGeometry
