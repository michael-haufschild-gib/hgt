import GaloisForLFunctions.RHTower.SoninEssentialNormExtensions

/-!
# The dilation sum is injective on a Fourier annulus

A vector killed by the two-sided dilation sum is an eigenvector of the square dilation with
eigenvalue `-1`.  Conjugating the Fourier cutoff through that dilation shrinks the band by a fixed
factor at every step, so such a vector is band-limited at arbitrarily small apertures.  A vector
annihilated by the Fourier cutoff at a fixed positive aperture then has to vanish.

The dilation sum is consequently injective on every Fourier annulus with positive inner radius.
-/

noncomputable section


namespace RHTower

open ContinuousLinearMap

/-- A vector killed by the dilation sum is a `(-1)`-eigenvector of the inverse square dilation. -/
theorem evenDilationCLM_inv_sq_apply_eq_neg_of_evenDilationSum_apply_eq_zero
    {r : ℝ} (hr : 1 < r) (hs : 0 < (r ^ (2 : ℕ))⁻¹) {v : evenSubspace}
    (hD : evenDilationSum r hr v = 0) :
    evenDilationCLM ((r ^ (2 : ℕ))⁻¹) hs v = -v := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hrinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
  have hsum :
      evenDilationCLM r hr0 v + evenDilationCLM r⁻¹ hrinv v = 0 := by
    rw [evenDilationSum_eq] at hD
    simpa using hD
  have happ := congrArg (fun w : evenSubspace => evenDilationCLM r⁻¹ hrinv w) hsum
  simp only [map_add, map_zero] at happ
  have hpow : r⁻¹ * r⁻¹ = (r ^ (2 : ℕ))⁻¹ := by rw [← mul_inv, ← sq]
  have h1 : evenDilationCLM r⁻¹ hrinv (evenDilationCLM r hr0 v) = v := by
    have h := DFunLike.congr_fun (evenDilationCLM_mul r⁻¹ r hrinv hr0) v
    rw [mul_apply_eq_comp] at h
    rw [h, DFunLike.congr_fun (evenDilationCLM_congr (mul_pos hrinv hr0)
      (inv_mul_cancel₀ hr0.ne')) v]
    have hone : evenDilationCLM (1 : ℝ) (inv_mul_cancel₀ hr0.ne' ▸ mul_pos hrinv hr0) =
        (1 : evenSubspace →L[ℂ] evenSubspace) := evenDilationCLM_one
    rw [hone]
    rfl
  have h2 : evenDilationCLM r⁻¹ hrinv (evenDilationCLM r⁻¹ hrinv v) =
      evenDilationCLM ((r ^ (2 : ℕ))⁻¹) hs v := by
    have h := DFunLike.congr_fun (evenDilationCLM_mul r⁻¹ r⁻¹ hrinv hrinv) v
    rw [mul_apply_eq_comp] at h
    rw [h]
    exact DFunLike.congr_fun (evenDilationCLM_congr (mul_pos hrinv hrinv) hpow) v
  rw [h1, h2] at happ
  linear_combination (norm := module) happ

/-- **Injectivity of the dilation sum on a Fourier annulus.**  A vector band-limited at `c`, killed
by the Fourier cutoff at a positive aperture `b`, and killed by the dilation sum, is zero. -/
theorem eq_zero_of_evenDilationSum_apply_eq_zero_of_fourierAnnulus
    {b c r : ℝ} (hb : 0 < b) (hr : 1 < r) {v : evenSubspace}
    (hD : evenDilationSum r hr v = 0)
    (hcv : evenFourierCutoff c v = v)
    (hbv : evenFourierCutoff b v = 0) :
    v = 0 := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hr2 : (1 : ℝ) < r ^ (2 : ℕ) := one_lt_pow₀ hr two_ne_zero
  have hspos : (0 : ℝ) < (r ^ (2 : ℕ))⁻¹ := inv_pos.mpr (by positivity)
  set s : ℝ := (r ^ (2 : ℕ))⁻¹ with hsdef
  have hs0 : 0 < s := hspos
  have hs1 : s < 1 := by
    rw [hsdef]
    exact inv_lt_one_of_one_lt₀ hr2
  have hUs : evenDilationCLM s hs0 v = -v :=
    evenDilationCLM_inv_sq_apply_eq_neg_of_evenDilationSum_apply_eq_zero hr hspos hD
  have hiter : ∀ n : ℕ, evenFourierCutoff (s ^ n * c) v = v := by
    intro n
    induction n with
    | zero => simpa using hcv
    | succ n ih =>
      have hcov := evenFourierCutoff_mul_evenDilationCLM (s * (s ^ n * c)) s hs0
      rw [show s⁻¹ * (s * (s ^ n * c)) = s ^ n * c from
        inv_mul_cancel_left₀ hs0.ne' _] at hcov
      have happ := DFunLike.congr_fun hcov v
      rw [mul_apply_eq_comp, mul_apply_eq_comp, ih, hUs, map_neg] at happ
      rw [show s ^ (n + 1) * c = s * (s ^ n * c) by ring]
      exact neg_injective happ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, s ^ n * c ≤ b := by
    rcases le_or_gt c 0 with hc | hc
    · exact ⟨0, by simpa using hc.trans hb.le⟩
    · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hb hc) hs1
      exact ⟨n, ((lt_div_iff₀ hc).mp hn).le⟩
  have hnest := DFunLike.congr_fun (evenFourierCutoff_mul_of_le_rev (s ^ n * c) b hn) v
  rw [mul_apply_eq_comp, hiter n, hbv] at hnest
  exact hnest.symm

end RHTower
