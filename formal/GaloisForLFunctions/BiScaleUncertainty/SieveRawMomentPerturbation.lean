import GaloisForLFunctions.BiScaleUncertainty.SieveMomentSpectralEquivalence

/-! Raw lag errors control normalized resonant products without factorial loss. -/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open AffineSieve
set_option autoImplicit false

private theorem momentDFT_error {P m : ℕ} [NeZero P]
    (T U : (Fin m → ZMod P) → ℂ) (ε : ℝ)
    (h : ∀ v, ‖T v - U v‖ ≤ ε) (r : Fin m → ZMod P) :
    ‖momentDFT T r - momentDFT U r‖ ≤ (P : ℝ)^m * ε := by
  classical
  unfold momentDFT
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ v : Fin m → ZMod P,
        ‖(∏ i, ZMod.stdAddChar (-(v i * r i))) * (T v - U v)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin m → ZMod P, ε := by
      apply Finset.sum_le_sum
      intro v _
      simpa [norm_mul, norm_prod, ZMod.stdAddChar_apply, Circle.norm_coe] using h v
    _ = _ := by simp [ZMod.card]

local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Fourier averaging has norm one after the exact factorial normalization. -/
theorem resonant_product_error (N : ℕ) (c e : ℕ → ℝ) (m : ℕ) (ε : ℝ)
    (h : ∀ v : Fin m → ℕ, |translatedMoment N c v - translatedMoment N e v| ≤ ε)
    (r : Fin m → ZMod N.factorial) (hz : (∑ i, r i) = 0) :
    |(∏ i, selbergMultiplesCoord N c (addOrderOf (r i))) -
      (∏ i, selbergMultiplesCoord N e (addOrderOf (r i)))| ≤ ε := by
  have hb := momentDFT_error
    (fun v : Fin m → ZMod N.factorial => (translatedMoment N c (fun i => (v i).val) : ℂ))
    (fun v : Fin m → ZMod N.factorial => (translatedMoment N e (fun i => (v i).val) : ℂ))
    ε (by
      intro v
      simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        using h (fun i => (v i).val)) r
  simp only [translatedMoment_complex_eq, ZMod.natCast_zmod_val] at hb
  change ‖momentDFT (translationMoment (residueSignal N (fun d => (c d : ℂ)))) r -
    momentDFT (translationMoment (residueSignal N (fun d => (e d : ℂ)))) r‖ ≤
      (N.factorial : ℝ)^m * ε at hb
  simp only [momentDFT_sieve, hz, if_true, coordinate_ofReal] at hb
  rw [← mul_sub] at hb
  simp only [← Complex.ofReal_prod, ← Complex.ofReal_sub, norm_mul, norm_pow,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs] at hb
  have hp : 0 < (N.factorial : ℝ)^m :=
    pow_pos (by exact_mod_cast Nat.factorial_pos N) m
  nlinarith only [hb, hp]

/-- A repeated opposite-frequency pair isolates the sixth power of every admitted mode. -/
theorem coordinate_sixth_error (N : ℕ) (c e : ℕ → ℝ) (ε : ℝ)
    (h : ∀ v : Fin 6 → ℕ, |translatedMoment N c v - translatedMoment N e v| ≤ ε)
    (q : ℕ) (hq : q ∈ Finset.Icc 1 N) :
    |selbergMultiplesCoord N c q ^ 6 - selbergMultiplesCoord N e q ^ 6| ≤ ε := by
  let r : ZMod N.factorial := (N.factorial / q : ℕ)
  have hr : addOrderOf r = q := frequency_order hq
  have hh := resonant_product_error N c e 6 ε h ![r,-r,r,-r,r,-r]
    (by simp [Fin.sum_univ_succ])
  simpa [Fin.prod_univ_succ, addOrderOf_neg, hr, pow_succ, mul_assoc] using hh

private theorem nonneg_sixth_root_error (x y δ : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hδ : 0 ≤ δ) (h : |x^6-y^6| ≤ δ^6) : |x-y| ≤ δ := by
  have step (u v : ℝ) (hv : 0 ≤ v) (hvu : v ≤ u)
      (hpow : u^6-v^6 ≤ δ^6) : u-v ≤ δ := by
    have hs := pow_add_pow_le (sub_nonneg.mpr hvu) hv (by omega : 6 ≠ 0)
    rw [sub_add_cancel] at hs
    have hb : (u-v)^6 ≤ δ^6 := by linarith
    exact (pow_le_pow_iff_left₀ (sub_nonneg.mpr hvu) hδ (by omega : 6 ≠ 0)).mp hb
  rcases le_total y x with hyx | hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact step x y hy hyx ((le_abs_self _).trans h)
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
    exact step y x hx hxy (by have := (neg_le_abs (x^6-y^6)).trans h; linarith)

/-- Sixth-array noise controls magnitudes uniformly, including zero coordinates. -/
theorem coordinate_magnitude_error (N : ℕ) (c e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ v : Fin 6 → ℕ,
      |translatedMoment N c v - translatedMoment N e v| ≤ δ^6)
    (q : ℕ) (hq : q ∈ Finset.Icc 1 N) :
    abs (|selbergMultiplesCoord N c q| - |selbergMultiplesCoord N e q|) ≤ δ := by
  apply nonneg_sixth_root_error _ _ δ (abs_nonneg _) (abs_nonneg _) hδ
  simpa only [show (6 : ℕ) = 2*3 from rfl, pow_abs_two_mul] using
    coordinate_sixth_error N c e (δ^6) h q hq

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
