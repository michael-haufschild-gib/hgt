import GaloisForLFunctions.BiScaleUncertainty.IncomparableSieveQuartic

/-!
# Complete translated arrays and resonant coordinate products

Finite Fourier inversion identifies every translated moment array with its
zero-sum coordinate products. Quadratic arrays determine all coordinate
squares; fourth arrays already determine those same squares.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open AffineSieve
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Complete lag data determine every resonant product, including zero coordinates. -/
theorem resonant_products_of_moments_eq (N : ℕ) (c e : ℕ → ℝ) (m : ℕ)
    (hm : ∀ h : Fin m → ℕ, translatedMoment N c h = translatedMoment N e h)
    (r : Fin m → ZMod N.factorial) (hz : (∑ i, r i) = 0) :
    (∏ i, selbergMultiplesCoord N c (addOrderOf (r i))) =
      ∏ i, selbergMultiplesCoord N e (addOrderOf (r i)) := by
  have ho :
      (fun h : Fin m → ZMod N.factorial =>
        (translatedMoment N c (fun i => (h i).val) : ℂ)) =
      (fun h : Fin m → ZMod N.factorial =>
        (translatedMoment N e (fun i => (h i).val) : ℂ)) := by
    funext h
    rw [hm]
  have hh := congrArg (fun f : (Fin m → ZMod N.factorial) → ℂ => momentDFT f r) ho
  simp only [translatedMoment_complex_eq, ZMod.natCast_zmod_val] at hh
  change momentDFT (translationMoment (residueSignal N (fun d => (c d : ℂ)))) r =
    momentDFT (translationMoment (residueSignal N (fun d => (e d : ℂ)))) r at hh
  simp only [momentDFT_sieve, hz, if_true] at hh
  have hP : (N.factorial : ℂ)^m ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero N)
  have hp := mul_left_cancel₀ hP hh
  simp only [coordinate_ofReal] at hp
  exact_mod_cast hp

/-- Exact Fourier characterization of equality of complete translated arrays. -/
theorem moments_eq_iff_resonant_products (N : ℕ) (c e : ℕ → ℝ) (m : ℕ) :
    (∀ h : Fin m → ℕ, translatedMoment N c h = translatedMoment N e h) ↔
    (∀ r : Fin m → ZMod N.factorial, (∑ i, r i) = 0 →
      (∏ i, selbergMultiplesCoord N c (addOrderOf (r i))) =
        ∏ i, selbergMultiplesCoord N e (addOrderOf (r i))) := by
  exact ⟨resonant_products_of_moments_eq N c e m,
    fun he h => translatedMoment_eq_of_resonant_products N c e m he h⟩

private theorem coordinate_zero_of_not_mem (N : ℕ) (c : ℕ → ℝ) (q : ℕ)
    (hq : q ∉ Finset.Icc 1 N) : selbergMultiplesCoord N c q = 0 := by
  unfold selbergMultiplesCoord
  apply Finset.sum_eq_zero
  intro d hd
  obtain ⟨hd,hdiv⟩ := Finset.mem_filter.mp hd
  obtain ⟨hdpos,hdN⟩ := Finset.mem_Icc.mp hd
  have hq0 : q ≠ 0 := by
    intro h0
    subst q
    have : d = 0 := by simpa using hdiv
    omega
  have hqd := Nat.le_of_dvd (by omega : 0 < d) hdiv
  exact (hq (Finset.mem_Icc.mpr ⟨by omega, hqd.trans hdN⟩)).elim

/-- Quadratic lag observations recover all sieve-coordinate magnitudes. -/
theorem quadratic_moments_iff_coordinate_squares (N : ℕ) (c e : ℕ → ℝ) :
    (∀ h : Fin 2 → ℕ, translatedMoment N c h = translatedMoment N e h) ↔
      ∀ q, selbergMultiplesCoord N c q ^ 2 = selbergMultiplesCoord N e q ^ 2 := by
  constructor
  · intro hm q
    by_cases hq : q ∈ Finset.Icc 1 N
    · let r : ZMod N.factorial := (N.factorial/q : ℕ)
      have hr : addOrderOf r = q := frequency_order hq
      have hh := resonant_products_of_moments_eq N c e 2 hm ![r,-r]
        (by simp [Fin.sum_univ_two])
      simpa [Fin.prod_univ_two, addOrderOf_neg, hr, pow_two] using hh
    · rw [coordinate_zero_of_not_mem N c q hq, coordinate_zero_of_not_mem N e q hq]
  · exact fun hq h => quadratic_moments_of_coordinate_squares N c e hq h

/-- The repeated pair `(r,-r,r,-r)` recovers each coordinate magnitude. -/
theorem coordinate_squares_of_fourth_moments (N : ℕ) (c e : ℕ → ℝ)
    (hm : ∀ h : Fin 4 → ℕ, translatedMoment N c h = translatedMoment N e h)
    (q : ℕ) : selbergMultiplesCoord N c q ^ 2 = selbergMultiplesCoord N e q ^ 2 := by
  by_cases hq : q ∈ Finset.Icc 1 N
  · let r : ZMod N.factorial := (N.factorial/q : ℕ)
    have hr : addOrderOf r = q := frequency_order hq
    have hh := resonant_products_of_moments_eq N c e 4 hm ![r,-r,r,-r]
      (by simp [Fin.sum_univ_four])
    simp [Fin.prod_univ_four, addOrderOf_neg, hr] at hh
    have hf : (selbergMultiplesCoord N c q ^ 2 - selbergMultiplesCoord N e q ^ 2) *
        (selbergMultiplesCoord N c q ^ 2 + selbergMultiplesCoord N e q ^ 2) = 0 := by
      nlinarith only [hh]
    rcases mul_eq_zero.mp hf with h | h
    · linarith
    · nlinarith only [sq_nonneg (selbergMultiplesCoord N c q),
        sq_nonneg (selbergMultiplesCoord N e q), h]
  · rw [coordinate_zero_of_not_mem N c q hq, coordinate_zero_of_not_mem N e q hq]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
