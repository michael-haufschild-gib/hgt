import GaloisForLFunctions.HTGeometry.LaurentShiftAutomorphism

/-!
# The fixed field of the translation is the constants

A formal Laurent series at infinity fixed by a nonzero translation is a constant: after inverting,
one may assume the series is a power series, and then the first coefficient beyond the order of a
nonconstant fixed series would have to vanish.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Low coefficients of the translation substitution -/

theorem constantCoeff_inv_one_add (h : ℂ) :
    PowerSeries.constantCoeff ((1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ)⁻¹) = 1 := by
  rw [PowerSeries.constantCoeff_inv, constantCoeff_one_add, inv_one]

theorem coeff_one_inv_one_add (h : ℂ) :
    PowerSeries.coeff 1 ((1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ)⁻¹) = -h := by
  have hne : PowerSeries.constantCoeff (1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ) ≠ 0 := by
    rw [constantCoeff_one_add]; exact one_ne_zero
  have hmul := PowerSeries.mul_inv_cancel _ hne
  have hc := congrArg (PowerSeries.coeff 1) hmul
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at hc
  rw [PowerSeries.coeff_one] at hc
  simp only [if_neg (by norm_num : ¬(1 = 0))] at hc
  have h0 : PowerSeries.coeff 0 (1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact constantCoeff_one_add h
  have h1 : PowerSeries.coeff 1 (1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ) = h := by
    simp
  have h0inv : PowerSeries.coeff 0
      ((1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ)⁻¹) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact constantCoeff_inv_one_add h
  rw [h0, h1, h0inv, one_mul, mul_one] at hc
  simp only [Nat.sub_zero, zero_add] at hc
  linear_combination hc

theorem coeff_zero_pow_inv (h : ℂ) (m : ℕ) :
    PowerSeries.coeff 0 (((1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ)⁻¹) ^ m) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_inv_one_add, one_pow]

theorem coeff_one_pow_inv (h : ℂ) : ∀ m : ℕ,
    PowerSeries.coeff 1 (((1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ)⁻¹) ^ m)
      = -((m : ℂ) * h) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      set u : PowerSeries ℂ := (1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ)⁻¹ with hu
      rw [pow_succ, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      simp only [Nat.sub_zero, Nat.sub_self, zero_add]
      rw [coeff_zero_pow_inv h m, ih]
      have h0 : PowerSeries.coeff 0 u = 1 := by
        rw [hu, PowerSeries.coeff_zero_eq_constantCoeff]
        exact constantCoeff_inv_one_add h
      have h1 : PowerSeries.coeff 1 u = -h := by
        rw [hu]
        exact coeff_one_inv_one_add h
      rw [h0, h1]
      push_cast
      ring

theorem shiftSubst_pow (h : ℂ) (m : ℕ) :
    (shiftSubst h) ^ m
      = PowerSeries.X ^ m * ((1 + PowerSeries.C h * PowerSeries.X : PowerSeries ℂ)⁻¹) ^ m := by
  rw [shiftSubst, mul_pow]

theorem coeff_shiftSubst_pow_of_lt (h : ℂ) {n d : ℕ} (hnd : n < d) :
    PowerSeries.coeff n ((shiftSubst h) ^ d) = 0 := by
  rw [shiftSubst_pow, PowerSeries.coeff_X_pow_mul']
  rw [if_neg (by omega)]

theorem coeff_shiftSubst_pow_self (h : ℂ) (m : ℕ) :
    PowerSeries.coeff m ((shiftSubst h) ^ m) = 1 := by
  rw [shiftSubst_pow, PowerSeries.coeff_X_pow_mul' , if_pos (le_refl m), Nat.sub_self,
    coeff_zero_pow_inv]

theorem coeff_shiftSubst_pow_succ (h : ℂ) (m : ℕ) :
    PowerSeries.coeff (m + 1) ((shiftSubst h) ^ m) = -((m : ℂ) * h) := by
  rw [shiftSubst_pow, PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
  have : m + 1 - m = 1 := by omega
  rw [this, coeff_one_pow_inv]

/-! ### The fixed power series are the constants -/

/-- **A power series fixed by a nonzero translation is constant.** -/
theorem eq_C_of_shiftPS_eq {h : ℂ} (hh : h ≠ 0) {A : PowerSeries ℂ} (hA : shiftPS h A = A) :
    A = PowerSeries.C (PowerSeries.constantCoeff A) := by
  classical
  by_contra hne
  set B : PowerSeries ℂ := A - PowerSeries.C (PowerSeries.constantCoeff A) with hBdef
  have hB0 : B ≠ 0 := by
    intro hc
    exact hne (by rwa [hBdef, sub_eq_zero] at hc)
  have hBfix : shiftPS h B = B := by
    rw [hBdef, map_sub, hA, shiftPS_C]
  have hBconst : PowerSeries.constantCoeff B = 0 := by
    rw [hBdef, map_sub, PowerSeries.constantCoeff_C, sub_self]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, B.order = (m : ℕ∞) := by
    rcases eq_or_ne B.order ⊤ with hc | hc
    · exact absurd (PowerSeries.order_eq_top.mp hc) hB0
    · lift B.order to ℕ using hc with m hmm
      exact ⟨m, rfl⟩
  obtain ⟨hcm, hlt⟩ := PowerSeries.order_eq_nat.mp hm
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      apply hcm
      rw [h0, PowerSeries.coeff_zero_eq_constantCoeff]
      exact hBconst
    · exact h0
  -- the coefficient of `X^{m+1}` in the translate
  have hsupp : (Function.support fun d : ℕ =>
      PowerSeries.coeff d B • PowerSeries.coeff (m + 1) ((shiftSubst h) ^ d))
      ⊆ (({m, m + 1} : Finset ℕ) : Set ℕ) := by
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hcon
    push Not at hcon
    obtain ⟨hd1, hd2⟩ := hcon
    rcases lt_or_gt_of_ne hd1 with hlt' | hgt
    · exact hd (by rw [hlt d hlt', zero_smul])
    · exact hd (by
        rw [coeff_shiftSubst_pow_of_lt h (by omega), smul_zero])
  have hkey : PowerSeries.coeff (m + 1) (shiftPS h B)
      = PowerSeries.coeff m B * (-((m : ℂ) * h)) + PowerSeries.coeff (m + 1) B := by
    rw [shiftPS_apply, PowerSeries.coeff_subst' (hasSubst_shiftSubst h)]
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    rw [Finset.sum_pair (by omega : m ≠ m + 1)]
    rw [coeff_shiftSubst_pow_succ, coeff_shiftSubst_pow_self]
    simp [smul_eq_mul]
  rw [hBfix] at hkey
  have hzero : PowerSeries.coeff m B * ((m : ℂ) * h) = 0 := by
    linear_combination hkey
  rcases mul_eq_zero.mp hzero with hc | hc
  · exact hcm hc
  · rcases mul_eq_zero.mp hc with hc2 | hc2
    · have : (m : ℂ) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega
      exact this hc2
    · exact hh hc2

/-! ### The fixed Laurent series are the constants -/

theorem coeff_algebraMap_of_neg (A : PowerSeries ℂ) {n : ℤ} (hn : n < 0) :
    (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) A).coeff n = 0 := by
  show ((HahnSeries.ofPowerSeries ℤ ℂ) A).coeff n = 0
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
  intro hmem
  simp only [Nat.castOrderEmbedding_apply, Set.mem_range] at hmem
  obtain ⟨k, hk⟩ := hmem
  omega

theorem exists_powerSeries_of_order_nonneg {F : LaurentSeries ℂ} (h0 : 0 ≤ F.order) :
    ∃ A : PowerSeries ℂ, algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) A = F := by
  refine ⟨PowerSeries.mk fun n => F.coeff (n : ℤ), ?_⟩
  ext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [coeff_algebraMap_of_neg _ hn]
    rcases eq_or_ne F 0 with rfl | hF0
    · simp
    · exact (HahnSeries.coeff_eq_zero_of_lt_order (by omega)).symm
  · lift n to ℕ using hn with k
    show ((HahnSeries.ofPowerSeries ℤ ℂ) _).coeff (k : ℤ) = _
    rw [LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_mk]

/-- **A formal Laurent series fixed by a nonzero translation is a constant.** -/
theorem exists_laurentC_of_shiftLaurent_eq {h : ℂ} (hh : h ≠ 0) {F : LaurentSeries ℂ}
    (hF : shiftLaurent h F = F) : ∃ c : ℂ, laurentC c = F := by
  classical
  have hstep : ∀ G : LaurentSeries ℂ, 0 ≤ G.order → shiftLaurent h G = G →
      ∃ c : ℂ, laurentC c = G := by
    intro G hG hGfix
    obtain ⟨A, rfl⟩ := exists_powerSeries_of_order_nonneg hG
    have hAfix : shiftPS h A = A := by
      refine algebraMap_powerSeries_injective ?_
      rw [← shiftLaurent_algebraMap]
      exact hGfix
    refine ⟨PowerSeries.constantCoeff A, ?_⟩
    rw [laurentC]
    congr 1
    exact (eq_C_of_shiftPS_eq hh hAfix).symm
  rcases eq_or_ne F 0 with rfl | hF0
  · exact ⟨0, by rw [laurentC, map_zero, map_zero]⟩
  rcases le_or_gt 0 F.order with hord | hord
  · exact hstep F hord hF
  · have hFinv : shiftLaurent h F⁻¹ = F⁻¹ := by
      rw [map_inv₀, hF]
    have hinvne : F⁻¹ ≠ 0 := inv_ne_zero hF0
    have hordinv : 0 ≤ (F⁻¹).order := by
      have hmul : (F * F⁻¹).order = F.order + (F⁻¹).order :=
        HahnSeries.order_mul hF0 hinvne
      rw [mul_inv_cancel₀ hF0, HahnSeries.order_one] at hmul
      omega
    obtain ⟨c, hc⟩ := hstep F⁻¹ hordinv hFinv
    have hcne : c ≠ 0 := by
      intro hc0
      rw [hc0, laurentC, map_zero, map_zero] at hc
      exact hinvne hc.symm
    refine ⟨c⁻¹, ?_⟩
    have hlaurentC_mul : laurentC c * laurentC c⁻¹ = 1 := by
      rw [laurentC, laurentC, ← map_mul, ← map_mul, mul_inv_cancel₀ hcne, map_one, map_one]
    have hlaurentC_inv : laurentC c⁻¹ = (laurentC c)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hlaurentC_mul)
    rw [hlaurentC_inv, hc, inv_inv]

end

end GaloisForLFunctions.HTGeometry
