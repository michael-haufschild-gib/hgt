import GaloisForLFunctions.BiScaleUncertainty.FullGridCappedCollarEnergy

/-!
# Capacity and low-coordinate comparisons for capped support

Ordered weight addition has unit l1 capacity. At fixed whole-block norm, moving
weight norm from the high part into the capped low part decreases support. These
two comparisons distinguish physical capacity growth from constraint growth.
-/

set_option autoImplicit false
open Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
variable {ι : Type*}

/-- Ordered weight changes alter capped support by at most their l1 mass. -/
theorem cappedBlockSupport_weight_bounds {L H A B t : ℝ}
    (hH : 0 ≤ H) (hLA : L ≤ A) (hHB : H ≤ B) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ cappedBlockSupport A B t - cappedBlockSupport L H t ∧
      cappedBlockSupport A B t - cappedBlockSupport L H t ≤ (A - L) + (B - H) := by
  constructor
  · obtain ⟨x, z, hx, hxt, hz, hs, he⟩ := cappedBlockSupport_disk_attained L H ht
    have h := cappedBlockSupport_bound (L := A) (hH.trans hHB) ht hx hxt hs.le
    have h₁ := mul_nonneg (sub_nonneg.mpr hLA) hx
    have h₂ := mul_nonneg (sub_nonneg.mpr hHB) hz
    linarith
  · obtain ⟨x, z, hx, hxt, hz, hs, he⟩ := cappedBlockSupport_disk_attained A B ht
    have h := cappedBlockSupport_bound (L := L) hH ht hx hxt hs.le
    have hx1 : x ≤ 1 := hxt.trans ht.2
    have hz1 : z ≤ 1 := by nlinarith [sq_nonneg x]
    have h₁ := mul_le_of_le_one_right (sub_nonneg.mpr hLA) hx1
    have h₂ := mul_le_of_le_one_right (sub_nonneg.mpr hHB) hz1
    linarith

/-- With no high weight, only the low cap contributes. -/
theorem cappedBlockSupport_zero_high {L t : ℝ} (hL : 0 ≤ L) (ht : t ∈ Icc (0 : ℝ) 1) :
    cappedBlockSupport L 0 t = L * t := by
  apply le_antisymm
  · obtain ⟨x, z, _, hxt, _, _, he⟩ := cappedBlockSupport_disk_attained L 0 ht
    rw [← he, zero_mul, add_zero]
    exact mul_le_mul_of_nonneg_left hxt hL
  · simpa only [mul_one, zero_mul, add_zero] using
      cappedBlockSupport_lower L 0 t 1 (by simp)

theorem cappedBlockSupport_zero {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cappedBlockSupport 0 0 t = 0 := by
  simpa using cappedBlockSupport_zero_high (L := 0) (by norm_num) ht

/-- A binding cap puts its outward normal beyond the weight direction. -/
theorem cappedBlockSupport_binding_slope {L H t : ℝ} (hL : 0 ≤ L)
    (ht : t ∈ Icc (0 : ℝ) 1) (hb : t * Real.sqrt (L ^ 2 + H ^ 2) ≤ L) :
    H * t ≤ L * Real.sqrt (1 - t ^ 2) := by
  have hD := Real.sq_sqrt (show 0 ≤ L ^ 2 + H ^ 2 by positivity)
  have hq := Real.sq_sqrt (show 0 ≤ 1 - t ^ 2 by nlinarith [ht.1, ht.2])
  have hprod := mul_nonneg (sub_nonneg.mpr hb)
    (add_nonneg hL (mul_nonneg ht.1 (Real.sqrt_nonneg (L ^ 2 + H ^ 2))))
  nlinarith [mul_nonneg hL (Real.sqrt_nonneg (1 - t ^ 2))]

/-- At fixed whole-block norm, a larger low component makes a cap stronger. -/
theorem cappedBlockSupport_antitone_low {L H A B t : ℝ}
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hLA : L ≤ A) (hnorm : L ^ 2 + H ^ 2 = A ^ 2 + B ^ 2)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    cappedBlockSupport A B t ≤ cappedBlockSupport L H t := by
  by_cases hfit : L ≤ t * Real.sqrt (L ^ 2 + H ^ 2)
  · rw [cappedBlockSupport_eq_norm hL hH ht hfit, hnorm]
    exact cappedBlockSupport_le_norm A B ht
  have hbind : t * Real.sqrt (L ^ 2 + H ^ 2) < L := lt_of_not_ge hfit
  have hbind' : t * Real.sqrt (A ^ 2 + B ^ 2) < A := by
    rw [← hnorm]
    exact hbind.trans_le hLA
  rw [cappedBlockSupport_eq_boundary hA hB ht hbind',
    cappedBlockSupport_eq_boundary hL hH ht hbind]
  have hBH : B ≤ H := by nlinarith
  by_cases hH0 : H = 0
  · have hB0 : B = 0 := by linarith
    have hAL : A = L := by nlinarith
    simp [hH0, hB0, hAL]
  have hHp : 0 < H := lt_of_le_of_ne hH (Ne.symm hH0)
  let q := Real.sqrt (1 - t ^ 2)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hslope : H * t ≤ L * q := cappedBlockSupport_binding_slope hL ht hbind.le
  have htan : L * (A - L) + H * (B - H) ≤ 0 := by
    nlinarith [sq_nonneg (A - L), sq_nonneg (B - H)]
  have h₁ := mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hLA)
  have h₂ := mul_nonpos_of_nonneg_of_nonpos hq htan
  have hscaled : H * (A * t + B * q) ≤ H * (L * t + H * q) := by nlinarith
  exact (mul_le_mul_iff_right₀ hHp).1 hscaled

/-- A blockwise support comparison passes through the common compact maximum. -/
theorem cappedCosetSupport_mono_of_blocks (M : Finset ι) (L H A B : Bool → ι → ℝ)
    (h : ∀ σ, ∀ m ∈ M, ∀ t ∈ Icc (0 : ℝ) 1,
      cappedBlockSupport (L σ m) (H σ m) t ≤ cappedBlockSupport (A σ m) (B σ m) t) :
    cappedCosetSupport M L H ≤ cappedCosetSupport M A B := by
  obtain ⟨t, ht, he, _⟩ := cappedCosetSupport_attained M L H
  obtain ⟨_, _, _, hmax⟩ := cappedCosetSupport_attained M A B
  rw [he]
  apply le_trans ?_ (hmax t ht)
  exact Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun m hm => h σ m hm _ (pairedCap_mem ht σ)

theorem cappedCosetSupport_weight_bounds (M : Finset ι) (L H A B : Bool → ι → ℝ)
    (hH : ∀ σ, ∀ m ∈ M, 0 ≤ H σ m)
    (hLA : ∀ σ, ∀ m ∈ M, L σ m ≤ A σ m)
    (hHB : ∀ σ, ∀ m ∈ M, H σ m ≤ B σ m) :
    0 ≤ cappedCosetSupport M A B - cappedCosetSupport M L H ∧
      cappedCosetSupport M A B - cappedCosetSupport M L H ≤
        ∑ σ : Bool, ∑ m ∈ M, ((A σ m - L σ m) + (B σ m - H σ m)) := by
  constructor
  · apply sub_nonneg.mpr
    apply cappedCosetSupport_mono_of_blocks
    intro σ m hm t ht
    exact sub_nonneg.mp (cappedBlockSupport_weight_bounds (hH σ m hm)
      (hLA σ m hm) (hHB σ m hm) ht).1
  · obtain ⟨t, ht, he, _⟩ := cappedCosetSupport_attained M A B
    obtain ⟨_, _, _, hmax⟩ := cappedCosetSupport_attained M L H
    have h := Finset.sum_le_sum fun σ (_ : σ ∈ (Finset.univ : Finset Bool)) =>
      Finset.sum_le_sum fun m hm => (cappedBlockSupport_weight_bounds (hH σ m hm)
        (hLA σ m hm) (hHB σ m hm) (pairedCap_mem ht σ)).2
    simp only [Finset.sum_sub_distrib] at h
    rw [← he] at h
    linarith [hmax t ht]

/-- The all-low angular support is exactly the paired Euclidean sign norm. -/
theorem cappedCosetSupport_zero_high (M : Finset ι) (L : Bool → ι → ℝ)
    (hL : ∀ σ, ∀ m ∈ M, 0 ≤ L σ m) :
    cappedCosetSupport M L (fun _ _ => 0) =
      Real.sqrt ((∑ m ∈ M, L false m) ^ 2 + (∑ m ∈ M, L true m) ^ 2) := by
  let A := ∑ m ∈ M, L false m
  let B := ∑ m ∈ M, L true m
  have hA : 0 ≤ A := Finset.sum_nonneg (hL false)
  have hB : 0 ≤ B := Finset.sum_nonneg (hL true)
  have hn : cappedBlockSupport A B 1 = Real.sqrt (A ^ 2 + B ^ 2) :=
    cappedBlockSupport_eq_norm hA hB (by simp) (by
      simpa only [one_mul] using (Real.le_sqrt_of_sq_le
        (show A ^ 2 ≤ A ^ 2 + B ^ 2 by nlinarith [sq_nonneg B])))
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∑ σ : Bool, ∑ m ∈ M, cappedBlockSupport (L σ m) 0 (pairedCap t σ)) =
        A * t + B * Real.sqrt (1 - t ^ 2) := by
    have hs (σ : Bool) : (∑ m ∈ M, cappedBlockSupport (L σ m) 0 (pairedCap t σ)) =
        (∑ m ∈ M, L σ m) * pairedCap t σ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun m hm => cappedBlockSupport_zero_high (hL σ m hm) (pairedCap_mem ht σ)
    simp only [Fintype.sum_bool]
    rw [hs true, hs false]
    dsimp [pairedCap, A, B]
    ring
  apply le_antisymm
  · obtain ⟨t, ht, htmax, _⟩ := cappedCosetSupport_attained M L (fun _ _ => 0)
    rw [htmax, he t ht]
    have h := cappedBlockSupport_lower A B 1 t ht
    simpa only [one_mul, hn] using h
  · obtain ⟨t, ht, htmax, _⟩ := cappedBlockSupport_attained A B 1
    obtain ⟨_, _, _, hmax⟩ := cappedCosetSupport_attained M L (fun _ _ => 0)
    have h := hmax t ht
    rw [he t ht] at h
    rw [hn] at htmax
    simp only [one_mul] at htmax
    change Real.sqrt (A ^ 2 + B ^ 2) ≤ cappedCosetSupport M L (fun _ _ => 0)
    rw [htmax]
    exact h

/-- The final common-origin radius has unit capacity in its angular argument. -/
theorem cappedRadial_monotone_bounds (W : ℝ) {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    0 ≤ Real.sqrt (W ^ 2 + B ^ 2) - Real.sqrt (W ^ 2 + A ^ 2) ∧
      Real.sqrt (W ^ 2 + B ^ 2) - Real.sqrt (W ^ 2 + A ^ 2) ≤ B - A := by
  simpa only [zero_pow (by decide : 2 ≠ 0), add_zero, sub_self] using
    pairedRadial_monotone_bounds W hA (show (0 : ℝ) ≤ 0 from le_rfl) hAB le_rfl

end
end GaloisForLFunctions.BiScaleUncertainty
