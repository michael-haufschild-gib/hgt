import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleReadsTheZeros
import GaloisForLFunctions.RHTower.ModularInvariantHeight

/-!
# The algebra of cusp-supported profiles

For profiles vanishing below a height strictly greater than `1`, half the
pseudo-Eisenstein periodization preserves pointwise products and every scalar
map fixing zero. Globally the periodization is twice the profile evaluated at
the invariant height `Y(z) = sup_γ Im(γz)`, which also determines its exact support.

Radiality on the fundamental domain does not imply radiality on the upper
half-plane. Invariance under `z ↦ -1/z` makes every globally height-dependent
function constant, without any regularity assumption. Thus a cusp-supported
profile has a globally height-dependent periodization exactly when it is zero.
-/

open UpperHalfPlane ModularGroup Complex
open scoped MatrixGroups

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower.RepPointPair

noncomputable section

private theorem im_modularS (z : ℍ) :
    (ModularGroup.S • z).im = z.im / (z.re ^ 2 + z.im ^ 2) := by
  rw [UpperHalfPlane.modular_S_smul]
  change ((-(z : ℂ))⁻¹).im = _
  rw [Complex.inv_im, Complex.neg_im, neg_neg, Complex.normSq_neg,
    Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, pow_two]

/-- Horizontal constancy and modular inversion force constancy on all of `ℍ`.
For heights at most one, a horizontal move followed by inversion reaches height one. -/
theorem eq_at_I_of_height_dependent_of_inversion_invariant {E : Type*} {F : ℍ → E}
    (hheight : ∀ z w : ℍ, z.im = w.im → F z = F w)
    (hS : ∀ z : ℍ, F (ModularGroup.S • z) = F z) (z : ℍ) :
    F z = F UpperHalfPlane.I := by
  have hlow : ∀ w : ℍ, w.im ≤ 1 → F w = F UpperHalfPlane.I := by
    intro w hw
    have hnonneg : 0 ≤ w.im - w.im ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hw w.im_pos.le
      nlinarith only [hmul]
    let v : ℍ := ⟨⟨Real.sqrt (w.im - w.im ^ 2), w.im⟩, w.im_pos⟩
    have hSv : (ModularGroup.S • v).im = UpperHalfPlane.I.im := by
      rw [im_modularS]
      change w.im / ((Real.sqrt (w.im - w.im ^ 2)) ^ 2 + w.im ^ 2) = 1
      rw [Real.sq_sqrt hnonneg, sub_add_cancel, div_self w.im_pos.ne']
    exact (hheight w v rfl).trans ((hS v).symm.trans
      (hheight (ModularGroup.S • v) UpperHalfPlane.I hSv))
  by_cases hz : z.im ≤ 1
  · exact hlow z hz
  · let v : ℍ := ⟨⟨0, z.im⟩, z.im_pos⟩
    have hSv : (ModularGroup.S • v).im ≤ 1 := by
      rw [im_modularS]
      change z.im / (0 ^ 2 + z.im ^ 2) ≤ 1
      rw [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]
      apply (div_le_one (sq_pos_of_pos z.im_pos)).2
      have hmul := mul_nonneg (sub_nonneg.2 (le_of_not_ge hz)) z.im_pos.le
      nlinarith only [hmul]
    exact (hheight z v rfl).trans ((hS v).symm.trans (hlow _ hSv))

private theorem vertical_mem_fd {y : ℝ} (hy : 1 ≤ y) :
    (⟨⟨0, y⟩, lt_of_lt_of_le zero_lt_one hy⟩ : ℍ) ∈ fd := by
  constructor
  · change 1 ≤ Complex.normSq (⟨0, y⟩ : ℂ)
    rw [Complex.normSq_apply]
    change 1 ≤ 0 * 0 + y * y
    nlinarith only [hy]
  · change |(0 : ℝ)| ≤ 1 / 2
    norm_num

section Profiles

variable {ψ φ : ℝ → ℂ} {a : ℝ}

/-- The correct global height is the maximum over the modular orbit. -/
theorem pseudoEisenstein_eq_profile_invHeight (ha : 1 < a)
    (hψ : ∀ y, y < a → ψ y = 0) (z : ℍ) :
    pseudoEisenstein ψ z = 2 * ψ (invHeight z) := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  rw [← pseudoEisenstein_smul g z, ← invHeight_smul g z,
    invHeight_eq_of_mem_fd hg, pseudoEisenstein_of_mem_fd ha hψ hg]

/-- Cusp support is a condition on invariant height, including all modular copies. -/
theorem support_pseudoEisenstein (ha : 1 < a) (hψ : ∀ y, y < a → ψ y = 0) :
    Function.support (pseudoEisenstein ψ) = invHeight ⁻¹' Function.support ψ := by
  ext z
  change pseudoEisenstein ψ z ≠ 0 ↔ ψ (invHeight z) ≠ 0
  rw [pseudoEisenstein_eq_profile_invHeight ha hψ]
  rw [mul_ne_zero_iff]
  exact ⟨And.right, fun h => ⟨by norm_num, h⟩⟩

/-- Periodization followed by division by two preserves every scalar map fixing zero. -/
theorem pseudoEisenstein_comp (ha : 1 < a) (hψ : ∀ y, y < a → ψ y = 0)
    (H : ℂ → ℂ) (hH : H 0 = 0) (z : ℍ) :
    pseudoEisenstein (H ∘ ψ) z = 2 * H (pseudoEisenstein ψ z / 2) := by
  have hHψ : ∀ y, y < a → (H ∘ ψ) y = 0 := by
    intro y hy
    simp only [Function.comp_apply, hψ y hy, hH]
  rw [pseudoEisenstein_eq_profile_invHeight ha hHψ,
    pseudoEisenstein_eq_profile_invHeight ha hψ]
  simp only [Function.comp_apply, mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)]

/-- Products of cusp-supported periodizations are periodizations of products. -/
theorem pseudoEisenstein_mul (ha : 1 < a) (hψ : ∀ y, y < a → ψ y = 0)
    (hφ : ∀ y, y < a → φ y = 0) (z : ℍ) :
    pseudoEisenstein ψ z * pseudoEisenstein φ z =
      2 * pseudoEisenstein (fun y => ψ y * φ y) z := by
  have hprod : ∀ y, y < a → ψ y * φ y = 0 := by
    intro y hy
    rw [hψ y hy, zero_mul]
  rw [pseudoEisenstein_eq_profile_invHeight ha hψ,
    pseudoEisenstein_eq_profile_invHeight ha hφ,
    pseudoEisenstein_eq_profile_invHeight ha hprod]
  ring

/-- The exact pointwise square law retains complex conjugation for complex profiles. -/
theorem pseudoEisenstein_conj_mul (ha : 1 < a) (hψ : ∀ y, y < a → ψ y = 0)
    (z : ℍ) :
    (starRingEnd ℂ) (pseudoEisenstein ψ z) * pseudoEisenstein ψ z =
      2 * pseudoEisenstein (fun y => (starRingEnd ℂ) (ψ y) * ψ y) z := by
  have hprod : ∀ y, y < a → (starRingEnd ℂ) (ψ y) * ψ y = 0 := by
    intro y hy
    rw [hψ y hy, mul_zero]
  rw [pseudoEisenstein_eq_profile_invHeight ha hψ,
    pseudoEisenstein_eq_profile_invHeight ha hprod,
    map_mul, map_ofNat]
  ring

/-- Periodization loses no information about a profile supported above height one. -/
theorem pseudoEisenstein_injective_on_profiles (ha : 1 < a)
    (hψ : ∀ y, y < a → ψ y = 0) (hφ : ∀ y, y < a → φ y = 0) :
    pseudoEisenstein ψ = pseudoEisenstein φ ↔ ψ = φ := by
  constructor
  · intro h
    funext y
    by_cases hy : y < a
    · rw [hψ y hy, hφ y hy]
    · have hy1 : 1 ≤ y := ha.le.trans (le_of_not_gt hy)
      let z : ℍ := ⟨⟨0, y⟩, lt_of_lt_of_le zero_lt_one hy1⟩
      have hz : z ∈ fd := vertical_mem_fd hy1
      have heq := congrFun h z
      rw [pseudoEisenstein_of_mem_fd ha hψ hz,
        pseudoEisenstein_of_mem_fd ha hφ hz] at heq
      exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) heq
  · rintro rfl
    rfl

/-- A cusp-supported periodization depends globally only on height exactly for the zero profile. -/
theorem pseudoEisenstein_height_dependent_iff (ha : 1 < a)
    (hψ : ∀ y, y < a → ψ y = 0) :
    (∃ f : ℝ → ℂ, ∀ z : ℍ, pseudoEisenstein ψ z = f z.im) ↔ ψ = 0 := by
  constructor
  · rintro ⟨f, hf⟩
    have hconstant : ∀ z : ℍ, pseudoEisenstein ψ z = pseudoEisenstein ψ UpperHalfPlane.I :=
      eq_at_I_of_height_dependent_of_inversion_invariant
        (fun z w h => by rw [hf z, hf w, h]) (pseudoEisenstein_smul ModularGroup.S)
    have hI : UpperHalfPlane.I ∈ fd := by
      constructor <;> norm_num [UpperHalfPlane.I, Complex.normSq_apply]
    have hzero : pseudoEisenstein ψ = pseudoEisenstein (0 : ℝ → ℂ) := by
      funext z
      rw [hconstant z, pseudoEisenstein_of_mem_fd ha hψ hI]
      change 2 * ψ 1 = _
      rw [hψ 1 ha, mul_zero]
      simp only [pseudoEisenstein, Pi.zero_apply, tsum_zero]
    exact (pseudoEisenstein_injective_on_profiles ha hψ (by simp)).1 hzero
  · rintro rfl
    exact ⟨0, fun z => by simp only [pseudoEisenstein, Pi.zero_apply, tsum_zero]⟩

/-- A profile value above height one reappears below height one by modular inversion. -/
theorem pseudoEisenstein_inverted_vertical (ha : 1 < a)
    (hψ : ∀ y, y < a → ψ y = 0) {y : ℝ} (hy : 1 ≤ y) :
    pseudoEisenstein ψ
      (ModularGroup.S • (⟨⟨0, y⟩, lt_of_lt_of_le zero_lt_one hy⟩ : ℍ)) = 2 * ψ y := by
  rw [pseudoEisenstein_smul, pseudoEisenstein_of_mem_fd ha hψ (vertical_mem_fd hy)]
  rfl

end Profiles

end

end GaloisForLFunctions.BlackHoleRingdown

#print axioms GaloisForLFunctions.BlackHoleRingdown.eq_at_I_of_height_dependent_of_inversion_invariant
#print axioms GaloisForLFunctions.BlackHoleRingdown.pseudoEisenstein_eq_profile_invHeight
#print axioms GaloisForLFunctions.BlackHoleRingdown.support_pseudoEisenstein
#print axioms GaloisForLFunctions.BlackHoleRingdown.pseudoEisenstein_comp
#print axioms GaloisForLFunctions.BlackHoleRingdown.pseudoEisenstein_mul
#print axioms GaloisForLFunctions.BlackHoleRingdown.pseudoEisenstein_conj_mul
#print axioms GaloisForLFunctions.BlackHoleRingdown.pseudoEisenstein_injective_on_profiles
#print axioms GaloisForLFunctions.BlackHoleRingdown.pseudoEisenstein_height_dependent_iff
#print axioms GaloisForLFunctions.BlackHoleRingdown.pseudoEisenstein_inverted_vertical
