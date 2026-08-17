import GaloisForLFunctions.RHTower.XiOrdinateBandCopies
import GaloisForLFunctions.RHTower.SuzukiGeneralWitnessAnnularPayment

/-!
# The annular copy count and the unconditional annular payment

Turning the divisor-mass lower bound of the annulus into a `Finset` of multiplicity copies is
immediate once the mass difference is identified with the band cardinality.  Feeding that finset to
the general witness payment removes the last hypothesis: every sufficiently high off-line atom has
its complete-mass-normalized transverse charge paid by copies in one fixed annulus.
-/

open Complex Set

noncomputable section

namespace RHTower

/-- **The annular copy count.**  Every fixed annulus of ratio `10` eventually carries any
prescribed number of divisor-multiplicity copies. -/
theorem exists_annular_copies (C : ℝ) :
    ∃ Γ₀ : ℝ, 0 < Γ₀ ∧ ∀ Γ : ℝ, Γ₀ ≤ Γ → ∃ S : Finset XiZeroCopy,
      (∀ r ∈ S, Γ ^ 2 ≤ (r.1 : ℂ).im ^ 2) ∧
      (∀ r ∈ S, (r.1 : ℂ).im ^ 2 ≤ (10 * Γ) ^ 2) ∧
      C ≤ (S.card : ℝ) := by
  obtain ⟨Γ₁, hΓ₁⟩ := exists_annular_mass_lower C
  refine ⟨max Γ₁ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun Γ hΓ => ?_⟩
  have hΓ1 : (1 : ℝ) ≤ Γ := le_trans (le_max_right _ _) hΓ
  have hΓ0 : (0 : ℝ) ≤ Γ := by linarith
  obtain ⟨T₁, T₂, hT₁, hT₁₂, hT₂, -, -, hmass⟩ := hΓ₁ Γ (le_trans (le_max_left _ _) hΓ)
  refine ⟨xiCopiesBand T₁ T₂, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨hlow, -⟩ := mem_xiCopiesBand.mp hr
    have habs : Γ ≤ |(r.1 : ℂ).im| := by linarith
    nlinarith [abs_nonneg ((r.1 : ℂ).im), sq_abs ((r.1 : ℂ).im), habs, hΓ0]
  · intro r hr
    obtain ⟨-, hhigh⟩ := mem_xiCopiesBand.mp hr
    have habs : |(r.1 : ℂ).im| ≤ 10 * Γ := by linarith
    nlinarith [abs_nonneg ((r.1 : ℂ).im), sq_abs ((r.1 : ℂ).im), habs, hΓ0]
  · have hT₁0 : (0 : ℝ) ≤ T₁ := by linarith
    have hcard := xiSymmetricMass_diff_eq_card hT₁0 (le_of_lt hT₁₂)
    have hcast : ((xiSymmetricMass T₂ : ℝ) - (xiSymmetricMass T₁ : ℝ))
        = (((xiCopiesBand T₁ T₂).card : ℤ) : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hcard
      push_cast at this ⊢
      linarith [this]
    push_cast at hcast
    linarith [hmass, hcast]

/-- **The unconditional annular payment.**  Every sufficiently high off-line atom has its
complete-mass-normalized transverse charge strictly paid by divisor copies in one fixed annulus. -/
theorem exists_annular_payment_of_large_height :
    ∃ h₀ : ℝ, ∀ q : XiZeroCopy, h₀ ≤ (q.1 : ℂ).im ^ 2 → ∃ S : Finset XiZeroCopy,
      (∑' i : XiZeroCopy, xiShiftedResponseMass 1 i) * xiShiftedTransverseChargeDensity 1 q
        < xiShiftedResponseMass 1 q *
          ∑ r ∈ S, xiShiftedResponseMass 1 r
              * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ 2 := by
  obtain ⟨Γ₀, hΓ₀, hcopies⟩ := exists_annular_copies ((87 / 256 : ℝ) * 10 ^ 2 + 1)
  refine ⟨max (Γ₀ ^ 2 / 3) 71, fun q hq => ?_⟩
  set h : ℝ := (q.1 : ℂ).im ^ 2 with hh
  have hh71 : (71 : ℝ) ≤ h := le_trans (le_max_right _ _) hq
  have hhΓ : Γ₀ ^ 2 / 3 ≤ h := le_trans (le_max_left _ _) hq
  have hheight : (141 / 2 : ℝ) < h := by linarith
  set Γ : ℝ := Real.sqrt (3 * (1 + h)) with hΓdef
  have h3h : (0 : ℝ) ≤ 3 * (1 + h) := by linarith
  have hΓsq : Γ ^ 2 = 3 * (1 + h) := Real.sq_sqrt h3h
  have hΓ0 : 0 ≤ Γ := Real.sqrt_nonneg _
  have hΓge : Γ₀ ≤ Γ := by
    have hle : Γ₀ ^ 2 ≤ Γ ^ 2 := by rw [hΓsq]; linarith
    nlinarith [hΓ0, hΓ₀, hle]
  obtain ⟨S, hlow, hhigh, hcard⟩ := hcopies Γ hΓge
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < (S.card : ℝ) := by
      have hnum : (0 : ℝ) < (87 / 256 : ℝ) * 10 ^ 2 + 1 := by norm_num
      linarith
    exact_mod_cast this
  refine ⟨S, annulus_general_payment q hSne (by norm_num : (1 : ℝ) ≤ 10) ?_ ?_ hheight ?_⟩
  · intro r hr
    have h1 := hlow r hr
    rw [hΓsq] at h1
    rw [← hh]
    linarith
  · intro r hr
    have h2 := hhigh r hr
    have hval : (10 * Γ) ^ 2 = 3 * 10 ^ 2 * (1 + h) := by
      rw [mul_pow, hΓsq]
      ring
    rw [hval] at h2
    rw [← hh]
    linarith
  · exact hcard

end RHTower
