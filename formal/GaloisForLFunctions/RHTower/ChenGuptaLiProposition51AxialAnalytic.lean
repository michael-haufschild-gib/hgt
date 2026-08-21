/-
# Chen--Gupta--Li Proposition 5.1 axial analytic estimate

For a surviving equal-character, non-all-equal row triple on an `S₁` axis,
one of the two zero-frequency coordinates has a certified nonzero ordinate
gap. This module applies CGL Lemma 4.3's all-order reciprocal decay there
and retains the remaining nonzero coordinate for the punctured tail estimate.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51CharacterBounds

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The two-zero-coordinate analytic budget for one axial `S₁` row term. -/
def cglProposition51FibreAxialAnalyticBudget {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) : ℝ :=
  (cglAffineFourierScale N (cglLemma45FibreModulus q) *
    (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n / P.spacing ^ n)) *
      (cglAffineFourierScale N (cglLemma45FibreModulus q) *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0)

/-- A same-character non-all-equal row triple forces reciprocal decay in one
of the two zero-frequency factors of an axial `S₁` term. -/
theorem norm_cglProposition51FibreEqualCharacterOffDiagonalTriple_axialAnalytic_le
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ)
    (u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P)
    (m : CGLProposition51PuncturedFrequency) :
    ‖cglProposition51AxialAnalyticAmplitude w N (cglLemma45FibreModulus q)
      (P.ordinate u.1.1 - P.ordinate u.1.2.1)
      (P.ordinate u.1.2.1 - P.ordinate u.1.2.2)
      (P.ordinate u.1.2.2 - P.ordinate u.1.1) m.val‖ ≤
      cglProposition51FibreAxialAnalyticBudget P w N n *
        ‖cglProposition51AxialNonzeroFourierAmplitude w N (cglLemma45FibreModulus q)
          (P.ordinate u.1.2.2 - P.ordinate u.1.1) m‖ := by
  let Q := cglLemma45FibreModulus q
  let U : ℝ := cglAffineFourierScale N Q *
    cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0
  let D : ℝ := cglAffineFourierScale N Q *
    (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n / P.spacing ^ n)
  let A₁ := cglLemma45ZeroModePairAmplitude w N Q (P.ordinate u.1.1 - P.ordinate u.1.2.1)
  let A₂ := cglLemma45ZeroModePairAmplitude w N Q (P.ordinate u.1.2.1 - P.ordinate u.1.2.2)
  let A₃ := cglProposition51AxialNonzeroFourierAmplitude w N Q
    (P.ordinate u.1.2.2 - P.ordinate u.1.1) m
  have huniform (t : ℝ) : ‖cglLemma45ZeroModePairAmplitude w N Q t‖ ≤ U := by
    simpa [U] using norm_cglLemma45ZeroModePairAmplitude_le_uniform w N Q t
  have hU : 0 ≤ U := (norm_nonneg _).trans (huniform 0)
  change ‖A₁ * A₂ * A₃‖ ≤ D * U * ‖A₃‖
  rw [norm_mul, norm_mul]
  by_cases hrs : u.1.1 ≠ u.1.2.1
  · let rs : CGLLemma45SameCharacterOffDiagonalPair P :=
      ⟨(u.1.1, u.1.2.1), hrs, u.2.2.1⟩
    have hdecay : ‖A₁‖ ≤ D := by
      simpa [A₁, D, rs] using
        norm_cglLemma45FibrePair_zeroModeAmplitude_le_reciprocal P w N n rs
    have hD : 0 ≤ D := (norm_nonneg _).trans hdecay
    calc
      ‖A₁‖ * ‖A₂‖ * ‖A₃‖ ≤ D * ‖A₂‖ * ‖A₃‖ := by
        gcongr
      _ ≤ D * U * ‖A₃‖ := by
        gcongr
        exact huniform _
  · have hrs_eq : u.1.1 = u.1.2.1 := not_not.mp hrs
    have hst : u.1.2.1 ≠ u.1.2.2 := by
      intro hst
      exact u.2.1 ⟨hrs_eq, hst⟩
    let st : CGLLemma45SameCharacterOffDiagonalPair P :=
      ⟨(u.1.2.1, u.1.2.2), hst, u.2.2.2⟩
    have hdecay : ‖A₂‖ ≤ D := by
      simpa [A₂, D, st] using
        norm_cglLemma45FibrePair_zeroModeAmplitude_le_reciprocal P w N n st
    have hD : 0 ≤ D := (norm_nonneg _).trans hdecay
    calc
      ‖A₁‖ * ‖A₂‖ * ‖A₃‖ ≤ U * ‖A₂‖ * ‖A₃‖ := by
        gcongr
        exact huniform _
      _ ≤ U * D * ‖A₃‖ := by
        gcongr
      _ = D * U * ‖A₃‖ := by ring

end RHTower
