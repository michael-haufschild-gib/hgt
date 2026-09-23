/-
# Chen--Gupta--Li Proposition 5.1 axial row bound

Combines the finite character factor bound with the certified separated-gap
analytic estimate for every surviving equal-character off-diagonal row triple.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51AxialAnalytic

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- A surviving equal-character axial row term is bounded by the cubic
modulus factor times its certified reciprocal-decay analytic tail. -/
theorem norm_cglProposition51AxialRowTerm_fibre_le
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ)
    (u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P)
    (m : CGLProposition51PuncturedFrequency) :
    ‖cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) u.1 m.val‖ ≤
      ((cglLemma45FibreModulus q).value : ℝ) ^ (3 : ℕ) *
        cglProposition51FibreAxialAnalyticBudget P w N n *
          ‖cglProposition51AxialNonzeroFourierAmplitude w N (cglLemma45FibreModulus q)
            (P.ordinate u.1.2.2 - P.ordinate u.1.1) m‖ := by
  have hchar1 : (cglLemma45FibreRows P u.1.1).character =
      (cglLemma45FibreRows P u.1.2.1).character := u.2.2.1
  have hchar2 : (cglLemma45FibreRows P u.1.2.1).character =
      (cglLemma45FibreRows P u.1.2.2).character := u.2.2.2
  have hchar1' : P.character u.1.1 = P.character u.1.2.1 := u.2.2.1
  have hchar2' : P.character u.1.2.1 = P.character u.1.2.2 := u.2.2.2
  have hphi : (((cglLemma45FibreModulus q).value.totient : ℝ)) ≤
      (cglLemma45FibreModulus q).value := by
    exact_mod_cast Nat.totient_le (cglLemma45FibreModulus q).value
  have hphi0 : 0 ≤ ((cglLemma45FibreModulus q).value.totient : ℝ) := by positivity
  have hQ0 : 0 ≤ ((cglLemma45FibreModulus q).value : ℝ) := by positivity
  have htwist : ‖cglProposition51AxialTwistedCharacterFactor (cglLemma45FibreModulus q)
      (cglLemma45FibreRows P u.1.2.2).character
      (cglLemma45FibreRows P u.1.1).character m.val‖ ≤ (cglLemma45FibreModulus q).value := by
    exact norm_cglProposition51AxialTwistedCharacterFactor_le (cglLemma45FibreModulus q)
      (P.character u.1.2.2) (P.character u.1.1) m.val
  have hanalytic := norm_cglProposition51FibreEqualCharacterOffDiagonalTriple_axialAnalytic_le
    P w N n u m
  rw [show cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) u.1 m.val =
      (((cglLemma45FibreModulus q).value.totient : ℂ) *
        ((cglLemma45FibreModulus q).value.totient : ℂ) *
        cglProposition51AxialTwistedCharacterFactor (cglLemma45FibreModulus q)
          (P.character u.1.2.2) (P.character u.1.1) m.val) *
          cglProposition51AxialAnalyticAmplitude w N (cglLemma45FibreModulus q)
            (P.ordinate u.1.1 - P.ordinate u.1.2.1)
            (P.ordinate u.1.2.1 - P.ordinate u.1.2.2)
            (P.ordinate u.1.2.2 - P.ordinate u.1.1) m.val by
      simp [cglProposition51AxialRowTerm, cglLemma45FibreRows, hchar1', hchar2']
      ]
  rw [norm_mul, norm_mul, norm_mul]
  norm_num
  calc
    ((cglLemma45FibreModulus q).value.totient : ℝ) *
        ((cglLemma45FibreModulus q).value.totient : ℝ) *
          ‖cglProposition51AxialTwistedCharacterFactor (cglLemma45FibreModulus q)
            (P.character u.1.2.2) (P.character u.1.1) m.val‖ *
        ‖cglProposition51AxialAnalyticAmplitude w N (cglLemma45FibreModulus q)
          (P.ordinate u.1.1 - P.ordinate u.1.2.1)
          (P.ordinate u.1.2.1 - P.ordinate u.1.2.2)
          (P.ordinate u.1.2.2 - P.ordinate u.1.1) m.val‖ ≤
      ((cglLemma45FibreModulus q).value : ℝ) ^ (3 : ℕ) *
        ‖cglProposition51AxialAnalyticAmplitude w N (cglLemma45FibreModulus q)
          (P.ordinate u.1.1 - P.ordinate u.1.2.1)
          (P.ordinate u.1.2.1 - P.ordinate u.1.2.2)
          (P.ordinate u.1.2.2 - P.ordinate u.1.1) m.val‖ := by
        have hmain : ((cglLemma45FibreModulus q).value.totient : ℝ) *
            ((cglLemma45FibreModulus q).value.totient : ℝ) *
            ‖cglProposition51AxialTwistedCharacterFactor (cglLemma45FibreModulus q)
              (P.character u.1.2.2) (P.character u.1.1) m.val‖ ≤
                ((cglLemma45FibreModulus q).value : ℝ) ^ (3 : ℕ) := by
          calc
            ((cglLemma45FibreModulus q).value.totient : ℝ) *
                ((cglLemma45FibreModulus q).value.totient : ℝ) *
                ‖cglProposition51AxialTwistedCharacterFactor (cglLemma45FibreModulus q)
                  (P.character u.1.2.2) (P.character u.1.1) m.val‖ ≤
              ((cglLemma45FibreModulus q).value : ℝ) *
                ((cglLemma45FibreModulus q).value : ℝ) *
                  ((cglLemma45FibreModulus q).value : ℝ) := by
                gcongr
                exact htwist
            _ = ((cglLemma45FibreModulus q).value : ℝ) ^ (3 : ℕ) := by ring
        exact mul_le_mul_of_nonneg_right hmain (norm_nonneg _)
    _ ≤ ((cglLemma45FibreModulus q).value : ℝ) ^ (3 : ℕ) *
        (cglProposition51FibreAxialAnalyticBudget P w N n *
          ‖cglProposition51AxialNonzeroFourierAmplitude w N (cglLemma45FibreModulus q)
            (P.ordinate u.1.2.2 - P.ordinate u.1.1) m‖) := by
      calc
        ((cglLemma45FibreModulus q).value : ℝ) ^ (3 : ℕ) *
            ‖cglProposition51AxialAnalyticAmplitude w N (cglLemma45FibreModulus q)
              (P.ordinate u.1.1 - P.ordinate u.1.2.1)
              (P.ordinate u.1.2.1 - P.ordinate u.1.2.2)
              (P.ordinate u.1.2.2 - P.ordinate u.1.1) m.val‖ ≤
          ((cglLemma45FibreModulus q).value : ℝ) ^ (3 : ℕ) *
            (cglProposition51FibreAxialAnalyticBudget P w N n *
              ‖cglProposition51AxialNonzeroFourierAmplitude w N (cglLemma45FibreModulus q)
                (P.ordinate u.1.2.2 - P.ordinate u.1.1) m‖) := by
            gcongr
        _ = _ := by ring
    _ = _ := by ring

end RHTower
