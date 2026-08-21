/-
# Chen--Gupta--Li Lemma 4.5 fibrewise zero-mode decay

Connects CGL's existing source-correct fibrewise-separated character packet
to the zero-frequency expansion.  An equal-character non-all-equal row triple
has a certified nonzero adjacent time gap; one coordinate receives arbitrary
reciprocal Fourier decay and the other two receive the closed order-zero
bound from Lemma 4.3.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45ZeroModeDecay
import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketFibreSeparation

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The literal positive modulus underlying a CGL fibrewise packet. -/
def cglLemma45FibreModulus (q : ℕ) : CGLPositiveModulus :=
  { value := q + 1, positive := Nat.succ_pos q }

/-- The CGL Lemma 4.5 rows carried by a fibrewise-separated packet. -/
def cglLemma45FibreRows {q R : ℕ} (P : CGLFibreSeparatedPacket q R) :
    Fin R → CGLCharacterDyadicRowData (cglLemma45FibreModulus q).value :=
  fun r => { time := P.ordinate r, character := P.character r }

/-- A distinct finite row pair carrying the same character.  The equality and
distinctness are retained in the subtype, so the reciprocal-decay theorem has
no external separation premise. -/
def CGLLemma45SameCharacterOffDiagonalPair {q R : ℕ} (P : CGLFibreSeparatedPacket q R) :=
  {rs : Fin R × Fin R // rs.1 ≠ rs.2 ∧ P.character rs.1 = P.character rs.2}

/-- The certified gap attached to a same-character off-diagonal row pair. -/
def cglLemma45FibrePairDifference {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (rs : CGLLemma45SameCharacterOffDiagonalPair P) : CGLLemma45SeparatedDifference :=
  { difference := P.ordinate rs.1.1 - P.ordinate rs.1.2
    spacing := P.spacing
    spacing_pos := P.spacing_pos
    spacing_le_abs := cglFibreSeparatedPacket_sameCharacter_separation P rs.1.1 rs.1.2
      rs.2.1 rs.2.2 }

/-- A same-character off-diagonal pair supplies the CGL Lemma 4.3(2)
reciprocal estimate for its exact zero-frequency Poisson coordinate. -/
theorem norm_cglLemma45FibrePair_zeroModeAmplitude_le_reciprocal
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ)
    (rs : CGLLemma45SameCharacterOffDiagonalPair P) :
    ‖cglLemma45ZeroModePairAmplitude w N (cglLemma45FibreModulus q)
        (P.ordinate rs.1.1 - P.ordinate rs.1.2)‖ ≤
      cglAffineFourierScale N (cglLemma45FibreModulus q) *
        (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n / P.spacing ^ n) := by
  simpa [cglLemma45FibrePairDifference] using
    norm_cglLemma45ZeroModePairAmplitude_le_reciprocal w N (cglLemma45FibreModulus q) n
      (cglLemma45FibrePairDifference P rs)

/-- A non-all-equal row triple whose three row characters agree.  This is the
only nonzero character configuration remaining after CGL zero-mode
orthogonality. -/
def CGLLemma45FibreEqualCharacterOffDiagonalTriple {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) :=
  {rst : Fin R × Fin R × Fin R //
    ¬ (rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2) ∧
      P.character rst.1 = P.character rst.2.1 ∧
        P.character rst.2.1 = P.character rst.2.2}

/-- Explicit three-coordinate analytic budget for CGL's zero-frequency
same-character off-diagonal row term: one reciprocal factor and two
order-zero factors. -/
def cglLemma45FibreTripleDecayBudget {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) : ℝ :=
  (cglAffineFourierScale N (cglLemma45FibreModulus q) *
    (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n / P.spacing ^ n)) *
      (cglAffineFourierScale N (cglLemma45FibreModulus q) *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0) *
      (cglAffineFourierScale N (cglLemma45FibreModulus q) *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0)

/-- **CGL Lemma 4.5, separated equal-character zero-mode estimate.** Every
surviving non-all-equal row triple has one certified separated adjacent time
difference.  That coordinate receives order-`n` reciprocal decay; the other
two receive the closed order-zero budget. -/
theorem norm_cglLemma45FibreEqualCharacterOffDiagonalTriple_analytic_le
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ)
    (u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P) :
    ‖cglLemma45ZeroModeTripleAnalyticAmplitude w N (cglLemma45FibreModulus q)
      (P.ordinate u.1.1 - P.ordinate u.1.2.1)
      (P.ordinate u.1.2.1 - P.ordinate u.1.2.2)
      (P.ordinate u.1.2.2 - P.ordinate u.1.1)‖ ≤
      cglLemma45FibreTripleDecayBudget P w N n := by
  let Q := cglLemma45FibreModulus q
  let U : ℝ := cglAffineFourierScale N Q *
    cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0
  let D : ℝ := cglAffineFourierScale N Q *
    (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n / P.spacing ^ n)
  have huniform (t : ℝ) : ‖cglLemma45ZeroModePairAmplitude w N Q t‖ ≤ U := by
    simpa [U] using norm_cglLemma45ZeroModePairAmplitude_le_uniform w N Q t
  have hU : 0 ≤ U := (norm_nonneg _).trans (huniform 0)
  unfold cglLemma45ZeroModeTripleAnalyticAmplitude
  rw [norm_mul, norm_mul]
  by_cases hrs : u.1.1 ≠ u.1.2.1
  · let rs : CGLLemma45SameCharacterOffDiagonalPair P :=
      ⟨(u.1.1, u.1.2.1), hrs, u.2.2.1⟩
    have hdecay : ‖cglLemma45ZeroModePairAmplitude w N Q
        (P.ordinate u.1.1 - P.ordinate u.1.2.1)‖ ≤ D := by
      simpa [D, rs] using norm_cglLemma45FibrePair_zeroModeAmplitude_le_reciprocal P w N n rs
    have hD : 0 ≤ D := (norm_nonneg _).trans hdecay
    calc
      _ ≤ D * ‖cglLemma45ZeroModePairAmplitude w N Q
          (P.ordinate u.1.2.1 - P.ordinate u.1.2.2)‖ *
          ‖cglLemma45ZeroModePairAmplitude w N Q
            (P.ordinate u.1.2.2 - P.ordinate u.1.1)‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right hdecay (norm_nonneg _)
        · exact norm_nonneg _
      _ ≤ D * U * ‖cglLemma45ZeroModePairAmplitude w N Q
          (P.ordinate u.1.2.2 - P.ordinate u.1.1)‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (huniform _) hD
        · exact norm_nonneg _
      _ ≤ D * U * U := by
        apply mul_le_mul_of_nonneg_left (huniform _)
        exact mul_nonneg hD hU
      _ = cglLemma45FibreTripleDecayBudget P w N n := by
        change D * U * U = D * U * U
        rfl
  · have hrs_eq : u.1.1 = u.1.2.1 := not_not.mp hrs
    have hst : u.1.2.1 ≠ u.1.2.2 := by
      intro hst
      exact u.2.1 ⟨hrs_eq, hst⟩
    let st : CGLLemma45SameCharacterOffDiagonalPair P :=
      ⟨(u.1.2.1, u.1.2.2), hst, u.2.2.2⟩
    have hdecay : ‖cglLemma45ZeroModePairAmplitude w N Q
        (P.ordinate u.1.2.1 - P.ordinate u.1.2.2)‖ ≤ D := by
      simpa [D, st] using norm_cglLemma45FibrePair_zeroModeAmplitude_le_reciprocal P w N n st
    have hD : 0 ≤ D := (norm_nonneg _).trans hdecay
    calc
      _ ≤ U * ‖cglLemma45ZeroModePairAmplitude w N Q
          (P.ordinate u.1.2.1 - P.ordinate u.1.2.2)‖ *
          ‖cglLemma45ZeroModePairAmplitude w N Q
            (P.ordinate u.1.2.2 - P.ordinate u.1.1)‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right (huniform _) (norm_nonneg _)
        · exact norm_nonneg _
      _ ≤ U * D * ‖cglLemma45ZeroModePairAmplitude w N Q
          (P.ordinate u.1.2.2 - P.ordinate u.1.1)‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hdecay hU
        · exact norm_nonneg _
      _ ≤ U * D * U := by
        apply mul_le_mul_of_nonneg_left (huniform _)
        exact mul_nonneg hU hD
      _ = cglLemma45FibreTripleDecayBudget P w N n := by
        change U * D * U = D * U * U
        ring

end RHTower
