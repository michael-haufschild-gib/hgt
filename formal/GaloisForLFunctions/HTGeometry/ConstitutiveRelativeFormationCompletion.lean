import Mathlib

/-!
# Relative formation completion

A centered two-endpoint first jet has two affine-gauge invariant coordinates: symmetric response
and directed formation current.  They reconstruct both directed Bregman works.  Reflection
evenization preserves the symmetric coordinate and kills exactly the current.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Values and slopes at the two endpoints of a centered formation experiment. -/
structure CenteredFormationJet where
  leftValue : ℝ
  rightValue : ℝ
  leftSlope : ℝ
  rightSlope : ℝ

@[ext]
theorem CenteredFormationJet.extensionality {J K : CenteredFormationJet}
    (hLeftValue : J.leftValue = K.leftValue)
    (hRightValue : J.rightValue = K.rightValue)
    (hLeftSlope : J.leftSlope = K.leftSlope)
    (hRightSlope : J.rightSlope = K.rightSlope) : J = K := by
  cases J
  cases K
  simp_all

/-- Average endpoint value. -/
def CenteredFormationJet.evenValue (J : CenteredFormationJet) : ℝ :=
  (J.leftValue + J.rightValue) / 2

/-- Half-difference of endpoint slopes. -/
def CenteredFormationJet.symmetricResponse (J : CenteredFormationJet) : ℝ :=
  (J.rightSlope - J.leftSlope) / 2

/-- Average endpoint slope. -/
def CenteredFormationJet.longitudinalResponse (J : CenteredFormationJet) : ℝ :=
  (J.rightSlope + J.leftSlope) / 2

/-- Affine-invariant directed current lost by centered reflection evenization. -/
def CenteredFormationJet.formationCurrent (a : ℝ) (J : CenteredFormationJet) : ℝ :=
  a * J.longitudinalResponse - (J.rightValue - J.leftValue) / 2

/-- Bregman work directed from the left endpoint to the right endpoint. -/
def CenteredFormationJet.leftRightWork (a : ℝ) (J : CenteredFormationJet) : ℝ :=
  J.leftValue - J.rightValue + 2 * a * J.rightSlope

/-- Bregman work directed from the right endpoint to the left endpoint. -/
def CenteredFormationJet.rightLeftWork (a : ℝ) (J : CenteredFormationJet) : ℝ :=
  J.rightValue - J.leftValue - 2 * a * J.leftSlope

/-- Add the affine potential `α * t + β` at the centered endpoints `c ± a`. -/
def CenteredFormationJet.affineGauge (c a α β : ℝ)
    (J : CenteredFormationJet) : CenteredFormationJet where
  leftValue := J.leftValue + α * (c - a) + β
  rightValue := J.rightValue + α * (c + a) + β
  leftSlope := J.leftSlope + α
  rightSlope := J.rightSlope + α

/-- Reflection evenization retains the even value and symmetric response. -/
def CenteredFormationJet.evenize (J : CenteredFormationJet) : CenteredFormationJet where
  leftValue := J.evenValue
  rightValue := J.evenValue
  leftSlope := -J.symmetricResponse
  rightSlope := J.symmetricResponse

/-- Two centered jets are affine-gauge equivalent at center `c` and half-span `a`. -/
def CenteredFormationJet.AffinelyEquivalent (c a : ℝ)
    (J K : CenteredFormationJet) : Prop :=
  ∃ α β : ℝ, J.affineGauge c a α β = K

namespace CenteredFormationJet

/-- Full value-and-slope reconstruction from even, symmetric, longitudinal, and current data. -/
theorem reconstruct (a : ℝ) (J : CenteredFormationJet) :
    J.rightValue = J.evenValue + a * J.longitudinalResponse - J.formationCurrent a ∧
      J.leftValue = J.evenValue - a * J.longitudinalResponse + J.formationCurrent a ∧
      J.rightSlope = J.longitudinalResponse + J.symmetricResponse ∧
      J.leftSlope = J.longitudinalResponse - J.symmetricResponse := by
  simp only [evenValue, longitudinalResponse, symmetricResponse, formationCurrent]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The two directed Bregman works are reconstructed by symmetric response and current. -/
theorem leftRightWork_eq (a : ℝ) (J : CenteredFormationJet) :
    J.leftRightWork a = 2 * a * J.symmetricResponse + 2 * J.formationCurrent a := by
  simp [leftRightWork, symmetricResponse, formationCurrent, longitudinalResponse]
  ring

theorem rightLeftWork_eq (a : ℝ) (J : CenteredFormationJet) :
    J.rightLeftWork a = 2 * a * J.symmetricResponse - 2 * J.formationCurrent a := by
  simp [rightLeftWork, symmetricResponse, formationCurrent, longitudinalResponse]
  ring

/-- Symmetric work retains only the even response coordinate. -/
theorem work_sum_eq (a : ℝ) (J : CenteredFormationJet) :
    J.leftRightWork a + J.rightLeftWork a = 4 * a * J.symmetricResponse := by
  rw [leftRightWork_eq, rightLeftWork_eq]
  ring

/-- Directed work asymmetry is exactly four times the formation current. -/
theorem work_difference_eq (a : ℝ) (J : CenteredFormationJet) :
    J.leftRightWork a - J.rightLeftWork a = 4 * J.formationCurrent a := by
  rw [leftRightWork_eq, rightLeftWork_eq]
  ring

@[simp] theorem symmetricResponse_affineGauge (c a α β : ℝ) (J : CenteredFormationJet) :
    (J.affineGauge c a α β).symmetricResponse = J.symmetricResponse := by
  simp [affineGauge, symmetricResponse]

@[simp] theorem longitudinalResponse_affineGauge (c a α β : ℝ) (J : CenteredFormationJet) :
    (J.affineGauge c a α β).longitudinalResponse = J.longitudinalResponse + α := by
  simp [affineGauge, longitudinalResponse]
  ring

@[simp] theorem evenValue_affineGauge (c a α β : ℝ) (J : CenteredFormationJet) :
    (J.affineGauge c a α β).evenValue = J.evenValue + α * c + β := by
  simp [affineGauge, evenValue]
  ring

@[simp] theorem formationCurrent_affineGauge (c a α β : ℝ) (J : CenteredFormationJet) :
    (J.affineGauge c a α β).formationCurrent a = J.formationCurrent a := by
  simp [affineGauge, formationCurrent, longitudinalResponse]
  ring

@[simp] theorem leftRightWork_affineGauge (c a α β : ℝ) (J : CenteredFormationJet) :
    (J.affineGauge c a α β).leftRightWork a = J.leftRightWork a := by
  simp [affineGauge, leftRightWork]
  ring

@[simp] theorem rightLeftWork_affineGauge (c a α β : ℝ) (J : CenteredFormationJet) :
    (J.affineGauge c a α β).rightLeftWork a = J.rightLeftWork a := by
  simp [affineGauge, rightLeftWork]
  ring

/-- The pair `(symmetricResponse, formationCurrent)` is the complete affine-gauge quotient. -/
theorem affinelyEquivalent_iff (c a : ℝ) (J K : CenteredFormationJet) :
    J.AffinelyEquivalent c a K ↔
      J.symmetricResponse = K.symmetricResponse ∧
        J.formationCurrent a = K.formationCurrent a := by
  constructor
  · rintro ⟨α, β, rfl⟩
    simp
  · rintro ⟨hS, hH⟩
    let α := K.longitudinalResponse - J.longitudinalResponse
    let β := K.evenValue - J.evenValue - α * c
    refine ⟨α, β, ?_⟩
    apply CenteredFormationJet.extensionality
    · have hJ := (reconstruct a J).2.1
      have hK := (reconstruct a K).2.1
      simp only [affineGauge]
      rw [hJ, hK]
      simp only [α, β]
      rw [hH]
      ring
    · have hJ := (reconstruct a J).1
      have hK := (reconstruct a K).1
      simp only [affineGauge]
      rw [hJ, hK]
      simp only [α, β]
      rw [hH]
      ring
    · have hJ := (reconstruct a J).2.2.2
      have hK := (reconstruct a K).2.2.2
      simp only [affineGauge]
      rw [hJ, hK]
      simp only [α]
      rw [hS]
      ring
    · have hJ := (reconstruct a J).2.2.1
      have hK := (reconstruct a K).2.2.1
      simp only [affineGauge]
      rw [hJ, hK]
      simp only [α]
      rw [hS]
      ring

/-- Positivity of both directed works is exactly the closed Lorentz wedge. -/
theorem nonnegative_works_iff {a : ℝ} (ha : 0 < a) (J : CenteredFormationJet) :
    0 ≤ J.leftRightWork a ∧ 0 ≤ J.rightLeftWork a ↔
      0 ≤ J.symmetricResponse ∧ |J.formationCurrent a| ≤ a * J.symmetricResponse := by
  rw [leftRightWork_eq, rightLeftWork_eq]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · nlinarith
    · rw [abs_le]
      constructor <;> linarith
  · rintro ⟨hS, hH⟩
    rw [abs_le] at hH
    constructor <;> linarith

@[simp] theorem symmetricResponse_evenize (J : CenteredFormationJet) :
    J.evenize.symmetricResponse = J.symmetricResponse := by
  simp [evenize, symmetricResponse]

@[simp] theorem longitudinalResponse_evenize (J : CenteredFormationJet) :
    J.evenize.longitudinalResponse = 0 := by
  simp [evenize, longitudinalResponse]

@[simp] theorem formationCurrent_evenize (a : ℝ) (J : CenteredFormationJet) :
    J.evenize.formationCurrent a = 0 := by
  rw [formationCurrent, longitudinalResponse_evenize]
  simp [evenize]

@[simp] theorem evenize_idempotent (J : CenteredFormationJet) :
    J.evenize.evenize = J.evenize := by
  ext <;> simp [evenize, evenValue, symmetricResponse]

/-- Even completion preserves symmetric work and makes both directions equal. -/
theorem evenize_directed_works (a : ℝ) (J : CenteredFormationJet) :
    J.evenize.leftRightWork a = 2 * a * J.symmetricResponse ∧
      J.evenize.rightLeftWork a = 2 * a * J.symmetricResponse := by
  rw [leftRightWork_eq, rightLeftWork_eq]
  simp

/-- The exact finite formation/completion certificate. -/
theorem relativeFormationCompletion_capstone (c : ℝ) {a : ℝ} (ha : 0 < a)
    (J K : CenteredFormationJet) :
    (J.leftRightWork a - J.rightLeftWork a = 4 * J.formationCurrent a) ∧
      (J.evenize.leftRightWork a = J.evenize.rightLeftWork a) ∧
      (J.AffinelyEquivalent c a K ↔
        J.symmetricResponse = K.symmetricResponse ∧
          J.formationCurrent a = K.formationCurrent a) ∧
      (0 ≤ J.leftRightWork a ∧ 0 ≤ J.rightLeftWork a ↔
        0 ≤ J.symmetricResponse ∧ |J.formationCurrent a| ≤ a * J.symmetricResponse) := by
  exact ⟨work_difference_eq a J,
    (evenize_directed_works a J).1.trans (evenize_directed_works a J).2.symm,
    affinelyEquivalent_iff c a J K,
    nonnegative_works_iff ha J⟩

end CenteredFormationJet

end

end GaloisForLFunctions.HTGeometry
