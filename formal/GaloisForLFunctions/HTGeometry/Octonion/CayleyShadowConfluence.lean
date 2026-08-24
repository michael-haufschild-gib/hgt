import GaloisForLFunctions.HTGeometry.Octonion.Basic

/-!
# Cayley shadow confluence

The compact octonions split as two quaternionic halves.  This file fixes a quaternionic
`I, J, K` frame in the first half and a transverse Cayley--Dickson unit in the second half.
It then computes the first genuinely octonionic obstruction: the two parenthesizations of
`I * J * (phase * K + grade * ell)` agree exactly when the transverse coefficient `grade`
vanishes.  The internal quaternionic coefficient `phase` remains completely free.

This is the finite algebra needed to distinguish motion inside a four-dimensional associative
shadow from departure into its eight-dimensional alternative completion.
-/

open scoped Quaternion

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

private def cayleyFrameQuaternionI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
private def cayleyFrameQuaternionJ : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
private def cayleyFrameQuaternionK : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

/-- First generator of the distinguished quaternionic Cayley plane. -/
def cayleyFrameI : RealOctonion := mk cayleyFrameQuaternionI 0

/-- Second generator of the distinguished quaternionic Cayley plane. -/
def cayleyFrameJ : RealOctonion := mk cayleyFrameQuaternionJ 0

/-- Product direction inside the distinguished quaternionic Cayley plane. -/
def cayleyFrameK : RealOctonion := mk cayleyFrameQuaternionK 0

/-- Cayley--Dickson unit transverse to the distinguished quaternionic half. -/
def cayleyFrameTransverse : RealOctonion := mk 0 1

/-- Nonzero associator direction exposed by leaving the quaternionic half. -/
def cayleyAssociatorWitness : RealOctonion :=
  mk 0 (cayleyFrameQuaternionK + cayleyFrameQuaternionK)

private theorem cayleyFrameI_mul_J : cayleyFrameI * cayleyFrameJ = cayleyFrameK := by
  apply ext
  · change cayleyFrameQuaternionI * cayleyFrameQuaternionJ - star (0 : ℍ[ℝ]) * 0 =
      cayleyFrameQuaternionK
    ext <;> norm_num [cayleyFrameQuaternionI, cayleyFrameQuaternionJ,
      cayleyFrameQuaternionK]
  · change (0 : ℍ[ℝ]) * cayleyFrameQuaternionI +
      0 * star cayleyFrameQuaternionJ = 0
    simp

private theorem cayleyFrameJ_mul_K : cayleyFrameJ * cayleyFrameK = cayleyFrameI := by
  apply ext
  · change cayleyFrameQuaternionJ * cayleyFrameQuaternionK - star (0 : ℍ[ℝ]) * 0 =
      cayleyFrameQuaternionI
    ext <;> norm_num [cayleyFrameQuaternionI, cayleyFrameQuaternionJ,
      cayleyFrameQuaternionK]
  · change (0 : ℍ[ℝ]) * cayleyFrameQuaternionJ +
      0 * star cayleyFrameQuaternionK = 0
    simp

private theorem cayleyFrameI_sq : cayleyFrameI * cayleyFrameI = -1 := by
  apply ext
  · change cayleyFrameQuaternionI * cayleyFrameQuaternionI - star (0 : ℍ[ℝ]) * 0 = -1
    ext <;> norm_num [cayleyFrameQuaternionI]
  · simp [cayleyFrameI, mul_snd]

private theorem cayleyFrameK_sq : cayleyFrameK * cayleyFrameK = -1 := by
  apply ext
  · change cayleyFrameQuaternionK * cayleyFrameQuaternionK - star (0 : ℍ[ℝ]) * 0 = -1
    ext <;> norm_num [cayleyFrameQuaternionK]
  · simp [cayleyFrameK, mul_snd]

private theorem cayleyFrameK_mul_transverse :
    cayleyFrameK * cayleyFrameTransverse = mk 0 cayleyFrameQuaternionK := by
  apply ext
  · change cayleyFrameQuaternionK * 0 - star (1 : ℍ[ℝ]) * 0 = 0
    simp
  · change (1 : ℍ[ℝ]) * cayleyFrameQuaternionK + 0 * star 0 = cayleyFrameQuaternionK
    simp

private theorem cayleyFrameJ_mul_transverse :
    cayleyFrameJ * cayleyFrameTransverse = mk 0 cayleyFrameQuaternionJ := by
  apply ext
  · change cayleyFrameQuaternionJ * 0 - star (1 : ℍ[ℝ]) * 0 = 0
    simp
  · change (1 : ℍ[ℝ]) * cayleyFrameQuaternionJ + 0 * star 0 = cayleyFrameQuaternionJ
    simp

private theorem cayleyFrameI_mul_zero_J :
    cayleyFrameI * mk 0 cayleyFrameQuaternionJ = mk 0 (-cayleyFrameQuaternionK) := by
  apply ext
  · change cayleyFrameQuaternionI * 0 - star cayleyFrameQuaternionJ * 0 = 0
    simp
  · change cayleyFrameQuaternionJ * cayleyFrameQuaternionI + 0 * star 0 =
      -cayleyFrameQuaternionK
    ext <;> norm_num [cayleyFrameQuaternionI, cayleyFrameQuaternionJ,
      cayleyFrameQuaternionK]

/-- Three directions inside the quaternionic Cayley plane associate. -/
theorem cayleyInternalAssociator_zero :
    IsAlternative.associator cayleyFrameI cayleyFrameJ cayleyFrameK = 0 := by
  simp [IsAlternative.associator, cayleyFrameI_mul_J, cayleyFrameJ_mul_K,
    cayleyFrameI_sq, cayleyFrameK_sq]

/-- A transverse Cayley--Dickson direction exposes a fixed nonzero associator. -/
theorem cayleyTransverseAssociator :
    IsAlternative.associator cayleyFrameI cayleyFrameJ cayleyFrameTransverse =
      cayleyAssociatorWitness := by
  rw [IsAlternative.associator, cayleyFrameI_mul_J, cayleyFrameK_mul_transverse,
    cayleyFrameJ_mul_transverse, cayleyFrameI_mul_zero_J]
  apply ext
  · change (0 : ℍ[ℝ]) - 0 = 0
    simp
  · change cayleyFrameQuaternionK - (-cayleyFrameQuaternionK) =
      cayleyFrameQuaternionK + cayleyFrameQuaternionK
    abel

/-- The transverse associator direction is genuinely nonzero. -/
theorem cayleyAssociatorWitness_ne_zero : cayleyAssociatorWitness ≠ 0 := by
  intro h
  have himK := congrArg (fun x : RealOctonion => x.2.imK) h
  norm_num [cayleyAssociatorWitness, cayleyFrameQuaternionK, mk] at himK

/-- A third direction with arbitrary internal phase and one transverse grade. -/
def cayleyTiltedThirdDirection (phase grade : ℝ) : RealOctonion :=
  phase • cayleyFrameK + grade • cayleyFrameTransverse

/-- Exact Cayley shadow law: only the transverse coefficient survives in the associator. -/
theorem cayleyTiltedAssociator (phase grade : ℝ) :
    IsAlternative.associator cayleyFrameI cayleyFrameJ
        (cayleyTiltedThirdDirection phase grade) =
      grade • cayleyAssociatorWitness := by
  rw [cayleyTiltedThirdDirection, IsAlternative.associator_add_right,
    associator_smul_right, associator_smul_right, cayleyInternalAssociator_zero,
    cayleyTransverseAssociator]
  simp

/-- Associator coherence detects exactly return to the four-dimensional quaternionic shadow. -/
theorem cayleyTiltedAssociator_eq_zero_iff (phase grade : ℝ) :
    IsAlternative.associator cayleyFrameI cayleyFrameJ
        (cayleyTiltedThirdDirection phase grade) = 0 ↔
      grade = 0 := by
  rw [cayleyTiltedAssociator]
  constructor
  · intro h
    rcases smul_eq_zero.mp h with hgrade | hwitness
    · exact hgrade
    · exact False.elim (cayleyAssociatorWitness_ne_zero hwitness)
  · rintro rfl
    simp

/-- Static two-schedule confluence holds exactly when the active carrier stays quaternionic. -/
theorem cayleyTiltedParenthesizations_confluent_iff (phase grade : ℝ) :
    (cayleyFrameI * cayleyFrameJ) * cayleyTiltedThirdDirection phase grade =
        cayleyFrameI * (cayleyFrameJ * cayleyTiltedThirdDirection phase grade) ↔
      grade = 0 := by
  rw [← sub_eq_zero, ← IsAlternative.associator]
  exact cayleyTiltedAssociator_eq_zero_iff phase grade

end

end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
