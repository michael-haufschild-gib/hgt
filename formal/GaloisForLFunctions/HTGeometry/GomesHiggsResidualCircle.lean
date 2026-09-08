import GaloisForLFunctions.HTGeometry.GomesHiggsOrbitClassification
import GaloisForLFunctions.HTGeometry.GomesWeakInvariantTensors

/-!
# The full residual unitary circle at the actual Higgs doublet

Gomes, arXiv:2509.25276v7, Proposition 1, identifies the complementary-line
phase as the stabilizer of a nonvanishing rank-two Higgs field. Existing
radial-orbit transport and the proved north-pole stabilizer now give an exact
classification at every doublet. The zero orbit retains the full unitary group.
The transported phase action is faithful and respects the circle group law.
This module makes a pointwise choice of radial gauge, without a regularity claim.
-/

open scoped Matrix ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The actual doublet norm vanishes precisely at the singular zero orbit. -/
theorem higgs_normSq_eq_zero_iff (H : Fin 2 → ℂ) :
    abelianHiggsSpinorNormSq H = 0 ↔ H = 0 := by
  constructor
  · intro h
    have h0 := Complex.normSq_nonneg (H 0)
    have h1 := Complex.normSq_nonneg (H 1)
    change Complex.normSq (H 0) + Complex.normSq (H 1) = 0 at h
    have hz0 : H 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
    have hz1 : H 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
    funext i
    fin_cases i <;> assumption
  · rintro rfl
    simp [abelianHiggsSpinorNormSq]

/-- A unitary choice of the already-proved radial transport. -/
def higgsRadialGauge (H : Fin 2 → ℂ) : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨Classical.choose (higgs_specialUnitary_radial_representative H),
    Matrix.specialUnitaryGroup_le_unitaryGroup
      (Classical.choose_spec (higgs_specialUnitary_radial_representative H)).1⟩

theorem higgsRadialGauge_apply (H : Fin 2 → ℂ) :
    (higgsRadialGauge H : Matrix (Fin 2) (Fin 2) ℂ).mulVec H = higgsRadialRepresentative H :=
  (Classical.choose_spec (higgs_specialUnitary_radial_representative H)).2

/-- A phase acting only on the line orthogonal to the north doublet. -/
def weakPerpendicularPhase (z : Circle) : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨!![1,0;0,(z:ℂ)], by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.normSq_eq_conj_mul_self]⟩

/-- Canonically transported residual phase at a doublet. -/
def higgsResidualPhase (H : Fin 2 → ℂ) (z : Circle) : Matrix.unitaryGroup (Fin 2) ℂ :=
  (higgsRadialGauge H)⁻¹ * weakPerpendicularPhase z * higgsRadialGauge H

/-- The radial representative is a real nonnegative multiple of the north spinor. -/
theorem higgsRadialRepresentative_smul (H : Fin 2 → ℂ) :
    higgsRadialRepresentative H = (Real.sqrt (abelianHiggsSpinorNormSq H) : ℂ) •
      (![1,0] : Fin 2 → ℂ) := by
  funext i
  fin_cases i <;> simp [higgsRadialRepresentative]

/-- Radial amplitude is zero exactly on the singular orbit. -/
theorem higgs_radial_amplitude_eq_zero_iff (H : Fin 2 → ℂ) :
    (Real.sqrt (abelianHiggsSpinorNormSq H) : ℂ) = 0 ↔ H = 0 := by
  have hn : 0 ≤ abelianHiggsSpinorNormSq H :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  rw [Complex.ofReal_eq_zero, Real.sqrt_eq_zero hn, higgs_normSq_eq_zero_iff]

/-- At any radial doublet, the residual phase fixes the complete representative. -/
theorem weakPerpendicularPhase_fixes_radial (H : Fin 2 → ℂ) (z : Circle) :
    (weakPerpendicularPhase z : Matrix (Fin 2) (Fin 2) ℂ).mulVec (higgsRadialRepresentative H) =
      higgsRadialRepresentative H := by
  funext i
  fin_cases i <;> simp [weakPerpendicularPhase, higgsRadialRepresentative, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

/-- Every transported phase fixes its original doublet, including the zero case. -/
theorem higgsResidualPhase_fixes (H : Fin 2 → ℂ) (z : Circle) :
    (higgsResidualPhase H z : Matrix (Fin 2) (Fin 2) ℂ).mulVec H = H := by
  let B := higgsRadialGauge H
  have hinv : ((B⁻¹ : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      (B : Matrix (Fin 2) (Fin 2) ℂ) = 1 := congrArg Subtype.val (inv_mul_cancel B)
  change (((B⁻¹).val * (weakPerpendicularPhase z).val) * (B.val : Matrix (Fin 2) (Fin 2) ℂ)).mulVec H = H
  rw [← Matrix.mulVec_mulVec, higgsRadialGauge_apply, ← Matrix.mulVec_mulVec,
    weakPerpendicularPhase_fixes_radial, ← higgsRadialGauge_apply,
    Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

/-- Conjugating by radial transport identifies the original and radial fixed-vector problems. -/
theorem higgs_unitary_radial_stabilizer_equivalence
    (U : Matrix.unitaryGroup (Fin 2) ℂ) (H : Fin 2 → ℂ) :
    (U : Matrix (Fin 2) (Fin 2) ℂ).mulVec H = H ↔
      ((higgsRadialGauge H * U * (higgsRadialGauge H)⁻¹ : Matrix.unitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ).mulVec (higgsRadialRepresentative H) = higgsRadialRepresentative H := by
  let B := higgsRadialGauge H
  have hinv : ((B⁻¹ : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      (B : Matrix (Fin 2) (Fin 2) ℂ) = 1 := congrArg Subtype.val (inv_mul_cancel B)
  have he : ((B * U * B⁻¹ : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).mulVec
      (higgsRadialRepresentative H) = (B : Matrix (Fin 2) (Fin 2) ℂ).mulVec
        ((U : Matrix (Fin 2) (Fin 2) ℂ).mulVec H) := by
    rw [← higgsRadialGauge_apply]
    simp only [Matrix.mulVec_mulVec]
    change ((B.val * U.val * (B⁻¹).val) * (B.val : Matrix (Fin 2) (Fin 2) ℂ)).mulVec H = _
    rw [Matrix.mul_assoc (B.val * U.val), hinv, Matrix.mul_one]
  rw [he, ← higgsRadialGauge_apply]
  constructor
  · intro h
    rw [h]
  · intro h
    have hh := congrArg (fun v => ((B⁻¹ : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).mulVec v) h
    change (B⁻¹).val.mulVec (B.val.mulVec (U.val.mulVec H)) =
      (B⁻¹).val.mulVec (B.val.mulVec H) at hh
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hinv, Matrix.one_mul,
      Matrix.one_mulVec] using hh

/-- The complete geometric stabilizer at every actual Higgs doublet. -/
theorem higgs_unitary_stabilizer_classification
    (U : Matrix.unitaryGroup (Fin 2) ℂ) (H : Fin 2 → ℂ) :
    (U : Matrix (Fin 2) (Fin 2) ℂ).mulVec H = H ↔
      H = 0 ∨ ∃ z : Circle, U = higgsResidualPhase H z := by
  constructor
  · intro h
    by_cases hH : H = 0
    · exact Or.inl hH
    · right
      let B := higgsRadialGauge H
      let V := B * U * B⁻¹
      have hv := (higgs_unitary_radial_stabilizer_equivalence U H).mp h
      rw [higgsRadialRepresentative_smul, Matrix.mulVec_smul] at hv
      have hn := (higgs_radial_amplitude_eq_zero_iff H).not.mpr hH
      have hv0 : (V : Matrix (Fin 2) (Fin 2) ℂ).mulVec ![1,0] = ![1,0] := by
        exact (smul_right_injective _ hn) hv
      obtain ⟨z,hz⟩ := (weak_unitary_stabilizer_north V).mp hv0
      have hV : V = weakPerpendicularPhase z := Subtype.ext hz
      refine ⟨z, ?_⟩
      change U = B⁻¹ * weakPerpendicularPhase z * B
      rw [← hV]
      dsimp only [V]
      group
  · rintro (rfl | ⟨z,rfl⟩)
    · simp
    · exact higgsResidualPhase_fixes H z

/-- The residual coordinate respects multiplication of phases. -/
theorem weakPerpendicularPhase_mul (z w : Circle) :
    weakPerpendicularPhase (z*w) = weakPerpendicularPhase z * weakPerpendicularPhase w := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weakPerpendicularPhase]

/-- The complementary-line action retains the full phase information. -/
theorem weakPerpendicularPhase_injective : Function.Injective weakPerpendicularPhase := by
  intro z w h
  apply Circle.ext
  exact congrArg (fun U : Matrix.unitaryGroup (Fin 2) ℂ => U 1 1) h

/-- Transport to a doublet preserves the residual circle group law. -/
theorem higgsResidualPhase_mul (H : Fin 2 → ℂ) (z w : Circle) :
    higgsResidualPhase H (z*w) = higgsResidualPhase H z * higgsResidualPhase H w := by
  simp only [higgsResidualPhase, weakPerpendicularPhase_mul]
  group

/-- The transported residual phase is faithful at every choice of reference frame. -/
theorem higgsResidualPhase_injective (H : Fin 2 → ℂ) : Function.Injective (higgsResidualPhase H) := by
  intro z w h
  apply weakPerpendicularPhase_injective
  have hh := congrArg (fun U => higgsRadialGauge H * U * (higgsRadialGauge H)⁻¹) h
  simpa [higgsResidualPhase, mul_assoc] using hh

/-- All residual phases commute after transport to the original Higgs doublet. -/
theorem higgsResidualPhase_commute (H : Fin 2 → ℂ) (z w : Circle) :
    higgsResidualPhase H z * higgsResidualPhase H w =
      higgsResidualPhase H w * higgsResidualPhase H z := by
  rw [← higgsResidualPhase_mul, mul_comm z w, higgsResidualPhase_mul]

end GaloisForLFunctions.HTGeometry
