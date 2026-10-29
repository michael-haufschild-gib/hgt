import GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2Rotation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Contracting real degree rotations

The unit `exp(-exp r)` parametrizes all real contraction factors in `(0,1)`.
Its image in the extended loop group acts on degree-`n` root parameters by
the `n`th power of that unit, giving the actual group-level degree rotation.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

/-- A positive contraction factor, covering the full positive-rotation range. -/
def realDegreeUnit (r : ℝ) : ℝˣ :=
  Units.mk0 (Real.exp (-Real.exp r)) (ne_of_gt (Real.exp_pos _))

@[simp] theorem coe_realDegreeUnit (r : ℝ) :
    (realDegreeUnit r : ℝ) = Real.exp (-Real.exp r) := rfl

theorem realDegreeUnit_pos (r : ℝ) : 0 < (realDegreeUnit r : ℝ) := Real.exp_pos _

theorem realDegreeUnit_lt_one (r : ℝ) : (realDegreeUnit r : ℝ) < 1 :=
  Real.exp_lt_one_iff.2 (neg_lt_zero.2 (Real.exp_pos r))

/-- No positive contraction factors are omitted by the hypothesis-free chart. -/
theorem range_realDegreeUnit :
    Set.range (fun r : ℝ => (realDegreeUnit r : ℝ)) = Set.Ioo 0 1 := by
  ext q
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨realDegreeUnit_pos r, realDegreeUnit_lt_one r⟩
  · rintro ⟨hq0, hq1⟩
    refine ⟨Real.log (-Real.log q), ?_⟩
    change Real.exp (-Real.exp (Real.log (-Real.log q))) = q
    rw [Real.exp_log (neg_pos.2 (Real.log_neg hq0 hq1)), neg_neg, Real.exp_log hq0]

/-- The actual contracting degree element in the semidirect product loop group. -/
def degreeRotation (r : ℝ) : ExtendedLoopSL2 ℝ := SemidirectProduct.inr (realDegreeUnit r)

/-- Conjugation by the degree element induces the constructed loop automorphism. -/
theorem degreeRotation_conjugation (r : ℝ) (g : LoopSL2 ℝ) :
    degreeRotation r * SemidirectProduct.inl g * (degreeRotation r)⁻¹ =
      SemidirectProduct.inl (LoopSL2.rotation (realDegreeUnit r) g) := by
  have h :=
    (SemidirectProduct.inl_aut (φ := LoopSL2.rotationAction) (realDegreeUnit r) g).symm
  have hact : (LoopSL2.rotationAction (realDegreeUnit r)) g =
      LoopSL2.rotation (realDegreeUnit r) g := rfl
  rw [hact, map_inv] at h
  exact h

/-- Real affine root groups have precisely their expected degree eigenvalue. -/
theorem degreeRotation_realRootElement (r : ℝ) (β : AffineA1.Root) (a : ℝ) :
    degreeRotation r * SemidirectProduct.inl (LoopSL2.realRootElement β a) *
      (degreeRotation r)⁻¹ =
      SemidirectProduct.inl
        (LoopSL2.realRootElement β ((↑(realDegreeUnit r ^ β.corootZero) : ℝ) * a)) := by
  rw [degreeRotation_conjugation, LoopSL2.rotation_realRootElement]

/-- A positive degree rotation is never the identity element. -/
theorem degreeRotation_ne_one (r : ℝ) : degreeRotation r ≠ 1 := by
  intro h
  have hq := congrArg SemidirectProduct.right h
  change realDegreeUnit r = 1 at hq
  have hv := congrArg (fun u : ℝˣ => (u : ℝ)) hq
  exact (ne_of_lt (realDegreeUnit_lt_one r)) hv

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
