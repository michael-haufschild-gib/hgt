import GaloisForLFunctions.RHTower.CCMRationalStrongCyclicLefschetz
import GaloisForLFunctions.RHTower.CCMRationalStrongTraceMultiplicationFracture
import GaloisForLFunctions.RHTower.KRealCyclicCliffordTransgression

/-!
# Real-corona versus CCM Lefschetz: parity obstruction and Clifford replacement

The literal CCM Lefschetz correspondence is Real-even and invertible.  The degree-zero Chern
character of the scalar Real-corona class is Real-odd.  They therefore cannot be identified in the
untwisted full-adeles cyclic module.  Together with the multiplication-fracture theorem, this gives
a complete negative answer to the proposed direct `K₀` lift.

The surviving comparison is canonical: multiply the CCM Lefschetz correspondence by `i`.  The
result is an anti-Real cyclic endomorphism, and at the identity class its square is `-1`, exactly the
Clifford/quaternionic transgression law.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev Section := CCMRationalClassSpaceSection
private abbrev Field := CCMRationalContinuousTraceNormField

/-- A concrete nonzero degree-zero chain in the exact strong cyclic target. -/
def ccmRationalStrongCyclicNonzeroWitness :
    CCMRationalStrongCyclicTarget.simplicial.degree 0 :=
  ⟨ccmRationalCyclicBarDegreeZeroTprod
      (ccmRationalMoritaConstantIdealField ccmRationalMoritaMatrixUnitOneNeg),
    ccmRationalMoritaMatrixUnitTprods_mem_strongCyclicDegreeZero.1⟩

private theorem ccmRationalMoritaMatrixUnitOneNeg_ne_zero :
    ccmRationalMoritaMatrixUnitOneNeg ≠ 0 := by
  intro hzero
  have hnorm := congrArg norm hzero
  rw [norm_zero] at hnorm
  have hone : ‖ccmRationalMoritaMatrixUnitOneNeg‖ = 1 := by
    rw [ccmRationalMoritaMatrixUnitOneNeg,
      ccmRationalMoritaLOneWeightedShift_norm]
    simp [ccmRationalMoritaLOneDelta]
  linarith

/-- The exact strong cyclic target is nontrivial already in degree zero. -/
theorem ccmRationalStrongCyclicNonzeroWitness_ne_zero :
    ccmRationalStrongCyclicNonzeroWitness ≠ 0 := by
  intro hzero
  have htensor :
      ccmRationalCyclicBarDegreeZeroTprod
          (ccmRationalMoritaConstantIdealField ccmRationalMoritaMatrixUnitOneNeg) = 0 :=
    congrArg Subtype.val hzero
  have hfield := congrArg
    (cyclicBarDegreeZeroProduct (R := ℂ) (A := Field)) htensor
  simp [ccmRationalCyclicBarDegreeZeroTprod] at hfield
  have hvalue := congrArg
    (fun F : Field => F (1 : Section)) hfield
  have hlp := congrArg WithLp.ofLp hvalue
  have hideal := congrArg
    (fun x : CCMRationalMoritaTraceNormUnitization => x.snd) hlp
  exact ccmRationalMoritaMatrixUnitOneNeg_ne_zero (by simpa
    [ccmRationalMoritaConstantIdealField,
      ccmRationalMoritaTraceNormL1IdealElement] using hideal)

/-- Every CCM Lefschetz translation is nonzero: its inverse translation recovers the explicit
degree-zero witness. -/
theorem ccmRationalStrongCyclicLefschetz_degreeZero_nonzero (c : Section) :
    ccmRationalStrongCyclicRightActionDegree c 0
        ccmRationalStrongCyclicNonzeroWitness ≠ 0 := by
  intro hzero
  have hinv := congrArg
    (ccmRationalStrongCyclicRightActionDegree c⁻¹ 0) hzero
  rw [map_zero, ccmRationalStrongCyclicRightActionDegree_mul] at hinv
  have hcinv : c⁻¹ * c = 1 := by simp
  rw [hcinv, ccmRationalStrongCyclicRightActionDegree_one] at hinv
  exact ccmRationalStrongCyclicNonzeroWitness_ne_zero hinv

/-- **Parity no-go.** No nonzero CCM Lefschetz correspondence can itself satisfy the anti-Real
naturality required by the Chern character of `κ`. -/
theorem ccmRationalStrongCyclicLefschetz_not_antiReal (c : Section) :
    ¬ ∀ n (x : CCMRationalStrongCyclicTarget.simplicial.degree n),
      (ccmRationalStrongCyclicKReal.real n).sigma
          ((ccmRationalStrongCyclicLefschetz c).toHom.simplicial.app
            (.op (.mk n)) x) =
        -(ccmRationalStrongCyclicLefschetz c).toHom.simplicial.app
          (.op (.mk n)) ((ccmRationalStrongCyclicKReal.real n).sigma x) := by
  intro hanti
  have hzero := CyclicModule.KRealHom.degree_eq_zero_of_anti
    (ccmRationalStrongCyclicLefschetz c) hanti 0
      ccmRationalStrongCyclicNonzeroWitness
  change ccmRationalStrongCyclicRightActionDegree c 0
      ccmRationalStrongCyclicNonzeroWitness = 0 at hzero
  exact ccmRationalStrongCyclicLefschetz_degreeZero_nonzero c hzero

/-- Exact scalar comparison law: a scalar multiple of a nonzero CCM Lefschetz translation has
the anti-Real parity of the corona character if and only if the scalar is purely imaginary. -/
theorem ccmRationalStrongCyclicLefschetz_smul_isAnti_iff_star_eq_neg
    (c : Section) (z : ℂ) :
    (∀ n (x : CCMRationalStrongCyclicTarget.simplicial.degree n),
      (ccmRationalStrongCyclicKReal.real n).sigma
          (((ccmRationalStrongCyclicLefschetz c).toHom.smul z).simplicial.app
            (.op (.mk n)) x) =
        -((ccmRationalStrongCyclicLefschetz c).toHom.smul z).simplicial.app
          (.op (.mk n)) ((ccmRationalStrongCyclicKReal.real n).sigma x)) ↔
      (starRingEnd ℂ) z = -z :=
  CyclicModule.KRealHom.smul_isAnti_iff_star_eq_neg
    (ccmRationalStrongCyclicLefschetz c)
    ⟨0, ccmRationalStrongCyclicNonzeroWitness,
      ccmRationalStrongCyclicLefschetz_degreeZero_nonzero c⟩ z

/-- Correct full-adeles cyclic-module replacement for the impossible direct `κ` lift. -/
def ccmRationalStrongCyclicKappaTransgression (c : Section) :
    CyclicModule.KRealAntiHom ccmRationalStrongCyclicKReal
      ccmRationalStrongCyclicKReal :=
  (ccmRationalStrongCyclicLefschetz c).cliffordTransgression

/-- The replacement is exactly `i` times the CCM Lefschetz correspondence in every degree. -/
@[simp]
theorem ccmRationalStrongCyclicKappaTransgression_apply
    (c : Section) (n : ℕ)
    (x : CCMRationalStrongCyclicTarget.simplicial.degree n) :
    (ccmRationalStrongCyclicKappaTransgression c).toHom.simplicial.app
        (.op (.mk n)) x =
      Complex.I • ccmRationalStrongCyclicRightActionDegree c n x :=
  rfl

/-- At the identity class, the full-adeles transgression is a quaternionic/Clifford generator. -/
theorem ccmRationalStrongCyclicKappaTransgression_one_sq
    (n : ℕ) (x : CCMRationalStrongCyclicTarget.simplicial.degree n) :
    (ccmRationalStrongCyclicKappaTransgression 1).toHom.simplicial.app
        (.op (.mk n))
      ((ccmRationalStrongCyclicKappaTransgression 1).toHom.simplicial.app
        (.op (.mk n)) x) = -x := by
  apply CyclicModule.KRealHom.cliffordTransgression_identity_sq
    (ccmRationalStrongCyclicLefschetz 1)
  intro m y
  change ccmRationalStrongCyclicRightActionDegree 1 m y = y
  exact ccmRationalStrongCyclicRightActionDegree_one m y

end RHTower
end GaloisForLFunctions
