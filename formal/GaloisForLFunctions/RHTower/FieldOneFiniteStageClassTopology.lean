import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassSpace
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Topology of finite-stage rational adelic class spaces

This file equips the algebraic finite-stage construction with its quotient topology.  It proves:

* every fixed idele scales the additive finite-stage adeles continuously;
* the diagonal `S`-unit orbit projection is an open quotient map;
* the descended idele action on the orbit quotient is continuous;
* every idele therefore acts by a homeomorphism; and
* the same statements factor through the finite-stage idele class group.

These results construct the topological scaling geometry required before attempting a quotient
measure.  No measure-preservation or `L²` claim is made here.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain

/-- Coordinatewise finite-stage idele scaling is continuous for every fixed idele. -/
instance fieldOneFiniteStageIdeleContinuousConstSMul
    (S : Finset (HeightOneSpectrum ℤ)) :
    ContinuousConstSMul (FieldOneFiniteStageIdele S)
      (FieldOneFiniteStageAdele S) where
  continuous_const_smul u := by
    change Continuous fun x : FieldOneFiniteStageAdele S =>
      ((u.1 : ℝ) * x.1,
        fun v => (u.2 v : v.1.adicCompletion ℚ) * x.2 v)
    apply Continuous.prodMk
    · exact continuous_const.mul continuous_fst
    · exact continuous_pi fun v =>
        continuous_const.mul ((continuous_apply v).comp continuous_snd)

/-- The restricted action of the diagonal `S`-unit image is continuously generated. -/
instance fieldOneFiniteStageSUnitImageContinuousConstSMul
    (S : Finset (HeightOneSpectrum ℤ)) :
    ContinuousConstSMul (fieldOneFiniteStageSUnitImage S)
      (FieldOneFiniteStageAdele S) where
  continuous_const_smul h := by
    simpa only [MulAction.subgroup_smul_def] using
      (continuous_const_smul
        (h : FieldOneFiniteStageIdele S))

/-- The diagonal `S`-unit orbit projection is an open quotient map. -/
theorem fieldOneFiniteStageClassQuotient_isOpenQuotientMap
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsOpenQuotientMap
      (Quotient.mk
        (MulAction.orbitRel
          (fieldOneFiniteStageSUnitImage S)
          (FieldOneFiniteStageAdele S))) :=
  MulAction.isOpenQuotientMap_quotientMk

/-- Scaling by a fixed finite-stage idele is continuous on the orbit quotient. -/
theorem fieldOneFiniteStageIdeleClassAction_continuous
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) :
    Continuous (fieldOneFiniteStageIdeleClassAction S u) := by
  rw [(fieldOneFiniteStageClassQuotient_isOpenQuotientMap S).isQuotientMap.continuous_iff]
  exact continuous_quotient_mk'.comp (continuous_const_smul u)

/-- The full finite-stage idele action on the orbit quotient is continuous in the space
variable for every fixed idele. -/
instance fieldOneFiniteStageIdeleClassContinuousConstSMul
    (S : Finset (HeightOneSpectrum ℤ)) :
    ContinuousConstSMul (FieldOneFiniteStageIdele S)
      (FieldOneFiniteStageClassSpace S) where
  continuous_const_smul :=
    fieldOneFiniteStageIdeleClassAction_continuous S

/-- Every finite-stage idele scales the orbit quotient by a homeomorphism. -/
def fieldOneFiniteStageIdeleClassHomeomorph
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) :
    FieldOneFiniteStageClassSpace S ≃ₜ
      FieldOneFiniteStageClassSpace S :=
  Homeomorph.smul u

/-- Scaling by a fixed finite-stage idele class is continuous. -/
theorem fieldOneFiniteStageIdeleClassGroup_const_smul_continuous
    (S : Finset (HeightOneSpectrum ℤ))
    (c : FieldOneFiniteStageIdeleClassGroup S) :
    Continuous fun x : FieldOneFiniteStageClassSpace S => c • x := by
  refine Quotient.inductionOn c ?_
  intro u
  simpa only [fieldOneFiniteStageIdeleClassGroup_mk_smul] using!
    (fieldOneFiniteStageIdeleClassAction_continuous S u)

/-- The factored idele-class action is continuous in the class-space variable. -/
instance fieldOneFiniteStageIdeleClassGroupContinuousConstSMul
    (S : Finset (HeightOneSpectrum ℤ)) :
    ContinuousConstSMul (FieldOneFiniteStageIdeleClassGroup S)
      (FieldOneFiniteStageClassSpace S) where
  continuous_const_smul :=
    fieldOneFiniteStageIdeleClassGroup_const_smul_continuous S

/-- Every finite-stage idele class scales the orbit quotient by a homeomorphism. -/
def fieldOneFiniteStageIdeleClassGroupHomeomorph
    (S : Finset (HeightOneSpectrum ℤ))
    (c : FieldOneFiniteStageIdeleClassGroup S) :
    FieldOneFiniteStageClassSpace S ≃ₜ
      FieldOneFiniteStageClassSpace S :=
  Homeomorph.smul c

end

end GaloisForLFunctions.RHTower
