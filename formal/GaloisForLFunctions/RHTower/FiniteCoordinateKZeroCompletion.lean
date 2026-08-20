import GaloisForLFunctions.HTGeometry.GrothendieckKTheoryIntersectionApplications
import GaloisForLFunctions.RHTower.RealCoronaKZeroMultiplicityFracture

/-!
# Concrete completion model for finite-coordinate K-zero

The existing `FiniteCoordinateKZero ι` is an abstract Grothendieck group.  This module identifies it
with finitely supported integer rank vectors and transports existing evaluation and total-rank maps
to coordinate projection and cycle degree.
-/

namespace GaloisForLFunctions.RHTower

open Algebra GaloisForLFunctions.HTGeometry

/-- Finite-coordinate K-zero is exactly group of finitely supported integer rank vectors. -/
noncomputable def finiteCoordinateKZeroEquiv (ι : Type*) :
    FiniteCoordinateKZero ι ≃+ (ι →₀ ℤ) :=
  effectiveFinsuppK0Equiv ι

theorem finiteCoordinateKZeroEquiv_of {ι : Type*} (q : ι →₀ ℕ) :
    finiteCoordinateKZeroEquiv ι (GrothendieckAddGroup.of q) =
      effectiveFinsuppToIntegral ι q :=
  effectiveFinsuppK0Class_of q

/-- Evaluation rank is coordinate projection of completed virtual-rank vector. -/
theorem finiteCoordinateKZeroEvaluationRank_eq_virtualRank
    {ι : Type*} (i : ι) (x : FiniteCoordinateKZero ι) :
    finiteCoordinateKZeroEvaluationRank i x = finiteCoordinateKZeroEquiv ι x i := by
  have hhom : finiteCoordinateKZeroEvaluationRank i =
      { toFun := fun x : FiniteCoordinateKZero ι => finiteCoordinateKZeroEquiv ι x i
        map_zero' := by simp
        map_add' := by simp } := by
    apply (GrothendieckAddGroup.lift
      (M := ι →₀ ℕ) (G := ℤ)).symm.injective
    apply AddMonoidHom.ext
    intro q
    change finiteCoordinateKZeroEvaluationRank i (GrothendieckAddGroup.of q) =
      finiteCoordinateKZeroEquiv ι (GrothendieckAddGroup.of q) i
    rw [finiteCoordinateKZeroEquiv_of]
    change finiteCoordinateKZeroEvaluationRank i (GrothendieckAddGroup.of q) = q i
    change ((GrothendieckAddGroup.lift
      (M := ι →₀ ℕ) (G := ℤ)).symm
        (GrothendieckAddGroup.lift (finiteCoordinateEvaluationMonoidHom i))) q = q i
    rw [Equiv.symm_apply_apply]
    rfl
  exact DFunLike.congr_fun hhom x

/-- Total K-zero rank is degree of completed virtual-rank cycle. -/
theorem finiteCoordinateKZeroRank_eq_virtualRankDegree
    {ι : Type*} (x : FiniteCoordinateKZero ι) :
    finiteCoordinateKZeroRank x =
      integralFinsuppDegree ι (finiteCoordinateKZeroEquiv ι x) := by
  have hhom : finiteCoordinateKZeroRank =
      (integralFinsuppDegree ι).comp (finiteCoordinateKZeroEquiv ι).toAddMonoidHom := by
    apply (GrothendieckAddGroup.lift
      (M := ι →₀ ℕ) (G := ℤ)).symm.injective
    apply AddMonoidHom.ext
    intro q
    change finiteCoordinateKZeroRank (GrothendieckAddGroup.of q) =
      integralFinsuppDegree ι
        (finiteCoordinateKZeroEquiv ι (GrothendieckAddGroup.of q))
    rw [finiteCoordinateKZeroEquiv_of]
    change ((GrothendieckAddGroup.lift
      (M := ι →₀ ℕ) (G := ℤ)).symm
        (GrothendieckAddGroup.lift finiteCoordinateRankMonoidHom)) q =
          integralFinsuppDegree ι (effectiveFinsuppToIntegral ι q)
    rw [Equiv.symm_apply_apply]
    simp [finiteCoordinateRankMonoidHom, integralFinsuppDegree,
      effectiveFinsuppToIntegral]
    rw [Finsupp.sum_mapRange_index]
    all_goals simp
  exact DFunLike.congr_fun hhom x

/-- Formal K-zero difference is corresponding signed virtual-rank vector. -/
theorem finiteCoordinateKZeroEquiv_difference
    {ι : Type*} (q r : ι →₀ ℕ) :
    finiteCoordinateKZeroEquiv ι
        (GrothendieckAddGroup.of q - GrothendieckAddGroup.of r) =
      effectiveFinsuppToIntegral ι q - effectiveFinsuppToIntegral ι r := by
  rw [map_sub, finiteCoordinateKZeroEquiv_of, finiteCoordinateKZeroEquiv_of]

/-- Existing Real-corona K-zero class becomes its integer support-rank cycle. -/
theorem finiteCoordinateKZeroEquiv_realCoronaFixedKZeroClass
    {ι : Type*} (q : ι →₀ ℕ) :
    finiteCoordinateKZeroEquiv ι (realCoronaFixedKZeroClass q) =
      effectiveFinsuppToIntegral ι (realCoronaKZeroSupportVector q) :=
  finiteCoordinateKZeroEquiv_of _

end GaloisForLFunctions.RHTower
