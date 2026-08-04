import GaloisForLFunctions.HTGeometry.RatFuncScaleInfiniteStabilizer
import GaloisForLFunctions.HTGeometry.ScalarDifferentialTorsor

/-!
# Infinitely many scaling symmetries collapse a scalar differential torsor

On the rank-one torsor `T = L(q)` over the logarithmic-current field, an element fixed by the
rescalings coming from an infinite set of constants lies in `L`.  Transporting through the rational
coordinate, the statement is that a rational function with infinitely many scaling symmetries is
constant; no scalar of infinite multiplicative order is needed, so an infinite torsion group of
constants — roots of unity of unbounded order — already collapses the fixed field to the current
field.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F T : Type*} [Field F] [Field T] [Algebra F T]
  [Differential F] [Differential T] [DifferentialAlgebra F T]
  [CharZero T]

/-- **Infinitely many scaling symmetries force membership in the current field.** -/
theorem mem_scalarLogCurrentField_of_infinite_scale_fixed
    (q : T) (hq : HypertranscendentalOver F q) (hq0 : q ≠ 0)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    (hconst : ∀ c : F, c′ = 0) [CharZero F]
    {S : Set Fˣ} (hS : S.Infinite) {z : T}
    (hz : ∀ u ∈ S, scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u z = z) :
    z ∈ scalarLogCurrentField F q := by
  let L : IntermediateField F T := scalarLogCurrentField F q
  let e : RatFunc L ≃ₐ[L] T := scalarTorsorRatFuncEquiv q hq hq0 hgen hconst
  set r : RatFunc L := e.symm z with hr
  have hfix : ∀ v ∈ (scalarLogCurrentUnit (F := F) q) '' S,
      ratFuncUnitScaleAction v r = r := by
    rintro _ ⟨u, hu, rfl⟩
    have heq := scalarTorsorRatFuncEquiv_scale q hq hq0 hgen hconst u r
    have hz' : scalarDifferentialScaleEquivCurrent q hq hq0 hgen hconst u (e r) = e r := by
      rw [hr, e.apply_symm_apply]
      exact hz u hu
    apply e.injective
    rw [heq, hz']
  have hinj : Set.InjOn (scalarLogCurrentUnit (F := F) q) S :=
    Set.injOn_of_injective (scalarLogCurrentUnit_injective (F := F) q)
  obtain ⟨c, hc⟩ := ratFuncUnitScale_fixed_eq_constant_of_infinite (hS.image hinj) hfix
  have hzc : z = algebraMap L T c := by
    have : e r = e (RatFunc.C c) := by rw [hc]
    rw [hr, e.apply_symm_apply] at this
    rw [this]
    have hCc : (RatFunc.C c : RatFunc L) = algebraMap L (RatFunc L) c := rfl
    rw [hCc, e.commutes]
  rw [hzc]
  exact c.2

end

end GaloisForLFunctions.HTGeometry
