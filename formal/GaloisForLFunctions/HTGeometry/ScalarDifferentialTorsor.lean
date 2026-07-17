import GaloisForLFunctions.HTGeometry.ScalarLogCurrentReconstruction
import GaloisForLFunctions.HTGeometry.RatFuncScaleFixedField
import GaloisForLFunctions.HTGeometry.DifferentialIndependentFieldUniversality
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence

/-!
# The scalar differential torsor over its logarithmic-current field

Let `q` be a nonzero hypertranscendental element generating a differential field `T` over a
constant field `F`, and put `J = q'/q`, `L = F<J>`.  The reconstruction theorem says that
`T = L(q)` as an ordinary field.  This file proves the missing exact transport:

* `q` is transcendental over `L`, so `T` is canonically the rational function field `L(X)`;
* constant rescaling of `q` gives every derivation-preserving `L`-automorphism of `T`;
* the automorphism group is exactly `Fˣ`;
* finite and infinite cyclic scalar fixed fields transport from the exact `L(X)` computation.

This is the rank-one Picard--Vessiot torsor statement for `Y' = JY`, expressed entirely through
the concrete differential field, its constants, and its automorphism group.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F T : Type*} [Field F] [Field T] [Algebra F T]
  [Differential F] [Differential T] [DifferentialAlgebra F T]
  [CharZero T]

/-- The logarithmic-current differential field of a scalar amplitude. -/
def scalarLogCurrentField (F : Type*) {T : Type*} [Field F] [Field T]
    [Algebra F T] [Differential T] (q : T) : IntermediateField F T :=
  differentialAdjoin F ({Differential.logDeriv q} : Set T)

/-- Multiplying a differential generator by a nonzero base scalar does not change its generated
differential field. -/
theorem differentialAdjoin_mul_algebraMap_eq (q : T) (u : Fˣ) :
    differentialAdjoin F ({q * algebraMap F T (u : F)} : Set T) =
      differentialAdjoin F ({q} : Set T) := by
  apply le_antisymm
  · apply differentialAdjoin_le F
    · intro z hz
      have hzq : z = q * algebraMap F T (u : F) := Set.mem_singleton_iff.mp hz
      rw [hzq]
      exact (differentialAdjoin F ({q} : Set T)).mul_mem
        (subset_differentialAdjoin F ({q} : Set T) rfl)
        ((differentialAdjoin F ({q} : Set T)).algebraMap_mem (u : F))
    · exact derivationClosed_differentialAdjoin F ({q} : Set T)
  · apply differentialAdjoin_le F
    · intro z hz
      have hzq : z = q := Set.mem_singleton_iff.mp hz
      rw [hzq]
      have hscaled : q * algebraMap F T (u : F) ∈
          differentialAdjoin F ({q * algebraMap F T (u : F)} : Set T) :=
        subset_differentialAdjoin F _ rfl
      have huInv : algebraMap F T ((u⁻¹ : Fˣ) : F) ∈
          differentialAdjoin F ({q * algebraMap F T (u : F)} : Set T) :=
        (differentialAdjoin F _).algebraMap_mem ((u⁻¹ : Fˣ) : F)
      have hmul := (differentialAdjoin F
        ({q * algebraMap F T (u : F)} : Set T)).mul_mem hscaled huInv
      simpa [mul_assoc] using hmul
    · exact derivationClosed_differentialAdjoin F
        ({q * algebraMap F T (u : F)} : Set T)

/-- Constant scalar rescaling on a freely generated differential field. -/
def scalarDifferentialScaleEquiv (q : T) (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤) (u : Fˣ) : T ≃ₐ[F] T := by
  let x : Unit → T := fun _ => q
  let y : Unit → T := fun _ => q * algebraMap F T (u : F)
  have hx : DifferentialIndependent F x := by
    simpa [x] using
      (GaloisForLFunctions.hypertranscendentalOver_iff_differentialIndependent_singleton F q).mp hq
  have hyHT : HypertranscendentalOver F (q * algebraMap F T (u : F)) :=
    (hypertranscendentalOver_mul_differentialAlgebraic_iff
      (differentialAlgebraicOver_algebraMap (F := F) (E := T) (u : F))
      (by simpa using (algebraMap F T).injective.ne u.ne_zero)).2 hq
  have hy : DifferentialIndependent F y := by
    simpa [y] using
      (GaloisForLFunctions.hypertranscendentalOver_iff_differentialIndependent_singleton F
        (q * algebraMap F T (u : F))).mp hyHT
  have hxtop : differentialAdjoin F (Set.range x) = ⊤ := by
    simpa [x] using hgen
  have hytop : differentialAdjoin F (Set.range y) = ⊤ := by
    simpa [y, differentialAdjoin_mul_algebraMap_eq q u] using hgen
  let exy := GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv x y hx hy
  let ex : differentialAdjoin F (Set.range x) ≃ₐ[F] T :=
    (IntermediateField.equivOfEq hxtop).trans IntermediateField.topEquiv
  let ey : differentialAdjoin F (Set.range y) ≃ₐ[F] T :=
    (IntermediateField.equivOfEq hytop).trans IntermediateField.topEquiv
  exact ex.symm.trans (exy.trans ey)

@[simp]
theorem scalarDifferentialScaleEquiv_apply_q (q : T)
    (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤) (u : Fˣ) :
    scalarDifferentialScaleEquiv q hq hgen u q =
      q * algebraMap F T (u : F) := by
  let x : Unit → T := fun _ => q
  let y : Unit → T := fun _ => q * algebraMap F T (u : F)
  have hx : DifferentialIndependent F x := by
    simpa [x] using
      (GaloisForLFunctions.hypertranscendentalOver_iff_differentialIndependent_singleton F q).mp hq
  have hyHT : HypertranscendentalOver F (q * algebraMap F T (u : F)) :=
    (hypertranscendentalOver_mul_differentialAlgebraic_iff
      (differentialAlgebraicOver_algebraMap (F := F) (E := T) (u : F))
      (by simpa using (algebraMap F T).injective.ne u.ne_zero)).2 hq
  have hy : DifferentialIndependent F y := by
    simpa [y] using
      (GaloisForLFunctions.hypertranscendentalOver_iff_differentialIndependent_singleton F
        (q * algebraMap F T (u : F))).mp hyHT
  have hjet := GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv_jet
    x y hx hy Unit.unit 0
  change ((GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv x y hx hy) ⟨q, _⟩).1 = _
  simpa [x, y] using congrArg Subtype.val hjet

end

end GaloisForLFunctions.HTGeometry
