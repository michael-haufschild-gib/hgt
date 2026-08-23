import GaloisForLFunctions.RHTower.DeningerDynSysValuedTriples
import GaloisForLFunctions.HTGeometry.SchemeStalkSpecializationRatio

/-!
# The residue field at a point is the fraction field of the local ring of its closure

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §13.

For `y ∈ closure {x}` the ring `𝒪_{closure {x} , y} = 𝒪_{X,y} / 𝔭` is by construction the image of
`𝒪_{X,y}` in `κ (x)`, so it embeds in `κ (x)`; and every element of `κ (x)` is a ratio of values at
`x` of germs at `y`, because the stalk at `x` is a localization of the stalk at `y`.  Hence

`κ (x) = Frac (𝒪_{closure {x} , y})` .
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory HTGeometry

noncomputable section

universe u

variable {X : Scheme.{u}} {x y : X}

/-- The embedding of the local ring of the closure of `x` at `y` into the residue field at `x`. -/
def deningerClosureToResidue (h : x ⤳ y) :
    DeningerClosureLocalRing h →+* X.residueField x :=
  Ideal.Quotient.lift (deningerClosureIdeal h)
    ((X.presheaf.stalkSpecializes h ≫ X.residue x).hom) (fun _ ha => ha)

@[simp] theorem deningerClosureToResidue_mk (h : x ⤳ y) (a : X.presheaf.stalk y) :
    deningerClosureToResidue h (DeningerClosureLocalRing.mk h a) = stalkValue h a := rfl

theorem deningerClosureToResidue_injective (h : x ⤳ y) :
    Function.Injective (deningerClosureToResidue h) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨b, rfl⟩ := DeningerClosureLocalRing.mk_surjective h a
  exact (Ideal.Quotient.eq_zero_iff_mem).2 ha

/-- The residue field at `x` as an algebra over the local ring of the closure of `x` at `y`. -/
@[reducible] def deningerClosureAlgebra (h : x ⤳ y) :
    Algebra (DeningerClosureLocalRing h) (X.residueField x) :=
  (deningerClosureToResidue h).toAlgebra

/-- **Deninger, §13.**  The residue field at `x` is the fraction field of the local ring at `y` of
the closure of `x`. -/
theorem deningerClosure_isFractionRing (h : x ⤳ y) :
    letI := deningerClosureAlgebra h
    IsFractionRing (DeningerClosureLocalRing h) (X.residueField x) := by
  letI := deningerClosureAlgebra h
  have halg : ∀ d : DeningerClosureLocalRing h,
      algebraMap (DeningerClosureLocalRing h) (X.residueField x) d
        = deningerClosureToResidue h d := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨d, hd⟩
    have hne : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.1 hd
    have : deningerClosureToResidue h d ≠ 0 := fun hc =>
      hne ((injective_iff_map_eq_zero _).1 (deningerClosureToResidue_injective h) _ hc)
    rw [halg]
    exact isUnit_iff_ne_zero.2 this
  · intro t
    obtain ⟨a, b, hb, hab⟩ := exists_stalkValue_ratio h t
    have hbne : DeningerClosureLocalRing.mk h b ≠ 0 := by
      intro hc
      apply hb
      have := congrArg (deningerClosureToResidue h) hc
      rwa [deningerClosureToResidue_mk, map_zero] at this
    refine ⟨⟨DeningerClosureLocalRing.mk h a, ⟨DeningerClosureLocalRing.mk h b,
      mem_nonZeroDivisors_of_ne_zero hbne⟩⟩, ?_⟩
    rw [halg, halg, deningerClosureToResidue_mk, deningerClosureToResidue_mk]
    exact hab
  · intro a b hab
    rw [halg, halg] at hab
    exact ⟨1, by rw [deningerClosureToResidue_injective h hab]⟩

end

end RHTower
