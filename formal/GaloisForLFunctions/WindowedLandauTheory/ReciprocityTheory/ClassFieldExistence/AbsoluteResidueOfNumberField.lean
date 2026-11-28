import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.GaloisValuations.Global
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteSubfieldImageUniqueness

/-! The prime residue field of a number field embeds in the absolute
residue field at a place above it. Elements whose difference has
positive valuation give the same residue. -/

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal
open WindowedLandauTheory.ConjugateSelfDual

namespace GlobalTheory.Reciprocity

variable {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
  (K : Type) [Field K] [NumberField K] [Algebra K Ω]

/-- Reduce a global integer in the absolute valuation ring. -/
def absoluteIntegerResidue : 𝓞 K →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp
    { toFun := fun x =>
        ⟨algebraMap K Ω (x : K), mem_of_isIntegral_int A (x.2.map (algebraMap K Ω).toIntAlgHom)⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }

theorem absoluteIntegerResidue_eq_zero_iff (x : 𝓞 K) :
    absoluteIntegerResidue A K x = 0 ↔ A.valuation (algebraMap K Ω (x : K)) < 1 := by
  unfold absoluteIntegerResidue
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
  exact A.valuation_lt_one_iff _

variable {K}

theorem absoluteIntegerResidue_eq_of_valuation_lt_one {L : Type} [Field L] [NumberField L]
    [Algebra L Ω] (x : 𝓞 K) (y : 𝓞 L)
    (h : A.valuation (algebraMap K Ω (x : K) - algebraMap L Ω (y : L)) < 1) :
    absoluteIntegerResidue A K x = absoluteIntegerResidue A L y := by
  unfold absoluteIntegerResidue
  rw [RingHom.comp_apply, RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact (A.valuation_lt_one_iff _).mpr h

theorem exists_absoluteResidueEmbedding {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)
    {k : Type} [Field k] (r : 𝓞 K →+* k) (hr : Function.Surjective r) (hk : RingHom.ker r = v.asIdeal) :
    ∃ f : k →+* IsLocalRing.ResidueField A, ∀ x, f (r x) = absoluteIntegerResidue A K x := by
  let s := absoluteIntegerResidue A K
  have hker : RingHom.ker r ≤ RingHom.ker s := by
    intro x hx
    rw [hk] at hx
    apply RingHom.mem_ker.mpr
    exact (absoluteIntegerResidue_eq_zero_iff A K x).mpr ((h x).mpr hx)
  exact ⟨RingHom.liftOfSurjective r hr ⟨s, hker⟩,
    fun x => RingHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩

theorem card_of_residueMap {v : HeightOneSpectrum (𝓞 K)} {k : Type} [Field k]
    (r : 𝓞 K →+* k) (hr : Function.Surjective r) (hk : RingHom.ker r = v.asIdeal) :
    Nat.card k = normV v := by
  let e := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hr)
  exact (Nat.card_congr e.toEquiv).symm

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_absoluteResidueEmbedding
