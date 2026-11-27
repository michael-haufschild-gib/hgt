import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DegreeOneFrobenius
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.GaloisValuations.FiniteRamification

/-! Removing the finitely many ramified places realizes each element of a
finite Galois group as an unramified degree-one Frobenius. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DegreeOneFrobenius

/-- Every element of a finite Galois group occurs as Frobenius at a
degree-one place, with trivial inertia in the finite extension. -/
theorem exists_unramified_degree_one_frobenius (F Ω : Type)
    [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (L : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L]
    (g : L ≃ₐ[F] L) (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧
      ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Ine (F := F) B ≤ L.fixingSubgroup ∧
        ∃ σ : G F Ω, IsFrob B (normV v) σ ∧ AlgEquiv.restrictNormalHom L σ = g := by
  letI : IsGalois F Ω := {}
  obtain ⟨γ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) Ω g
  let T := {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
    ¬ Ine (F := F) B ≤ L.fixingSubgroup}
  have hT : T.Finite := InertiaAlmostAll.finite_ramified F Ω L
  obtain ⟨v, hv, hp, B, hB, s, hs, hcoset⟩ := exists_frobenius_in_coset F Ω L γ (S ∪ T) (hS.union hT)
  have hv' : v ∉ S ∧ v ∉ T := by simpa only [Set.mem_union, not_or] using hv
  have hd : v.asIdeal.inertiaDeg ℤ = 1 :=
    Nat.Prime.eq_one_of_pow (Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal ▸ hp)
  have hI : Ine (F := F) B ≤ L.fixingSubgroup := by
    by_contra hn
    exact hv'.2 ⟨B, hB, hn⟩
  refine ⟨v, hv'.1, hd, B, hB, hI, s, hs, ?_⟩
  rwa [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hcoset

end GlobalTheory.DegreeOneFrobenius
