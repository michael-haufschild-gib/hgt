import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DensityOfSplitFrobenius
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteCoefficientsOfFrobeniusSystem

/-! A finite collection of Hecke eigenvalue systems admits a common
finite set of coefficients determining integral-model descent. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions.N
open ReciprocityTheory.Gal

namespace GlobalTheory.CompactRepField

open WindowedLandauTheory.ConjugateSelfDual

/-- The standard normalization of the Hecke polynomial of a system. -/
def complexHeckePolynomial {E : Type} [Field E] [NumberField E] (a : ℕ)
    (s : HeightOneSpectrum (𝓞 E) → ℕ → ℂ) (v : HeightOneSpectrum (𝓞 E)) : ℂ[X] :=
  X ^ a + ∑ k ∈ Finset.Icc 1 a,
    C ((-1 : ℂ) ^ k * (normV v : ℂ) ^ (k * (k - 1) / 2) * s v k) * X ^ (a - k)

/-- A common coefficient set works for every member of a finite family.
Cofinite split Frobenius density compares the semisimple realizations. -/
theorem exists_finite_hecke_coefficients {R : Ranks} (H : Host R) {Ω : Type}
    [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]
    (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ)
    (a : ℕ) (T : Set (PlE H)) (hT : T.Finite) (Es : Finset (PlE H → ℕ → ℂ)) :
    ∃ S : Finset ℂ, ∀ s ∈ Es,
      ∀ K : IntermediateField ℚ_[l] (PadicAlgCl l), (∀ z ∈ S, ι.symm z ∈ K) →
        ∀ (ρ : (Ω ≃ₐ[H.E] Ω) →* GL (Fin a) (PadicAlgCl l)),
          (Continuous fun g => (ρ g).val) → IsSSRep ρ →
          (∀ v ∉ T, IsSplitPl H v →
            ∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[H.E] Ω),
              IsPlaceOver (F := H.E) B v → IsFrob (F := H.E) B (normV v) g →
                (ρ g).val.charpoly.map ι.toRingHom = complexHeckePolynomial a s v) →
          ∃ P : GL (Fin a) (PadicAlgCl l), ∀ g i j, (P⁻¹ * ρ g * P).val i j ∈ K := by
  letI : IsGalois H.E Ω := {}
  classical
  let U : Set (Ω ≃ₐ[H.E] Ω) := {g | ∃ v : PlE H, v ∉ T ∧ IsSplitPl H v ∧
    ∃ B : ValuationSubring Ω, IsPlaceOver (F := H.E) B v ∧ IsFrob (F := H.E) B (normV v) g}
  have hU : Dense U := GlobalTheory.FrobDense.dense_split_frobenius H T hT
  let p (s : PlE H → ℕ → ℂ) (g : Ω ≃ₐ[H.E] Ω) : ℂ[X] :=
    if hg : g ∈ U then complexHeckePolynomial a s hg.choose else 0
  choose S hS using fun s => exists_finite_coefficients_of_frobenius_system l ι a U (p s) hU
  refine ⟨Es.biUnion S, fun s hs K hK ρ hc hss hρ => ?_⟩
  refine hS s K (fun z hz => hK z (Finset.mem_biUnion.mpr ⟨s, hs, hz⟩)) ρ hc hss ?_
  intro g hg
  obtain ⟨hv, hsplit, B, hB, hφ⟩ := hg.choose_spec
  simpa only [p, dif_pos hg] using hρ hg.choose hv hsplit B g hB hφ

end GlobalTheory.CompactRepField
