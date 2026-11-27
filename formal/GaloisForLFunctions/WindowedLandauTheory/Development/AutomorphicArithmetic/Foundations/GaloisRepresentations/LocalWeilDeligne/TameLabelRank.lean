import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneTamePart
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantCharpolyBlocks

/-! The degree of an inertia label is the dimension of the wild inertia
invariants. A full-degree label therefore reads the original inertia action. -/

noncomputable section

open NumberField IsDedekindDomain Module Polynomial
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open WindowedLandauTheory.CyclotomicNorms GlobalTheory.TameKummer

namespace GlobalTheory.WeilDeligne.WDRep

variable {E Ω V : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem natDegree_eq_finrank_tameSpace (a : WDRep h V) {p : ℕ} [Fact p.Prime]
    (τ : Ine (F := E) A) (t : Fbar p →* ℂ) {f : (ZMod p)[X]}
    (hf : (a.tamePart.ρ (ineIncl h τ)).charpoly =
      ((rootsBar f).map fun x => X - C (t x)).prod) :
    f.natDegree = finrank ℂ a.tameSpace := by
  have he := congrArg Polynomial.natDegree hf
  change (a.tamePart.ρ (ineIncl h τ)).charpoly.natDegree =
    ((rootsBar f).map fun x => X - C (t x)).prod.natDegree at he
  have hm : ((rootsBar f).map fun x => X - C (t x)) =
      ((rootsBar f).map t).map (fun x => X - C x) := by
    simp only [Multiset.map_map, Function.comp_def]
  rw [LinearMap.charpoly_natDegree, hm, natDegree_multiset_prod_X_sub_C_eq_card,
    Multiset.card_map, rootsBar,
    IsAlgClosed.card_roots_eq_natDegree, natDegree_map] at he
  exact he.symm

omit [IsAlgClosure E Ω] in
theorem Tame.tameSpace_eq_top {a : WDRep h V} (ha : a.Tame) : a.tameSpace = ⊤ := by
  apply top_unique
  intro v _
  exact a.mem_tameSpace.mpr fun σ hσ => by rw [ha σ hσ]; rfl

theorem tame_iff_finrank_tameSpace (a : WDRep h V) :
    a.Tame ↔ finrank ℂ a.tameSpace = finrank ℂ V :=
  ⟨fun h => by rw [h.tameSpace_eq_top, finrank_top], a.tame_of_finrank_tameSpace⟩

omit [IsAlgClosure E Ω] in
theorem charpoly_wild_of_tame {a : WDRep h V} (ha : a.Tame) (σ : Weil h)
    (hσ : (σ : G E Ω) ∈ wildInertia A) :
    (a.ρ σ).charpoly = (X - 1) ^ finrank ℂ V := by
  rw [ha σ hσ, LinearMap.charpoly_one]

theorem charpoly_eq_tamePart_of_tame {a : WDRep h V} (ha : a.Tame) (σ : Weil h) :
    (a.ρ σ).charpoly = (a.tamePart.ρ σ).charpoly := by
  rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ a.tameSpace (a.ρ σ) (a.ρ_mem_tameSpace σ)]
  have hdim : finrank ℂ (V ⧸ a.tameSpace) = 0 := by
    have hr := a.tameSpace.finrank_quotient_add_finrank
    rw [(a.tame_iff_finrank_tameSpace).mp ha] at hr
    omega
  have h :
      (a.tameSpace.mapQ a.tameSpace (a.ρ σ) (a.ρ_mem_tameSpace σ)).charpoly = 1 := by
    apply (LinearMap.charpoly_monic _).natDegree_eq_zero.mp
    rw [LinearMap.charpoly_natDegree, hdim]
  rw [h, mul_one]
  rfl

end GlobalTheory.WeilDeligne.WDRep
