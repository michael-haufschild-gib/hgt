import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalTameStageNorm
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneOrbitPolynomialChanges
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicUnitCharacterReduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EllipticNameDeterminantTwist

/-! Tame local characters pull back under inverse Artin to the norm
character on the residue inertia quotient. Thus the Weil twist
changes each inertia eigenvalue by the same residue norm factor. -/

noncomputable section

open Matrix NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.Reciprocity GlobalTheory.GLp GlobalTheory.EllipticCharacters

namespace GlobalTheory.WeilDeligne

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}
  {p n : ℕ} [Fact p.Prime]
  {α : Weil h →* (v.adicCompletion K)ˣ} (hα : IsLocalArtin K Ω α)

include hα in
theorem artin_inertia_residue_norm_character (D : LocalTameStage h p n) (hn : 0 < n)
    (i : ℚ_[p] ≃+* v.adicCompletion K) (hi : Continuous i)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (δ : (ZMod p)ˣ →* ℂˣ)
    (hδ : ∀ z : ℤ_[p]ˣ, δ (padicUnitReduction z) =
      (χ.comp (Units.map i.toRingHom.toMonoidHom))
        (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom z))
    (t : Ine (F := K) A) :
    χ (α (ineIncl h t)) = δ (residueUnitNorm (g := p) D.residue (D.inertiaResidue t)) := by
  obtain ⟨z, hz, hr⟩ := D.base_artin_unit hα D.inertiaResidue D.inertiaResidue_spec i hi hn t
  let e := algebraMap (ZMod p) D.residue
  have hnorm := residueUnitNorm_eq_frobeniusProduct hn D.residue_rank (D.inertiaResidue t)
  have hN : e (residueUnitNorm (g := p) D.residue (D.inertiaResidue t) : ZMod p) =
      ∏ j ∈ Finset.range n, ((D.inertiaResidue t ^ p ^ j : D.residueˣ) : D.residue) := by
    exact (congrArg Units.val hnorm).trans (map_prod (Units.coeHom D.residue) _ _)
  have hred : padicUnitReduction z = residueUnitNorm (g := p) D.residue (D.inertiaResidue t) :=
    Units.ext (e.injective (hr.trans hN.symm))
  have he : α (ineIncl h t) = Units.map i.toRingHom.toMonoidHom
      (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom z) := Units.ext hz
  calc
    χ (α (ineIncl h t)) = _ := congrArg χ he
    _ = δ (padicUnitReduction z) := (hδ z).symm
    _ = _ := congrArg δ hred

include hα in
theorem WDRep.charpoly_tameTwist_at_stage (D : LocalTameStage h p n) (hn : 0 < n)
    (i : ℚ_[p] ≃+* v.adicCompletion K) (hi : Continuous i)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set (v.adicCompletion K)ˣ))
    (δ : (ZMod p)ˣ →* ℂˣ)
    (hδ : ∀ z : ℤ_[p]ˣ, δ (padicUnitReduction z) =
      (χ.comp (Units.map i.toRingHom.toMonoidHom))
        (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom z))
    (θ : D.residueˣ →* ℂˣ) (a : WDRep h (Fin n → ℂ))
    (ha : ∀ t : Ine (F := K) A, (a.ρ (ineIncl h t)).charpoly =
      ∏ j ∈ Finset.range n, (X - C ((θ (D.inertiaResidue t ^ p ^ j) : ℂˣ) : ℂ)))
    (t : Ine (F := K) A) :
    ((a.twist (χ.comp α) (IsLocalArtin.smooth K Ω hα hχ)).ρ (ineIncl h t)).charpoly =
      ∏ j ∈ Finset.range n,
        (X - C (((θ * δ.comp (residueUnitNorm (g := p) D.residue)) (D.inertiaResidue t ^ p ^ j) : ℂˣ) : ℂ)) := by
  rw [WDRep.charpoly_twist_of_orbitPolynomial a _ _ D.inertiaResidue θ p n ha]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
    artin_inertia_residue_norm_character hα D hn i hi χ δ hδ]
  have hp : δ (residueUnitNorm (g := p) D.residue (D.inertiaResidue t ^ p ^ j)) =
      δ (residueUnitNorm (g := p) D.residue (D.inertiaResidue t)) := by
    rw [map_pow]
    congr 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ZMod.pow_card_pow]
  rw [hp]

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.WDRep.charpoly_tameTwist_at_stage
