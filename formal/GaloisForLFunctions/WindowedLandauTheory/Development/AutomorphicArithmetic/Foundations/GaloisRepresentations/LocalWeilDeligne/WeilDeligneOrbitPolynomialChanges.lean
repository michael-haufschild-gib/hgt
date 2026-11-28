import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneDual
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneScalarTwist

/-! A scalar twist multiplies each root in an inertia polynomial.
Duality inverts the roots when the orbit polynomial comes from
a character of an inertia quotient. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial Module
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.WeilDeligne

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

theorem WDRep.charpoly_dual {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (σ : Weil h) : (a.dual.ρ σ).charpoly = (a.ρ σ⁻¹).charpoly := by
  classical
  rw [WDRep.dual_ρ, ← LinearMap.charpoly_toMatrix (a.ρ σ⁻¹) (finBasis ℂ V),
    ← LinearMap.charpoly_toMatrix (a.ρ σ⁻¹).dualMap (finBasis ℂ V).dualBasis,
    ← Matrix.charpoly_transpose, LinearMap.dualMap_def, LinearMap.toMatrix_transpose,
    Matrix.transpose_transpose]

theorem WDRep.charpoly_dual_of_orbitPolynomial {U V : Type} [Group U]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (r : Ine (F := K) A →* U) (θ : U →* ℂˣ) (q n : ℕ)
    (ha : ∀ t : Ine (F := K) A, (a.ρ (ineIncl h t)).charpoly =
      ∏ j ∈ Finset.range n, (X - C ((θ (r t ^ q ^ j) : ℂˣ) : ℂ)))
    (t : Ine (F := K) A) :
    (a.dual.ρ (ineIncl h t)).charpoly =
      ∏ j ∈ Finset.range n, (X - C ((θ⁻¹ (r t ^ q ^ j) : ℂˣ) : ℂ)) := by
  rw [WDRep.charpoly_dual, ← map_inv, ha]
  simp only [map_inv, inv_pow, MonoidHom.inv_apply]

theorem WDRep.charpoly_twist_of_orbitPolynomial {U : Type} [Group U]
    {m : ℕ} (a : WDRep h (Fin m → ℂ))
    (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ)
    (r : Ine (F := K) A →* U) (θ : U →* ℂˣ) (q n : ℕ)
    (ha : ∀ t : Ine (F := K) A, (a.ρ (ineIncl h t)).charpoly =
      ∏ j ∈ Finset.range n, (X - C ((θ (r t ^ q ^ j) : ℂˣ) : ℂ)))
    (t : Ine (F := K) A) :
    ((a.twist χ hχ).ρ (ineIncl h t)).charpoly =
      ∏ j ∈ Finset.range n, (X - C (((θ (r t ^ q ^ j) * χ (ineIncl h t)) : ℂˣ) : ℂ)) := by
  let b := Pi.basisFun ℂ (Fin m)
  let u (j : Fin n) : ℂ := θ (r t ^ q ^ (j : ℕ))
  let T := LinearMap.toMatrix b b (a.ρ (ineIncl h t))
  let s : ℂ := χ (ineIncl h t)
  let l : Multiset ℂ := (Finset.univ : Finset (Fin n)).val.map u
  have hT : T.charpoly = (l.map fun z => X - C z).prod := by
    rw [LinearMap.charpoly_toMatrix, ha, ← Fin.prod_univ_eq_prod_range]
    simp only [l, Multiset.map_map, Finset.prod, Function.comp_apply, u]
  have hs := GlobalTheory.SSComplement.charpoly_smul_of_prod T l s hT
  change (s • a.ρ (ineIncl h t)).charpoly = _
  rw [← LinearMap.charpoly_toMatrix _ b, map_smul, hs, ← Fin.prod_univ_eq_prod_range]
  simp only [l, Multiset.map_map, Finset.prod, Function.comp_apply, u, s, Units.val_mul]

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.WDRep.charpoly_dual_of_orbitPolynomial
#print axioms GlobalTheory.WeilDeligne.WDRep.charpoly_twist_of_orbitPolynomial
