import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilParameterOfInertiaQuotient
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.ResidueCharacterPeriods
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneCharacterTwists
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! A regular residue-field name gives an irreducible tame Weil
parameter. The determinant on inertia is the product over the
Frobenius orbit. A matching Frobenius value then fixes it everywhere. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.Published
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TameKummer

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A v}

private theorem determinant_of_orbitPolynomial {n : ℕ} (T : Module.End ℂ (Fin n → ℂ))
    (z : ℕ → ℂ) (he : T.charpoly = ∏ j ∈ Finset.range n, (X - C (z j))) :
    LinearMap.det T = ∏ j ∈ Finset.range n, z j := by
  rw [LinearMap.det_eq_sign_charpoly_coeff, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, he,
    coeff_zero_prod]
  simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
  have he' : ∏ j ∈ Finset.range n, -(z j) = ∏ j ∈ Finset.range n, (-1 : ℂ) * z j :=
    Finset.prod_congr rfl fun j _ => (neg_one_mul (z j)).symm
  rw [he', Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← mul_assoc, ← mul_pow]
  simp

theorem exists_tame_wdRep_of_regular_residue_orbit {g n : ℕ} [Fact g.Prime] {K : Type}
    [Field K] [Algebra (ZMod g) K] [Finite K] (hn : 0 < n) (hd : Module.finrank (ZMod g) K = n)
    (r : Ine (F := E) A →* Kˣ) (hr : Function.Surjective r)
    (hop : IsOpen (r.ker : Set (Ine (F := E) A)))
    (hw : ∀ t : Ine (F := E) A, t.val ∈ wildInertia A → r t = 1)
    (φ : Weil h) (hφ : deg φ = 1)
    (hF : ∀ t t' : Ine (F := E) A, ineIncl h t' = φ * ineIncl h t * φ⁻¹ → r t' = r t ^ g)
    (χ : Kˣ →* ℂˣ) (hχ : IsRegularChar g n χ)
    (d : Weil h →* ℂˣ)
    (hdI : ∀ t : Ine (F := E) A, χ (∏ j ∈ Finset.range n, r t ^ g ^ j) = d (ineIncl h t)) :
    ∃ a : WDRep h (Fin n → ℂ), a.ρ.IsIrreducible ∧ a.N = 0 ∧ a.Tame ∧
      (∀ σ, LinearMap.det (a.ρ σ) = (d σ : ℂ)) ∧
      ∀ t : Ine (F := E) A, (a.ρ (ineIncl h t)).charpoly =
        ∏ j ∈ Finset.range n, (X - C ((χ (r t ^ g ^ j) : ℂˣ) : ℂ)) := by
  let f := residueUnitsFrobenius (ZMod g) K
  have hq : Nat.card (ZMod g) = g := Nat.card_zmod g
  have hf (u : Kˣ) : f u = u ^ g := by
    change residueUnitsFrobenius (ZMod g) K u = u ^ g
    rw [residueUnitsFrobenius_apply, hq]
  have hfp (j : ℕ) (u : Kˣ) : (f ^ j) u = u ^ g ^ j := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', MulAut.mul_apply, ih, hf, ← pow_mul, ← pow_succ]
  obtain ⟨a, hA, hN, hD, hP, hT⟩ := exists_wdRep_of_inertia_quotient
    r hr hop φ hφ f (fun t t' he => (hF t t' he).trans (hf (r t)).symm)
    χ n hn (regularCharacter_has_fullPeriod g K n hn hd χ hχ) (d φ : ℂ) (Units.ne_zero _)
  have hpol (t : Ine (F := E) A) : (a.ρ (ineIncl h t)).charpoly =
      ∏ j ∈ Finset.range n, (X - C ((χ (r t ^ g ^ j) : ℂˣ) : ℂ)) := by
    simpa only [hfp] using hP t
  have hδφ : a.detChar φ = d φ := Units.ext hD
  have hδI (t : Ine (F := E) A) : a.detChar (ineIncl h t) = d (ineIncl h t) := by
    apply Units.ext
    change LinearMap.det (a.ρ (ineIncl h t)) = (d (ineIncl h t) : ℂ)
    rw [determinant_of_orbitPolynomial _ _ (hpol t), ← hdI t, map_prod]
    exact (map_prod (Units.coeHom ℂ) _ _).symm
  refine ⟨a, hA, hN, hT hw, fun σ => ?_, hpol⟩
  obtain ⟨t, ht⟩ := exists_eq_zpow_mul hφ σ
  change (a.detChar σ : ℂ) = (d σ : ℂ)
  rw [ht, map_mul, map_mul, map_zpow, map_zpow, hδφ, hδI]

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.exists_tame_wdRep_of_regular_residue_orbit
