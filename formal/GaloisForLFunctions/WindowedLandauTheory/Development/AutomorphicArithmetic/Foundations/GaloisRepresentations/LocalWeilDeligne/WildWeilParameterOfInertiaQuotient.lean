import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilParameterOfInertiaQuotient
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FrobeniusPowerOnTameInertia
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-! A full Frobenius orbit of characters of residue-characteristic
exponent gives an irreducible parameter with unitary determinant and
a nonscalar wild inertia action. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial Module
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TameKummer

namespace GlobalTheory.WeilDeligne

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

private theorem eq_one_of_frobenius_exponent_on_tameInertia {p : ℕ} [Fact p.Prime]
    (hp : A.valuation (p : Ω) < 1) (φ : Weil h) (hφ : deg φ = 1)
    (ξ : Ine (F := K) A →* ℂˣ)
    (hξ : ∀ t : Ine (F := K) A, ξ t ^ normV v = 1)
    (hw : ∀ t : Ine (F := K) A, t.val ∈ wildInertia A → ξ t = 1)
    (t t' : Ine (F := K) A) (ht : ineIncl h t' = φ * ineIncl h t * φ⁻¹) : ξ t' = 1 := by
  obtain ⟨-, hW⟩ := frobenius_conj_div_wild_of_card A hp t.2 (deg_eq_one_iff.mp hφ)
  have he : t'.val = φ.val * t.val * φ.val⁻¹ := congrArg Subtype.val ht
  have hδ : (((t ^ normV v)⁻¹ * t' : Ine (F := K) A) : G K Ω) ∈ wildInertia A := by
    apply (mem_wildInertia_iff _ _).mpr
    change ∀ y : Ω, y ≠ 0 →
      A.valuation (((t.val ^ normV v)⁻¹ * t'.val) y / y - 1) < 1
    rw [he]
    exact hW
  have h1 := hw _ hδ
  rw [map_mul, map_inv, map_pow, hξ, inv_one, one_mul] at h1
  exact h1

private theorem eigenvalue_eq_of_scalar {n : ℕ} (T : End ℂ (Fin n → ℂ)) {z c : ℂ}
    (he : T = c • 1) (hz : T.HasEigenvalue z) : z = c := by
  obtain ⟨x, hx⟩ := hz.exists_hasEigenvector
  have hm := (Module.End.hasEigenvector_iff.mp hx).1
  have hne := (Module.End.hasEigenvector_iff.mp hx).2
  have hTx := Module.End.mem_eigenspace_iff.mp hm
  rw [he] at hTx
  exact (smul_left_injective ℂ hne) (by simpa using hTx.symm)

theorem exists_wdRep_nonscalar_wild_of_inertia_quotient {U : Type} [Group U]
    {p : ℕ} [Fact p.Prime] (hp : A.valuation (p : Ω) < 1)
    (r : Ine (F := K) A →* U) (hr : Function.Surjective r)
    (hop : IsOpen (r.ker : Set (Ine (F := K) A)))
    (φ : Weil h) (hφ : deg φ = 1) (f : MulAut U)
    (hF : ∀ t t' : Ine (F := K) A, ineIncl h t' = φ * ineIncl h t * φ⁻¹ → r t' = f (r t))
    (χ : U →* ℂˣ) (hχ : ∀ u, χ u ^ normV v = 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hper : ∀ i j : ℤ, χ.comp (f ^ i).toMonoidHom = χ.comp (f ^ j).toMonoidHom ↔
      (n : ℤ) ∣ i - j) :
    ∃ a : WDRep h (Fin n → ℂ), a.ρ.IsIrreducible ∧ a.N = 0 ∧
      (∀ σ, ‖LinearMap.det (a.ρ σ)‖ = 1) ∧
      ∃ t : Ine (F := K) A, t.val ∈ wildInertia A ∧ ∀ c : ℂ, a.ρ (ineIncl h t) ≠ c • 1 := by
  obtain ⟨a, hA, hN, hdet, hpol, -⟩ :=
    exists_wdRep_of_inertia_quotient r hr hop φ hφ f hF χ n (by omega) hper 1 one_ne_zero
  have hnormχ (u : U) : ‖((χ u : ℂˣ) : ℂ)‖ = 1 := by
    have hu := congrArg (fun z : ℂˣ => (z : ℂ)) (hχ u)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at hu
    exact Complex.norm_eq_one_of_pow_eq_one hu (one_lt_normV v).pos.ne'
  have hdetI (t : Ine (F := K) A) : ‖LinearMap.det (a.ρ (ineIncl h t))‖ = 1 := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, coeff_zero_eq_eval_zero, hpol, eval_prod,
      norm_mul, norm_pow]
    simp only [eval_sub, eval_X, eval_C, zero_sub, norm_neg, norm_one, one_pow, one_mul,
      norm_prod, hnormχ, Finset.prod_const_one]
  refine ⟨a, hA, hN, fun σ => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := exists_eq_zpow_mul hφ σ
    let d := ((LinearMap.det : End ℂ (Fin n → ℂ) →* ℂ).comp a.ρ).toHomUnits
    change ‖((d σ : ℂˣ) : ℂ)‖ = 1
    have hφd : d φ = 1 := Units.ext hdet
    rw [ht, map_mul, map_zpow, hφd, one_zpow, one_mul]
    exact hdetI t
  · let ξ := ((χ.comp f.toMonoidHom) / χ).comp r
    have hξ (t : Ine (F := K) A) : ξ t ^ normV v = 1 := by
      change (χ (f (r t)) / χ (r t)) ^ normV v = 1
      rw [div_pow, hχ, hχ, div_one]
    have hex : ∃ t : Ine (F := K) A, t.val ∈ wildInertia A ∧ χ (f (r t)) ≠ χ (r t) := by
      by_contra! hk
      have hw (t : Ine (F := K) A) (ht : t.val ∈ wildInertia A) : ξ t = 1 := by
        change χ (f (r t)) / χ (r t) = 1
        rw [hk t ht, div_self']
      have hs : χ.comp f.toMonoidHom = χ := by
        apply MonoidHom.ext
        intro u
        obtain ⟨s, hs⟩ := f.surjective u
        obtain ⟨t, rfl⟩ := hr s
        let w := φ * ineIncl h t * φ⁻¹
        have hd : deg w = 0 := by simp [w]
        let t' : Ine (F := K) A := ⟨w.val, deg_eq_zero_iff.mp hd⟩
        have hconj : ineIncl h t' = w := Subtype.ext rfl
        have h := eq_one_of_frobenius_exponent_on_tameInertia hp φ hφ ξ hξ hw t t' hconj
        change χ (f (r t')) / χ (r t') = 1 at h
        rw [div_eq_one] at h
        rw [hF t t' hconj, hs] at h
        exact h
      have hd := (hper 1 0).mp (by
        rw [zpow_one, zpow_zero, hs]
        rfl)
      have hdvd : n ∣ 1 := Int.natCast_dvd_natCast.mp (by simpa using hd)
      exact (by omega : n ≠ 1) (Nat.dvd_one.mp hdvd)
    obtain ⟨t, ht, hne⟩ := hex
    refine ⟨t, ht, fun c hscalar => ?_⟩
    have he (i : ℕ) (hi : i < n) :
        Module.End.HasEigenvalue (a.ρ (ineIncl h t)) (χ ((f ^ i) (r t)) : ℂ) := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, IsRoot.def, hpol, eval_prod,
        Finset.prod_eq_zero_iff]
      exact ⟨i, Finset.mem_range.mpr hi, by simp⟩
    have h0 := eigenvalue_eq_of_scalar _ hscalar (he 0 (by omega))
    have h1 := eigenvalue_eq_of_scalar _ hscalar (he 1 (by omega))
    apply hne
    apply Units.ext
    simpa using h1.trans h0.symm

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.exists_wdRep_nonscalar_wild_of_inertia_quotient
