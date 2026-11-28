import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.InertiaActionFromOrbitPolynomial
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.CyclicFrobeniusBasis
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.IrreducibleWeilDeligne

/-! A regular cyclic inertia orbit and the Frobenius determinant
determine the irreducible Weil–Deligne parameter. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial Module
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.WeilDeligne

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

theorem WDRep.iso_of_regular_cyclic_inertia {V V' U : Type}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    [Group U] [Finite U] [IsCyclic U]
    (r : Ine (F := K) A →* U) (hr : Function.Surjective r)
    (φ : Weil h) (hφ : deg φ = 1)
    (f : MulAut U) (q n : ℕ) (hn : 0 < n) (hf : ∀ u : U, f u = u ^ q) (hperiod : f ^ n = 1)
    (hF : ∀ t t' : Ine (F := K) A, ineIncl h t' = φ * ineIncl h t * φ⁻¹ → r t' = f (r t))
    (χ : U →* ℂˣ)
    (hreg : Function.Injective fun i : Fin n => χ.comp (f ^ (i : ℕ)).toMonoidHom)
    (a : WDRep h V) (b : WDRep h V') (ha : a.ρ.IsIrreducible) (hb : b.ρ.IsIrreducible)
    (haI : ∀ t : Ine (F := K) A, (a.ρ (ineIncl h t)).charpoly =
      ∏ j ∈ Finset.range n, (X - C ((χ ((f ^ j) (r t)) : ℂˣ) : ℂ)))
    (hbI : ∀ t : Ine (F := K) A, (b.ρ (ineIncl h t)).charpoly =
      ∏ j ∈ Finset.range n, (X - C ((χ ((f ^ j) (r t)) : ℂˣ) : ℂ)))
    (hdet : LinearMap.det (a.ρ φ) = LinearMap.det (b.ρ φ)) : a.Iso b := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := U)
  obtain ⟨t₀, ht₀⟩ := hr u
  let ι := ineIncl h
  let z : ℂ := χ u
  have hpow (j : ℕ) : (f ^ j) u = u ^ q ^ j := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', MulAut.mul_apply, ih, hf, ← pow_mul, ← pow_succ]
  have hzp : z ^ q ^ n = z := by
    have he := hpow n
    rw [hperiod] at he
    change u = u ^ q ^ n at he
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← he]
  have hsep : Function.Injective (fun j : Fin n => z ^ q ^ (j : ℕ)) := by
    intro i j hij
    apply hreg
    apply (MonoidHom.eq_iff_eq_on_generator hu _ _).mpr
    apply Units.ext
    change ((χ ((f ^ (i : ℕ)) u) : ℂˣ) : ℂ) = ((χ ((f ^ (j : ℕ)) u) : ℂˣ) : ℂ)
    simpa only [hpow, map_pow, Units.val_pow_eq_pow_val] using hij
  let t₁ : Ine (F := K) A := ⟨(φ * ι t₀ * φ⁻¹).val, deg_eq_zero_iff.mp (by simp [ι])⟩
  have ht₁ : ι t₁ = φ * ι t₀ * φ⁻¹ := Subtype.ext rfl
  have hr₁ : r t₁ = u ^ q := by rw [hF t₀ t₁ ht₁, ht₀, hf]
  have pair {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (c : WDRep h W)
      (hcI : ∀ t : Ine (F := K) A, (c.ρ (ι t)).charpoly =
        ∏ j ∈ Finset.range n, (X - C ((χ ((f ^ j) (r t)) : ℂˣ) : ℂ))) :
      ∃ Rc : U →* End ℂ W, Rc.comp r = c.ρ.comp ι ∧ Module.finrank ℂ W = n ∧
        Module.End.HasEigenvalue (c.ρ (ι t₀)) z ∧
        c.ρ (ι t₀) * c.ρ φ⁻¹ = c.ρ φ⁻¹ * (c.ρ (ι t₀)) ^ q := by
    obtain ⟨Rc, hRc⟩ := c.inertia_factors_of_orbitPolynomial r hr f n χ hcI
    have hR (t : Ine (F := K) A) : Rc (r t) = c.ρ (ι t) := DFunLike.congr_fun hRc t
    have hdim := congrArg Polynomial.natDegree (hcI t₀)
    rw [LinearMap.charpoly_natDegree, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_range] at hdim
    refine ⟨Rc, hRc, hdim, ?_, ?_⟩
    · rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, IsRoot.def, hcI, eval_prod, Finset.prod_eq_zero_iff]
      exact ⟨0, Finset.mem_range.mpr hn, by simp [ht₀, z]⟩
    · have hrho₁ : c.ρ (ι t₁) = c.ρ (ι t₀) ^ q := by
        rw [← hR t₁, hr₁, map_pow, ← ht₀, hR t₀]
      rw [← hrho₁, ← map_mul, ← map_mul, ht₁]
      congr 1
      group
  obtain ⟨Ra, hRa, hda, haz, haφ⟩ := pair a haI
  obtain ⟨Rb, hRb, hdb, hbz, hbφ⟩ := pair b hbI
  let δa := (LinearMap.det.comp a.ρ).toHomUnits
  let δb := (LinearMap.det.comp b.ρ).toHomUnits
  have hδ : δa φ = δb φ := Units.ext hdet
  have hdet' : LinearMap.det (a.ρ φ⁻¹) = LinearMap.det (b.ρ φ⁻¹) := by
    change (δa φ⁻¹ : ℂ) = (δb φ⁻¹ : ℂ)
    rw [map_inv, map_inv, hδ]
  obtain ⟨e, he₀, heφ⟩ := exists_equiv_of_cyclic_eigenvalue_pairs
    (a.ρ (ι t₀)) (a.ρ φ⁻¹) (b.ρ (ι t₀)) (b.ρ φ⁻¹)
    ((a.ρ.toHomUnits φ⁻¹).isUnit) ((b.ρ.toHomUnits φ⁻¹).isUnit)
    hn hda hdb haφ hbφ z haz hbz hzp hsep hdet'
  have heI (t : Ine (F := K) A) (x : V) : e (a.ρ (ι t) x) = b.ρ (ι t) (e x) := by
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp
      (mem_powers_iff_mem_zpowers.mpr (hu (r t)))
    have haa : a.ρ (ι t) = (a.ρ (ι t₀)) ^ j := by
      change (a.ρ.comp ι) t = (a.ρ.comp ι t₀) ^ j
      rw [← hRa, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hj, ht₀, map_pow]
    have hbb : b.ρ (ι t) = (b.ρ (ι t₀)) ^ j := by
      change (b.ρ.comp ι) t = (b.ρ.comp ι t₀) ^ j
      rw [← hRb, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hj, ht₀, map_pow]
    rw [haa, hbb]
    clear hj haa hbb
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, he₀, ih]
  have hFrob (x : V) : e (a.ρ φ x) = b.ρ φ (e x) := by
    have hh := heφ (a.ρ φ x)
    rw [← End.mul_apply, ← map_mul, inv_mul_cancel, map_one, End.one_apply] at hh
    rw [hh, ← End.mul_apply, ← map_mul, mul_inv_cancel, map_one, End.one_apply]
  have hPow (i : ℤ) (x : V) : e (a.ρ (φ ^ i) x) = b.ρ (φ ^ i) (e x) := by
    induction i using Int.induction_on generalizing x with
    | zero => simp
    | succ i ih => rw [zpow_add_one, map_mul, map_mul, End.mul_apply, End.mul_apply, ih, hFrob]
    | pred i ih => rw [zpow_sub_one, map_mul, map_mul, End.mul_apply, End.mul_apply, ih, heφ]
  refine ⟨e, fun σ x => ?_, fun x => by rw [a.monodromy_eq_zero_of_irreducible ha,
    b.monodromy_eq_zero_of_irreducible hb]; simp⟩
  obtain ⟨t, ht⟩ := exists_eq_zpow_mul hφ σ
  rw [ht, map_mul, map_mul, End.mul_apply, End.mul_apply, hPow, heI]

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.WDRep.iso_of_regular_cyclic_inertia
