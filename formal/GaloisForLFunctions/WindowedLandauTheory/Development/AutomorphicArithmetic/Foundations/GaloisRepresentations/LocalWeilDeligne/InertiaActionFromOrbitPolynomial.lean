import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneTamePart
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-! A semisimple inertia action with an orbit polynomial factors
through the quotient on which its character orbit is defined. For
a cyclic quotient, testing at a lifted generator determines the orbit. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial Module
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.WeilDeligne

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

theorem WDRep.inertia_eq_one_of_charpoly {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a : WDRep h V) (t : Ine (F := K) A) {n : ℕ}
    (hc : (a.ρ (ineIncl h t)).charpoly = (X - 1) ^ n) : a.ρ (ineIncl h t) = 1 := by
  let f := a.ρ (ineIncl h t)
  have hn := LinearMap.aeval_self_charpoly f
  rw [show f.charpoly = _ from hc, map_pow, map_sub, aeval_X, map_one] at hn
  have hs : End.IsSemisimple (f - 1) := by
    simpa only [map_one] using
      (End.isSemisimple_sub_algebraMap_iff (μ := (1 : ℂ))).mpr (a.semisimple (ineIncl h t))
  exact sub_eq_zero.mp (End.eq_zero_of_isNilpotent_isSemisimple ⟨n, hn⟩ hs)

theorem WDRep.inertia_factors_of_orbitPolynomial {V U : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Group U] (a : WDRep h V)
    (r : Ine (F := K) A →* U) (hr : Function.Surjective r) (f : MulAut U) (n : ℕ)
    (χ : U →* ℂˣ)
    (hpol : ∀ t : Ine (F := K) A, (a.ρ (ineIncl h t)).charpoly =
      ∏ j ∈ Finset.range n, (X - C ((χ ((f ^ j) (r t)) : ℂˣ) : ℂ))) :
    ∃ b : U →* End ℂ V, b.comp r = a.ρ.comp (ineIncl h) := by
  let R := (a.ρ.comp (ineIncl h)).toHomUnits
  have hker : r.ker ≤ R.ker := by
    intro t ht
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    change a.ρ (ineIncl h t) = 1
    apply a.inertia_eq_one_of_charpoly t (n := n)
    rw [hpol]
    simp only [MonoidHom.mem_ker.mp ht, map_one, Units.val_one, map_one, Finset.prod_const, Finset.card_range]
  let b := r.liftOfSurjective hr ⟨R, hker⟩
  have hb : b.comp r = R := r.liftOfRightInverse_comp _ (Function.rightInverse_surjInv hr) ⟨R, hker⟩
  exact ⟨(Units.coeHom (End ℂ V)).comp b, MonoidHom.ext fun t =>
    congrArg Units.val (DFunLike.congr_fun hb t)⟩

theorem eq_frobeniusConjugate_of_orbitPolynomials_eq {U : Type*} [Group U] [IsCyclic U]
    (f : MulAut U) (n : ℕ) (hn : 0 < n) (χ ψ : U →* ℂˣ)
    (he : ∀ u : U, ∏ j ∈ Finset.range n, (X - C ((χ ((f ^ j) u) : ℂˣ) : ℂ)) =
      ∏ j ∈ Finset.range n, (X - C ((ψ ((f ^ j) u) : ℂˣ) : ℂ))) :
    ∃ j < n, ψ = χ.comp (f ^ j).toMonoidHom := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := U)
  have h0 : eval (ψ u : ℂ) (∏ j ∈ Finset.range n, (X - C ((χ ((f ^ j) u) : ℂˣ) : ℂ))) = 0 := by
    rw [he, eval_prod, Finset.prod_eq_zero_iff]
    exact ⟨0, Finset.mem_range.mpr hn, by simp⟩
  rw [eval_prod, Finset.prod_eq_zero_iff] at h0
  obtain ⟨j, hj, hh⟩ := h0
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hh
  refine ⟨j, Finset.mem_range.mp hj, (MonoidHom.eq_iff_eq_on_generator hu _ _).mpr ?_⟩
  exact Units.ext hh

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.WDRep.inertia_factors_of_orbitPolynomial
#print axioms GlobalTheory.WeilDeligne.eq_frobeniusConjugate_of_orbitPolynomials_eq
