import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalTameStageSystem
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.CyclicInertiaWeilUniqueness
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.ResidueCharacterPeriods

/-! The inertia polynomial on a generator recovers the finite name
up to Frobenius. For a regular name, the inertia polynomial and
the determinant at degree one determine the Weil parameter. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Reciprocity GlobalTheory.Published

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A v}
  {p n : ℕ} [Fact p.Prime]

theorem exists_name_frobeniusPower_of_same_inertiaPolynomial
    (D : LocalTameStage h p n) (hn : 0 < n) (θ θ' : D.residueˣ →* ℂˣ)
    (he : ∀ t : Ine (F := E) A,
      (∏ j ∈ Finset.range n, (X - C ((θ (D.inertiaResidue t ^ p ^ j) : ℂˣ) : ℂ))) =
        ∏ j ∈ Finset.range n, (X - C ((θ' (D.inertiaResidue t ^ p ^ j) : ℂˣ) : ℂ))) :
    ∃ j < n, θ' = θ ^ p ^ j := by
  letI := D.finite_residue
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := D.residueˣ)
  obtain ⟨t, ht⟩ := D.inertiaResidue_surjective u
  let c : ℂ := θ' u
  have hh := congrArg (eval c) (he t)
  rw [ht, eval_prod, eval_prod] at hh
  have hz : (∏ j ∈ Finset.range n, eval c (X - C ((θ' (u ^ p ^ j) : ℂˣ) : ℂ))) = 0 := by
    apply Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr hn)
    simp [c]
  rw [hz] at hh
  obtain ⟨j, hj, heq⟩ := Finset.prod_eq_zero_iff.mp hh
  refine ⟨j, Finset.mem_range.mp hj, (MonoidHom.eq_iff_eq_on_generator hu _ _).mpr ?_⟩
  apply Units.ext
  change (θ' u : ℂ) = ((θ ^ p ^ j) u : ℂˣ).val
  rw [MonoidHom.pow_apply, ← map_pow]
  exact sub_eq_zero.mp (by simpa only [eval_sub, eval_X, eval_C] using heq)

theorem WDRep.iso_of_inertiaPolynomial_at_tameStage {V W : Type}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (D : LocalTameStage h p n) (hn : 0 < n) (hp : normV v = p) (θ : D.residueˣ →* ℂˣ)
    (hθ : IsRegularChar p n θ) (a : WDRep h V) (b : WDRep h W)
    (ha : a.ρ.IsIrreducible) (hb : b.ρ.IsIrreducible)
    (haI : ∀ t : Ine (F := E) A, (a.ρ (ineIncl h t)).charpoly =
      ∏ j ∈ Finset.range n, (X - C ((θ (D.inertiaResidue t ^ p ^ j) : ℂˣ) : ℂ)))
    (hbI : ∀ t : Ine (F := E) A, (b.ρ (ineIncl h t)).charpoly =
      ∏ j ∈ Finset.range n, (X - C ((θ (D.inertiaResidue t ^ p ^ j) : ℂˣ) : ℂ)))
    (hdet : LinearMap.det (a.ρ (frob h)) = LinearMap.det (b.ρ (frob h))) : a.Iso b := by
  letI := D.finite_residue
  let f := residueUnitsFrobenius (ZMod p) D.residue
  have hfp (u : D.residueˣ) : f u = u ^ p := by
    rw [show f u = u ^ Nat.card (ZMod p) from residueUnitsFrobenius_apply _ _ _, Nat.card_zmod]
  have hf (j : ℕ) (u : D.residueˣ) : (f ^ j) u = u ^ p ^ j := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', MulAut.mul_apply, ih, hfp, ← pow_mul, ← pow_succ]
  have horder : orderOf f = n :=
    (orderOf_residueUnitsFrobenius (ZMod p) D.residue).trans D.residue_rank
  have hperiod : f ^ n = 1 := by
    simpa only [horder] using pow_orderOf_eq_one f
  have hreg : Function.Injective fun i : Fin n => θ.comp (f ^ (i : ℕ)).toMonoidHom := by
    intro i j he
    apply Fin.ext
    apply hθ i.val j.val i.isLt j.isLt
    apply MonoidHom.ext
    intro u
    have hh := DFunLike.congr_fun he u
    change θ ((f ^ i.val) u) = θ ((f ^ j.val) u) at hh
    simpa only [hf, map_pow, MonoidHom.pow_apply] using hh
  exact WDRep.iso_of_regular_cyclic_inertia D.inertiaResidue D.inertiaResidue_surjective
    (frob h) deg_frob f p n hn hfp hperiod
    (fun t t' ht => by rw [hfp]; simpa only [hp] using D.inertiaResidue_conjugation (frob h) deg_frob t t' ht)
    θ hreg a b ha hb (fun t => by simpa only [hf] using haI t) (fun t => by simpa only [hf] using hbI t) hdet

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.exists_name_frobeniusPower_of_same_inertiaPolynomial
#print axioms GlobalTheory.WeilDeligne.WDRep.iso_of_inertiaPolynomial_at_tameStage
