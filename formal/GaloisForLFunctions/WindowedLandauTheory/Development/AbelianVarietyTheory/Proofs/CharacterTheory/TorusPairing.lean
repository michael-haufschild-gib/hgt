import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacteristicPolynomialMass
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorus
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitivePairing
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitivePrimarySupport
import Mathlib.FieldTheory.Perfect

/-! Evaluation of the primitive root-sum pairing on a finite-field torus. -/

open Polynomial

namespace GlobalTheory.CuspGL

private theorem torus_iff {F : Type} [Field F] [Finite F] (n : ℕ) (α : AlgebraicClosure F) (h0 : α ≠ 0) :
    α ^ (Nat.card F ^ n - 1) = 1 ↔ (minpoly F α).natDegree ∣ n := by
  rw [minpoly_natDegree_dvd_iff_pow]
  have hq : 0 < Nat.card F ^ n := pow_pos Nat.card_pos _
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F ^ n = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hq).symm⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  constructor
  · intro h; rw [h, one_mul]
  · intro h; exact mul_right_cancel₀ h0 (h.trans (one_mul α).symm)

private theorem finite_monic_natDegree {F : Type} [Field F] [Finite F] (n : ℕ) :
    {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}.Finite := by
  have : Finite (Polynomial.degreeLT F (n + 1)) := Finite.of_equiv _ (degreeLTEquiv F (n + 1)).symm.toEquiv
  have h : (Polynomial.degreeLT F (n + 1) : Set F[X]).Finite := Set.toFinite _
  refine h.subset fun P hP => ?_
  simp only [SetLike.mem_coe, mem_degreeLT]
  exact (degree_le_of_natDegree_le hP.2.1.le).trans_lt (by exact_mod_cast Nat.lt_succ_self n)

private theorem finite_torus {F : Type} [Field F] [Finite F] (n : ℕ) (hn : 0 < n) :
    {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}.Finite := by
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  refine (Polynomial.nthRootsFinset (Nat.card F ^ n - 1) (1 : AlgebraicClosure F)).finite_toSet.subset
    fun α hα => ?_
  exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset (by omega) _).2 hα)

/-- Group the torus elements by their primary characteristic polynomials. -/
theorem sum_poly_eq_sum_torus (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (n : ℕ) (hn : 0 < n) (c : F[X] → ℂ) (l : ℕ)
    (hc : ∀ P : F[X], P.Monic → P.natDegree = n →
      (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) → c P = 0) :
    ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}, c P * star (rootSum θ l P) =
      ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1},
        ((n / (minpoly F α).natDegree : ℕ) : ℂ) *
          c (minpoly F α ^ (n / (minpoly F α).natDegree)) * star (θ α ^ l) := by
  classical
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  have hi : ∀ α : AlgebraicClosure F, IsIntegral F α := fun α => Algebra.IsIntegral.isIntegral α
  have hne : ∀ α : AlgebraicClosure F, α ^ (Nat.card F ^ n - 1) = 1 → α ≠ 0 := by
    rintro α h rfl
    rw [zero_pow (by omega)] at h
    exact zero_ne_one h
  rw [finsum_mem_eq_finite_toFinset_sum _ (finite_monic_natDegree n),
    finsum_mem_eq_finite_toFinset_sum _ (finite_torus n hn),
    ← Finset.sum_fiberwise_of_maps_to (s := (finite_torus (F := F) n hn).toFinset) (t := (finite_monic_natDegree (F := F) n).toFinset)
      (g := fun α => minpoly F α ^ (n / (minpoly F α).natDegree))]
  swap
  · intro α hα
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hα ⊢
    have hm := minpoly.monic (hi α)
    refine ⟨hm.pow _, ?_, ?_⟩
    · rw [hm.natDegree_pow, Nat.div_mul_cancel ((torus_iff n α (hne α hα)).1 hα)]
    · rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
      exact pow_ne_zero _ (minpoly.coeff_zero_ne_zero (hi α) (hne α hα))
  refine Finset.sum_congr rfl fun P hP => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
  obtain ⟨hP, hd, h0⟩ := hP
  by_cases hex : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m
  swap
  · rw [hc P hP hd hex, zero_mul]
    refine (Finset.sum_eq_zero fun α hα => ?_).symm
    rw [(Finset.mem_filter.1 hα).2, hc P hP hd hex, mul_zero, zero_mul]
  obtain ⟨f, m, hf, hirr, hm, rfl⟩ := hex
  rw [hf.natDegree_pow] at hd
  have hdiv : n / f.natDegree = m := by
    rw [← hd, Nat.mul_div_cancel _ hirr.natDegree_pos]
  have hmp : ∀ α : AlgebraicClosure F, aeval α f = 0 → minpoly F α = f := fun α h =>
    (minpoly.eq_of_irreducible_of_monic hirr h hf).symm
  have hfib : Finset.filter (fun α : AlgebraicClosure F => minpoly F α ^ (n / (minpoly F α).natDegree) = f ^ m)
      (finite_torus (F := F) n hn).toFinset = (f.map (algebraMap F (AlgebraicClosure F))).roots.toFinset := by
    ext α
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Multiset.mem_toFinset]
    rw [mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : n / (minpoly F α).natDegree ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd hn ((torus_iff n α (hne α h1)).1 h1)) (minpoly.natDegree_pos (hi α))).ne'
      have h4 := congrArg (aeval α) h2
      rw [map_pow, map_pow, minpoly.aeval, zero_pow h3] at h4
      exact pow_eq_zero_iff hm.ne' |>.1 h4.symm
    · intro h
      have hα : α ≠ 0 := by
        rintro rfl
        apply h0
        rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
        rw [aeval_def, eval₂_at_zero, map_eq_zero] at h
        rw [h, zero_pow hm.ne']
      rw [torus_iff n α hα, hmp α h, hdiv]
      exact ⟨Dvd.intro_left _ hd, rfl⟩
  have hsep : f.Separable := PerfectField.separable_of_irreducible hirr
  have hnd : (f.map (algebraMap F (AlgebraicClosure F))).roots.Nodup := nodup_roots hsep.map
  rw [hfib, rootSum, Polynomial.map_pow, roots_pow, Multiset.map_nsmul, Multiset.sum_nsmul,
    ← Multiset.dedup_eq_self.2 hnd, ← Multiset.toFinset_val, ← Finset.sum_eq_multiset_sum,
    Finset.val_toFinset, Finset.smul_sum, star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Multiset.mem_toFinset, mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap] at hα
  rw [hmp α hα, hdiv, star_nsmul, nsmul_eq_mul]
  ring

private theorem ipGL_charpoly_eq_finsum_mass (F : Type) [Field F] [Finite F]
    (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (φ : Module.End F V → ℂ) (s : F[X] → ℂ) :
    ipGL φ (fun g => s (LinearMap.charpoly g)) =
      ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0},
        mass φ P * star (s P) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) :=
    Finite.of_injective (fun g : Module.End F V => (g : V → V)) DFunLike.coe_injective
  set S := {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0} with hS
  set I := S ∩ Set.range (fun g : Module.End F V => LinearMap.charpoly g) with hI
  have hunit : ∀ g : Module.End F V, IsUnit g ↔ LinearMap.charpoly g ∈ S := by
    intro g
    simp only [hS, Set.mem_setOf_eq, LinearMap.charpoly_monic, LinearMap.charpoly_natDegree,
      true_and]
    rw [LinearMap.isUnit_iff_isUnit_det, LinearMap.det_eq_sign_charpoly_coeff, isUnit_iff_ne_zero]
    simp
  have hset : {g : Module.End F V | IsUnit g} =
      ⋃ P ∈ I, {g : Module.End F V | LinearMap.charpoly g = P} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, hI, Set.mem_inter_iff, Set.mem_range,
      exists_prop]
    rw [hunit]
    constructor
    · intro h
      exact ⟨_, ⟨h, g, rfl⟩, rfl⟩
    · rintro ⟨P, ⟨hP, _⟩, rfl⟩
      exact hP
  have hsupp : S ∩ Function.support (fun P => mass φ P * star (s P)) =
      I ∩ Function.support (fun P => mass φ P * star (s P)) := by
    ext P
    simp only [hI, Set.mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨hPS, hne⟩
      refine ⟨⟨hPS, ?_⟩, hne⟩
      by_contra hr
      apply hne
      have hempty : {g : Module.End F V | LinearMap.charpoly g = P} = ∅ := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hr ⟨g, h⟩
      unfold mass
      simp [hempty]
    · rintro ⟨⟨hPS, _⟩, hne⟩
      exact ⟨hPS, hne⟩
  rw [finsum_mem_inter_support_eq _ S I hsupp]
  unfold ipGL mass
  rw [hset, finsum_mem_biUnion ?_ ((Set.finite_range _).subset Set.inter_subset_right)
    (fun _ _ => Set.toFinite _)]
  · refine finsum_mem_congr rfl fun P _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
      finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_mul]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [Set.Finite.mem_toFinset] at hg
    show φ g * star (s (LinearMap.charpoly g)) = _
    rw [show LinearMap.charpoly g = P from hg]
  · intro P _ Q _ hPQ
    exact Set.disjoint_left.2 fun g hP hQ => hPQ (hP.symm.trans hQ)

/-- The root-sum pairing of a primitive class function reduces to the finite-field torus. -/
theorem ipGL_rootSum_eq_sum_torus (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ)
    (hcl : IsClassFn φ) (hprim : IsPrimitive φ) (hpos : 0 < Module.finrank F V) (l : ℕ) :
    ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) =
      ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ Module.finrank F V - 1) = 1},
        ((Module.finrank F V / (minpoly F α).natDegree : ℕ) : ℂ) *
          mass φ (minpoly F α ^ (Module.finrank F V / (minpoly F α).natDegree)) * star (θ α ^ l) := by
  rw [ipGL_charpoly_eq_finsum_mass F V φ (rootSum θ l)]
  refine sum_poly_eq_sum_torus F θ (Module.finrank F V) hpos (mass φ) l ?_

  intro P _ _ hP
  unfold mass
  rw [finsum_mem_def]
  refine finsum_eq_zero_of_forall_eq_zero fun g => ?_
  by_cases hg : LinearMap.charpoly g = P
  · rw [Set.indicator_of_mem (show g ∈ {g : Module.End F V | LinearMap.charpoly g = P} from hg)]
    exact eq_zero_of_not_primary F V φ hcl hprim hpos g (hg ▸ hP)
  · exact Set.indicator_of_notMem (show g ∉ {g : Module.End F V | LinearMap.charpoly g = P} from hg) _

end GlobalTheory.CuspGL
