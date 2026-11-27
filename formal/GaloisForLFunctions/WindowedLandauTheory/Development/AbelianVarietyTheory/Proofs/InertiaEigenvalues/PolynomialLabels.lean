import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.DegreeLT

/-! Counting polynomial labels and comparing their Frobenius orbits. -/

open GlobalTheory.GLq GlobalTheory.Published Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.PrimeLabOrbit

variable {g : ℕ} [hg : Fact g.Prime]

private theorem aeval_pow_frob {K : Type} [Field K] [Algebra (ZMod g) K] (n : ℕ) (Q : (ZMod g)[X]) (y : K) :
    aeval (y ^ g ^ n) Q = (aeval y Q) ^ g ^ n := by
  haveI : CharP K g := (Algebra.charP_iff (ZMod g) K g).1 (ZMod.charP g)
  haveI : ExpChar K g := ExpChar.prime hg.out
  rw [← iterateFrobenius_def g n y, ← iterateFrobenius_def g n (aeval y Q), aeval_def, aeval_def, hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

private theorem frob_injective {K : Type} [Field K] [Algebra (ZMod g) K] (n : ℕ) :
    Function.Injective (fun y : K => y ^ g ^ n) := by
  haveI : CharP K g := (Algebra.charP_iff (ZMod g) K g).1 (ZMod.charP g)
  haveI : ExpChar K g := ExpChar.prime hg.out
  intro a b h
  apply (iterateFrobenius K g n).injective
  simpa only [iterateFrobenius_def] using h

section adjoin

variable {d : ℕ} {P : (ZMod g)[X]} (hP : IsPrimeLab d P)
include hP

private theorem finrank_adjoin : haveI := Fact.mk hP.2.1; Module.finrank (ZMod g) (AdjoinRoot P) = d := by
  haveI := Fact.mk hP.2.1
  rw [(AdjoinRoot.powerBasis hP.1.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hP.2.2.2]

end adjoin

variable {K : Type} [Field K] [Algebra (ZMod g) K]

private theorem exists_unit_root {d : ℕ} (hd : 0 < d) (hK : Module.finrank (ZMod g) K = d) {P : (ZMod g)[X]}
    (hP : IsPrimeLab d P) : ∃ u : Kˣ, aeval (u : K) P = 0 := by
  haveI := Fact.mk hP.2.1
  haveI : Module.Finite (ZMod g) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.1.ne_zero).finite
  haveI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod g)
  letI : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite _
  have hc : Fintype.card (AdjoinRoot P) = Fintype.card K := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), Module.card_eq_pow_finrank (K := ZMod g) (V := K),
      finrank_adjoin hP, hK]
  let φ := FiniteField.algEquivOfCardEq g hc
  have hr : aeval (φ (AdjoinRoot.root P)) P = 0 := by
    rw [show φ (AdjoinRoot.root P) = φ.toAlgHom (AdjoinRoot.root P) from rfl, aeval_algHom_apply,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  have hne : φ (AdjoinRoot.root P) ≠ 0 := by
    intro h0
    rw [h0, aeval_def, eval₂_at_zero] at hr
    exact hP.2.2.1 ((algebraMap (ZMod g) K).injective (hr.trans (map_zero _).symm))
  exact ⟨Units.mk0 _ hne, hr⟩

private theorem orbit_regular {d : ℕ} {P : (ZMod g)[X]} (hP : IsPrimeLab d P) {u : K} (hu : aeval u P = 0) :
    ∀ i j, i < d → j < d → u ^ g ^ i = u ^ g ^ j → i = j := by
  have key : ∀ i j, i < j → j < d → u ^ g ^ i = u ^ g ^ j → False := by
    intro i j hij hj h
    have hk : 0 < j - i := Nat.sub_pos_of_lt hij
    have hfix : u ^ g ^ (j - i) = u := by
      apply frob_injective (g := g) (K := K) i
      simp only
      rw [h, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
    have hmin : P = minpoly (ZMod g) u := minpoly.eq_of_irreducible_of_monic hP.2.1 hu hP.1
    have hdvd : P ∣ X ^ (g ^ (j - i)) - X := by
      rw [hmin]
      apply minpoly.dvd
      rw [map_sub, map_pow, aeval_X, hfix, sub_self]
    have hdvd' : P.natDegree ∣ j - i := by
      apply hP.2.1.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
      rwa [Nat.card_zmod]
    rw [hP.2.2.2] at hdvd'
    have := Nat.le_of_dvd hk hdvd'
    omega
  intro i j hi hj h
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (key i j hij hj h).elim
  · exact hij
  · exact (key j i hij hi h.symm).elim

/-- Choosing a root and dualizing the finite-field unit group injects polynomial labels
into regular character orbits. -/
theorem primeLab_to_regularChar : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K],
    Module.finrank (ZMod g) K = d → ∃ c : (ZMod g)[X] → (Kˣ →* ℂˣ), (∀ P, IsPrimeLab d P → IsRegularChar g d (c P)) ∧
      ∀ P P', IsPrimeLab d P → IsPrimeLab d P' → (∃ i < d, c P' = c P ^ g ^ i) → P = P' := by
  intro g _ d hd K _ _ hK
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  let e : Kˣ ≃* (Kˣ →* ℂˣ) := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Kˣ ℂ).some.symm
  let c : (ZMod g)[X] → (Kˣ →* ℂˣ) := fun P =>
    if h : ∃ u : Kˣ, aeval (u : K) P = 0 then e h.choose else 1
  have hc : ∀ P, IsPrimeLab d P → ∃ u : Kˣ, aeval (u : K) P = 0 ∧ c P = e u := by
    intro P hP
    have h := exists_unit_root hd hK hP
    exact ⟨h.choose, h.choose_spec, dif_pos h⟩
  refine ⟨c, fun P hP => ?_, fun P P' hP hP' ⟨i, hi, h⟩ => ?_⟩
  · obtain ⟨u, hu, hcu⟩ := hc P hP
    intro i j hi hj h
    rw [hcu] at h
    have he : u ^ g ^ i = u ^ g ^ j :=
      e.injective ((map_pow e u (g ^ i)).trans (h.trans (map_pow e u (g ^ j)).symm))
    have h' := congrArg Units.val he
    simp only [Units.val_pow_eq_pow_val] at h'
    exact orbit_regular hP hu i j hi hj h'
  · obtain ⟨u, hu, hcu⟩ := hc P hP
    obtain ⟨u', hu', hcu'⟩ := hc P' hP'
    rw [hcu, hcu'] at h
    have he : u' = u ^ g ^ i := e.injective (h.trans (map_pow e u (g ^ i)).symm)
    have h' := congrArg Units.val he
    simp only [Units.val_pow_eq_pow_val] at h'
    have hr : aeval (u' : K) P = 0 := by rw [h', aeval_pow_frob, hu, zero_pow (pow_ne_zero _ (Fact.out : g.Prime).ne_zero)]
    rw [minpoly.eq_of_irreducible_of_monic hP.2.1 hr hP.1, minpoly.eq_of_irreducible_of_monic hP'.2.1 hu' hP'.1]

end GlobalTheory.PrimeLabOrbit

end

namespace GlobalTheory.GrPolys

private theorem monic_deg_equiv_card (g : ℕ) [Fact g.Prime] (n : ℕ) :
    Set.ncard {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} = g ^ n ∧
      Set.Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} := by
  have e : {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} ≃ (Fin n → ZMod g) :=
    (monicEquivDegreeLT n).trans (degreeLTEquiv (ZMod g) n).toEquiv
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_eq_fintype_card,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
  · haveI : Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} := Finite.of_equiv _ e.symm
    exact Set.toFinite _

private theorem zero_part_eq (g : ℕ) [Fact g.Prime] (n : ℕ) (hn : 0 < n) :
    {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 = 0} =
      (fun h => X * h) '' {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n - 1} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hm, hd, h0⟩
    obtain ⟨h, rfl⟩ := X_dvd_iff.mpr h0
    have hmh : h.Monic := Monic.of_mul_monic_left monic_X hm
    refine ⟨h, ⟨hmh, ?_⟩, rfl⟩
    rw [natDegree_X_mul hmh.ne_zero] at hd
    omega
  · rintro ⟨h, ⟨hm, hd⟩, rfl⟩
    refine ⟨monic_X.mul hm, ?_, ?_⟩
    · rw [natDegree_X_mul hm.ne_zero]; omega
    · simp [mul_coeff_zero]

end GlobalTheory.GrPolys

/-- Positive-degree monic polynomials with nonzero constant term have the expected finite count. -/
theorem GlobalTheory.GrPolys.card_monic_coeff_zero_ne_zero :
    ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → Set.ncard {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0} = g ^ n - g ^ (n - 1) ∧ Set.Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0} := by
  intro g _ n hn
  obtain ⟨hcS, hfS⟩ := GlobalTheory.GrPolys.monic_deg_equiv_card g n
  obtain ⟨hcT, hfT⟩ := GlobalTheory.GrPolys.monic_deg_equiv_card g (n - 1)
  set S := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n}
  set A := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0}
  set B := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 = 0}
  have hAS : A ⊆ S := fun f hf => ⟨hf.1, hf.2.1⟩
  have hBS : B ⊆ S := fun f hf => ⟨hf.1, hf.2.1⟩
  have hfA : A.Finite := hfS.subset hAS
  have hfB : B.Finite := hfS.subset hBS
  have hU : A ∪ B = S := by
    ext f
    simp only [A, B, S, Set.mem_union, Set.mem_setOf_eq]
    tauto
  have hD : Disjoint A B := by
    rw [Set.disjoint_left]
    intro f hA hB
    exact hA.2.2 hB.2.2
  have hB : B.ncard = g ^ (n - 1) := by
    rw [show B = _ from GlobalTheory.GrPolys.zero_part_eq g n hn, Set.ncard_image_of_injective _
      (fun a b h => mul_left_cancel₀ X_ne_zero h), hcT]
  have := Set.ncard_union_eq hD hfA hfB
  rw [hU, hcS, hB] at this
  exact ⟨by omega, hfA⟩
