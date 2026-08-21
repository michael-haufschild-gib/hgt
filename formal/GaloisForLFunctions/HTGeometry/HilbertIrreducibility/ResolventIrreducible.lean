import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.SeparatingLabel
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# The resolvent of a polynomial with full symmetric Galois group is irreducible

If the automorphism group of a splitting field realizes every permutation of the roots, then the
`(deg)!` labelled actions form a single orbit, so the minimal polynomial of one of them already has
degree `(deg)!` and therefore *is* the resolvent.
-/

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial

/-- **The resolvent is irreducible when the automorphism group is as large as possible.** -/
theorem irreducible_resolvent_of_indexing
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (φK : ℚ →+* K) (φL : ℚ →+* L) (hφ : (algebraMap K L).comp φK = φL)
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    {F : Polynomial K}
    {β : σ → L} (hβ : Function.Injective β)
    (hFprod : F.map (algebraMap K L) = ∏ j, (Polynomial.X - Polynomial.C (β j)))
    (hgen : Algebra.adjoin K (Set.range β) = ⊤)
    (hcard : Nat.card (L ≃ₐ[K] L) = Nat.card (Equiv.Perm σ)) :
    ∃ k : σ → ℚ, Irreducible (resolvent k φK F) := by
  classical
  obtain ⟨k, hk⟩ := exists_separating_label φL hβ
  obtain ⟨θ, hθ⟩ : ∃ θ : Equiv.Perm σ → L,
      θ = fun π => ∑ j, φL (k j) * β (π j) := ⟨_, rfl⟩
  rw [← hθ] at hk
  refine ⟨k, ?_⟩
  obtain ⟨R, hR⟩ : ∃ R : Polynomial K, R = resolvent k φK F := ⟨_, rfl⟩
  have hRmonic : R.Monic := hR ▸ monic_resolvent k φK F
  have hRdeg : R.natDegree = Fintype.card (Equiv.Perm σ) :=
    hR ▸ natDegree_resolvent k φK F
  have hRmap : R.map (algebraMap K L)
      = ∏ π : Equiv.Perm σ, (Polynomial.X - Polynomial.C (θ π)) := by
    rw [hR, resolvent_map k φK (algebraMap K L) F, hφ, hFprod, resolvent_eq_prod, hθ]
  have hperm : ∀ (g : L ≃ₐ[K] L) (j : σ), ∃ i, g (β j) = β i := by
    intro g j
    have hroot : Polynomial.aeval (β j) F = 0 := by
      have h1 : Polynomial.eval (β j) (F.map (algebraMap K L)) = 0 := by
        rw [hFprod, Polynomial.eval_prod]
        refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
        simp
      rwa [Polynomial.aeval_def, ← Polynomial.eval_map]
    have hroot2 : Polynomial.aeval (g (β j)) F = 0 := by
      rw [Polynomial.aeval_algHom_apply, hroot, map_zero]
    have h2 : Polynomial.eval (g (β j)) (F.map (algebraMap K L)) = 0 := by
      rwa [Polynomial.eval_map, ← Polynomial.aeval_def]
    rw [hFprod, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h2
    obtain ⟨i, -, hi⟩ := h2
    refine ⟨i, ?_⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hi
    exact hi
  choose ρ hρ using hperm
  have hρinj : ∀ g : L ≃ₐ[K] L, Function.Injective (ρ g) := by
    intro g a b hab
    apply hβ
    apply g.injective
    rw [hρ g a, hρ g b, hab]
  obtain ⟨τ, hτ⟩ : ∃ τ : (L ≃ₐ[K] L) → Equiv.Perm σ, ∀ g j, (τ g) j = ρ g j :=
    ⟨fun g => Equiv.ofBijective (ρ g) ((Finite.injective_iff_bijective).mp (hρinj g)),
      fun _ _ => rfl⟩
  have hτapp : ∀ (g : L ≃ₐ[K] L) (j : σ), g (β j) = β (τ g j) := by
    intro g j
    rw [hτ]
    exact hρ g j
  have hτinj : Function.Injective τ := by
    intro g h hgh
    have hval : ∀ x ∈ Set.range β, (g : L →ₐ[K] L) x = (h : L →ₐ[K] L) x := by
      rintro _ ⟨j, rfl⟩
      rw [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, hτapp g j, hτapp h j, hgh]
    have hEq := AlgHom.ext_of_adjoin_eq_top hgen hval
    exact AlgEquiv.coe_toAlgHom_injective hEq
  have hτsurj : Function.Surjective τ :=
    ((Nat.bijective_iff_injective_and_card τ).mpr ⟨hτinj, hcard⟩).2
  have hact : ∀ (g : L ≃ₐ[K] L) (π : Equiv.Perm σ), g (θ π) = θ (τ g * π) := by
    intro g π
    simp only [hθ]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hτapp g (π j)]
    congr 1
    rw [← hφ]
    exact g.commutes _
  have hθroot : Polynomial.aeval (θ 1) R = 0 := by
    have h1 : Polynomial.eval (θ 1) (R.map (algebraMap K L)) = 0 := by
      rw [hRmap, Polynomial.eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ (1 : Equiv.Perm σ)) ?_
      simp
    rwa [Polynomial.eval_map, ← Polynomial.aeval_def] at h1
  have hint : IsIntegral K (θ 1) := ⟨R, hRmonic, by rwa [← Polynomial.aeval_def]⟩
  have hdvd : minpoly K (θ 1) ∣ R := minpoly.dvd K (θ 1) hθroot
  have hMne : minpoly K (θ 1) ≠ 0 := minpoly.ne_zero hint
  have hMmonic : (minpoly K (θ 1)).Monic := minpoly.monic hint
  have hMroot : ∀ π : Equiv.Perm σ, Polynomial.aeval (θ π) (minpoly K (θ 1)) = 0 := by
    intro π
    obtain ⟨g, hg⟩ := hτsurj π
    have hgθ : θ π = g (θ 1) := by rw [hact g 1, hg, mul_one]
    rw [hgθ, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hdegM : Fintype.card (Equiv.Perm σ) ≤ (minpoly K (θ 1)).natDegree := by
    have hmapne : (minpoly K (θ 1)).map (algebraMap K L) ≠ 0 := Polynomial.map_ne_zero hMne
    have hsub : (Finset.univ.image θ) ⊆
        ((minpoly K (θ 1)).map (algebraMap K L)).roots.toFinset := by
      intro x hx
      obtain ⟨π, -, rfl⟩ := Finset.mem_image.mp hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hmapne]
      rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact hMroot π
    calc Fintype.card (Equiv.Perm σ)
        = (Finset.univ.image θ).card := by
          rw [Finset.card_image_of_injective _ hk, Finset.card_univ]
      _ ≤ ((minpoly K (θ 1)).map (algebraMap K L)).roots.toFinset.card :=
          Finset.card_le_card hsub
      _ ≤ Multiset.card ((minpoly K (θ 1)).map (algebraMap K L)).roots :=
          Multiset.toFinset_card_le _
      _ ≤ ((minpoly K (θ 1)).map (algebraMap K L)).natDegree := Polynomial.card_roots' _
      _ = (minpoly K (θ 1)).natDegree :=
          Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective _
  have hRne : R ≠ 0 := hRmonic.ne_zero
  have hdegle : (minpoly K (θ 1)).natDegree ≤ R.natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hRne
  obtain ⟨q, hq⟩ := hdvd
  have hqne : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hRne hq
  have hqmonic : q.Monic := hMmonic.of_mul_monic_left (hq ▸ hRmonic)
  have hqdeg : q.natDegree = 0 := by
    have hmul := Polynomial.natDegree_mul hMne hqne
    rw [← hq] at hmul
    omega
  have hq1 : q = 1 := by
    have h1 := Polynomial.eq_C_of_natDegree_eq_zero hqdeg
    have h2 : q.coeff 0 = 1 := by
      have h3 := hqmonic
      rw [Polynomial.Monic, Polynomial.leadingCoeff, hqdeg] at h3
      exact h3
    rw [h1, h2, map_one]
  rw [← hR, hq, hq1, mul_one]
  exact minpoly.irreducible hint
end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
