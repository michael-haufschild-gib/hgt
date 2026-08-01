import GaloisForLFunctions.HTGeometry.CenteredGenericGeneration

/-!
# The Galois group of the centered generic polynomial

An automorphism of the centered field over the centered coefficients fixes every coefficient of the
centered polynomial, so it carries each centered root to a centered root, and the centered roots
are distinct.  Since such an automorphism is determined by its values on the roots, the
automorphism group injects into the permutations of the indices.

The symmetric group injects the other way, so both injections are bijections: the Galois group of
the centered generic polynomial of degree `d` is the full symmetric group.
-/

set_option maxHeartbeats 2000000

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Polynomial

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-- The centered polynomial, read over the centered field. -/
noncomputable def centeredMonicL (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    Polynomial (centeredField K d) :=
  ∏ i : Fin d, (Polynomial.X - Polynomial.C (centeredRootIn K d i))

theorem monic_centeredMonicL : (centeredMonicL K d).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem natDegree_centeredMonicL : (centeredMonicL K d).natDegree = d := by
  rw [centeredMonicL,
    natDegree_prod_of_monic _ _ fun (i : Fin d) _ => monic_X_sub_C (centeredRootIn K d i)]
  simp

theorem map_centeredMonicL :
    Polynomial.map (algebraMap (centeredField K d) (SymmetricRationalField K d))
      (centeredMonicL K d) = centeredMonicF K d := by
  rw [centeredMonicL, centeredMonicF, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl

theorem coeff_centeredMonicL_lt {k : ℕ} (hk : k < d) :
    (centeredMonicL K d).coeff k = centeredCoeff K d ⟨k, hk⟩ := by
  have hinj : Function.Injective
      (algebraMap (centeredField K d) (SymmetricRationalField K d)) :=
    (algebraMap (centeredField K d) (SymmetricRationalField K d)).injective
  refine hinj ?_
  have h := congrArg (fun p : Polynomial (SymmetricRationalField K d) => p.coeff k)
    (map_centeredMonicL (K := K) (d := d))
  rw [Polynomial.coeff_map] at h
  rw [h]
  rfl

/-- **Every coefficient of the centered polynomial is fixed.** -/
theorem coeff_centeredMonicL_fixed
    (σ : (centeredField K d) ≃ₐ[centeredCoeffField K d] (centeredField K d)) (k : ℕ) :
    σ ((centeredMonicL K d).coeff k) = (centeredMonicL K d).coeff k := by
  rcases lt_trichotomy k d with hk | hk | hk
  · rw [coeff_centeredMonicL_lt hk]
    have hmem : centeredCoeff K d ⟨k, hk⟩ ∈ centeredCoeffField K d :=
      IntermediateField.subset_adjoin _ _ ⟨⟨k, hk⟩, rfl⟩
    have hval : (algebraMap (centeredCoeffField K d) (centeredField K d))
        ⟨centeredCoeff K d ⟨k, hk⟩, hmem⟩ = centeredCoeff K d ⟨k, hk⟩ := rfl
    rw [← hval, AlgEquiv.commutes]
  · have h1 : (centeredMonicL K d).coeff k = 1 := by
      have hm := monic_centeredMonicL (K := K) (d := d)
      rw [Polynomial.Monic, Polynomial.leadingCoeff, natDegree_centeredMonicL] at hm
      rw [hk]
      exact hm
    rw [h1, map_one]
  · have h0 : (centeredMonicL K d).coeff k = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      rw [natDegree_centeredMonicL]
      exact hk
    rw [h0, map_zero]

theorem eval_centeredMonicL_root (i : Fin d) :
    (centeredMonicL K d).eval (centeredRootIn K d i) = 0 := by
  rw [centeredMonicL, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- **An automorphism carries each centered root to a centered root.** -/
theorem exists_centeredRootIn_eq
    (σ : (centeredField K d) ≃ₐ[centeredCoeffField K d] (centeredField K d)) (i : Fin d) :
    ∃ j : Fin d, σ (centeredRootIn K d i) = centeredRootIn K d j := by
  have hmapfix : Polynomial.map (σ : (centeredField K d) →+* (centeredField K d))
      (centeredMonicL K d) = centeredMonicL K d := by
    refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_map]
    exact coeff_centeredMonicL_fixed σ k
  have hev : (centeredMonicL K d).eval (σ (centeredRootIn K d i)) = 0 := by
    have h := congrArg σ (eval_centeredMonicL_root (K := K) (d := d) i)
    rw [map_zero] at h
    rw [← h]
    show Polynomial.eval
        ((σ : (centeredField K d) →+* (centeredField K d)) (centeredRootIn K d i))
        (centeredMonicL K d) =
      (σ : (centeredField K d) →+* (centeredField K d))
        (Polynomial.eval (centeredRootIn K d i) (centeredMonicL K d))
    rw [← Polynomial.eval₂_hom, Polynomial.eval₂_eq_eval_map, hmapfix]
  rw [centeredMonicL, Polynomial.eval_prod] at hev
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 hev
  refine ⟨j, ?_⟩
  have := sub_eq_zero.1 (by simpa using hj)
  exact this

theorem centeredRootIn_injective : Function.Injective (centeredRootIn K d) := by
  intro i j hij
  exact centeredRoot_injective (Subtype.ext_iff.1 hij)

/-- The permutation of indices induced by an automorphism. -/
noncomputable def centeredRootPerm
    (σ : (centeredField K d) ≃ₐ[centeredCoeffField K d] (centeredField K d)) :
    Equiv.Perm (Fin d) := by
  classical
  refine Equiv.ofBijective (fun i => (exists_centeredRootIn_eq σ i).choose) ?_
  refine Finite.injective_iff_bijective.1 fun i j hij => ?_
  have hi := (exists_centeredRootIn_eq σ i).choose_spec
  have hj := (exists_centeredRootIn_eq σ j).choose_spec
  have : σ (centeredRootIn K d i) = σ (centeredRootIn K d j) := by
    rw [hi, hj, hij]
  exact centeredRootIn_injective (σ.injective this)

theorem centeredRootPerm_spec
    (σ : (centeredField K d) ≃ₐ[centeredCoeffField K d] (centeredField K d)) (i : Fin d) :
    σ (centeredRootIn K d i) = centeredRootIn K d (centeredRootPerm σ i) :=
  (exists_centeredRootIn_eq σ i).choose_spec

theorem centeredRootPerm_injective :
    Function.Injective
      (centeredRootPerm (K := K) (d := d)) := by
  intro σ τ hστ
  refine centeredAlgEquiv_ext fun i => ?_
  rw [centeredRootPerm_spec, centeredRootPerm_spec, hστ]

noncomputable instance centeredAutFinite (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    Finite ((centeredField K d) ≃ₐ[centeredCoeffField K d] (centeredField K d)) :=
  Finite.of_injective _ (centeredRootPerm_injective (K := K) (d := d))

/-- **The automorphism group of the centered field over its centered coefficients has exactly `d!`
elements.** -/
theorem card_centeredAut (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    Nat.card ((centeredField K d) ≃ₐ[centeredCoeffField K d] (centeredField K d)) =
      Nat.factorial d := by
  have hperm : Nat.card (Equiv.Perm (Fin d)) = Nat.factorial d := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  refine le_antisymm ?_ ?_
  · rw [← hperm]
    exact Nat.card_le_card_of_injective _ (centeredRootPerm_injective (K := K) (d := d))
  · rw [← hperm]
    exact Nat.card_le_card_of_injective _ (centeredPermAlgEquiv_injective K d)

/-- **The Galois group of the centered generic polynomial of degree `d` is the full symmetric
group.** -/
noncomputable def centeredGaloisEquiv (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    Equiv.Perm (Fin d) ≃*
      ((centeredField K d) ≃ₐ[centeredCoeffField K d] (centeredField K d)) := by
  refine MulEquiv.ofBijective (centeredPermAlgEquiv K d) ?_
  refine (Nat.bijective_iff_injective_and_card _).2
    ⟨centeredPermAlgEquiv_injective K d, ?_⟩
  rw [card_centeredAut, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

end GaloisForLFunctions.HTGeometry
