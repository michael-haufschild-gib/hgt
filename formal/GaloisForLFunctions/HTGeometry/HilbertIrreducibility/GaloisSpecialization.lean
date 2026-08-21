import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.ResolventIrreducible
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.SeveralVariables
import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-!
# Specializing a parametrised polynomial without losing the Galois group

The resolvent of a parametrised polynomial is a monic polynomial in the parameters, irreducible
because the generic Galois group is the full symmetric group.  Hilbert irreducibility keeps it
irreducible at a rational point, and an irreducible resolvent of degree `D !` forces the specialized
splitting field to have degree `D !`.
-/

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial IntermediateField

/-- A monic polynomial that splits is the product of `natDegree` linear factors indexed by
`Fin D`. -/
theorem exists_root_index {F : Type*} [Field F] {M : Type*} [Field M] [Algebra F M]
    {p : Polynomial F} (hp : p.Monic) (hsplit : (p.map (algebraMap F M)).Splits)
    {D : ℕ} (hD : p.natDegree = D) :
    ∃ γ : Fin D → M, p.map (algebraMap F M) = ∏ j, (Polynomial.X - Polynomial.C (γ j)) := by
  classical
  have hqm : (p.map (algebraMap F M)).Monic := hp.map _
  have hlen : (p.map (algebraMap F M)).roots.toList.length = D := by
    rw [Multiset.length_toList, ← hsplit.natDegree_eq_card_roots,
      Polynomial.natDegree_map_eq_of_injective (algebraMap F M).injective, hD]
  have hprod : ∀ l : List M, (l.map (fun t => Polynomial.X - Polynomial.C t)).prod
      = ∏ i : Fin l.length, (Polynomial.X - Polynomial.C (l.get i)) := by
    intro l
    conv_lhs => rw [← List.ofFn_get l]
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  refine ⟨fun i => (p.map (algebraMap F M)).roots.toList.get ((finCongr hlen).symm i), ?_⟩
  conv_lhs => rw [hsplit.eq_prod_roots_of_monic hqm,
    ← Multiset.coe_toList (p.map (algebraMap F M)).roots, Multiset.map_coe, Multiset.prod_coe,
    hprod]
  exact Fintype.prod_equiv (finCongr hlen)
    (fun i => Polynomial.X - Polynomial.C ((p.map (algebraMap F M)).roots.toList.get i))
    (fun j => Polynomial.X - Polynomial.C ((p.map (algebraMap F M)).roots.toList.get
      ((finCongr hlen).symm j)))
    (fun i => by rw [Equiv.symm_apply_apply])

/-- **The resolvent is irreducible whenever the Galois group is the full symmetric group.** -/
theorem exists_irreducible_resolvent {K : Type*} [Field K] (φK : ℚ →+* K) {D : ℕ}
    {F : Polynomial K} (hFm : F.Monic) (hFsep : F.Separable) (hFdeg : F.natDegree = D)
    (hgal : Nat.card F.Gal = D.factorial) :
    ∃ k : Fin D → ℚ, Irreducible (resolvent k φK F) := by
  classical
  have hsplit : (F.map (algebraMap K F.SplittingField)).Splits :=
    Polynomial.IsSplittingField.splits _ F
  obtain ⟨β, hβprod⟩ := exists_root_index hFm hsplit hFdeg
  have hrootsβ : (F.map (algebraMap K F.SplittingField)).roots
      = Multiset.map β Finset.univ.val := by
    have hrw : (∏ j, (Polynomial.X - Polynomial.C (β j)))
        = (Multiset.map (fun a => Polynomial.X - Polynomial.C a)
            (Multiset.map β Finset.univ.val)).prod := by
      rw [Multiset.map_map]
      rfl
    rw [hβprod, hrw, Polynomial.roots_multiset_prod_X_sub_C]
  have hnodup : (Multiset.map β Finset.univ.val).Nodup := by
    rw [← hrootsβ]
    exact Polynomial.nodup_roots hFsep.map
  have hβinj : Function.Injective β := by
    intro a b hab
    exact Multiset.inj_on_of_nodup_map hnodup a (Finset.mem_univ a) b (Finset.mem_univ b) hab
  have hrange : Set.range β = F.rootSet F.SplittingField := by
    rw [Polynomial.rootSet, Polynomial.aroots, hrootsβ]
    simp
    rfl
  have hgen : Algebra.adjoin K (Set.range β) = ⊤ := by
    rw [hrange]
    exact Polynomial.IsSplittingField.adjoin_rootSet _ F
  have hcard : Nat.card (F.SplittingField ≃ₐ[K] F.SplittingField)
      = Nat.card (Equiv.Perm (Fin D)) := by
    have h1 : Nat.card (Equiv.Perm (Fin D)) = D.factorial := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rw [h1]
    exact hgal
  exact irreducible_resolvent_of_indexing φK ((algebraMap K F.SplittingField).comp φK) rfl
    hβinj hβprod hgen hcard

/-- **An irreducible resolvent forces the full symmetric Galois group.** -/
theorem gal_card_of_irreducible_resolvent {F : Type*} [Field F] [CharZero F] (φ : ℚ →+* F)
    {D : ℕ} {p : Polynomial F} (hpm : p.Monic) (hpdeg : p.natDegree = D) {k : Fin D → ℚ}
    (hirr : Irreducible (resolvent k φ p)) :
    Nat.card p.Gal = D.factorial := by
  classical
  have hsplit : (p.map (algebraMap F p.SplittingField)).Splits :=
    Polynomial.IsSplittingField.splits p.SplittingField p
  haveI : Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨hsplit⟩
  haveI : Normal F p.SplittingField := Polynomial.SplittingField.instNormal p
  haveI : IsGalois F p.SplittingField := ⟨⟩
  obtain ⟨γ, hγprod⟩ := exists_root_index hpm hsplit hpdeg
  have hRmonic : (resolvent k φ p).Monic := monic_resolvent k φ p
  have hRdeg : (resolvent k φ p).natDegree = D.factorial := by
    rw [natDegree_resolvent, Fintype.card_perm, Fintype.card_fin]
  have hRmap : (resolvent k φ p).map (algebraMap F p.SplittingField)
      = ∏ π : Equiv.Perm (Fin D),
        (Polynomial.X - Polynomial.C
          (∑ j, (algebraMap F p.SplittingField) (φ (k j)) * γ (π j))) := by
    rw [resolvent_map k φ (algebraMap F p.SplittingField) p, hγprod, resolvent_eq_prod]
    rfl
  obtain ⟨θ, hθ⟩ : ∃ θ : p.SplittingField,
      θ = ∑ j, (algebraMap F p.SplittingField) (φ (k j)) * γ j := ⟨_, rfl⟩
  have hθroot : Polynomial.aeval θ (resolvent k φ p) = 0 := by
    have h1 : Polynomial.eval θ
        ((resolvent k φ p).map (algebraMap F p.SplittingField)) = 0 := by
      rw [hRmap, Polynomial.eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ (1 : Equiv.Perm (Fin D))) ?_
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hθ, sub_eq_zero]
      simp
    rwa [Polynomial.eval_map, ← Polynomial.aeval_def] at h1
  have hint : IsIntegral F θ := ⟨_, hRmonic, by rwa [← Polynomial.aeval_def]⟩
  have hmin : resolvent k φ p = minpoly F θ :=
    minpoly.eq_of_irreducible_of_monic hirr hθroot hRmonic
  have hfr : Module.finrank F F⟮θ⟯ = D.factorial := by
    rw [IntermediateField.adjoin.finrank hint, ← hmin, hRdeg]
  have hdvd : D.factorial ∣ Module.finrank F p.SplittingField := by
    refine ⟨Module.finrank F⟮θ⟯ p.SplittingField, ?_⟩
    rw [← hfr]
    exact (Module.finrank_mul_finrank F F⟮θ⟯ p.SplittingField).symm
  have hpos : 0 < Module.finrank F p.SplittingField := Module.finrank_pos
  have hlow : D.factorial ≤ Module.finrank F p.SplittingField := Nat.le_of_dvd hpos hdvd
  have hgalcard : Nat.card p.Gal = Module.finrank F p.SplittingField :=
    IsGalois.card_aut_eq_finrank F p.SplittingField
  have hup : Nat.card p.Gal ≤ D.factorial := by
    have h1 : Nat.card p.Gal ≤ Nat.card (Equiv.Perm (p.rootSet p.SplittingField)) :=
      Nat.card_le_card_of_injective _ (Polynomial.Gal.galActionHom_injective p p.SplittingField)
    have h2 : Fintype.card (p.rootSet p.SplittingField) ≤ D := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      exact le_trans (Polynomial.ncard_rootSet_le p _) (le_of_eq hpdeg)
    have h3 : Nat.card (Equiv.Perm (p.rootSet p.SplittingField))
        = (Fintype.card (p.rootSet p.SplittingField)).factorial := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    rw [h3] at h1
    exact le_trans h1 (Nat.factorial_le h2)
  omega

/-- **Hilbert irreducibility preserving the Galois group.**  If a monic parametrised polynomial of
degree `D` is separable with full symmetric Galois group over the field of rational functions in the
parameters, then for a rational parameter point avoiding the zero locus of any prescribed nonzero
polynomial the specialized polynomial still has Galois group of order `D !`. -/
theorem gal_card_of_specialisation {m D : ℕ}
    {f : Polynomial (MvPolynomial (Fin m) ℚ)} (hf : f.Monic) (hfdeg : f.natDegree = D)
    (hsep : (f.map (algebraMap (MvPolynomial (Fin m) ℚ)
        (FractionRing (MvPolynomial (Fin m) ℚ)))).Separable)
    (hgal : Nat.card (f.map (algebraMap (MvPolynomial (Fin m) ℚ)
        (FractionRing (MvPolynomial (Fin m) ℚ)))).Gal = D.factorial)
    {g : MvPolynomial (Fin m) ℚ} (hg : g ≠ 0) :
    ∃ y : Fin m → ℚ, MvPolynomial.eval y g ≠ 0 ∧
      Nat.card (f.map (MvPolynomial.eval y)).Gal = D.factorial := by
  classical
  have hFm : (f.map (algebraMap (MvPolynomial (Fin m) ℚ)
      (FractionRing (MvPolynomial (Fin m) ℚ)))).Monic := hf.map _
  have hFdeg : (f.map (algebraMap (MvPolynomial (Fin m) ℚ)
      (FractionRing (MvPolynomial (Fin m) ℚ)))).natDegree = D := by
    rw [hf.natDegree_map, hfdeg]
  obtain ⟨k, hk⟩ := exists_irreducible_resolvent
    ((algebraMap (MvPolynomial (Fin m) ℚ) (FractionRing (MvPolynomial (Fin m) ℚ))).comp
      (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ)) hFm hsep hFdeg hgal
  have hR0map : (resolvent k (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ) f).map
      (algebraMap (MvPolynomial (Fin m) ℚ) (FractionRing (MvPolynomial (Fin m) ℚ)))
      = resolvent k ((algebraMap (MvPolynomial (Fin m) ℚ)
          (FractionRing (MvPolynomial (Fin m) ℚ))).comp
        (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ))
        (f.map (algebraMap (MvPolynomial (Fin m) ℚ)
          (FractionRing (MvPolynomial (Fin m) ℚ)))) :=
    resolvent_map k _ _ f
  have hR0irr : Irreducible (resolvent k (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ) f) :=
    Polynomial.Monic.irreducible_of_irreducible_map _ _
      (monic_resolvent k (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ) f)
      (by rw [hR0map]; exact hk)
  have hR0deg : (resolvent k (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ) f).natDegree
      = D.factorial := by
    rw [natDegree_resolvent, Fintype.card_perm, Fintype.card_fin]
  obtain ⟨y, hy1, hy2, -⟩ := hilbert_multivariate hR0irr
    (by rw [hR0deg]; exact Nat.factorial_pos D) hg
  refine ⟨y, hy1, ?_⟩
  have hcomp : (MvPolynomial.eval y).comp (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ)
      = RingHom.id ℚ := by
    refine RingHom.ext fun q => ?_
    simp
  have hspec : (resolvent k (MvPolynomial.C : ℚ →+* MvPolynomial (Fin m) ℚ) f).map
      (MvPolynomial.eval y) = resolvent k (RingHom.id ℚ) (f.map (MvPolynomial.eval y)) := by
    rw [resolvent_map k _ (MvPolynomial.eval y) f, hcomp]
  rw [hspec] at hy2
  exact gal_card_of_irreducible_resolvent (RingHom.id ℚ) (hf.map _)
    (by rw [hf.natDegree_map, hfdeg]) hy2

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility



