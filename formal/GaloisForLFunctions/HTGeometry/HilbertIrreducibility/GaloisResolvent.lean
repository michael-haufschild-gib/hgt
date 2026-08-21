import GaloisForLFunctions.HTGeometry.SymmetricEsymmRepresentation
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The Galois resolvent as a universal construction

For a fixed label vector `k` the polynomial `∏_π (T - ∑_j k_j α_{π j})` has coefficients symmetric
in the roots `α`, hence — by the fundamental theorem of symmetric polynomials — fixed polynomial
expressions in the elementary symmetric functions, i.e. in the coefficients of the polynomial whose
roots the `α` are.  Writing the resolvent that way makes it a construction on *coefficients*, so it
commutes with every ring homomorphism, in particular with specialization of parameters.
-/

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open MvPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The representative, in the elementary symmetric functions, of the `m`-th coefficient of the
universal resolvent. -/
noncomputable def resolventRepr (k : σ → ℚ) (m : ℕ) :
    MvPolynomial (Fin (Fintype.card σ)) ℚ :=
  Classical.choose (exists_bind₁_esymm_of_isSymmetric ((labeledActionPoly k).coeff m)
    (isSymmetric_coeff_labeledActionPoly k m))

theorem bind₁_resolventRepr (k : σ → ℚ) (m : ℕ) :
    MvPolynomial.bind₁ (fun i : Fin (Fintype.card σ) => MvPolynomial.esymm σ ℚ (i + 1))
        (resolventRepr k m)
      = (labeledActionPoly k).coeff m :=
  Classical.choose_spec (exists_bind₁_esymm_of_isSymmetric ((labeledActionPoly k).coeff m)
    (isSymmetric_coeff_labeledActionPoly k m))

theorem eval₂_resolventRepr (k : σ → ℚ) {A : Type*} [CommRing A] (φ : ℚ →+* A) (β : σ → A)
    (m : ℕ) :
    MvPolynomial.eval₂ φ β ((labeledActionPoly k).coeff m)
      = MvPolynomial.eval₂ φ
          (fun i : Fin (Fintype.card σ) =>
            MvPolynomial.eval₂ φ β (MvPolynomial.esymm σ ℚ (i + 1))) (resolventRepr k m) := by
  rw [← bind₁_resolventRepr k m, eval₂_of_bind₁_esymm]

/-- The elementary-symmetric coordinates read off the coefficients of a monic polynomial of
degree `Fintype.card σ`. -/
def esymmCoord (σ : Type*) [Fintype σ] {A : Type*} [CommRing A] (p : Polynomial A) :
    Fin (Fintype.card σ) → A :=
  fun i => (-1) ^ ((i : ℕ) + 1) * p.coeff (Fintype.card σ - ((i : ℕ) + 1))

/-- **The resolvent of a monic polynomial.** -/
noncomputable def resolvent (k : σ → ℚ) {A : Type*} [CommRing A] (φ : ℚ →+* A)
    (p : Polynomial A) : Polynomial A :=
  ∑ m ∈ Finset.range (Fintype.card (Equiv.Perm σ) + 1),
    Polynomial.C (MvPolynomial.eval₂ φ (esymmCoord σ p) (resolventRepr k m)) * Polynomial.X ^ m

omit [DecidableEq σ] in
theorem esymmCoord_map {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (p : Polynomial A) (i : Fin (Fintype.card σ)) :
    esymmCoord σ (p.map ψ) i = ψ (esymmCoord σ p i) := by
  simp [esymmCoord, Polynomial.coeff_map]

/-- **The resolvent commutes with every ring homomorphism.** -/
theorem resolvent_map (k : σ → ℚ) {A B : Type*} [CommRing A] [CommRing B]
    (φ : ℚ →+* A) (ψ : A →+* B) (p : Polynomial A) :
    (resolvent k φ p).map ψ = resolvent k (ψ.comp φ) (p.map ψ) := by
  rw [resolvent, resolvent, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    MvPolynomial.hom_eval₂]
  have hfun : (fun i => ψ (esymmCoord σ p i)) = esymmCoord σ (Polynomial.map ψ p) := by
    funext i
    rw [esymmCoord_map]
  rw [hfun]

theorem monic_labeledActionPoly (k : σ → ℚ) : (labeledActionPoly k).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem natDegree_labeledActionPoly (k : σ → ℚ) :
    (labeledActionPoly k).natDegree = Fintype.card (Equiv.Perm σ) := by
  classical
  rw [labeledActionPoly, Polynomial.natDegree_prod _ _ fun _ _ => (Polynomial.X_sub_C_ne_zero _)]
  simp [Finset.card_univ]

omit [DecidableEq σ] in
theorem eval₂_esymm_eq_esymmCoord {A : Type*} [CommRing A] (φ : ℚ →+* A) (β : σ → A)
    (i : Fin (Fintype.card σ)) :
    MvPolynomial.eval₂ φ β (MvPolynomial.esymm σ ℚ ((i : ℕ) + 1))
      = esymmCoord σ (∏ j, (Polynomial.X - Polynomial.C (β j))) i := by
  classical
  have hs : (Multiset.map β Finset.univ.val).card = Fintype.card σ := by
    simp [Finset.card_univ]
  have hprod : (∏ j, (Polynomial.X - Polynomial.C (β j)))
      = (Multiset.map (fun t => Polynomial.X - Polynomial.C t)
          (Multiset.map β Finset.univ.val)).prod := by
    rw [Multiset.map_map]
    rfl
  have hle : Fintype.card σ - ((i : ℕ) + 1) ≤ (Multiset.map β Finset.univ.val).card := by
    rw [hs]; omega
  have hi : (i : ℕ) + 1 ≤ Fintype.card σ := i.isLt
  have hsub : (Multiset.map β Finset.univ.val).card - (Fintype.card σ - ((i : ℕ) + 1))
      = (i : ℕ) + 1 := by rw [hs]; omega
  have hcoeff := Multiset.prod_X_sub_C_coeff (Multiset.map β Finset.univ.val) hle
  rw [hsub] at hcoeff
  have hlhs : MvPolynomial.eval₂ φ β (MvPolynomial.esymm σ ℚ ((i : ℕ) + 1))
      = (Multiset.map β Finset.univ.val).esymm ((i : ℕ) + 1) := by
    rw [MvPolynomial.eval₂_eq_eval_map, MvPolynomial.map_esymm]
    have h := MvPolynomial.aeval_esymm_eq_multiset_esymm σ A ((i : ℕ) + 1) β
    rw [MvPolynomial.aeval_eq_eval] at h
    exact h
  rw [hlhs, esymmCoord, hprod, hcoeff, ← mul_assoc, ← mul_pow]
  simp

/-- **The product formula.**  On a polynomial that splits, the resolvent is the product over all
labellings of the roots. -/
theorem resolvent_eq_prod (k : σ → ℚ) {A : Type*} [CommRing A] (φ : ℚ →+* A) (β : σ → A) :
    resolvent k φ (∏ j, (Polynomial.X - Polynomial.C (β j)))
      = ∏ π : Equiv.Perm σ, (Polynomial.X - Polynomial.C (∑ j, φ (k j) * β (π j))) := by
  classical
  have hmapeq : Polynomial.map (MvPolynomial.eval₂Hom φ β) (labeledActionPoly k)
      = ∏ π : Equiv.Perm σ, (Polynomial.X - Polynomial.C (∑ j, φ (k j) * β (π j))) := by
    rw [labeledActionPoly, ← Polynomial.coe_mapRingHom, map_prod, Polynomial.coe_mapRingHom]
    refine Finset.prod_congr rfl fun π _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    congr 2
    rw [labeledAction, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [← hmapeq]
  refine Polynomial.ext fun m => ?_
  rw [Polynomial.coeff_map, resolvent, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq _ m
    (fun m' => MvPolynomial.eval₂ φ (esymmCoord σ (∏ j, (Polynomial.X - Polynomial.C (β j))))
      (resolventRepr k m'))]
  by_cases hm : m ∈ Finset.range (Fintype.card (Equiv.Perm σ) + 1)
  · rw [if_pos hm, MvPolynomial.coe_eval₂Hom]
    rw [eval₂_resolventRepr k φ β m]
    congr 1
    funext i
    exact (eval₂_esymm_eq_esymmCoord φ β i).symm
  · rw [if_neg hm, MvPolynomial.coe_eval₂Hom]
    have hdz : (labeledActionPoly k).coeff m = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      rw [natDegree_labeledActionPoly]
      simpa [Finset.mem_range] using hm
    rw [hdz]
    simp

theorem coeff_resolvent (k : σ → ℚ) {A : Type*} [CommRing A] (φ : ℚ →+* A) (p : Polynomial A)
    (m : ℕ) :
    (resolvent k φ p).coeff m
      = if m ∈ Finset.range (Fintype.card (Equiv.Perm σ) + 1)
        then MvPolynomial.eval₂ φ (esymmCoord σ p) (resolventRepr k m) else 0 := by
  rw [resolvent, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq _ m _

theorem coeff_labeledActionPoly_top (k : σ → ℚ) :
    (labeledActionPoly k).coeff (Fintype.card (Equiv.Perm σ)) = 1 := by
  have h := monic_labeledActionPoly k
  rw [Polynomial.Monic, Polynomial.leadingCoeff, natDegree_labeledActionPoly] at h
  exact h

theorem resolventRepr_top (k : σ → ℚ) :
    resolventRepr k (Fintype.card (Equiv.Perm σ)) = 1 := by
  refine MvPolynomial.esymmAlgHom_injective (σ := σ) ℚ le_rfl (Subtype.ext ?_)
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.esymmAlgHom_apply, map_one,
    MvPolynomial.aeval_eq_bind₁, bind₁_resolventRepr, coeff_labeledActionPoly_top]

theorem natDegree_resolvent_le (k : σ → ℚ) {A : Type*} [CommRing A] (φ : ℚ →+* A)
    (p : Polynomial A) :
    (resolvent k φ p).natDegree ≤ Fintype.card (Equiv.Perm σ) := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_resolvent, if_neg]
  simp only [Finset.mem_range]
  omega

theorem coeff_resolvent_top (k : σ → ℚ) {A : Type*} [CommRing A] (φ : ℚ →+* A)
    (p : Polynomial A) :
    (resolvent k φ p).coeff (Fintype.card (Equiv.Perm σ)) = 1 := by
  rw [coeff_resolvent, if_pos (by simp), resolventRepr_top]
  simp

theorem monic_resolvent (k : σ → ℚ) {A : Type*} [CommRing A] (φ : ℚ →+* A)
    (p : Polynomial A) : (resolvent k φ p).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ (natDegree_resolvent_le k φ p)
    (coeff_resolvent_top k φ p)

theorem natDegree_resolvent (k : σ → ℚ) {A : Type*} [CommRing A] [Nontrivial A] (φ : ℚ →+* A)
    (p : Polynomial A) :
    (resolvent k φ p).natDegree = Fintype.card (Equiv.Perm σ) :=
  le_antisymm (natDegree_resolvent_le k φ p)
    (Polynomial.le_natDegree_of_ne_zero (by rw [coeff_resolvent_top]; exact one_ne_zero))

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility


