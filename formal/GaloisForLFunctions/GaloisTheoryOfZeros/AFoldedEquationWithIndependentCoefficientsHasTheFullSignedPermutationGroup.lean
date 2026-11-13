import GaloisForLFunctions.GaloisTheoryOfZeros.TheFoldedCoefficientsGenerateTheFixedFieldOfTheSignedPermutations
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# A folded equation with independent coefficients has the full signed permutation group

Specialization of the generic folded equation. Let `c₀, …, c_{n−1}` be elements of an extension
of `K`, algebraically independent over `K`. Then the group of the folded equation
`X^{2n} + Σ_k c_k X^{2k}` over the field `K(c)` of its coefficients is the group `C₂ ≀ S_n` of
signed permutations of `n` pairs (`foldedGaloisEquivOfAlgebraicIndependent`), of order `2ⁿ n!`.

* The folded coefficients `γ_k` of the generic equation are, up to sign, the elementary symmetric
  functions of the squares `x_i²`. These are algebraically independent: the symmetric functions
  are, and `x_i ↦ x_i²` is injective on polynomials (`algebraicIndependent_foldedCoeff`).
* Two algebraically independent families of the same size generate isomorphic fields, so
  `K(c) ≅ K(γ)` by `c_k ↦ γ_k`, and this carries the equation to the generic folded equation.
* A splitting field and its group of automorphisms pass through an isomorphism of the base fields
  (`isSplittingField_of_compatible`, `autEquivOfCompatible`).

Contrapositive: a folded equation whose group over its coefficients is smaller than `2ⁿ n!` has
algebraically dependent coefficients (`not_algebraicIndependent_of_card_foldedGal_ne`).
-/

namespace GaloisForLFunctions.GaloisTheoryOfZeros

open MvPolynomial
open GaloisForLFunctions.HTGeometry (SymmetricRationalField)
open FibreSignedPerm

noncomputable section
set_option autoImplicit false

/-! ## Scaling an independent family -/

/-- Scaling the members of an algebraically independent family by nonzero constants keeps it
algebraically independent: the substitution `X_i ↦ u_i X_i` is invertible. -/
theorem algebraicIndependent_const_mul {K A ι : Type*} [Field K] [CommRing A] [Algebra K A]
    {x : ι → A} (hx : AlgebraicIndependent K x) (u : ι → K) (hu : ∀ i, u i ≠ 0) :
    AlgebraicIndependent K fun i => algebraMap K A (u i) * x i := by
  rw [algebraicIndependent_iff_injective_aeval] at hx ⊢
  have hfac : (aeval fun i => algebraMap K A (u i) * x i : MvPolynomial ι K →ₐ[K] A) =
      (aeval x).comp (aeval fun i => C (u i) * X i) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, aeval_X, aeval_X, map_mul, aeval_C, aeval_X]
  have hinv : Function.LeftInverse
      (aeval fun i => C (u i)⁻¹ * X i : MvPolynomial ι K →ₐ[K] MvPolynomial ι K)
      (aeval fun i => C (u i) * X i : MvPolynomial ι K →ₐ[K] MvPolynomial ι K) := by
    intro p
    have hcomp : ((aeval fun i => C (u i)⁻¹ * X i :
          MvPolynomial ι K →ₐ[K] MvPolynomial ι K).comp
        (aeval fun i => C (u i) * X i)) = AlgHom.id K (MvPolynomial ι K) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, aeval_X, map_mul, aeval_C, aeval_X, AlgHom.id_apply,
        MvPolynomial.algebraMap_eq, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (hu i), C_1, one_mul]
    exact congrArg (fun f : MvPolynomial ι K →ₐ[K] MvPolynomial ι K => f p) hcomp
  rw [hfac, AlgHom.coe_comp]
  exact hx.comp hinv.injective

/-! ## Transport along an isomorphism of base fields -/

section Transport

variable {A B E : Type*} [Field A] [Field B] [Field E] [Algebra A E] [Algebra B E]

/-- If `A` acts on `E` through an isomorphism `A ≃ B`, the automorphisms of `E` over `B` are the
automorphisms of `E` over `A`. -/
def autEquivOfCompatible (e : A ≃+* B) (he : ∀ a, algebraMap B E (e a) = algebraMap A E a) :
    (E ≃ₐ[B] E) ≃* (E ≃ₐ[A] E) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun a => by
    show σ (algebraMap A E a) = algebraMap A E a
    rw [← he, σ.commutes]
  invFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun b => by
    show σ (algebraMap B E b) = algebraMap B E b
    rw [← e.apply_symm_apply b, he, σ.commutes]
  left_inv _ := AlgEquiv.ext fun _ => rfl
  right_inv _ := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

/-- If `A` acts on `E` through an isomorphism `A ≃ B` and `E` is a splitting field over `B` of the
image of `p`, then `E` is a splitting field of `p` over `A`. -/
theorem isSplittingField_of_compatible (e : A ≃+* B)
    (he : ∀ a, algebraMap B E (e a) = algebraMap A E a) (p : Polynomial A)
    [h : Polynomial.IsSplittingField B E (p.map (e : A →+* B))] :
    Polynomial.IsSplittingField A E p := by
  have hmap : (p.map (e : A →+* B)).map (algebraMap B E) = p.map (algebraMap A E) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext he
  have hroot : (p.map (e : A →+* B)).rootSet E = p.rootSet E := by
    ext z
    rw [Polynomial.mem_rootSet', Polynomial.mem_rootSet', Polynomial.aeval_def,
      Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_eq_eval_map, hmap]
  have hrange : Set.range (algebraMap B E) = Set.range (algebraMap A E) := by
    ext w
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨e.symm b, by rw [← he, e.apply_symm_apply]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨e a, he a⟩
  refine ⟨?_, ?_⟩
  · rw [← hmap]
    exact Polynomial.IsSplittingField.splits E (p.map (e : A →+* B))
  · have hadj := Polynomial.IsSplittingField.adjoin_rootSet E (p.map (e : A →+* B))
    rw [hroot] at hadj
    refine eq_top_iff.2 fun z _ => ?_
    have hz : z ∈ Algebra.adjoin B (p.rootSet E) := by
      rw [hadj]
      exact Algebra.mem_top
    rw [← Subalgebra.mem_toSubring, Algebra.adjoin_eq_ring_closure] at hz ⊢
    rw [hrange] at hz
    exact hz

end Transport

variable {K : Type*} [Field K] {n : ℕ}

/-! ## The folded coefficients are algebraically independent -/

private theorem coeff_prod_X_sub_C_X {k : ℕ} (hk : k ≤ n) :
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (X i : MvPolynomial (Fin n) K))).coeff k =
      (-1) ^ (n - k) * esymm (Fin n) K (n - k) := by
  classical
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hrewrite : (∏ i : Fin n, (Polynomial.X - Polynomial.C (X i : MvPolynomial (Fin n) K))) =
      ∏ i : Fin n, (Polynomial.X + Polynomial.C (-(X i : MvPolynomial (Fin n) K))) :=
    Finset.prod_congr rfl fun i _ => by rw [map_neg, sub_eq_add_neg]
  rw [hrewrite, Finset.prod_X_add_C_coeff _ _ (by rw [hcard]; exact hk), hcard,
    MvPolynomial.esymm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_powersetCard] at ht
  rw [Finset.prod_neg, ht.2]

private theorem foldedQuotientF_eq_map :
    foldedQuotientF K n =
      (∏ i : Fin n, (Polynomial.X - Polynomial.C (X i : MvPolynomial (Fin n) K))).map
        ((algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n)).comp
          (expand 2 : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K).toRingHom) := by
  rw [foldedQuotientF, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  congr 2
  show foldedRoot K n i ^ 2 =
    algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n) (expand 2 (X i))
  rw [expand_X, map_pow]
  rfl

/-- **Vieta for the folded coefficients:** `γ_k = (−1)^{n−k} e_{n−k}(x₁², …, x_n²)`. -/
theorem foldedCoeff_eq (k : Fin n) :
    foldedCoeff K n k =
      algebraMap K (SymmetricRationalField K n) ((-1) ^ (n - (k : ℕ))) *
        algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n)
          (expand 2 (esymm (Fin n) K (n - (k : ℕ)))) := by
  have h1 : foldedCoeff K n k =
      algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n)
        (expand 2 ((-1) ^ (n - (k : ℕ)) * esymm (Fin n) K (n - (k : ℕ)))) := by
    rw [foldedCoeff, foldedQuotientF_eq_map, Polynomial.coeff_map,
      coeff_prod_X_sub_C_X (le_of_lt k.2)]
    rfl
  rw [h1]
  simp only [map_mul, map_pow, map_neg, map_one]

/-- The elementary symmetric functions of the squares of the variables. -/
private def squareEsymm (K : Type*) [Field K] (n : ℕ) (j : Fin n) : SymmetricRationalField K n :=
  algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n)
    (expand 2 (esymm (Fin n) K ((j : ℕ) + 1)))

private theorem algebraicIndependent_squareEsymm :
    AlgebraicIndependent K (squareEsymm K n) := by
  have hfactor : (aeval (squareEsymm K n) :
        MvPolynomial (Fin n) K →ₐ[K] SymmetricRationalField K n) =
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) (SymmetricRationalField K n)).comp
        ((expand 2).comp ((Subalgebra.val _).comp (esymmAlgHom (Fin n) K n))) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp only [aeval_X, AlgHom.comp_apply, Subalgebra.val_apply, esymmAlgHom_apply,
      IsScalarTower.toAlgHom_apply, squareEsymm]
  have h1 : Function.Injective (esymmAlgHom (Fin n) K n) :=
    esymmAlgHom_injective (R := K) (σ := Fin n) (n := n) (Fintype.card_fin n).ge
  have h2 : Function.Injective
      (expand 2 : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K) :=
    expand_injective (by norm_num)
  rw [algebraicIndependent_iff_injective_aeval, hfactor]
  intro p q hpq
  simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] at hpq
  exact h1 (Subtype.ext (h2 (IsFractionRing.injective _ _ hpq)))

/-- **The folded coefficients are algebraically independent over the constants.** -/
theorem algebraicIndependent_foldedCoeff (K : Type*) [Field K] (n : ℕ) :
    AlgebraicIndependent K (foldedCoeff K n) := by
  have h1 := (algebraicIndependent_squareEsymm (K := K) (n := n)).comp Fin.rev Fin.rev_injective
  have h2 := algebraicIndependent_const_mul h1 (fun k : Fin n => (-1 : K) ^ (n - (k : ℕ)))
    fun k => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have hfun : (fun k : Fin n =>
      algebraMap K (SymmetricRationalField K n) ((-1 : K) ^ (n - (k : ℕ))) *
        (squareEsymm K n ∘ Fin.rev) k) = foldedCoeff K n := by
    funext k
    have hk : ((Fin.rev k : Fin n) : ℕ) + 1 = n - (k : ℕ) := by
      have := k.2
      rw [Fin.val_rev]
      omega
    rw [foldedCoeff_eq, Function.comp_apply, squareEsymm, hk]
  rw [← hfun]
  exact h2

/-! ## Specialization -/

variable {L : Type*} [Field L] [Algebra K L]

/-- The members of a family as elements of the field they generate. -/
def adjoinGen (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L] {n : ℕ} (c : Fin n → L)
    (k : Fin n) : IntermediateField.adjoin K (Set.range c) :=
  ⟨c k, IntermediateField.subset_adjoin K _ ⟨k, rfl⟩⟩

/-- The folded equation `X^{2n} + Σ_k c_k X^{2k}` over the field `K(c)` generated by its
coefficients. -/
def foldedEquationOver (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L] {n : ℕ}
    (c : Fin n → L) : Polynomial (IntermediateField.adjoin K (Set.range c)) :=
  foldedEquation (adjoinGen K c)

theorem map_foldedEquationOver_algebraMap (c : Fin n → L) :
    (foldedEquationOver K c).map (algebraMap (IntermediateField.adjoin K (Set.range c)) L) =
      foldedEquation c := by
  rw [foldedEquationOver, map_foldedEquation]
  rfl

/-- The field generated by an algebraically independent family of `n` elements is the field of
the generic folded coefficients, by `c_k ↦ γ_k`. -/
def coeffFieldEquiv {c : Fin n → L} (hc : AlgebraicIndependent K c) :
    IntermediateField.adjoin K (Set.range c) ≃ₐ[K] foldedCoeffField K n :=
  hc.aevalEquivField.symm.trans (algebraicIndependent_foldedCoeff K n).aevalEquivField

theorem coeffFieldEquiv_adjoinGen {c : Fin n → L} (hc : AlgebraicIndependent K c) (k : Fin n) :
    coeffFieldEquiv hc (adjoinGen K c k) = foldedCoeffIn K n k := by
  have h1 : hc.aevalEquivField (algebraMap (MvPolynomial (Fin n) K)
      (FractionRing (MvPolynomial (Fin n) K)) (X k)) = adjoinGen K c k :=
    Subtype.ext ((hc.aevalEquivField_algebraMap_apply_coe (X k)).trans (aeval_X c k))
  have h2 : (algebraicIndependent_foldedCoeff K n).aevalEquivField
      (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (X k)) =
        foldedCoeffIn K n k :=
    Subtype.ext (((algebraicIndependent_foldedCoeff K n).aevalEquivField_algebraMap_apply_coe
      (X k)).trans (aeval_X (foldedCoeff K n) k))
  rw [coeffFieldEquiv, AlgEquiv.trans_apply, ← h1, AlgEquiv.symm_apply_apply]
  exact h2

/-- The isomorphism `K(c) ≅ K(γ)` carries the folded equation to the generic folded equation. -/
theorem map_foldedEquationOver {c : Fin n → L} (hc : AlgebraicIndependent K c) :
    (foldedEquationOver K c).map
        ((coeffFieldEquiv hc).toRingEquiv :
          IntermediateField.adjoin K (Set.range c) →+* foldedCoeffField K n) =
      genericFoldedOver K n := by
  rw [foldedEquationOver, map_foldedEquation, genericFoldedOver]
  congr 1
  funext k
  exact coeffFieldEquiv_adjoinGen hc k

/-- **A folded equation with algebraically independent coefficients has the full group of signed
permutations of its `n` pairs of roots.** -/
def foldedGaloisEquivOfAlgebraicIndependent [NeZero (2 : K)] {c : Fin n → L}
    (hc : AlgebraicIndependent K c) :
    FibreSignedPerm (Fin n) ≃* (foldedEquationOver K c).Gal :=
  letI : Algebra (IntermediateField.adjoin K (Set.range c)) (SymmetricRationalField K n) :=
    ((algebraMap (foldedCoeffField K n) (SymmetricRationalField K n)).comp
      ((coeffFieldEquiv hc).toRingEquiv :
        IntermediateField.adjoin K (Set.range c) →+* foldedCoeffField K n)).toAlgebra
  haveI : Polynomial.IsSplittingField (foldedCoeffField K n) (SymmetricRationalField K n)
      ((foldedEquationOver K c).map ((coeffFieldEquiv hc).toRingEquiv :
        IntermediateField.adjoin K (Set.range c) →+* foldedCoeffField K n)) := by
    rw [map_foldedEquationOver hc]
    infer_instance
  haveI : Polynomial.IsSplittingField (IntermediateField.adjoin K (Set.range c))
      (SymmetricRationalField K n) (foldedEquationOver K c) :=
    isSplittingField_of_compatible (coeffFieldEquiv hc).toRingEquiv (fun _ => rfl)
      (foldedEquationOver K c)
  ((foldedCoeffGaloisEquiv K n).trans
    (autEquivOfCompatible (coeffFieldEquiv hc).toRingEquiv fun _ => rfl)).trans
    (AlgEquiv.autCongr
      (Polynomial.IsSplittingField.algEquiv (SymmetricRationalField K n)
        (foldedEquationOver K c)))

theorem card_foldedGal_of_algebraicIndependent [NeZero (2 : K)] {c : Fin n → L}
    (hc : AlgebraicIndependent K c) :
    Nat.card (foldedEquationOver K c).Gal = n.factorial * 2 ^ n := by
  rw [← Nat.card_congr (foldedGaloisEquivOfAlgebraicIndependent hc).toEquiv, natCard]

/-- **The reflection of all roots is central** in the group of a folded equation with independent
coefficients. -/
theorem foldedGal_uniformFlip_comm [NeZero (2 : K)] {c : Fin n → L}
    (hc : AlgebraicIndependent K c) (g : (foldedEquationOver K c).Gal) :
    g * foldedGaloisEquivOfAlgebraicIndependent hc (uniformFlip (Fin n)) =
      foldedGaloisEquivOfAlgebraicIndependent hc (uniformFlip (Fin n)) * g := by
  obtain ⟨a, rfl⟩ := (foldedGaloisEquivOfAlgebraicIndependent hc).surjective g
  rw [← map_mul, ← map_mul, uniformFlip_mul_comm]

/-- **Specialization.** A folded equation whose group over the field of its coefficients does not
have order `2ⁿ n!` has algebraically dependent coefficients. -/
theorem not_algebraicIndependent_of_card_foldedGal_ne [NeZero (2 : K)] {c : Fin n → L}
    (h : Nat.card (foldedEquationOver K c).Gal ≠ n.factorial * 2 ^ n) :
    ¬ AlgebraicIndependent K c :=
  fun hc => h (card_foldedGal_of_algebraicIndependent hc)

end

end GaloisForLFunctions.GaloisTheoryOfZeros
