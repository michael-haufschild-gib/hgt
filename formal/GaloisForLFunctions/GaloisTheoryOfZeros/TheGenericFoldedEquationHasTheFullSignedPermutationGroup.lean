import GaloisForLFunctions.GaloisTheoryOfZeros.TheSignedPermutationsOfTheZeroFibres
import GaloisForLFunctions.HTGeometry.GenericPolynomialSplitting

/-!
# The generic folded equation has the full signed permutation group

A folded equation is `E(X²) = 0`: its roots come in pairs `±x`, as the centred zeros of `ξ` and the
roots of the centred Jensen equations do, and as the Frobenius roots of a curve do under
`α ↦ q/α`. Its group permutes the pairs and changes signs inside them, so it lies in the group of
signed permutations `C₂ ≀ S_n` (`FibreSignedPerm (Fin n)`).

For the generic folded equation the group is the whole of it. The signed permutations act on the
field of rational functions in `x₁, …, x_n` by `x_i ↦ ± x_{σ i}`; the action is faithful away from
characteristic two; the generic folded polynomial `∏ (X² − x_i²)` has coefficients in the fixed
field, splits, and its roots generate the field. By Artin's theorem the Galois group is the group
of signed permutations (`genericFoldedGaloisEquiv`), of order `2ⁿ n!` (`card_genericFoldedGal`).

The reflection `x ↦ −x` of all roots is the uniform flip. It is central
(`uniformFlip_mul_comm`), and it is the functional equation of the folded equation
(`uniformFlip_smul_foldedRoot`). This is the calibration of the function-field case: there the
Riemann hypothesis is not a statement on the size of this group; it says that complex conjugation
is the uniform flip.
-/

namespace GaloisForLFunctions.GaloisTheoryOfZeros

open MvPolynomial
open GaloisForLFunctions.HTGeometry (SymmetricRationalField)

noncomputable section
set_option autoImplicit false

variable {K : Type*} [Field K] {n : ℕ}

/-! ## Signed permutations of the variables -/

namespace FibreSignedPerm

/-- The sign with which `a` carries the variable `i` to the variable `a.perm i`. -/
def varSign (a : FibreSignedPerm (Fin n)) (i : Fin n) : ℤˣ := a.sign (a.perm i)

theorem varSign_one (i : Fin n) : (1 : FibreSignedPerm (Fin n)).varSign i = 1 := rfl

private theorem perm_inv_apply (a : Equiv.Perm (Fin n)) (x : Fin n) : a⁻¹ (a x) = x := by
  change (a⁻¹ * a) x = x
  rw [inv_mul_cancel]
  rfl

private theorem perm_apply_inv (a : Equiv.Perm (Fin n)) (x : Fin n) : a (a⁻¹ x) = x := by
  change (a * a⁻¹) x = x
  rw [mul_inv_cancel]
  rfl

theorem varSign_mul (a b : FibreSignedPerm (Fin n)) (i : Fin n) :
    (a * b).varSign i = a.varSign (b.perm i) * b.varSign i := by
  simp only [varSign, mul_sign, mul_perm, Equiv.Perm.mul_apply, perm_inv_apply]

theorem ext_of_varSign {a b : FibreSignedPerm (Fin n)} (hp : ∀ i, a.perm i = b.perm i)
    (hs : ∀ i, a.varSign i = b.varSign i) : a = b := by
  have hperm : a.perm = b.perm := Equiv.ext hp
  refine FibreSignedPerm.ext hperm (funext fun x => ?_)
  have h := hs (a.perm⁻¹ x)
  rw [varSign, varSign, ← hperm, perm_apply_inv] at h
  exact h

/-- The signed permutations as pairs of a permutation and a sign vector. -/
def equivProd : FibreSignedPerm (Fin n) ≃ Equiv.Perm (Fin n) × (Fin n → ℤˣ) where
  toFun a := (a.perm, a.sign)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem natCard : Nat.card (FibreSignedPerm (Fin n)) = n.factorial * 2 ^ n := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_perm, Nat.card_fun, Nat.card_fin,
    Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int]

theorem uniformFlip_mul_comm (a : FibreSignedPerm (Fin n)) :
    a * uniformFlip (Fin n) = uniformFlip (Fin n) * a := by
  refine FibreSignedPerm.ext ?_ (funext fun x => ?_)
  · show a.perm * 1 = 1 * a.perm
    rw [mul_one, one_mul]
  · show a.sign x * -1 = -1 * a.sign ((1 : Equiv.Perm (Fin n))⁻¹ x)
    rw [inv_one, Equiv.Perm.one_apply, mul_comm]

end FibreSignedPerm

open FibreSignedPerm

/-- A unit of `ℤ` in a ring. -/
private def unitCast (R : Type*) [Ring R] (u : ℤˣ) : R := ((u : ℤ) : R)

private theorem unitCast_mul (R : Type*) [Ring R] (u v : ℤˣ) :
    unitCast R (u * v) = unitCast R u * unitCast R v := by
  simp only [unitCast, Units.val_mul, Int.cast_mul]

private theorem unitCast_one (R : Type*) [Ring R] : unitCast R 1 = 1 := by
  simp only [unitCast, Units.val_one, Int.cast_one]

private theorem unitCast_sq (R : Type*) [Ring R] (u : ℤˣ) : unitCast R u ^ 2 = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [unitCast, h]

private theorem unitCast_injective (R : Type*) [CommRing R] [NeZero (2 : R)] :
    Function.Injective (unitCast R) := by
  intro u v h
  have h2 : (2 : R) ≠ 0 := NeZero.ne 2
  rcases Int.units_eq_one_or u with hu | hu <;> rcases Int.units_eq_one_or v with hv | hv
  · rw [hu, hv]
  · exfalso
    rw [hu, hv] at h
    simp only [unitCast, Units.val_one, Int.cast_one, Units.val_neg, Int.cast_neg] at h
    exact h2 (by linear_combination h)
  · exfalso
    rw [hu, hv] at h
    simp only [unitCast, Units.val_one, Int.cast_one, Units.val_neg, Int.cast_neg] at h
    exact h2 (by linear_combination -h)
  · rw [hu, hv]

/-- The image of the variable `i` under `a`: `± x_{a i}`. -/
private def varImage (K : Type*) [Field K] (a : FibreSignedPerm (Fin n)) (i : Fin n) :
    MvPolynomial (Fin n) K :=
  C (unitCast K (a.varSign i)) * X (a.perm i)

private theorem aeval_varImage_varImage (a b : FibreSignedPerm (Fin n)) (i : Fin n) :
    aeval (varImage K a) (varImage K b i) = varImage K (a * b) i := by
  rw [varImage, map_mul, aeval_C, aeval_X, varImage, varImage, varSign_mul, unitCast_mul,
    MvPolynomial.algebraMap_eq, map_mul, mul_perm, Equiv.Perm.mul_apply]
  ring

/-- Signed permutations act on the polynomial ring by `x_i ↦ ± x_{σ i}`. -/
scoped instance signedMvPolynomialAction (K : Type*) [Field K] (n : ℕ) :
    MulSemiringAction (FibreSignedPerm (Fin n)) (MvPolynomial (Fin n) K) where
  smul a p := aeval (varImage K a) p
  one_smul p := by
    show aeval (varImage K (1 : FibreSignedPerm (Fin n))) p = p
    have h : varImage K (1 : FibreSignedPerm (Fin n)) = X := by
      funext i
      rw [varImage, varSign_one, unitCast_one, map_one, one_mul]
      rfl
    rw [h, aeval_X_left_apply]
  mul_smul a b p := by
    show aeval (varImage K (a * b)) p = aeval (varImage K a) (aeval (varImage K b) p)
    rw [← AlgHom.comp_apply, comp_aeval]
    exact congrArg (fun f => aeval f p) (funext fun i => (aeval_varImage_varImage a b i).symm)
  smul_zero a := map_zero (aeval (varImage K a))
  smul_add a p q := map_add (aeval (varImage K a)) p q
  smul_one a := map_one (aeval (varImage K a))
  smul_mul a p q := map_mul (aeval (varImage K a)) p q

theorem signed_smul_X (a : FibreSignedPerm (Fin n)) (i : Fin n) :
    a • (X i : MvPolynomial (Fin n) K) = C (((a.varSign i : ℤˣ) : ℤ) : K) * X (a.perm i) :=
  aeval_X (varImage K a) i

theorem signed_smul_C (a : FibreSignedPerm (Fin n)) (c : K) :
    a • (C c : MvPolynomial (Fin n) K) = C c := by
  show aeval (varImage K a) (C c) = C c
  rw [aeval_C, MvPolynomial.algebraMap_eq]

/-- Away from characteristic two the action is faithful. -/
scoped instance signedMvPolynomialFaithful (K : Type*) [Field K] [NeZero (2 : K)] (n : ℕ) :
    FaithfulSMul (FibreSignedPerm (Fin n)) (MvPolynomial (Fin n) K) where
  eq_of_smul_eq_smul {a b} h := by
    have key : ∀ i, a.perm i = b.perm i ∧ a.varSign i = b.varSign i := by
      intro i
      have h1 := congrArg (coeff (Finsupp.single (a.perm i) 1)) (h (X i))
      rw [signed_smul_X, signed_smul_X, coeff_C_mul, coeff_C_mul, coeff_X, coeff_X,
        if_pos rfl, mul_one] at h1
      have hne : (((a.varSign i : ℤˣ) : ℤ) : K) ≠ 0 := by
        have hsq := unitCast_sq K (a.varSign i)
        intro h0
        rw [unitCast, h0] at hsq
        norm_num at hsq
      by_cases hp : Finsupp.single (b.perm i) 1 = Finsupp.single (a.perm i) 1
      · have hpi : b.perm i = a.perm i :=
          Finsupp.single_left_injective (one_ne_zero : (1 : ℕ) ≠ 0) hp
        rw [if_pos hp, mul_one] at h1
        exact ⟨hpi.symm, unitCast_injective K h1⟩
      · rw [if_neg hp, mul_zero] at h1
        exact absurd h1 hne
    exact ext_of_varSign (fun i => (key i).1) fun i => (key i).2

scoped instance signedRationalFieldAction (K : Type*) [Field K] (n : ℕ) :
    MulSemiringAction (FibreSignedPerm (Fin n)) (SymmetricRationalField K n) :=
  IsFractionRing.mulSemiringAction (FibreSignedPerm (Fin n)) (MvPolynomial (Fin n) K)
    (SymmetricRationalField K n)

scoped instance signedRationalFieldFaithful (K : Type*) [Field K] [NeZero (2 : K)] (n : ℕ) :
    FaithfulSMul (FibreSignedPerm (Fin n)) (SymmetricRationalField K n) :=
  IsFractionRing.faithfulSMul (FibreSignedPerm (Fin n)) (MvPolynomial (Fin n) K)
    (SymmetricRationalField K n)

/-- The field of the folded coefficients: the rational functions invariant under every signed
permutation of the variables. -/
abbrev foldedPart (K : Type*) [Field K] (n : ℕ) : Subfield (SymmetricRationalField K n) :=
  FixedPoints.subfield (FibreSignedPerm (Fin n)) (SymmetricRationalField K n)

theorem algebraMap_signed_smul (a : FibreSignedPerm (Fin n)) (p : MvPolynomial (Fin n) K) :
    algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n) (a • p) =
      a • algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n) p :=
  algebraMap.smul' _ _ _

/-- **Artin's theorem for signed permutations.** The rational function field has degree `2ⁿ n!`
over the field of the folded coefficients. -/
theorem finrank_foldedPart (K : Type*) [Field K] [NeZero (2 : K)] (n : ℕ) :
    Module.finrank (foldedPart K n) (SymmetricRationalField K n) = n.factorial * 2 ^ n := by
  classical
  haveI : Fintype (FibreSignedPerm (Fin n)) := Fintype.ofFinite _
  rw [foldedPart, FixedPoints.finrank_eq_card, ← Nat.card_eq_fintype_card, natCard]

/-! ## The generic folded polynomial -/

/-- The variables, read as rational functions: one root from each pair. -/
def foldedRoot (K : Type*) [Field K] (n : ℕ) (i : Fin n) : SymmetricRationalField K n :=
  algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n) (X i)

theorem signed_smul_foldedRoot (a : FibreSignedPerm (Fin n)) (i : Fin n) :
    a • foldedRoot K n i =
      (((a.varSign i : ℤˣ) : ℤ) : SymmetricRationalField K n) * foldedRoot K n (a.perm i) := by
  rw [foldedRoot, ← algebraMap_signed_smul, signed_smul_X, map_mul,
    show (C (((a.varSign i : ℤˣ) : ℤ) : K) : MvPolynomial (Fin n) K) =
      (((a.varSign i : ℤˣ) : ℤ) : MvPolynomial (Fin n) K) from map_intCast C _, map_intCast]
  rfl

/-- **The reflection of all roots is the uniform flip.** -/
theorem uniformFlip_smul_foldedRoot (i : Fin n) :
    uniformFlip (Fin n) • foldedRoot K n i = -foldedRoot K n i := by
  rw [signed_smul_foldedRoot]
  show (((-1 : ℤˣ) : ℤ) : SymmetricRationalField K n) * foldedRoot K n i = -foldedRoot K n i
  simp

theorem signed_smul_foldedRoot_sq (a : FibreSignedPerm (Fin n)) (i : Fin n) :
    a • foldedRoot K n i ^ 2 = foldedRoot K n (a.perm i) ^ 2 := by
  rw [smul_pow', signed_smul_foldedRoot, mul_pow]
  have h := unitCast_sq (SymmetricRationalField K n) (a.varSign i)
  rw [unitCast] at h
  rw [h, one_mul]

/-- The generic folded polynomial `∏ (X² − x_i²)`, read over the rational function field. -/
def genericFoldedF (K : Type*) [Field K] (n : ℕ) : Polynomial (SymmetricRationalField K n) :=
  ∏ i : Fin n, (Polynomial.X ^ 2 - Polynomial.C (foldedRoot K n i ^ 2))

/-- It is the polynomial `∏ (Y − x_i²)` in `Y = X²`. -/
theorem genericFoldedF_eq_expand :
    genericFoldedF K n =
      Polynomial.expand (SymmetricRationalField K n) 2
        (∏ i : Fin n, (Polynomial.X - Polynomial.C (foldedRoot K n i ^ 2))) := by
  rw [genericFoldedF, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_sub, Polynomial.expand_X, Polynomial.expand_C]

theorem genericFoldedF_eq_prod :
    genericFoldedF K n = ∏ i : Fin n, ((Polynomial.X - Polynomial.C (foldedRoot K n i)) *
      (Polynomial.X + Polynomial.C (foldedRoot K n i))) := by
  rw [genericFoldedF]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.C_pow]
  ring

theorem monic_genericFoldedF : (genericFoldedF K n).Monic := by
  rw [genericFoldedF_eq_prod]
  exact Polynomial.monic_prod_of_monic _ _ fun i _ =>
    (Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_add_C _)

/-- **The generic folded polynomial is invariant under signed permutations.** -/
theorem map_genericFoldedF (a : FibreSignedPerm (Fin n)) :
    Polynomial.map
        (MulSemiringAction.toRingHom (FibreSignedPerm (Fin n)) (SymmetricRationalField K n) a)
        (genericFoldedF K n) = genericFoldedF K n := by
  rw [genericFoldedF, Polynomial.map_prod]
  have hterm : ∀ i : Fin n,
      Polynomial.map
          (MulSemiringAction.toRingHom (FibreSignedPerm (Fin n)) (SymmetricRationalField K n) a)
          (Polynomial.X ^ 2 - Polynomial.C (foldedRoot K n i ^ 2)) =
        Polynomial.X ^ 2 - Polynomial.C (foldedRoot K n (a.perm i) ^ 2) := by
    intro i
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    congr 2
    exact signed_smul_foldedRoot_sq a i
  rw [Finset.prod_congr rfl fun i _ => hterm i]
  exact Equiv.prod_comp a.perm fun i => Polynomial.X ^ 2 - Polynomial.C (foldedRoot K n i ^ 2)

theorem coeff_genericFoldedF_mem (k : ℕ) : (genericFoldedF K n).coeff k ∈ foldedPart K n := by
  intro a
  have h := congrArg (fun p : Polynomial (SymmetricRationalField K n) => p.coeff k)
    (map_genericFoldedF (K := K) (n := n) a)
  rwa [Polynomial.coeff_map] at h

theorem coeffs_genericFoldedF_subset :
    ↑(genericFoldedF K n).coeffs ⊆
      ((foldedPart K n).toSubring : Set (SymmetricRationalField K n)) := by
  intro c hc
  obtain ⟨k, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hc
  exact coeff_genericFoldedF_mem k

/-- **The generic folded polynomial of degree `2n`**, over the field of the folded
coefficients. -/
def genericFolded (K : Type*) [Field K] (n : ℕ) : Polynomial (foldedPart K n) :=
  (genericFoldedF K n).toSubring (foldedPart K n).toSubring coeffs_genericFoldedF_subset

theorem map_genericFolded :
    Polynomial.map (algebraMap (foldedPart K n) (SymmetricRationalField K n))
      (genericFolded K n) = genericFoldedF K n :=
  Polynomial.map_toSubring _ _ _

theorem genericFolded_ne_zero : genericFolded K n ≠ 0 := by
  intro hcon
  have h := map_genericFolded (K := K) (n := n)
  rw [hcon, Polynomial.map_zero] at h
  exact (monic_genericFoldedF (K := K) (n := n)).ne_zero h.symm

/-! ## Splitting -/

theorem splits_genericFolded :
    (Polynomial.map (algebraMap (foldedPart K n) (SymmetricRationalField K n))
      (genericFolded K n)).Splits := by
  rw [map_genericFolded, genericFoldedF_eq_prod]
  exact Polynomial.Splits.prod fun _ _ =>
    (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.X_add_C _)

theorem foldedRoot_mem_rootSet (i : Fin n) :
    foldedRoot K n i ∈ (genericFolded K n).rootSet (SymmetricRationalField K n) := by
  rw [Polynomial.mem_rootSet]
  refine ⟨genericFolded_ne_zero, ?_⟩
  have heval : Polynomial.aeval (foldedRoot K n i) (genericFolded K n) =
      Polynomial.eval (foldedRoot K n i) (genericFoldedF K n) := by
    rw [← map_genericFolded, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  rw [heval, genericFoldedF, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem algebraMap_mem_foldedPart (c : K) :
    algebraMap K (SymmetricRationalField K n) c ∈ foldedPart K n := by
  intro a
  have hC : algebraMap K (SymmetricRationalField K n) c =
      algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n) (C c) := by
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K) (SymmetricRationalField K n)]
    rfl
  rw [hC, ← algebraMap_signed_smul, signed_smul_C]

/-- **The roots generate the rational function field over the folded coefficients.** -/
theorem adjoin_rootSet_genericFolded (K : Type*) [Field K] [NeZero (2 : K)] (n : ℕ) :
    Algebra.adjoin (foldedPart K n)
      ((genericFolded K n).rootSet (SymmetricRationalField K n)) = ⊤ := by
  classical
  set S := Algebra.adjoin (foldedPart K n)
    ((genericFolded K n).rootSet (SymmetricRationalField K n)) with hS
  have hroots : ∀ i : Fin n, foldedRoot K n i ∈ S := fun i =>
    Algebra.subset_adjoin (foldedRoot_mem_rootSet i)
  have hpoly : ∀ p : MvPolynomial (Fin n) K,
      algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n) p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
        have hC : algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n) (C c) =
            algebraMap K (SymmetricRationalField K n) c := by
          rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K)
            (SymmetricRationalField K n)]
          rfl
        rw [hC]
        exact Subalgebra.algebraMap_mem S ⟨_, algebraMap_mem_foldedPart c⟩
    | add p q hp hq =>
        rw [map_add]
        exact add_mem hp hq
    | mul_X p i hp =>
        rw [map_mul]
        exact mul_mem hp (hroots i)
  have hfield : IsField S := Subalgebra.isField_of_algebraic S
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n)) :=
    IsFractionRing.injective _ _
  refine le_antisymm le_top fun z _ => ?_
  obtain ⟨p, q, hq, hz⟩ := IsFractionRing.div_surjective
    (A := MvPolynomial (Fin n) K) (K := SymmetricRationalField K n) z
  have hq0 : algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n) q ≠ 0 :=
    fun hcon => nonZeroDivisors.ne_zero hq (hinj (by rw [hcon, map_zero]))
  obtain ⟨y, hy⟩ := hfield.mul_inv_cancel
    (a := (⟨_, hpoly q⟩ : S)) (fun hcon => hq0 (congrArg Subtype.val hcon))
  have hyF : algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n) q *
      (y : SymmetricRationalField K n) = 1 := congrArg Subtype.val hy
  have hyinv : (y : SymmetricRationalField K n) =
      (algebraMap (MvPolynomial (Fin n) K) (SymmetricRationalField K n) q)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm] at hyF; exact hyF)
  rw [← hz, div_eq_mul_inv, ← hyinv]
  exact mul_mem (hpoly p) y.2

instance isSplittingField_genericFolded (K : Type*) [Field K] [NeZero (2 : K)] (n : ℕ) :
    Polynomial.IsSplittingField (foldedPart K n) (SymmetricRationalField K n)
      (genericFolded K n) :=
  ⟨splits_genericFolded, adjoin_rootSet_genericFolded K n⟩

/-! ## The Galois group -/

/-- The Galois group of the rational function field over the folded coefficients is the group of
signed permutations. -/
def signedGaloisEquiv (K : Type*) [Field K] [NeZero (2 : K)] (n : ℕ) :
    FibreSignedPerm (Fin n) ≃*
      (SymmetricRationalField K n ≃ₐ[foldedPart K n] SymmetricRationalField K n) :=
  FixedPoints.toAlgAutMulEquiv _ _

@[simp]
theorem signedGaloisEquiv_apply (K : Type*) [Field K] [NeZero (2 : K)] (n : ℕ)
    (a : FibreSignedPerm (Fin n)) (z : SymmetricRationalField K n) :
    signedGaloisEquiv K n a z = a • z := rfl

/-- **The Galois group of the generic folded polynomial of degree `2n` is the full group of signed
permutations of `n` pairs.** -/
def genericFoldedGaloisEquiv (K : Type*) [Field K] [NeZero (2 : K)] (n : ℕ) :
    FibreSignedPerm (Fin n) ≃* (genericFolded K n).Gal :=
  (signedGaloisEquiv K n).trans
    (AlgEquiv.autCongr
      (Polynomial.IsSplittingField.algEquiv (SymmetricRationalField K n) (genericFolded K n)))

theorem card_genericFoldedGal (K : Type*) [Field K] [NeZero (2 : K)] (n : ℕ) :
    Nat.card (genericFolded K n).Gal = n.factorial * 2 ^ n := by
  rw [← Nat.card_congr (genericFoldedGaloisEquiv K n).toEquiv, natCard]

/-- **The functional equation is central.** In the group of the generic folded equation the
reflection of all roots commutes with every element. -/
theorem genericFoldedGaloisEquiv_uniformFlip_comm (K : Type*) [Field K] [NeZero (2 : K)] (n : ℕ)
    (g : (genericFolded K n).Gal) :
    g * genericFoldedGaloisEquiv K n (uniformFlip (Fin n)) =
      genericFoldedGaloisEquiv K n (uniformFlip (Fin n)) * g := by
  obtain ⟨a, rfl⟩ := (genericFoldedGaloisEquiv K n).surjective g
  rw [← map_mul, ← map_mul, uniformFlip_mul_comm]

theorem natDegree_genericFolded : (genericFolded K n).natDegree = 2 * n := by
  have h := congrArg Polynomial.natDegree (map_genericFolded (K := K) (n := n))
  rw [Polynomial.natDegree_map_eq_of_injective
    (algebraMap (foldedPart K n) (SymmetricRationalField K n)).injective] at h
  rw [h, genericFoldedF, Polynomial.natDegree_prod_of_monic _ _ fun (i : Fin n) _ => by
    have h2 : (Polynomial.X ^ 2 - Polynomial.C (foldedRoot K n i ^ 2)) =
        (Polynomial.X - Polynomial.C (foldedRoot K n i)) *
          (Polynomial.X + Polynomial.C (foldedRoot K n i)) := by
      rw [Polynomial.C_pow]
      ring
    rw [h2]
    exact (Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_add_C _)]
  have hdeg : ∀ i : Fin n,
      (Polynomial.X ^ 2 - Polynomial.C (foldedRoot K n i ^ 2)).natDegree = 2 := fun i =>
    Polynomial.natDegree_X_pow_sub_C
  rw [Finset.sum_congr rfl fun i _ => hdeg i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_comm]

end

end GaloisForLFunctions.GaloisTheoryOfZeros
