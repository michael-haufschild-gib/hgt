import GaloisForLFunctions.HTGeometry.GenericPolynomialVieta

/-!
# The centered generic polynomial

Subtracting the average of the roots from each of them produces roots summing to zero, so the
monic polynomial they define has no next-to-leading coefficient.  That is the centered generic
polynomial of degree `d`.

Permuting the variables permutes the centered roots, because the average is symmetric, and the
centered roots are still pairwise distinct.  So the symmetric group acts on the field they generate
exactly as it acts on their indices.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Polynomial

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-- The average of the generic roots. -/
noncomputable def genericAverage (K : Type*) [Field K] (d : ℕ) :
    SymmetricRationalField K d :=
  (∑ j : Fin d, genericRoot K d j) * ((d : SymmetricRationalField K d))⁻¹

/-- The centered generic roots: the generic roots with their average removed. -/
noncomputable def centeredRoot (K : Type*) [Field K] (d : ℕ) (i : Fin d) :
    SymmetricRationalField K d :=
  genericRoot K d i - genericAverage K d

omit [CharZero K] in
theorem smul_genericAverage (e : Equiv.Perm (Fin d)) :
    e • genericAverage K d = genericAverage K d := by
  have hsum : e • (∑ j : Fin d, genericRoot K d j) = ∑ j : Fin d, genericRoot K d j := by
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv e _ _ fun j => ?_
    exact smul_genericRoot e j
  have hd : e • ((d : SymmetricRationalField K d))⁻¹ =
      ((d : SymmetricRationalField K d))⁻¹ := by
    have h1 : e • ((d : SymmetricRationalField K d))⁻¹ =
        (MulSemiringAction.toRingEquiv (Equiv.Perm (Fin d)) (SymmetricRationalField K d) e)
          ((d : SymmetricRationalField K d))⁻¹ := rfl
    rw [h1, map_inv₀, map_natCast]
  rw [genericAverage, smul_mul', hsum, hd]

omit [CharZero K] in
theorem smul_centeredRoot (e : Equiv.Perm (Fin d)) (i : Fin d) :
    e • centeredRoot K d i = centeredRoot K d (e i) := by
  rw [centeredRoot, centeredRoot, smul_sub, smul_genericRoot, smul_genericAverage]

omit [CharZero K] in
theorem genericRoot_injective : Function.Injective (genericRoot K d) := by
  intro i j hij
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d)) :=
    IsFractionRing.injective _ _
  exact MvPolynomial.X_injective (hinj hij)

omit [CharZero K] in
theorem centeredRoot_injective : Function.Injective (centeredRoot K d) := by
  intro i j hij
  refine genericRoot_injective (K := K) (d := d) ?_
  rw [centeredRoot, centeredRoot] at hij
  have h := congrArg (fun x : SymmetricRationalField K d => x + genericAverage K d) hij
  simpa using h

/-- **The centered roots sum to zero.** -/
theorem sum_centeredRoot (hd : d ≠ 0) : ∑ i : Fin d, centeredRoot K d i = 0 := by
  have hdF : (d : SymmetricRationalField K d) ≠ 0 := Nat.cast_ne_zero.2 hd
  simp only [centeredRoot, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, genericAverage]
  field_simp
  ring

/-- The centered generic polynomial, read over the rational function field. -/
noncomputable def centeredMonicF (K : Type*) [Field K] (d : ℕ) :
    Polynomial (SymmetricRationalField K d) :=
  ∏ i : Fin d, (Polynomial.X - Polynomial.C (centeredRoot K d i))

omit [CharZero K] in
theorem monic_centeredMonicF : (centeredMonicF K d).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

omit [CharZero K] in
theorem natDegree_centeredMonicF : (centeredMonicF K d).natDegree = d := by
  rw [centeredMonicF,
    natDegree_prod_of_monic _ _ fun (i : Fin d) _ => monic_X_sub_C (centeredRoot K d i)]
  simp

omit [CharZero K] in
theorem map_centeredMonicF (e : Equiv.Perm (Fin d)) :
    Polynomial.map
        (MulSemiringAction.toRingHom (Equiv.Perm (Fin d)) (SymmetricRationalField K d) e)
        (centeredMonicF K d) = centeredMonicF K d := by
  rw [centeredMonicF, Polynomial.map_prod]
  have hterm : ∀ i : Fin d,
      Polynomial.map
          (MulSemiringAction.toRingHom (Equiv.Perm (Fin d)) (SymmetricRationalField K d) e)
          (Polynomial.X - Polynomial.C (centeredRoot K d i)) =
        Polynomial.X - Polynomial.C (centeredRoot K d (e i)) := by
    intro i
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    congr 2
    exact smul_centeredRoot e i
  rw [Finset.prod_congr rfl fun i _ => hterm i]
  exact Equiv.prod_comp e fun i => Polynomial.X - Polynomial.C (centeredRoot K d i)

/-- **The centered generic polynomial has no next-to-leading coefficient.** -/
theorem coeff_centeredMonicF_pred (hd : d ≠ 0) :
    (centeredMonicF K d).coeff (d - 1) = 0 := by
  classical
  have hcard : (Finset.univ : Finset (Fin d)).card = d := by simp
  have hle : d - 1 ≤ d := by omega
  have hrewrite : centeredMonicF K d =
      ∏ i : Fin d, (Polynomial.X + Polynomial.C (-centeredRoot K d i)) := by
    rw [centeredMonicF]
    exact Finset.prod_congr rfl fun i _ => by rw [map_neg, sub_eq_add_neg]
  rw [hrewrite, Finset.prod_X_add_C_coeff _ _ (by rw [hcard]; exact hle), hcard,
    show d - (d - 1) = 1 from by omega]
  rw [Finset.powersetCard_one]
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Finset.prod_singleton]
  rw [Finset.sum_neg_distrib, sum_centeredRoot hd, neg_zero]

end GaloisForLFunctions.HTGeometry
