import GaloisForLFunctions.HTGeometry.ParameterizedPicardVessiotSystem

/-!
# Generation of parameterized Picard--Vessiot quotients

All differential-coordinate variables, together with the inverse zeroth-jet determinant, generate
the localized parameterized coordinate ring and every quotient.  The coordinate indexed by order
`k` is exactly the `k`-fold derivative of its zeroth-jet fundamental entry.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-- Differential-coordinate variables and the inverse determinant generate the parameterized
localization as an ordinary algebra. -/
theorem ppvLocalization_adjoin_jetVariables :
    Algebra.adjoin K
      (Set.range (fun q : (Fin n × Fin n) × ℕ =>
        algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
          (MvPolynomial.X q)) ∪
        {IsLocalization.Away.invSelf ((jetFundamentalMatrix K n).det)}) = ⊤ := by
  let U : Subalgebra K (ppvLocalization K n) := Algebra.adjoin K
    (Set.range (fun q : (Fin n × Fin n) × ℕ =>
      algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
        (MvPolynomial.X q)) ∪
      {IsLocalization.Away.invSelf ((jetFundamentalMatrix K n).det)})
  have hpolynomial : ∀ a : DifferentialPolynomial (Fin n × Fin n) K,
      algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n) a ∈ U := by
    intro a
    apply MvPolynomial.induction_on a
    · intro c
      change algebraMap K (ppvLocalization K n) c ∈ U
      exact U.algebraMap_mem c
    · intro p q hp hq
      rw [map_add]
      exact U.add_mem hp hq
    · intro p i hp
      rw [map_mul]
      exact U.mul_mem hp (Algebra.subset_adjoin (Set.mem_union_left _ ⟨i, rfl⟩))
  apply eq_top_iff.mpr
  intro z _
  change z ∈ U
  obtain ⟨m, a, hza⟩ := IsLocalization.Away.surj
    ((jetFundamentalMatrix K n).det) z
  have hz : algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n) a *
      IsLocalization.Away.invSelf ((jetFundamentalMatrix K n).det) ^ m = z := by
    rw [← hza, mul_assoc]
    rw [← mul_pow, IsLocalization.Away.mul_invSelf]
    simp
  rw [← hz]
  exact U.mul_mem (hpolynomial a)
    (U.pow_mem
      (Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _))) m)

/-- Images of all jet coordinates and the inverse determinant generate every parameterized
quotient. -/
theorem ppvQuotient_adjoin_jetVariables (M : Ideal (ppvLocalization K n)) :
    Algebra.adjoin K
      (Set.range (fun q : (Fin n × Fin n) × ℕ =>
        Ideal.Quotient.mk M
          (algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
            (MvPolynomial.X q))) ∪
        {Ideal.Quotient.mk M
          (IsLocalization.Away.invSelf ((jetFundamentalMatrix K n).det))}) = ⊤ := by
  change Algebra.adjoin K
    (Set.range (fun q : (Fin n × Fin n) × ℕ =>
      (Ideal.Quotient.mkₐ K M)
        (algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
          (MvPolynomial.X q))) ∪
      {(Ideal.Quotient.mkₐ K M)
        (IsLocalization.Away.invSelf ((jetFundamentalMatrix K n).det))}) = ⊤
  have h := Algebra.adjoin_image (R := K) (Ideal.Quotient.mkₐ K M)
    (Set.range (fun q : (Fin n × Fin n) × ℕ =>
      algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
        (MvPolynomial.X q)) ∪
      {IsLocalization.Away.invSelf ((jetFundamentalMatrix K n).det)})
  rw [ppvLocalization_adjoin_jetVariables, Algebra.map_top,
    (AlgHom.range_eq_top (Ideal.Quotient.mkₐ K M)).2 Ideal.Quotient.mk_surjective] at h
  have himage : (Ideal.Quotient.mkₐ K M) ''
      (Set.range (fun q : (Fin n × Fin n) × ℕ =>
        algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
          (MvPolynomial.X q)) ∪
        {IsLocalization.Away.invSelf ((jetFundamentalMatrix K n).det)}) =
      Set.range (fun q : (Fin n × Fin n) × ℕ =>
        (Ideal.Quotient.mkₐ K M)
          (algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
            (MvPolynomial.X q))) ∪
        {(Ideal.Quotient.mkₐ K M)
          (IsLocalization.Away.invSelf ((jetFundamentalMatrix K n).det))} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨q, rfl⟩ | rfl
      · exact Set.mem_union_left _ ⟨q, rfl⟩
      · exact Set.mem_union_right _ (Set.mem_singleton _)
    · rintro (⟨q, rfl⟩ | rfl)
      · exact ⟨_, Set.mem_union_left _ ⟨q, rfl⟩, rfl⟩
      · exact ⟨_, Set.mem_union_right _ (Set.mem_singleton _), rfl⟩
  rwa [himage] at h

/-- The distinguished inverse remains a right inverse of the parameterized fundamental
determinant in every quotient. -/
theorem ppvQuotient_det_mul_inverse (M : Ideal (ppvLocalization K n)) :
    (((ppvFundamental K n).map (Ideal.Quotient.mk M)).det) *
      Ideal.Quotient.mk M
        (IsLocalization.Away.invSelf ((jetFundamentalMatrix K n).det)) = 1 := by
  have hmap : ((ppvFundamental K n).map (Ideal.Quotient.mk M)).det =
      Ideal.Quotient.mk M (ppvFundamental K n).det := by
    rw [RingHom.map_det (Ideal.Quotient.mk M) (ppvFundamental K n),
      RingHom.mapMatrix_apply]
  rw [hmap]
  have hdet : (ppvFundamental K n).det =
      algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
        ((jetFundamentalMatrix K n).det) := by
    rw [ppvFundamental, RingHom.map_det, RingHom.mapMatrix_apply]
  rw [hdet]
  change Ideal.Quotient.mk M
      (algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
        ((jetFundamentalMatrix K n).det)) *
    Ideal.Quotient.mk M
      (IsLocalization.Away.invSelf ((jetFundamentalMatrix K n).det)) = 1
  rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]

variable [Differential K]

/-- Higher coordinate variables are the iterated derivatives of zeroth-jet fundamental entries. -/
theorem iterate_deriv_ppvFundamental (i j : Fin n) (k : ℕ) :
    (Differential.deriv^[k]) (ppvFundamental K n i j) =
      algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
        (MvPolynomial.X ((i, j), k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, ppvLocalization_deriv_algebraMap]
      have hjet := iterate_jetCoordDeriv_X (K := K) (p := (i, j)) (k + 1)
      rw [Function.iterate_succ_apply', iterate_jetCoordDeriv_X] at hjet
      rw [hjet]

/-- The quotient jet coordinates remain exactly the iterated derivatives of the quotient
fundamental entries. -/
theorem iterate_deriv_ppvQuotientFundamental
    (M : Ideal (ppvLocalization K n))
    (hM : ∀ x ∈ M, Differential.deriv x ∈ M)
    (i j : Fin n) (k : ℕ) :
    letI : Differential ((ppvLocalization K n) ⧸ M) := quotientDifferential M hM
    (Differential.deriv^[k])
        (Ideal.Quotient.mk M (ppvFundamental K n i j)) =
      Ideal.Quotient.mk M
        (algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
          (MvPolynomial.X ((i, j), k))) := by
  letI : Differential ((ppvLocalization K n) ⧸ M) := quotientDifferential M hM
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, quotientDifferential_deriv_mk,
        ppvLocalization_deriv_algebraMap]
      have hjet := iterate_jetCoordDeriv_X (K := K) (p := (i, j)) (k + 1)
      rw [Function.iterate_succ_apply', iterate_jetCoordDeriv_X] at hjet
      rw [hjet]

end


end GaloisForLFunctions.HTGeometry
