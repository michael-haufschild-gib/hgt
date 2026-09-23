import GaloisForLFunctions.HTGeometry.ProjectiveHorizonJetDerivation

/-!
# The observer Lie algebra of a span

The infinitesimal observers form a Lie algebra: the assignment of a derivation of the jet field to a
matrix of constants is linear and turns the matrix commutator into the derivation bracket.

That is what supplies the infinitesimal directions which are not themselves transvections.  The
bracket of the two elementary transvections between a pair of directions of a span is the traceless
diagonal in that pair, and since a bracket of derivations killing an element again kills it, the
traceless diagonals of a span also kill its horizon field.  Together with the elementary
transvections whose column lies in the span they span the full observer Lie algebra.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## Linearity -/

omit [DecidableEq n] in
theorem jetDerivationPoly_add (M M' : Matrix n n K) :
    jetDerivationPoly (M + M') = jetDerivationPoly M + jetDerivationPoly M' := by
  apply MvPolynomial.derivation_ext
  rintro ⟨k, l⟩
  rw [jetDerivationPoly_X, Derivation.add_apply, jetDerivationPoly_X, jetDerivationPoly_X,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by rw [Matrix.add_apply, map_add, add_mul]

omit [DecidableEq n] in
theorem jetDerivationPoly_smul (c : K) (M : Matrix n n K) :
    jetDerivationPoly (c • M) = c • jetDerivationPoly M := by
  apply MvPolynomial.derivation_ext
  rintro ⟨k, l⟩
  rw [jetDerivationPoly_X, Derivation.smul_apply, jetDerivationPoly_X, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← MvPolynomial.smul_eq_C_mul]

omit [DecidableEq n] in
theorem jetDerivationPoly_zero :
    jetDerivationPoly (0 : Matrix n n K) = 0 := by
  apply MvPolynomial.derivation_ext
  rintro ⟨k, l⟩
  rw [jetDerivationPoly_X, Derivation.zero_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [Matrix.zero_apply, map_zero, zero_mul]

omit [DecidableEq n] in
theorem jetDerivation_add (M M' : Matrix n n K) :
    jetDerivation (M + M') = jetDerivation M + jetDerivation M' := by
  refine GaloisForLFunctions.fractionRing_derivation_ext
    (A := MvPolynomial (n × ℕ) K) _ _ fun p => ?_
  rw [jetDerivation_algebraMap_projectiveHorizonJetDerivation, jetDerivationPoly_add, Derivation.add_apply, map_add,
    Derivation.add_apply, jetDerivation_algebraMap_projectiveHorizonJetDerivation, jetDerivation_algebraMap_projectiveHorizonJetDerivation]

omit [DecidableEq n] in
theorem jetDerivation_smul (c : K) (M : Matrix n n K) :
    jetDerivation (c • M) = c • jetDerivation M := by
  rw [jetDerivation, jetDerivationPoly_smul,
    extendFreeCoordinatePolynomialDerivation_smul]
  rfl

omit [DecidableEq n] in
theorem jetDerivation_zero : jetDerivation (0 : Matrix n n K) = 0 := by
  rw [jetDerivation, jetDerivationPoly_zero, extendFreeCoordinatePolynomialDerivation_zero]

/-! ## The bracket -/

omit [DecidableEq n] in
/-- **The infinitesimal observers form a Lie algebra.**  The derivation bracket is the matrix
commutator. -/
theorem jetDerivationPoly_lie (M M' : Matrix n n K) :
    ⁅jetDerivationPoly M, jetDerivationPoly M'⁆ = jetDerivationPoly (M' * M - M * M') := by
  have hstep : ∀ (A B : Matrix n n K) (k : n) (l : ℕ),
      jetDerivationPoly A (∑ m, MvPolynomial.C (B k m) * MvPolynomial.X ((m, l) : n × ℕ)) =
        ∑ q, MvPolynomial.C ((B * A) k q) * MvPolynomial.X ((q, l) : n × ℕ) := by
    intro A B k l
    rw [map_sum]
    have hterm : ∀ m : n,
        jetDerivationPoly A (MvPolynomial.C (B k m) * MvPolynomial.X ((m, l) : n × ℕ)) =
          ∑ q, MvPolynomial.C (B k m * A m q) * MvPolynomial.X ((q, l) : n × ℕ) := by
      intro m
      rw [Derivation.leibniz, jetDerivationPoly_C, smul_zero, add_zero, smul_eq_mul,
        jetDerivationPoly_X, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [← mul_assoc, ← map_mul]
    rw [Finset.sum_congr rfl fun m (_ : m ∈ Finset.univ) => hterm m, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
  apply MvPolynomial.derivation_ext
  rintro ⟨k, l⟩
  rw [Derivation.commutator_apply, jetDerivationPoly_X, jetDerivationPoly_X, hstep M M' k l,
    hstep M' M k l, jetDerivationPoly_X, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => by rw [Matrix.sub_apply, map_sub, sub_mul]

omit [DecidableEq n] in
theorem jetDerivation_lie (M M' : Matrix n n K) :
    ⁅jetDerivation M, jetDerivation M'⁆ = jetDerivation (M' * M - M * M') := by
  rw [jetDerivation, jetDerivation, extendFreeCoordinatePolynomialDerivation_lie,
    jetDerivationPoly_lie]
  rfl

/-! ## The traceless diagonals of a span -/

/-- **The traceless diagonal directions of a span kill its horizon field.**  They are brackets of
the elementary transvections between two directions of the span. -/
theorem jetDerivation_diag_eq_zero_of_mem_horizonField [Infinite K] {t : Set n} {a b : n}
    (ha : a ∈ t) (hb : b ∈ t) (hab : a ≠ b) {f : HomogeneousJetField n K}
    (hf : f ∈ horizonField (K := K) t) :
    jetDerivation (Matrix.single a a (1 : K) - Matrix.single b b (1 : K)) f = 0 := by
  have hM : Matrix.single a b (1 : K) * Matrix.single b a (1 : K) -
      Matrix.single b a (1 : K) * Matrix.single a b (1 : K) =
      Matrix.single a a (1 : K) - Matrix.single b b (1 : K) := by
    rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, one_mul]
  have h1 : jetDerivation (Matrix.single b a (1 : K)) f = 0 :=
    jetDerivation_single_eq_zero_of_mem_horizonField ha (Ne.symm hab) hf
  have h2 : jetDerivation (Matrix.single a b (1 : K)) f = 0 :=
    jetDerivation_single_eq_zero_of_mem_horizonField hb hab hf
  have hbr := jetDerivation_lie (Matrix.single b a (1 : K)) (Matrix.single a b (1 : K))
  rw [hM] at hbr
  rw [← hbr, Derivation.commutator_apply, h2, h1, map_zero, map_zero, sub_zero]

/-! ## The observer Lie algebra -/

/-- The infinitesimal generators of the observer group of a covector span: the elementary
transvections with column in the span, and the traceless diagonals of the span. -/
def observerGenerators (t : Set n) (K : Type*) [Field K] : Set (Matrix n n K) :=
  {M | (∃ i ∈ t, ∃ x, x ≠ i ∧ M = Matrix.single x i (1 : K)) ∨
    (∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧
      M = Matrix.single a a (1 : K) - Matrix.single b b (1 : K))}

omit [Fintype n] in
theorem single_mem_observerGenerators {t : Set n} {i x : n} (hi : i ∈ t) (hx : x ≠ i) :
    Matrix.single x i (1 : K) ∈ observerGenerators t K :=
  Or.inl ⟨i, hi, x, hx, rfl⟩

omit [Fintype n] in
theorem diag_mem_observerGenerators {t : Set n} {a b : n} (ha : a ∈ t) (hb : b ∈ t)
    (hab : a ≠ b) :
    Matrix.single a a (1 : K) - Matrix.single b b (1 : K) ∈ observerGenerators t K :=
  Or.inr ⟨a, ha, b, hb, hab, rfl⟩

/-- **The observer Lie algebra kills the horizon field.**  Every infinitesimal observer of a span,
i.e. every element of the span of its infinitesimal generators, annihilates every horizon
observable of that span. -/
theorem jetDerivation_eq_zero_of_mem_span [Infinite K] {t : Set n} {M : Matrix n n K}
    (hM : M ∈ Submodule.span K (observerGenerators t K)) {f : HomogeneousJetField n K}
    (hf : f ∈ horizonField (K := K) t) :
    jetDerivation M f = 0 := by
  induction hM using Submodule.span_induction with
  | mem M hMem =>
      rcases hMem with ⟨i, hi, x, hx, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩
      · exact jetDerivation_single_eq_zero_of_mem_horizonField hi hx hf
      · exact jetDerivation_diag_eq_zero_of_mem_horizonField ha hb hab hf
  | zero =>
      rw [jetDerivation_zero]
      rfl
  | add M M' _ _ h h' =>
      rw [jetDerivation_add, Derivation.add_apply, h, h', add_zero]
  | smul c M _ h =>
      rw [jetDerivation_smul, Derivation.smul_apply, h, smul_zero]

end

end GaloisForLFunctions.HTGeometry
