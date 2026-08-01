import GaloisForLFunctions.HTGeometry.ProjectiveHorizonJetLoopCurrent

/-!
# The loop currents form a graded Lie algebra

The depth-`k` current attached to a matrix of constants lowers jet order by `k` with a falling
factorial coefficient, and falling factorials compose: lowering by `j` and then by `k` is lowering
by `j+k`.  Consequently the bracket of a depth-`k` and a depth-`j` current is the depth-`(k+j)`
current of the matrix commutator, so the currents realise the polynomial current algebra of the
observer group as derivations of the jet field.

Since a bracket of derivations annihilating an element again annihilates it, this is what propagates
an annihilation hypothesis from a finite generating packet of currents to every mode.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

/-! ## Falling factorials compose -/

theorem descFactorial_add (l k j : ℕ) :
    l.descFactorial (k + j) = l.descFactorial k * (l - k).descFactorial j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [← Nat.add_assoc, Nat.descFactorial_succ, ih, Nat.descFactorial_succ,
        show l - (k + j) = l - k - j from by omega]
      ring

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

omit [DecidableEq n] in
@[simp]
theorem jetLoopDerivationPoly_C (k : ℕ) (M : Matrix n n K) (c : K) :
    jetLoopDerivationPoly k M (MvPolynomial.C c) = 0 := by
  rw [← MvPolynomial.algebraMap_eq]
  exact Derivation.map_algebraMap _ _

/-! ## Linearity in the matrix -/

omit [DecidableEq n] in
theorem jetLoopDerivationPoly_add (k : ℕ) (M M' : Matrix n n K) :
    jetLoopDerivationPoly k (M + M') =
      jetLoopDerivationPoly k M + jetLoopDerivationPoly k M' := by
  apply MvPolynomial.derivation_ext
  rintro ⟨a, l⟩
  rw [jetLoopDerivationPoly_X, Derivation.add_apply, jetLoopDerivationPoly_X,
    jetLoopDerivationPoly_X, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by
    rw [Matrix.add_apply, mul_add, map_add, add_mul]

omit [DecidableEq n] in
theorem jetLoopDerivationPoly_smul (k : ℕ) (c : K) (M : Matrix n n K) :
    jetLoopDerivationPoly k (c • M) = c • jetLoopDerivationPoly k M := by
  apply MvPolynomial.derivation_ext
  rintro ⟨a, l⟩
  rw [jetLoopDerivationPoly_X, Derivation.smul_apply, jetLoopDerivationPoly_X, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, show (l.descFactorial k : K) * (c * M a m) =
    c * ((l.descFactorial k : K) * M a m) from by ring, map_mul, mul_assoc,
    ← MvPolynomial.smul_eq_C_mul]

omit [DecidableEq n] in
theorem jetLoopDerivation_add (k : ℕ) (M M' : Matrix n n K) :
    jetLoopDerivation k (M + M') = jetLoopDerivation k M + jetLoopDerivation k M' := by
  refine GaloisForLFunctions.fractionRing_derivation_ext
    (A := MvPolynomial (n × ℕ) K) _ _ fun p => ?_
  rw [jetLoopDerivation_algebraMap, jetLoopDerivationPoly_add, Derivation.add_apply, map_add,
    Derivation.add_apply, jetLoopDerivation_algebraMap, jetLoopDerivation_algebraMap]

omit [DecidableEq n] in
theorem jetLoopDerivation_smul (k : ℕ) (c : K) (M : Matrix n n K) :
    jetLoopDerivation k (c • M) = c • jetLoopDerivation k M := by
  rw [jetLoopDerivation, jetLoopDerivationPoly_smul,
    extendFreeCoordinatePolynomialDerivation_smul]
  rfl

/-! ## The graded bracket -/

omit [DecidableEq n] in
/-- **The loop currents form a graded Lie algebra.**  The bracket of a depth-`k` and a depth-`j`
current is the depth-`(k+j)` current of the matrix commutator. -/
theorem jetLoopDerivationPoly_lie (k j : ℕ) (M M' : Matrix n n K) :
    ⁅jetLoopDerivationPoly k M, jetLoopDerivationPoly j M'⁆ =
      jetLoopDerivationPoly (k + j) (M' * M - M * M') := by
  have hstep : ∀ (A B : Matrix n n K) (kk jj : ℕ) (a : n) (l : ℕ),
      jetLoopDerivationPoly kk A
          (∑ m, MvPolynomial.C ((l.descFactorial jj : K) * B a m) *
            MvPolynomial.X ((m, l - jj) : n × ℕ)) =
        ∑ q, MvPolynomial.C ((l.descFactorial (jj + kk) : K) * (B * A) a q) *
          MvPolynomial.X ((q, l - jj - kk) : n × ℕ) := by
    intro A B kk jj a l
    rw [map_sum]
    have hterm : ∀ m : n,
        jetLoopDerivationPoly kk A (MvPolynomial.C ((l.descFactorial jj : K) * B a m) *
            MvPolynomial.X ((m, l - jj) : n × ℕ)) =
          ∑ q, MvPolynomial.C ((l.descFactorial jj : K) * B a m *
            (((l - jj).descFactorial kk : K) * A m q)) *
              MvPolynomial.X ((q, l - jj - kk) : n × ℕ) := by
      intro m
      rw [Derivation.leibniz, jetLoopDerivationPoly_C, smul_zero, add_zero, smul_eq_mul,
        jetLoopDerivationPoly_X, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [← mul_assoc, ← map_mul]
    rw [Finset.sum_congr rfl fun m (_ : m ∈ Finset.univ) => hterm m, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_apply, descFactorial_add, Nat.cast_mul, Finset.mul_sum, map_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show (l.descFactorial jj : K) * B a m * (((l - jj).descFactorial kk : K) * A m q) =
      (l.descFactorial jj : K) * ((l - jj).descFactorial kk : K) * (B a m * A m q) from by ring]
  apply MvPolynomial.derivation_ext
  rintro ⟨a, l⟩
  rw [Derivation.commutator_apply, jetLoopDerivationPoly_X, jetLoopDerivationPoly_X,
    hstep M M' k j a l, hstep M' M j k a l, jetLoopDerivationPoly_X,
    show l - j - k = l - (k + j) from by omega, show l - k - j = l - (k + j) from by omega,
    show j + k = k + j from Nat.add_comm j k, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => by
    rw [Matrix.sub_apply, mul_sub, map_sub, sub_mul]

omit [DecidableEq n] in
theorem jetLoopDerivation_lie (k j : ℕ) (M M' : Matrix n n K) :
    ⁅jetLoopDerivation k M, jetLoopDerivation j M'⁆ =
      jetLoopDerivation (k + j) (M' * M - M * M') := by
  rw [jetLoopDerivation, jetLoopDerivation, extendFreeCoordinatePolynomialDerivation_lie,
    jetLoopDerivationPoly_lie]
  rfl

/-! ## Propagation of annihilation -/

omit [Fintype n] [DecidableEq n] in
/-- A bracket of derivations annihilating an element again annihilates it. -/
theorem lie_apply_eq_zero
    {D E : Derivation K (HomogeneousJetField n K) (HomogeneousJetField n K)}
    {f : HomogeneousJetField n K} (hD : D f = 0) (hE : E f = 0) : ⁅D, E⁆ f = 0 := by
  rw [Derivation.commutator_apply, hD, hE, map_zero, map_zero, sub_zero]

omit [DecidableEq n] in
/-- **Propagation.**  If two loop currents annihilate a jet observable, so does the depth-summed
current of their matrix commutator. -/
theorem jetLoopDerivation_lie_eq_zero {k j : ℕ} {M M' : Matrix n n K}
    {f : HomogeneousJetField n K} (hM : jetLoopDerivation k M f = 0)
    (hM' : jetLoopDerivation j M' f = 0) :
    jetLoopDerivation (k + j) (M' * M - M * M') f = 0 := by
  rw [← jetLoopDerivation_lie]
  exact lie_apply_eq_zero hM hM'

end

end GaloisForLFunctions.HTGeometry
