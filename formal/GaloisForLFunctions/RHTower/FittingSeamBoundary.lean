import GaloisForLFunctions.RHTower.SigmaDivisorJet

/-!
# Fitting seam boundary classes

This file formalizes the algebraic shape of the only viable pinned-annulus
`{sigma_p}` divisor refinement candidate: an adjugate/Fitting boundary class.

Given a local seam presentation by a square matrix `A`, a defect `Delta` has boundary
trace `tr(adj(A) Delta)`.  If `det A = X^m`, this trace has a class in the local
divisor-jet algebra `R[X]/(X^m)`.  Fake defects, i.e. defects factoring through the
presentation as `A H` (even modulo `X^m`), have zero boundary class.
-/

noncomputable section

namespace RHTower

open Matrix Polynomial

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The adjugate/Fitting boundary trace attached to a local seam matrix and a defect. -/
def fittingBoundaryTrace (A Delta : Matrix n n (Polynomial R)) : Polynomial R :=
  (A.adjugate * Delta).trace

/-- The adjugate/Fitting boundary class in the local divisor-jet algebra `R[X]/(X^m)`. -/
def fittingBoundaryClass (m : ℕ) (A Delta : Matrix n n (Polynomial R)) :
    LocalDivisorJet R m :=
  jetClass R m (fittingBoundaryTrace A Delta)

/-- A defect family has a nontrivial Fitting seam boundary if one sigma-labelled defect has
nonzero class in `R[X]/(X^m)`. -/
def HasNontrivialFittingBoundary {Sigma : Type*} (m : ℕ)
    (A : Matrix n n (Polynomial R)) (Delta : Sigma → Matrix n n (Polynomial R)) : Prop :=
  ∃ p : Sigma, fittingBoundaryClass m A (Delta p) ≠ 0

/-- The Fitting boundary class is zero exactly when the boundary trace has no
coefficient below the local multiplicity cutoff. -/
theorem fittingBoundaryClass_eq_zero_iff_coeff_lt_eq_zero (m : ℕ)
    (A Delta : Matrix n n (Polynomial R)) :
    fittingBoundaryClass m A Delta = 0 ↔
      ∀ j < m, (fittingBoundaryTrace A Delta).coeff j = 0 := by
  exact jetClass_eq_zero_iff_coeff_lt_eq_zero R m

/-- Equivalently, the Fitting boundary is nonzero exactly when a coefficient below
the local multiplicity cutoff survives. -/
theorem fittingBoundaryClass_ne_zero_iff_exists_coeff_lt_ne_zero (m : ℕ)
    (A Delta : Matrix n n (Polynomial R)) :
    fittingBoundaryClass m A Delta ≠ 0 ↔
      ∃ j, j < m ∧ (fittingBoundaryTrace A Delta).coeff j ≠ 0 := by
  exact jetClass_ne_zero_iff_exists_coeff_lt_ne_zero R m

/-- The Fitting boundary is zero exactly when the determinant-level first variation
is divisible by the local divisor equation. -/
theorem fittingBoundaryClass_eq_zero_iff_trace_X_pow_dvd (m : ℕ)
    (A Delta : Matrix n n (Polynomial R)) :
    fittingBoundaryClass m A Delta = 0 ↔
      (Polynomial.X : Polynomial R) ^ m ∣ fittingBoundaryTrace A Delta := by
  rw [fittingBoundaryClass_eq_zero_iff_coeff_lt_eq_zero]
  exact Iff.symm Polynomial.X_pow_dvd_iff

/-- Equivalently, the Fitting boundary is nonzero exactly when the determinant-level
first variation is transverse to the pinned divisor modulo `X^m`. -/
theorem fittingBoundaryClass_ne_zero_iff_not_trace_X_pow_dvd (m : ℕ)
    (A Delta : Matrix n n (Polynomial R)) :
    fittingBoundaryClass m A Delta ≠ 0 ↔
      ¬ (Polynomial.X : Polynomial R) ^ m ∣ fittingBoundaryTrace A Delta := by
  rw [ne_eq, fittingBoundaryClass_eq_zero_iff_trace_X_pow_dvd]

/-- If the determinant-level first variation is still divisible by `X^m`, the
Fitting boundary class is zero.  Thus a live seam defect must be determinant-
transverse to the pinned divisor. -/
theorem fittingBoundaryClass_eq_zero_of_trace_X_pow_dvd (m : ℕ)
    {A Delta : Matrix n n (Polynomial R)}
    (htrace : (Polynomial.X : Polynomial R) ^ m ∣ fittingBoundaryTrace A Delta) :
    fittingBoundaryClass m A Delta = 0 := by
  rw [fittingBoundaryClass]
  exact jetClass_eq_zero_of_X_pow_dvd R m htrace

/-- If every sigma-labelled boundary trace remains divisible by `X^m`, there is no
nontrivial sigma-labelled Fitting boundary. -/
theorem no_nontrivialFittingBoundary_of_trace_X_pow_dvd {Sigma : Type*} (m : ℕ)
    {A : Matrix n n (Polynomial R)} {Delta : Sigma → Matrix n n (Polynomial R)}
    (htrace : ∀ p : Sigma,
      (Polynomial.X : Polynomial R) ^ m ∣ fittingBoundaryTrace A (Delta p)) :
    ¬ HasNontrivialFittingBoundary m A Delta := by
  rintro ⟨p, hp⟩
  exact hp (fittingBoundaryClass_eq_zero_of_trace_X_pow_dvd m (htrace p))

/-- The adjugate trace of a fake right-factor defect is `det(A) * trace(H)`. -/
theorem fittingBoundaryTrace_right_factor (A H : Matrix n n (Polynomial R)) :
    fittingBoundaryTrace A (A * H) = A.det * H.trace := by
  rw [fittingBoundaryTrace]
  rw [← Matrix.mul_assoc, Matrix.adjugate_mul]
  rw [Matrix.smul_mul, Matrix.one_mul]
  rw [Matrix.trace_smul]
  rfl

/-- The adjugate trace of a fake left-factor defect is also `det(A) * trace(H)`.
This closes the source-basis-change version of the fake presentation defect. -/
theorem fittingBoundaryTrace_left_factor (A H : Matrix n n (Polynomial R)) :
    fittingBoundaryTrace A (H * A) = A.det * H.trace := by
  rw [fittingBoundaryTrace]
  rw [Matrix.trace_mul_cycle' A.adjugate H A]
  rw [← Matrix.mul_assoc, Matrix.mul_adjugate]
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul]
  rfl

/-- The adjugate trace commutes with scalar multiplication of the defect. -/
theorem fittingBoundaryTrace_smul (c : Polynomial R) (A K : Matrix n n (Polynomial R)) :
    fittingBoundaryTrace A (c • K) = c * (A.adjugate * K).trace := by
  rw [fittingBoundaryTrace]
  have h : A.adjugate * (c • K) = c • (A.adjugate * K) := by
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc, mul_comm]
  rw [h, Matrix.trace_smul]
  rfl

/-- The Fitting boundary class is additive in the defect. -/
theorem fittingBoundaryClass_add (m : ℕ)
    (A Delta E : Matrix n n (Polynomial R)) :
    fittingBoundaryClass m A (Delta + E) =
      fittingBoundaryClass m A Delta + fittingBoundaryClass m A E := by
  rw [fittingBoundaryClass, fittingBoundaryClass, fittingBoundaryClass, fittingBoundaryTrace,
    fittingBoundaryTrace, fittingBoundaryTrace, Matrix.mul_add, Matrix.trace_add, jetClass]
  rfl

/-- The cofactor column used to expand along row `i` is independent of row `i`. -/
theorem adjugate_updateRow_same_col (A : Matrix n n (Polynomial R)) (i j : n)
    (v : n → Polynomial R) :
    (A.updateRow i v).adjugate j i = A.adjugate j i := by
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  congr 1
  ext r c
  by_cases hr : r = i
  · subst r
    simp [Matrix.updateRow]
  · simp [Matrix.updateRow, hr]

/-- Expanding the determinant after replacing row `i` uses the corresponding cofactor
column of the original matrix. -/
theorem det_updateRow_eq_sum_mul_adjugate (A : Matrix n n (Polynomial R)) (i : n)
    (v : n → Polynomial R) :
    (A.updateRow i v).det = ∑ j : n, v j * A.adjugate j i := by
  rw [Matrix.det_eq_sum_mul_adjugate_row (A.updateRow i v) i]
  congr 1
  ext j
  rw [adjugate_updateRow_same_col A i j v]
  simp [Matrix.updateRow]

/-- Jacobi row form for the Fitting boundary trace: the adjugate trace is the sum of
the determinants obtained by replacing one row of `A` by the corresponding row of
the defect. -/
theorem fittingBoundaryTrace_eq_sum_det_updateRow (A Delta : Matrix n n (Polynomial R)) :
    fittingBoundaryTrace A Delta = ∑ i : n, (A.updateRow i (Delta i)).det := by
  rw [fittingBoundaryTrace]
  calc
    (A.adjugate * Delta).trace = ∑ i : n, ∑ j : n, A.adjugate i j * Delta j i := by
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    _ = ∑ j : n, ∑ i : n, Delta j i * A.adjugate i j := by
      rw [Finset.sum_comm]
      simp_rw [mul_comm (A.adjugate _ _) (Delta _ _)]
    _ = ∑ j : n, (A.updateRow j (Delta j)).det := by
      congr 1
      ext j
      rw [det_updateRow_eq_sum_mul_adjugate]

/-- Fake defects `Delta = A H` vanish in the local divisor jet when `det A = X^m`. -/
theorem fittingBoundaryClass_eq_zero_of_right_factor (m : ℕ)
    {A H : Matrix n n (Polynomial R)}
    (hdet : A.det = (Polynomial.X : Polynomial R) ^ m) :
    fittingBoundaryClass m A (A * H) = 0 := by
  rw [fittingBoundaryClass, fittingBoundaryTrace_right_factor, hdet]
  exact jetClass_mul_X_pow_eq_zero R m H.trace

/-- Fake left-factor defects `Delta = H A` vanish in the local divisor jet when
`det A = X^m`. -/
theorem fittingBoundaryClass_eq_zero_of_left_factor (m : ℕ)
    {A H : Matrix n n (Polynomial R)}
    (hdet : A.det = (Polynomial.X : Polynomial R) ^ m) :
    fittingBoundaryClass m A (H * A) = 0 := by
  rw [fittingBoundaryClass, fittingBoundaryTrace_left_factor, hdet]
  exact jetClass_mul_X_pow_eq_zero R m H.trace

/-- Fake defects modulo the local zero ideal still vanish: if
`Delta = A H + X^m K`, then its Fitting boundary class is zero. -/
theorem fittingBoundaryClass_eq_zero_of_right_factor_mod_X_pow (m : ℕ)
    {A H K Delta : Matrix n n (Polynomial R)}
    (hdet : A.det = (Polynomial.X : Polynomial R) ^ m)
    (hDelta : Delta = A * H + ((Polynomial.X : Polynomial R) ^ m) • K) :
    fittingBoundaryClass m A Delta = 0 := by
  rw [fittingBoundaryClass]
  apply jetClass_eq_zero_of_X_pow_dvd R m
  refine ⟨H.trace + (A.adjugate * K).trace, ?_⟩
  rw [fittingBoundaryTrace, hDelta, Matrix.mul_add, Matrix.trace_add]
  rw [← fittingBoundaryTrace, fittingBoundaryTrace_right_factor, hdet]
  rw [← fittingBoundaryTrace, fittingBoundaryTrace_smul]
  ring

/-- Left-factor fake defects modulo the local zero ideal still vanish: if
`Delta = H A + X^m K`, then its Fitting boundary class is zero. -/
theorem fittingBoundaryClass_eq_zero_of_left_factor_mod_X_pow (m : ℕ)
    {A H K Delta : Matrix n n (Polynomial R)}
    (hdet : A.det = (Polynomial.X : Polynomial R) ^ m)
    (hDelta : Delta = H * A + ((Polynomial.X : Polynomial R) ^ m) • K) :
    fittingBoundaryClass m A Delta = 0 := by
  rw [fittingBoundaryClass]
  apply jetClass_eq_zero_of_X_pow_dvd R m
  refine ⟨H.trace + (A.adjugate * K).trace, ?_⟩
  rw [fittingBoundaryTrace, hDelta, Matrix.mul_add, Matrix.trace_add]
  rw [← fittingBoundaryTrace, fittingBoundaryTrace_left_factor, hdet]
  rw [← fittingBoundaryTrace, fittingBoundaryTrace_smul]
  ring

/-- Adding a right-factor fake defect modulo `X^m` does not change the Fitting
boundary class.  The boundary therefore descends through the quotient by
`A End + (X^m)`. -/
theorem fittingBoundaryClass_add_right_factor_mod_X_pow (m : ℕ)
    {A H K Delta : Matrix n n (Polynomial R)}
    (hdet : A.det = (Polynomial.X : Polynomial R) ^ m) :
    fittingBoundaryClass m A (Delta + (A * H + ((Polynomial.X : Polynomial R) ^ m) • K)) =
      fittingBoundaryClass m A Delta := by
  rw [fittingBoundaryClass_add,
    fittingBoundaryClass_eq_zero_of_right_factor_mod_X_pow m hdet rfl, add_zero]

/-- Adding a left-factor fake defect modulo `X^m` does not change the Fitting
boundary class. -/
theorem fittingBoundaryClass_add_left_factor_mod_X_pow (m : ℕ)
    {A H K Delta : Matrix n n (Polynomial R)}
    (hdet : A.det = (Polynomial.X : Polynomial R) ^ m) :
    fittingBoundaryClass m A (Delta + (H * A + ((Polynomial.X : Polynomial R) ^ m) • K)) =
      fittingBoundaryClass m A Delta := by
  rw [fittingBoundaryClass_add,
    fittingBoundaryClass_eq_zero_of_left_factor_mod_X_pow m hdet rfl, add_zero]

/-- Equality after adding a right-factor fake defect preserves the Fitting boundary
class. -/
theorem fittingBoundaryClass_eq_of_eq_add_right_factor_mod_X_pow (m : ℕ)
    {A H K Delta Delta' : Matrix n n (Polynomial R)}
    (hdet : A.det = (Polynomial.X : Polynomial R) ^ m)
    (hDelta : Delta' = Delta + (A * H + ((Polynomial.X : Polynomial R) ^ m) • K)) :
    fittingBoundaryClass m A Delta' = fittingBoundaryClass m A Delta := by
  rw [hDelta, fittingBoundaryClass_add_right_factor_mod_X_pow m hdet]

/-- Equality after adding a left-factor fake defect preserves the Fitting boundary
class. -/
theorem fittingBoundaryClass_eq_of_eq_add_left_factor_mod_X_pow (m : ℕ)
    {A H K Delta Delta' : Matrix n n (Polynomial R)}
    (hdet : A.det = (Polynomial.X : Polynomial R) ^ m)
    (hDelta : Delta' = Delta + (H * A + ((Polynomial.X : Polynomial R) ^ m) • K)) :
    fittingBoundaryClass m A Delta' = fittingBoundaryClass m A Delta := by
  rw [hDelta, fittingBoundaryClass_add_left_factor_mod_X_pow m hdet]

/-- If a Fitting boundary class is nonzero, the corresponding defect cannot factor through
the seam presentation modulo the local zero ideal. -/
theorem nonzero_fittingBoundaryClass_obstructs_right_factor_mod_X_pow (m : ℕ)
    {A Delta : Matrix n n (Polynomial R)}
    (hdet : A.det = (Polynomial.X : Polynomial R) ^ m)
    (hclass : fittingBoundaryClass m A Delta ≠ 0) :
    ¬ ∃ H K : Matrix n n (Polynomial R),
      Delta = A * H + ((Polynomial.X : Polynomial R) ^ m) • K := by
  rintro ⟨H, K, hDelta⟩
  exact hclass (fittingBoundaryClass_eq_zero_of_right_factor_mod_X_pow m hdet hDelta)

/-- If a Fitting boundary class is nonzero, the corresponding defect cannot factor
through the seam presentation on the left modulo the local zero ideal. -/
theorem nonzero_fittingBoundaryClass_obstructs_left_factor_mod_X_pow (m : ℕ)
    {A Delta : Matrix n n (Polynomial R)}
    (hdet : A.det = (Polynomial.X : Polynomial R) ^ m)
    (hclass : fittingBoundaryClass m A Delta ≠ 0) :
    ¬ ∃ H K : Matrix n n (Polynomial R),
      Delta = H * A + ((Polynomial.X : Polynomial R) ^ m) • K := by
  rintro ⟨H, K, hDelta⟩
  exact hclass (fittingBoundaryClass_eq_zero_of_left_factor_mod_X_pow m hdet hDelta)

/-- If every sigma-labelled defect factors through the seam presentation modulo `X^m`,
then there is no nontrivial sigma-labelled Fitting boundary. -/
theorem no_nontrivialFittingBoundary_of_right_factor_mod_X_pow {Sigma : Type*} (m : ℕ)
    {A : Matrix n n (Polynomial R)} {Delta : Sigma → Matrix n n (Polynomial R)}
    (hdet : A.det = (Polynomial.X : Polynomial R) ^ m)
    (hfake : ∀ p : Sigma, ∃ H K : Matrix n n (Polynomial R),
      Delta p = A * H + ((Polynomial.X : Polynomial R) ^ m) • K) :
    ¬ HasNontrivialFittingBoundary m A Delta := by
  rintro ⟨p, hp⟩
  rcases hfake p with ⟨H, K, hDelta⟩
  exact hp (fittingBoundaryClass_eq_zero_of_right_factor_mod_X_pow m hdet hDelta)

/-- If every sigma-labelled defect factors through the seam presentation on the left
modulo `X^m`, then there is no nontrivial sigma-labelled Fitting boundary. -/
theorem no_nontrivialFittingBoundary_of_left_factor_mod_X_pow {Sigma : Type*} (m : ℕ)
    {A : Matrix n n (Polynomial R)} {Delta : Sigma → Matrix n n (Polynomial R)}
    (hdet : A.det = (Polynomial.X : Polynomial R) ^ m)
    (hfake : ∀ p : Sigma, ∃ H K : Matrix n n (Polynomial R),
      Delta p = H * A + ((Polynomial.X : Polynomial R) ^ m) • K) :
    ¬ HasNontrivialFittingBoundary m A Delta := by
  rintro ⟨p, hp⟩
  rcases hfake p with ⟨H, K, hDelta⟩
  exact hp (fittingBoundaryClass_eq_zero_of_left_factor_mod_X_pow m hdet hDelta)

/-! ## Torsion criterion for a supported seam boundary -/

/-- A module has a nonzero local class supported on the divisor element `f` if it has
nonzero `f`-torsion.  This is the algebraic target behind a boundary map into `R/(f)`. -/
def HasSupportedTorsion (S M : Type*) [Zero S] [Zero M] [SMul S M] (f : S) : Prop :=
  ∃ x : M, x ≠ 0 ∧ f • x = 0

/-- For every positive divisor order, the local divisor jet has a canonical nonzero class supported
on `X^m`: the class of `1` survives modulo `X^m` and multiplication by `X^m` kills it. -/
theorem localDivisorJet_hasSupportedTorsion
    (R : Type*) [CommRing R] [Nontrivial R] {m : ℕ} (hm : 0 < m) :
    HasSupportedTorsion (Polynomial R) (LocalDivisorJet R m)
      ((Polynomial.X : Polynomial R) ^ m) := by
  refine ⟨jetClass R m 1, ?_, ?_⟩
  · exact (jetClass_ne_zero_iff_exists_coeff_lt_ne_zero R m).mpr
      ⟨0, hm, by simp⟩
  · change jetClass R m (((Polynomial.X : Polynomial R) ^ m) * 1) = 0
    exact jetClass_mul_X_pow_eq_zero R m 1

/-- If scalar multiplication has no zero divisors, a nonzero divisor element has no
supported torsion.  Regular/free local lanes therefore cannot supply a boundary class
supported on the pinned divisor. -/
theorem no_supportedTorsion_of_noZeroSMulDivisors {S M : Type*} [Zero S] [Zero M] [SMul S M]
    [NoZeroSMulDivisors S M] {f : S} (hf : f ≠ 0) :
    ¬ HasSupportedTorsion S M f := by
  rintro ⟨x, hx, hfx⟩
  rcases NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero hfx with hf0 | hx0
  · exact hf hf0
  · exact hx hx0

/-- Contrapositive form: a supported seam class forces scalar multiplication by the
divisor element to fail injectivity. -/
theorem supportedTorsion_forces_not_noZeroSMulDivisors {S M : Type*}
    [Zero S] [Zero M] [SMul S M] {f : S} (hf : f ≠ 0)
    (h : HasSupportedTorsion S M f) :
    ¬ NoZeroSMulDivisors S M := by
  intro hno
  exact no_supportedTorsion_of_noZeroSMulDivisors (S := S) (M := M) hf h

end RHTower
