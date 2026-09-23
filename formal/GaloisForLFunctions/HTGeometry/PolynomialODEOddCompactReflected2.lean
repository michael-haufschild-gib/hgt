import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactReflectedBase

/-!
# Exact reflected compact source jet of order 2

Complex source incidence is normalized separately from the real polynomial
identity. One derivative order per module keeps transient proof state bounded.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Exact scalar polynomial for the reflected source jet of order 2. -/
def oddCompactReflectedScalar2 (u a w : ℝ) : ℝ :=
  ((((-45 / 64 : ℝ) +
    ((165 / 256 : ℝ)*a^(1 : ℕ) +
    (-3 / 16 : ℝ)*a^(1 : ℕ)*w^(2 : ℕ))) +
    (((-21 / 256 : ℝ)*a^(2 : ℕ) +
    (-1 / 1024 : ℝ)*a^(3 : ℕ)) +
    ((1 / 32 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (1 / 192 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ)))) +
    ((((15 / 64 : ℝ)*u^(2 : ℕ) +
    (-35 / 384 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)) +
    ((1 / 48 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (-1 / 2304 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ))) +
    (((-1 / 288 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (-5 / 192 : ℝ)*u^(4 : ℕ)) +
    ((5 / 2304 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ) +
    (5 / 5184 : ℝ)*u^(6 : ℕ)))))

/-- Symbolic normalization of the reflected jet before determinant formation. -/
theorem oddCompactReflectedScalar2_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w) (oddCompactReflectedJetPolynomial 2) =
      (oddCompactReflectedScalar2 u a w : ℂ) := by
  have hf : MvPolynomial.eval (oddCompactState u a w)
      (oddCompactReflectedJetPolynomial 2) =
      ((((1 : ℝ)*oddCompactSourceScalar0 u a w*oddCompactSourceScalar2 u a w +
    ((-2 : ℝ)*oddCompactSourceScalar1 u a w*oddCompactSourceScalar1 u a w +
    (1 : ℝ)*oddCompactSourceScalar2 u a w*oddCompactSourceScalar0 u a w)) : ℝ) : ℂ) := by
    rw [eval_oddCompactReflectedJetPolynomial]
    norm_num only [Finset.sum_range_succ, Finset.sum_empty, Nat.choose, Nat.reduceSub, Nat.reduceAdd]
    simp only [oddCompactSourceScalar0_eq, oddCompactSourceScalar1_eq, oddCompactSourceScalar2_eq]
    push_cast
    ring
  rw [hf]
  apply congrArg Complex.ofReal
  unfold oddCompactSourceScalar0 oddCompactSourceScalar1 oddCompactSourceScalar2 oddCompactReflectedScalar2
  ring


end
end HTGeometry
