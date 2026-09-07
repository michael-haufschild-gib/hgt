import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactReflected2

/-!
# Exact reflected compact source jet of order 4

Complex source incidence is normalized separately from the real polynomial
identity. One derivative order per module keeps transient proof state bounded.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Exact scalar polynomial for the reflected source jet of order 4. -/
def oddCompactReflectedScalar4 (u a w : ℝ) : ℝ :=
  ((((((765 / 64 : ℝ) +
    (-2505 / 128 : ℝ)*a^1) +
    ((753 / 64 : ℝ)*a^1*w^2 +
    (-3 / 4 : ℝ)*a^1*w^4)) +
    (((4461 / 1024 : ℝ)*a^2 +
    (-3 / 32 : ℝ)*a^2*w^2) +
    ((77 / 1024 : ℝ)*a^3 +
    (3 / 256 : ℝ)*a^3*w^2))) +
    ((((27 / 4096 : ℝ)*a^4 +
    (-29 / 32 : ℝ)*u^1*a^1*w^1) +
    ((7 / 8 : ℝ)*u^1*a^1*w^3 +
    (-29 / 192 : ℝ)*u^1*a^2*w^1)) +
    (((1 / 16 : ℝ)*u^1*a^2*w^3 +
    (3 / 128 : ℝ)*u^1*a^3*w^1) +
    ((-45 / 8 : ℝ)*u^2 +
    (1555 / 384 : ℝ)*u^2*a^1)))) +
    (((((-163 / 96 : ℝ)*u^2*a^1*w^2 +
    (1 / 12 : ℝ)*u^2*a^1*w^4) +
    ((-965 / 4608 : ℝ)*u^2*a^2 +
    (-1 / 48 : ℝ)*u^2*a^2*w^2)) +
    (((41 / 3072 : ℝ)*u^2*a^3 +
    (11 / 144 : ℝ)*u^3*a^1*w^1) +
    ((-7 / 72 : ℝ)*u^3*a^1*w^3 +
    (23 / 576 : ℝ)*u^3*a^2*w^1))) +
    ((((95 / 96 : ℝ)*u^4 +
    (-973 / 3456 : ℝ)*u^4*a^1) +
    ((25 / 576 : ℝ)*u^4*a^1*w^2 +
    (319 / 27648 : ℝ)*u^4*a^2)) +
    (((7 / 2592 : ℝ)*u^5*a^1*w^1 +
    (-25 / 324 : ℝ)*u^6) +
    ((253 / 31104 : ℝ)*u^6*a^1 +
    (35 / 15552 : ℝ)*u^8)))))

/-- Symbolic normalization of the reflected jet before determinant formation. -/
theorem oddCompactReflectedScalar4_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w) (oddCompactReflectedJetPolynomial 4) =
      (oddCompactReflectedScalar4 u a w : ℂ) := by
  have hf : MvPolynomial.eval (oddCompactState u a w)
      (oddCompactReflectedJetPolynomial 4) =
      (((((1 : ℝ)*oddCompactSourceScalar0 u a w*oddCompactSourceScalar4 u a w +
    (-4 : ℝ)*oddCompactSourceScalar1 u a w*oddCompactSourceScalar3 u a w) +
    ((6 : ℝ)*oddCompactSourceScalar2 u a w*oddCompactSourceScalar2 u a w +
    ((-4 : ℝ)*oddCompactSourceScalar3 u a w*oddCompactSourceScalar1 u a w +
    (1 : ℝ)*oddCompactSourceScalar4 u a w*oddCompactSourceScalar0 u a w))) : ℝ) : ℂ) := by
    rw [eval_oddCompactReflectedJetPolynomial]
    norm_num only [Finset.sum_range_succ, Finset.sum_empty, Nat.choose, Nat.reduceSub, Nat.reduceAdd]
    simp only [oddCompactSourceScalar0_eq, oddCompactSourceScalar1_eq, oddCompactSourceScalar2_eq, oddCompactSourceScalar3_eq, oddCompactSourceScalar4_eq]
    push_cast
    ring
  rw [hf]
  apply congrArg Complex.ofReal
  unfold oddCompactSourceScalar0 oddCompactSourceScalar1 oddCompactSourceScalar2 oddCompactSourceScalar3 oddCompactSourceScalar4 oddCompactReflectedScalar4
  ring


end
end HTGeometry
