import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactReflected4

/-!
# Exact reflected compact source jet of order 6

Complex source incidence is normalized separately from the real polynomial
identity. One derivative order per module keeps transient proof state bounded.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Exact scalar polynomial for the reflected source jet of order 6. -/
def oddCompactReflectedScalar6 (u a w : ℝ) : ℝ :=
  ((((((-24345 / 64 : ℝ) +
    ((243615 / 256 : ℝ)*a^1 +
    (-58287 / 64 : ℝ)*a^1*w^2)) +
    (((1965 / 16 : ℝ)*a^1*w^4 +
    (-3 / 1 : ℝ)*a^1*w^6) +
    ((-333759 / 1024 : ℝ)*a^2 +
    (4515 / 256 : ℝ)*a^2*w^2))) +
    (((3 / 2 : ℝ)*a^2*w^4 +
    ((-31519 / 4096 : ℝ)*a^3 +
    (-597 / 256 : ℝ)*a^3*w^2)) +
    (((3 / 64 : ℝ)*a^3*w^4 +
    (-8199 / 4096 : ℝ)*a^4) +
    ((-51 / 1024 : ℝ)*a^4*w^2 +
    (21 / 16384 : ℝ)*a^5)))) +
    ((((61 / 2 : ℝ)*u^1*a^1*w^1 +
    ((-2195 / 16 : ℝ)*u^1*a^1*w^3 +
    (21 / 2 : ℝ)*u^1*a^1*w^5)) +
    (((-1423 / 384 : ℝ)*u^1*a^2*w^1 +
    (-27 / 2 : ℝ)*u^1*a^2*w^3) +
    ((1 / 4 : ℝ)*u^1*a^2*w^5 +
    (-2817 / 512 : ℝ)*u^1*a^3*w^1))) +
    ((((-27 / 64 : ℝ)*u^1*a^3*w^3 +
    (-119 / 1024 : ℝ)*u^1*a^4*w^1) +
    ((15465 / 64 : ℝ)*u^2 +
    (-52855 / 192 : ℝ)*u^2*a^1)) +
    (((32419 / 192 : ℝ)*u^2*a^1*w^2 +
    (-635 / 24 : ℝ)*u^2*a^1*w^4) +
    ((1 / 3 : ℝ)*u^2*a^1*w^6 +
    (341681 / 9216 : ℝ)*u^2*a^2))))) +
    (((((-289 / 384 : ℝ)*u^2*a^2*w^2 +
    ((-29 / 24 : ℝ)*u^2*a^2*w^4 +
    (-29263 / 6144 : ℝ)*u^2*a^3)) +
    (((5 / 256 : ℝ)*u^2*a^3*w^2 +
    (403 / 12288 : ℝ)*u^2*a^4) +
    ((167 / 24 : ℝ)*u^3*a^1*w^1 +
    (1295 / 72 : ℝ)*u^3*a^1*w^3))) +
    (((-7 / 6 : ℝ)*u^3*a^1*w^5 +
    ((-3871 / 576 : ℝ)*u^3*a^2*w^1 +
    (73 / 72 : ℝ)*u^3*a^2*w^3)) +
    (((-1247 / 4608 : ℝ)*u^3*a^3*w^1 +
    (-5815 / 96 : ℝ)*u^4) +
    ((120595 / 3456 : ℝ)*u^4*a^1 +
    (-1375 / 192 : ℝ)*u^4*a^1*w^2)))) +
    ((((205 / 144 : ℝ)*u^4*a^1*w^4 +
    ((-128183 / 27648 : ℝ)*u^4*a^2 +
    (-3007 / 6912 : ℝ)*u^4*a^2*w^2)) +
    (((4145 / 36864 : ℝ)*u^4*a^3 +
    (-293 / 324 : ℝ)*u^5*a^1*w^1) +
    ((-395 / 1296 : ℝ)*u^5*a^1*w^3 +
    (-1213 / 10368 : ℝ)*u^5*a^2*w^1))) +
    ((((19465 / 2592 : ℝ)*u^6 +
    (-12097 / 5184 : ℝ)*u^6*a^1) +
    ((-205 / 5184 : ℝ)*u^6*a^1*w^2 +
    (30865 / 248832 : ℝ)*u^6*a^2)) +
    (((-53 / 1944 : ℝ)*u^7*a^1*w^1 +
    (-7175 / 15552 : ℝ)*u^8) +
    ((34189 / 559872 : ℝ)*u^8*a^1 +
    (175 / 15552 : ℝ)*u^10))))))

/-- Symbolic normalization of the reflected jet before determinant formation. -/
theorem oddCompactReflectedScalar6_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w) (oddCompactReflectedJetPolynomial 6) =
      (oddCompactReflectedScalar6 u a w : ℂ) := by
  have hf : MvPolynomial.eval (oddCompactState u a w)
      (oddCompactReflectedJetPolynomial 6) =
      (((((1 : ℝ)*oddCompactSourceScalar0 u a w*oddCompactSourceScalar6 u a w +
    ((-6 : ℝ)*oddCompactSourceScalar1 u a w*oddCompactSourceScalar5 u a w +
    (15 : ℝ)*oddCompactSourceScalar2 u a w*oddCompactSourceScalar4 u a w)) +
    (((-20 : ℝ)*oddCompactSourceScalar3 u a w*oddCompactSourceScalar3 u a w +
    (15 : ℝ)*oddCompactSourceScalar4 u a w*oddCompactSourceScalar2 u a w) +
    ((-6 : ℝ)*oddCompactSourceScalar5 u a w*oddCompactSourceScalar1 u a w +
    (1 : ℝ)*oddCompactSourceScalar6 u a w*oddCompactSourceScalar0 u a w))) : ℝ) : ℂ) := by
    rw [eval_oddCompactReflectedJetPolynomial]
    norm_num only [Finset.sum_range_succ, Finset.sum_empty, Nat.choose, Nat.reduceSub, Nat.reduceAdd]
    simp only [oddCompactSourceScalar0_eq, oddCompactSourceScalar1_eq, oddCompactSourceScalar2_eq, oddCompactSourceScalar3_eq, oddCompactSourceScalar4_eq, oddCompactSourceScalar5_eq, oddCompactSourceScalar6_eq]
    push_cast
    ring
  rw [hf]
  apply congrArg Complex.ofReal
  unfold oddCompactSourceScalar0 oddCompactSourceScalar1 oddCompactSourceScalar2 oddCompactSourceScalar3 oddCompactSourceScalar4 oddCompactSourceScalar5 oddCompactSourceScalar6 oddCompactReflectedScalar6
  ring


end
end HTGeometry
