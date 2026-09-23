import GaloisForLFunctions.HTGeometry.RittRationalTransport

/-!
# The cyclic normal form of a map with two totally ramified critical points

A rational map of degree `p` whose only critical points are two totally ramified ones can be put,
by a Möbius change of coordinate carrying them to `0` and `∞`, into the two-parameter shape

`h(w) = (A − B λ w^p)/(1 − λ w^p)`,   `h(0) = A`,  `h(∞) = B`.

Three exact identities carry the whole theory of such a map:

`h − A = λ w^p (A−B)/(1−λw^p)`,   `h − B = (A−B)/(1−λw^p)`,
`h′ = p λ (A−B) w^{p−1}/(1−λw^p)²`.

They exhibit `0` as the only preimage of `A` and show that the derivative vanishes only there, so
every fibre over a point other than the two critical values consists of `p` distinct non-critical
points — the fibre over `y` is the set of `p`-th roots of `(y−A)/(λ(y−B))`.

Because `h` depends on `w` only through `w^p`, the map is invariant under the cyclic group of `p`-th
roots of unity.  That symmetry is what makes the divisor count for an invariant differential sharp.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K] [CharZero K]

noncomputable section

/-- The quotient rule for the derivative of a rational function. -/
theorem ratFuncDeriv_div {N D : K[X]} (hD : D ≠ 0) :
    ratFuncDeriv (algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) D)
      = algebraMap K[X] (RatFunc K) (derivative N * D - N * derivative D)
        / algebraMap K[X] (RatFunc K) (D ^ (2 : ℕ)) := by
  have hDR : algebraMap K[X] (RatFunc K) D ≠ 0 := algebraMap_ne_zero_of_ne_zero hD
  set f : RatFunc K :=
    algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) D with hf
  have hfD : f * algebraMap K[X] (RatFunc K) D = algebraMap K[X] (RatFunc K) N := by
    rw [hf, div_mul_cancel₀ _ hDR]
  have hstep : f * algebraMap K[X] (RatFunc K) (derivative D)
      + algebraMap K[X] (RatFunc K) D * ratFuncDeriv f
      = algebraMap K[X] (RatFunc K) (derivative N) := by
    have h := congrArg ratFuncDeriv hfD
    rwa [ratFuncDeriv_mul, ratFuncDeriv_algebraMap, ratFuncDeriv_algebraMap] at h
  have hsq : algebraMap K[X] (RatFunc K) (D ^ (2 : ℕ)) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (pow_ne_zero _ hD)
  rw [eq_div_iff hsq]
  have hD2 : algebraMap K[X] (RatFunc K) (D ^ (2 : ℕ))
      = algebraMap K[X] (RatFunc K) D * algebraMap K[X] (RatFunc K) D := by
    rw [← map_mul]
    ring_nf
  rw [hD2, map_sub, map_mul, map_mul]
  have hfN : f * algebraMap K[X] (RatFunc K) D = algebraMap K[X] (RatFunc K) N := hfD
  calc ratFuncDeriv f * (algebraMap K[X] (RatFunc K) D * algebraMap K[X] (RatFunc K) D)
      = (algebraMap K[X] (RatFunc K) D * ratFuncDeriv f) * algebraMap K[X] (RatFunc K) D := by
        ring
    _ = (algebraMap K[X] (RatFunc K) (derivative N)
          - f * algebraMap K[X] (RatFunc K) (derivative D)) * algebraMap K[X] (RatFunc K) D := by
        rw [← hstep]; ring
    _ = algebraMap K[X] (RatFunc K) (derivative N) * algebraMap K[X] (RatFunc K) D
          - (f * algebraMap K[X] (RatFunc K) D) * algebraMap K[X] (RatFunc K) (derivative D) := by
        ring
    _ = algebraMap K[X] (RatFunc K) (derivative N) * algebraMap K[X] (RatFunc K) D
          - algebraMap K[X] (RatFunc K) N * algebraMap K[X] (RatFunc K) (derivative D) := by
        rw [hfN]

/-! ## The normal form -/

/-- The denominator of the cyclic normal form. -/
def cnfDen (p : ℕ) (lam : K) : K[X] := 1 - C lam * X ^ p

/-- The numerator of the cyclic normal form. -/
def cnfNum (p : ℕ) (A B lam : K) : K[X] := C A - C (B * lam) * X ^ p

/-- **The cyclic normal form** `(A − Bλw^p)/(1 − λw^p)`. -/
def cnf (p : ℕ) (A B lam : K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (cnfNum p A B lam)
    / algebraMap K[X] (RatFunc K) (cnfDen p lam)

omit [CharZero K] in
@[simp] theorem cnfDen_eval (p : ℕ) (lam z : K) :
    (cnfDen p lam).eval z = 1 - lam * z ^ p := by
  simp [cnfDen]

omit [CharZero K] in
@[simp] theorem cnfNum_eval (p : ℕ) (A B lam z : K) :
    (cnfNum p A B lam).eval z = A - B * lam * z ^ p := by
  simp [cnfNum]

omit [CharZero K] in
theorem cnfDen_ne_zero {p : ℕ} (hp : 0 < p) (lam : K) : cnfDen p lam ≠ 0 := by
  intro h
  have hev := congrArg (Polynomial.eval (0 : K)) h
  rw [cnfDen_eval, eval_zero, zero_pow (by omega : p ≠ 0), mul_zero, sub_zero] at hev
  exact one_ne_zero hev

omit [CharZero K] in
theorem natDegree_cnfDen (p : ℕ) {lam : K} (hlam : lam ≠ 0) :
    (cnfDen p lam).natDegree = p := by
  have h : cnfDen p lam = C (-lam) * X ^ p + C 1 := by
    rw [cnfDen, map_neg, map_one]
    ring
  rw [h, Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul_X_pow p _ (neg_ne_zero.mpr hlam)]

/-! ## The three identities -/

omit [CharZero K] in
/-- The map minus the critical value at the origin. -/
theorem cnf_sub_C_A {p : ℕ} (hp : 0 < p) (A B lam : K) :
    cnf p A B lam - RatFunc.C A
      = algebraMap K[X] (RatFunc K) (C (lam * (A - B)) * X ^ p)
        / algebraMap K[X] (RatFunc K) (cnfDen p lam) := by
  have hD : algebraMap K[X] (RatFunc K) (cnfDen p lam) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (cnfDen_ne_zero hp lam)
  rw [cnf, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD, ← RatFunc.algebraMap_C, ← map_mul,
    ← map_sub]
  congr 1
  rw [cnfNum, cnfDen]
  simp only [map_mul, map_sub]
  ring

omit [CharZero K] in
/-- The map minus the critical value at infinity. -/
theorem cnf_sub_C_B {p : ℕ} (hp : 0 < p) (A B lam : K) :
    cnf p A B lam - RatFunc.C B
      = algebraMap K[X] (RatFunc K) (C (A - B))
        / algebraMap K[X] (RatFunc K) (cnfDen p lam) := by
  have hD : algebraMap K[X] (RatFunc K) (cnfDen p lam) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (cnfDen_ne_zero hp lam)
  rw [cnf, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD, ← RatFunc.algebraMap_C, ← map_mul,
    ← map_sub]
  congr 1
  rw [cnfNum, cnfDen]
  simp only [map_mul, map_sub]
  ring

omit [CharZero K] in
/-- The numerator of the derivative of the normal form. -/
theorem cnf_deriv_poly {p : ℕ} (hp : 0 < p) (A B lam : K) :
    derivative (cnfNum p A B lam) * cnfDen p lam
        - cnfNum p A B lam * derivative (cnfDen p lam)
      = C ((p : K) * lam * (A - B)) * X ^ (p - 1) := by
  have hpow : (X : K[X]) ^ p = X ^ (p - 1) * X := by
    conv_lhs => rw [show p = (p - 1) + 1 by omega]
    rw [pow_succ]
  rw [cnfNum, cnfDen, derivative_sub, derivative_sub, derivative_C, derivative_one,
    derivative_C_mul, derivative_C_mul, derivative_X_pow]
  simp only [map_mul, map_sub, zero_sub]
  rw [hpow]
  ring

/-- The derivative of the normal form. -/
theorem ratFuncDeriv_cnf {p : ℕ} (hp : 0 < p) (A B lam : K) :
    ratFuncDeriv (cnf p A B lam)
      = algebraMap K[X] (RatFunc K) (C ((p : K) * lam * (A - B)) * X ^ (p - 1))
        / algebraMap K[X] (RatFunc K) ((cnfDen p lam) ^ (2 : ℕ)) := by
  rw [cnf, ratFuncDeriv_div (cnfDen_ne_zero hp lam), cnf_deriv_poly hp]

end

end GaloisForLFunctions.HTGeometry
