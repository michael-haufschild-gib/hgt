import GaloisForLFunctions.HTGeometry.GeometricInverseTruncation
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The fiber equation of the reciprocal jet

The top coefficient of the truncated inverse of `a + t R` is an alternating sum of the coefficients
of the powers of `R`, weighted by powers of the inverse of `a`.  Clearing those inverse powers by
multiplying with `a ^ (n+1)` turns the equation for that coefficient into a polynomial equation in
`a` of degree `n + 1` with no term of degree `n`.

Its coefficients are the alternating tail coefficients `(-1) ^ (n-j)` times the `j`-th coefficient
of `R ^ (n-j)`, which is the parameter change of the rank-one horizon cover.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [CommRing A]

theorem pow_mul_pow_of_mul_eq_one {a b : A} (hab : a * b = 1) {n k : ℕ} (hk : k ≤ n) :
    b ^ (k + 1) * a ^ (n + 1) = a ^ (n - k) := by
  have hsplit : a ^ (n + 1) = a ^ (n - k) * a ^ (k + 1) := by
    rw [← pow_add]
    congr 1
    omega
  calc b ^ (k + 1) * a ^ (n + 1)
      = a ^ (n - k) * (a ^ (k + 1) * b ^ (k + 1)) := by rw [hsplit]; ring
    _ = a ^ (n - k) * (a * b) ^ (k + 1) := by rw [mul_pow]
    _ = a ^ (n - k) := by rw [hab, one_pow, mul_one]

/-- **The fiber equation of the reciprocal jet.**  The top coefficient of the inverse of `a + t R`,
cleared of denominators, is the alternating tail polynomial evaluated at `a`. -/
theorem coeff_mul_pow_eq_tail_sum {a b : A} (hab : a * b = 1) (R Y : PowerSeries A)
    (hY : ((PowerSeries.C a : PowerSeries A) + PowerSeries.X * R) * Y = 1) {n : ℕ} (hn : 0 < n) :
    PowerSeries.coeff n Y * a ^ (n + 1) =
      ∑ j ∈ Finset.range n,
        (-1 : A) ^ (n - j) * PowerSeries.coeff j (R ^ (n - j)) * a ^ j := by
  have h1 : PowerSeries.coeff n Y =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : A) ^ k * b ^ (k + 1) * PowerSeries.coeff (n - k) (R ^ k) := by
    rw [coeff_eq_geomInverseSum_of_mul_eq_one hab R Y hY (le_refl n),
      coeff_geomInverseSum_top]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((-1 : A) ^ k * b ^ (k + 1) * PowerSeries.coeff (n - k) (R ^ k)) * a ^ (n + 1) =
        (-1 : A) ^ k * PowerSeries.coeff (n - k) (R ^ k) * a ^ (n - k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    calc ((-1 : A) ^ k * b ^ (k + 1) * PowerSeries.coeff (n - k) (R ^ k)) * a ^ (n + 1)
        = (-1 : A) ^ k * PowerSeries.coeff (n - k) (R ^ k) *
            (b ^ (k + 1) * a ^ (n + 1)) := by ring
      _ = (-1 : A) ^ k * PowerSeries.coeff (n - k) (R ^ k) * a ^ (n - k) := by
          rw [pow_mul_pow_of_mul_eq_one hab (by omega : k ≤ n)]
  rw [h1, Finset.sum_mul, Finset.sum_congr rfl hterm, Finset.sum_range_succ']
  have hzero : (-1 : A) ^ (0 : ℕ) * PowerSeries.coeff (n - 0) (R ^ (0 : ℕ)) * a ^ (n - 0) = 0 := by
    rw [pow_zero, pow_zero, one_mul, PowerSeries.coeff_one, if_neg (by omega : ¬ n - 0 = 0),
      zero_mul]
  rw [hzero, add_zero]
  refine (Finset.sum_range_reflect _ n).symm.trans (Finset.sum_congr rfl fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have hidx : n - 1 - j + 1 = n - j := by omega
  have hjj : n - (n - j) = j := by omega
  rw [hidx, hjj]

/-- **The same, with the tail given by a polynomial.**  The coefficients of the fiber equation are
the alternating coefficients of the powers of the tail polynomial. -/
theorem coeff_mul_pow_eq_polynomial_tail_sum {a b : A} (hab : a * b = 1) (p : Polynomial A)
    (Y : PowerSeries A)
    (hY : ((PowerSeries.C a : PowerSeries A) +
      PowerSeries.X * (p : PowerSeries A)) * Y = 1) {n : ℕ} (hn : 0 < n) :
    PowerSeries.coeff n Y * a ^ (n + 1) =
      ∑ j ∈ Finset.range n,
        (-1 : A) ^ (n - j) * (p ^ (n - j)).coeff j * a ^ j := by
  rw [coeff_mul_pow_eq_tail_sum hab (p : PowerSeries A) Y hY hn]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Polynomial.coe_pow, Polynomial.coeff_coe]

/-! ## The fiber equation as a polynomial -/

/-- The fiber equation of the rank-one horizon cover, as a polynomial in the source coefficient. -/
noncomputable def fiberPolynomial (q : A) (R : PowerSeries A) (n : ℕ) : Polynomial A :=
  Polynomial.C q * Polynomial.X ^ (n + 1) -
    ∑ j ∈ Finset.range n,
      Polynomial.C ((-1 : A) ^ (n - j) * PowerSeries.coeff j (R ^ (n - j))) *
        Polynomial.X ^ j

theorem natDegree_fiberTail_lt (R : PowerSeries A) (n : ℕ) :
    (∑ j ∈ Finset.range n,
      Polynomial.C ((-1 : A) ^ (n - j) * PowerSeries.coeff j (R ^ (n - j))) *
        Polynomial.X ^ j).natDegree < n + 1 := by
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_)
    (by omega : n < n + 1)
  rw [Finset.mem_range] at hj
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  exact le_trans (Polynomial.natDegree_X_pow_le j) (by omega)

/-- **The fiber equation has degree one more than the tail length.** -/
theorem natDegree_fiberPolynomial [IsDomain A] {q : A} (hq : q ≠ 0) (R : PowerSeries A)
    (n : ℕ) : (fiberPolynomial q R n).natDegree = n + 1 := by
  have hlead : (Polynomial.C q * Polynomial.X ^ (n + 1) : Polynomial A).natDegree = n + 1 := by
    rw [Polynomial.natDegree_C_mul hq, Polynomial.natDegree_X_pow]
  rw [fiberPolynomial, Polynomial.natDegree_sub_eq_left_of_natDegree_lt, hlead]
  rw [hlead]
  exact natDegree_fiberTail_lt R n

/-- **The fiber equation has no term of degree one less than its degree.** -/
theorem coeff_fiberPolynomial_self (q : A) (R : PowerSeries A) (n : ℕ) :
    (fiberPolynomial q R n).coeff n = 0 := by
  rw [fiberPolynomial, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, if_neg (by omega : ¬ n = n + 1), mul_zero,
    Polynomial.finsetSum_coeff]
  have hterm : ∀ j ∈ Finset.range n,
      (Polynomial.C ((-1 : A) ^ (n - j) * PowerSeries.coeff j (R ^ (n - j))) *
        Polynomial.X ^ j).coeff n = 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega : ¬ n = j), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero, sub_zero]

/-- **The source coefficient is a root of the fiber equation.** -/
theorem eval_fiberPolynomial_eq_zero {a b : A} (hab : a * b = 1) (R Y : PowerSeries A)
    (hY : ((PowerSeries.C a : PowerSeries A) + PowerSeries.X * R) * Y = 1) {n : ℕ}
    (hn : 0 < n) :
    Polynomial.eval a (fiberPolynomial (PowerSeries.coeff n Y) R n) = 0 := by
  rw [fiberPolynomial, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum, sub_eq_zero]
  rw [coeff_mul_pow_eq_tail_sum hab R Y hY hn]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_assoc]

/-! ## Reciprocal duality -/

/-- The constant term of the inverse is the inverse of the constant term. -/
theorem constantCoeff_inverse {a b : A} (hab : a * b = 1) (R Y : PowerSeries A)
    (hY : ((PowerSeries.C a : PowerSeries A) + PowerSeries.X * R) * Y = 1) :
    PowerSeries.constantCoeff Y = b := by
  have h := congrArg PowerSeries.constantCoeff hY
  rw [map_mul, map_add, map_one, PowerSeries.constantCoeff_C, map_mul,
    PowerSeries.constantCoeff_X, zero_mul, add_zero] at h
  calc PowerSeries.constantCoeff Y
      = (b * a) * PowerSeries.constantCoeff Y := by rw [mul_comm b a, hab, one_mul]
    _ = b * (a * PowerSeries.constantCoeff Y) := by ring
    _ = b := by rw [h, mul_one]

/-- The tail of the inverse. -/
noncomputable def reciprocalTail (Y : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun p => PowerSeries.coeff (p + 1) Y

theorem eq_const_add_X_mul_reciprocalTail (Y : PowerSeries A) :
    Y = (PowerSeries.C (PowerSeries.constantCoeff Y) : PowerSeries A) +
      PowerSeries.X * reciprocalTail Y := by
  conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const Y]
  rw [reciprocalTail]
  ring

/-- **Reciprocal duality.**  The inverse of a jet with invertible constant term is again such a jet,
and its fiber equation is the same equation with the two packets exchanged. -/
theorem coeff_mul_pow_eq_tail_sum_reciprocal {a b : A} (hab : a * b = 1) (R Y : PowerSeries A)
    (hY : ((PowerSeries.C a : PowerSeries A) + PowerSeries.X * R) * Y = 1) {n : ℕ}
    (hn : 0 < n) :
    PowerSeries.coeff n ((PowerSeries.C a : PowerSeries A) + PowerSeries.X * R) * b ^ (n + 1) =
      ∑ j ∈ Finset.range n,
        (-1 : A) ^ (n - j) * PowerSeries.coeff j (reciprocalTail Y ^ (n - j)) * b ^ j := by
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  have hconst : PowerSeries.constantCoeff Y = b := constantCoeff_inverse hab R Y hY
  have hdecomp : Y = (PowerSeries.C b : PowerSeries A) +
      PowerSeries.X * reciprocalTail Y := by
    conv_lhs => rw [eq_const_add_X_mul_reciprocalTail Y]
    rw [hconst]
  have hswap : ((PowerSeries.C b : PowerSeries A) + PowerSeries.X * reciprocalTail Y) *
      ((PowerSeries.C a : PowerSeries A) + PowerSeries.X * R) = 1 := by
    rw [← hdecomp, mul_comm]
    exact hY
  exact coeff_mul_pow_eq_tail_sum hba (reciprocalTail Y)
    ((PowerSeries.C a : PowerSeries A) + PowerSeries.X * R) hswap hn

end GaloisForLFunctions.HTGeometry
