import GaloisForLFunctions.RHTower.PrimeArchBernsteinLoschmidtPurity
import GaloisForLFunctions.RHTower.PrimeArchBernsteinAbelSusceptibility

/-!
# The Bernstein Legendre double-source kernel

The degree-`n` Bernstein row kernel is

```
S_n(x,y) = ∑_i B_{n,i}(x) B_{n,i}(y),
```

and the bivariate moment functional `L_m ⊗ L_m` evaluates it to the coefficient purity `Π_n`.
Summing the row kernels is the classical Legendre generating function: with

```
A(x,y) = 1 - x - y + 2xy,   D(x,y) = 1 - x - y,
b = x(1-y),   c = (1-x)y,
```

the `t^n` coefficient of `(1 - 2tA + t²D²)^{-1/2}` is the polynomial
`∑_{2k ≤ n} C(n,2k) C(2k,k) A^{n-2k} (bc)^k`, and that polynomial *is* `S_n`.

The whole identity reduces to Vandermonde: after writing `P = xy`, `Q = (1-x)(1-y)` one has
`A = P + Q` and `bc = PQ`, and the coefficient of `P^i Q^{n-i}` on the kernel side is
`∑_k C(n,2k)C(2k,k)C(n-2k,i-k) = C(n,i) ∑_k C(i,k)C(n-i,k) = C(n,i)²`.

Along the conjugate reflection `y = conj x` the quadratic under the radical factors as
`(1 - B₊(u)² t)(1 - B₋(u)² t)` with `B_±(u) = ‖u‖ ± ‖1-u‖`, so the first positive branch point is
`t = B₊(u)^{-2}` — exactly the reciprocal square of the endpoint Bernstein atom amplitude whose
maximum the corpus already identifies with the false-RH Abel radius.
-/

open Finset Polynomial
open scoped Nat

namespace RHTower

noncomputable section

open HTGeometry


theorem choose_triple_eq {n i k : ℕ} (hki : k ≤ i) (hik : i + k ≤ n) :
    n.choose (2*k) * ((2*k).choose k * (n - 2*k).choose (i - k))
      = n.choose i * (i.choose k * (n - i).choose k) := by
  have h2k : 2 * k ≤ n := by omega
  have hkn : k ≤ 2 * k := by omega
  have hik2 : i - k ≤ n - 2 * k := by omega
  have hin : i ≤ n := by omega
  have hkni : k ≤ n - i := by omega
  have hpos : 0 < k ! * k ! * (i - k)! * (n - i - k)! := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  have e1 := Nat.choose_mul_factorial_mul_factorial h2k
  have e2 := Nat.choose_mul_factorial_mul_factorial hkn
  have e3 := Nat.choose_mul_factorial_mul_factorial hik2
  have e4 := Nat.choose_mul_factorial_mul_factorial hin
  have e5 := Nat.choose_mul_factorial_mul_factorial hki
  have e6 := Nat.choose_mul_factorial_mul_factorial hkni
  rw [show 2 * k - k = k by omega] at e2
  rw [show n - 2 * k - (i - k) = n - i - k by omega] at e3
  calc n.choose (2*k) * ((2*k).choose k * (n - 2*k).choose (i - k)) *
        (k ! * k ! * (i - k)! * (n - i - k)!)
      = n.choose (2*k) * ((2*k).choose k * k ! * k !) *
        ((n - 2*k).choose (i - k) * (i - k)! * (n - i - k)!) := by ring
    _ = n.choose (2*k) * (2*k)! * (n - 2*k)! := by rw [e2, e3]
    _ = n ! := e1
    _ = n.choose i * i ! * (n - i)! := e4.symm
    _ = n.choose i * (i.choose k * k ! * (i - k)!) * ((n-i).choose k * k ! * (n - i - k)!) := by
        rw [e5, e6]
    _ = n.choose i * (i.choose k * (n - i).choose k) *
        (k ! * k ! * (i - k)! * (n - i - k)!) := by ring

theorem sum_choose_pair {n i : ℕ} (hi : i ≤ n) :
    ∑ k ∈ Finset.range (n + 1), i.choose k * (n - i).choose k = n.choose i := by
  have hv := Nat.add_choose_eq i (n - i) (n - i)
  rw [show i + (n - i) = n by omega] at hv
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  have hv2 : n.choose (n - i) = ∑ a ∈ Finset.range (n - i + 1), i.choose a * (n - i).choose a := by
    rw [hv]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : a ≤ n - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rw [Nat.choose_symm ha']
  rw [Nat.choose_symm hi] at hv2
  rw [hv2]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro a ha
    rw [Finset.mem_range] at *
    omega
  · intro a _ ha
    rw [Finset.mem_range] at ha
    rw [Nat.choose_eq_zero_of_lt (by omega : n - i < a)]
    ring

theorem sum_choose_triple {n i : ℕ} (hi : i ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
      (if k ≤ i ∧ i + k ≤ n then
        n.choose (2*k) * ((2*k).choose k * (n - 2*k).choose (i - k)) else 0)
      = (n.choose i)^(2 : ℕ) := by
  have h1 : ∀ k ∈ Finset.range (n+1),
      (if k ≤ i ∧ i + k ≤ n then
        n.choose (2*k) * ((2*k).choose k * (n - 2*k).choose (i - k)) else 0)
      = n.choose i * (i.choose k * (n - i).choose k) := by
    intro k _
    by_cases hc : k ≤ i ∧ i + k ≤ n
    · rw [if_pos hc, choose_triple_eq hc.1 hc.2]
    · rw [if_neg hc]
      rcases Nat.lt_or_ge i k with h | h
      · rw [Nat.choose_eq_zero_of_lt h]
        ring
      · have hk : n - i < k := by omega
        rw [Nat.choose_eq_zero_of_lt hk]
        ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, sum_choose_pair hi, sq]

/-- **The Legendre row identity.** -/
theorem legendre_row_identity {R : Type*} [CommRing R] (P Q : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (if 2 * k ≤ n then ((n.choose (2*k) * (2*k).choose k : ℕ) : R)
          * (P + Q) ^ (n - 2*k) * (P * Q) ^ k else 0)
      = ∑ i ∈ Finset.range (n + 1), ((n.choose i ^ (2 : ℕ) : ℕ) : R) * P ^ i * Q ^ (n - i) := by
  classical
  set F : ℕ → ℕ → R := fun i k =>
    if k ≤ i ∧ i + k ≤ n then
      ((n.choose (2*k) * ((2*k).choose k * (n - 2*k).choose (i - k)) : ℕ) : R)
        * P ^ i * Q ^ (n - i)
    else 0 with hFdef
  have hA : ∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1), F i k
      = ∑ i ∈ Finset.range (n + 1), ((n.choose i ^ (2 : ℕ) : ℕ) : R) * P ^ i * Q ^ (n - i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hterm : ∀ k ∈ Finset.range (n + 1), F i k
        = ((if k ≤ i ∧ i + k ≤ n then
            n.choose (2*k) * ((2*k).choose k * (n - 2*k).choose (i - k)) else 0 : ℕ) : R)
          * P ^ i * Q ^ (n - i) := by
      intro k _
      rw [hFdef]
      by_cases hc : k ≤ i ∧ i + k ≤ n
      · simp only [if_pos hc]
      · simp only [if_neg hc]
        simp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum,
      sum_choose_triple hi']
  have hB : ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1), F i k
      = ∑ k ∈ Finset.range (n + 1),
        (if 2 * k ≤ n then ((n.choose (2*k) * (2*k).choose k : ℕ) : R)
          * (P + Q) ^ (n - 2*k) * (P * Q) ^ k else 0) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    by_cases hkn : 2 * k ≤ n
    · rw [if_pos hkn]
      have hfilter : (Finset.range (n + 1)).filter (fun i => k ≤ i ∧ i + k ≤ n)
          = Finset.Ico k (n - k + 1) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [hFdef]
      simp only
      rw [← Finset.sum_filter, hfilter, Finset.sum_Ico_eq_sum_range]
      rw [show n - k + 1 - k = n - 2 * k + 1 by omega]
      have hexp : ∀ j ∈ Finset.range (n - 2*k + 1),
          ((n.choose (2*k) * ((2*k).choose k * (n - 2*k).choose (k + j - k)) : ℕ) : R)
            * P ^ (k + j) * Q ^ (n - (k + j))
          = (((n.choose (2*k) * (2*k).choose k : ℕ) : R) * (P * Q) ^ k)
            * (P ^ j * Q ^ (n - 2*k - j) * (((n - 2*k).choose j : ℕ) : R)) := by
        intro j hj
        have hj' : j ≤ n - 2*k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [show k + j - k = j by omega]
        push_cast
        rw [mul_pow, show n - (k + j) = (n - 2*k - j) + k by omega, pow_add]
        ring
      rw [Finset.sum_congr rfl hexp, ← Finset.mul_sum, ← add_pow]
      ring
    · rw [if_neg hkn]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hFdef]
      simp only
      rw [if_neg (by omega)]
  rw [← hA, ← hB, Finset.sum_comm]

/-! ### The bivariate moment functional -/

/-- The bivariate moment functional `L_m ⊗ L_m`, determined by `(L_m ⊗ L_m)(x^j y^k) = m_j m_k`.
Bivariate polynomials are represented as `ℝ[x][y]`. -/
def bivariateMomentFunctional (m : ℕ → ℝ) (p : Polynomial (Polynomial ℝ)) : ℝ :=
  p.sum fun k c => momentFunctional m c * m k

theorem bivariateMomentFunctional_add (m : ℕ → ℝ) (p q : Polynomial (Polynomial ℝ)) :
    bivariateMomentFunctional m (p + q)
      = bivariateMomentFunctional m p + bivariateMomentFunctional m q := by
  refine Polynomial.sum_add_index p q _ (fun i => by simp) (fun a b₁ b₂ => ?_)
  rw [momentFunctional_add]
  ring

theorem bivariateMomentFunctional_zero (m : ℕ → ℝ) :
    bivariateMomentFunctional m 0 = 0 := by
  simp [bivariateMomentFunctional]

theorem bivariateMomentFunctional_sum (m : ℕ → ℝ) {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (Polynomial ℝ)) :
    bivariateMomentFunctional m (∑ i ∈ s, f i)
      = ∑ i ∈ s, bivariateMomentFunctional m (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [bivariateMomentFunctional_zero]
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha, bivariateMomentFunctional_add, ih, Finset.sum_insert ha]

/-- The tensor property: on a product `p(x) q(y)` the functional splits. -/
theorem bivariateMomentFunctional_mul (m : ℕ → ℝ) (p q : Polynomial ℝ) :
    bivariateMomentFunctional m
        (Polynomial.C p * q.map (Polynomial.C : ℝ →+* Polynomial ℝ))
      = momentFunctional m p * momentFunctional m q := by
  classical
  have hcoeff : ∀ k : ℕ,
      (Polynomial.C p * q.map (Polynomial.C : ℝ →+* Polynomial ℝ)).coeff k
        = Polynomial.C (q.coeff k) * p := by
    intro k
    rw [Polynomial.C_mul', Polynomial.coeff_smul, Polynomial.coeff_map]
    simp [mul_comm]
  have hsupp : (Polynomial.C p * q.map (Polynomial.C : ℝ →+* Polynomial ℝ)).support ⊆ q.support := by
    intro k hk
    rw [Polynomial.mem_support_iff] at hk ⊢
    intro hq
    apply hk
    rw [hcoeff k, hq]
    simp
  rw [bivariateMomentFunctional, Polynomial.sum_def]
  have hq : momentFunctional m q = ∑ k ∈ q.support, q.coeff k * m k :=
    momentFunctional_eq_support_sum m q
  rw [hq, Finset.mul_sum]
  refine (Finset.sum_subset hsupp ?_).trans ?_
  · intro k _ hk
    rw [Polynomial.notMem_support_iff.mp hk]
    simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcoeff k]
    have hval : momentFunctional m (Polynomial.C (q.coeff k) * p)
        = q.coeff k * momentFunctional m p := by
      rw [← Polynomial.smul_eq_C_mul, momentFunctional_smul]
    rw [hval]
    ring

/-! ### The Bernstein row kernel and the Legendre kernel coefficient -/

/-- The `x` variable of `ℝ[x][y]`. -/
def xVar : Polynomial (Polynomial ℝ) := Polynomial.C Polynomial.X

/-- The `y` variable of `ℝ[x][y]`. -/
def yVar : Polynomial (Polynomial ℝ) := Polynomial.X

/-- `S_n(x,y) = ∑_i B_{n,i}(x) B_{n,i}(y)`. -/
def bernsteinRowKernel (n : ℕ) : Polynomial (Polynomial ℝ) :=
  ∑ i ∈ Finset.range (n + 1),
    Polynomial.C (bernsteinPolynomial ℝ n i) *
      (bernsteinPolynomial ℝ n i).map (Polynomial.C : ℝ →+* Polynomial ℝ)

/-- **(4)** The bivariate moment functional evaluates the row kernel to the coefficient purity. -/
theorem bivariateMomentFunctional_bernsteinRowKernel (m : ℕ → ℝ) (n : ℕ) :
    bivariateMomentFunctional m (bernsteinRowKernel n) = bernsteinCoefficientPurity m n := by
  rw [bernsteinRowKernel, bivariateMomentFunctional_sum, bernsteinCoefficientPurity]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bivariateMomentFunctional_mul, bernsteinCoefficient, sq]

theorem C_bernsteinPolynomial (n i : ℕ) :
    Polynomial.C (bernsteinPolynomial ℝ n i)
      = ((n.choose i : ℕ) : Polynomial (Polynomial ℝ)) * xVar ^ i * (1 - xVar) ^ (n - i) := by
  rw [bernsteinPolynomial, xVar]
  simp [Polynomial.C_pow, Polynomial.C_mul, Polynomial.C_sub, map_natCast]

theorem map_bernsteinPolynomial (n i : ℕ) :
    (bernsteinPolynomial ℝ n i).map (Polynomial.C : ℝ →+* Polynomial ℝ)
      = ((n.choose i : ℕ) : Polynomial (Polynomial ℝ)) * yVar ^ i * (1 - yVar) ^ (n - i) := by
  rw [bernsteinPolynomial, yVar]
  simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_natCast,
    Polynomial.map_one, Polynomial.map_X]

theorem bernsteinRowKernel_eq_sum (n : ℕ) :
    bernsteinRowKernel n
      = ∑ i ∈ Finset.range (n + 1), ((n.choose i ^ (2 : ℕ) : ℕ) : Polynomial (Polynomial ℝ))
          * (xVar * yVar) ^ i * ((1 - xVar) * (1 - yVar)) ^ (n - i) := by
  rw [bernsteinRowKernel]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [C_bernsteinPolynomial, map_bernsteinPolynomial, mul_pow, mul_pow]
  push_cast
  ring

/-- `A(x,y) = 1 - x - y + 2xy`. -/
def kernelA : Polynomial (Polynomial ℝ) := 1 - xVar - yVar + 2 * (xVar * yVar)

/-- `b(x,y) = x(1-y)`. -/
def kernelB : Polynomial (Polynomial ℝ) := xVar * (1 - yVar)

/-- `c(x,y) = (1-x)y`. -/
def kernelC : Polynomial (Polynomial ℝ) := (1 - xVar) * yVar

/-- `D(x,y) = 1 - x - y`. -/
def kernelD : Polynomial (Polynomial ℝ) := 1 - xVar - yVar

/-- The `t^n` coefficient of `(1 - 2tA + t²D²)^{-1/2}`, as a polynomial. -/
def legendreKernelCoeff (n : ℕ) : Polynomial (Polynomial ℝ) :=
  ∑ k ∈ Finset.range (n + 1),
    (if 2 * k ≤ n then ((n.choose (2*k) * (2*k).choose k : ℕ) : Polynomial (Polynomial ℝ))
      * kernelA ^ (n - 2*k) * (kernelB * kernelC) ^ k else 0)

theorem kernelA_eq : kernelA = xVar * yVar + (1 - xVar) * (1 - yVar) := by
  rw [kernelA]; ring

theorem kernelBC_eq : kernelB * kernelC = (xVar * yVar) * ((1 - xVar) * (1 - yVar)) := by
  rw [kernelB, kernelC]; ring

/-- **(6)** The row kernel is the Legendre kernel coefficient. -/
theorem bernsteinRowKernel_eq_legendreKernelCoeff (n : ℕ) :
    bernsteinRowKernel n = legendreKernelCoeff n := by
  rw [bernsteinRowKernel_eq_sum, legendreKernelCoeff]
  have hcongr : ∀ k ∈ Finset.range (n + 1),
      (if 2 * k ≤ n then ((n.choose (2*k) * (2*k).choose k : ℕ) : Polynomial (Polynomial ℝ))
        * kernelA ^ (n - 2*k) * (kernelB * kernelC) ^ k else 0)
      = (if 2 * k ≤ n then ((n.choose (2*k) * (2*k).choose k : ℕ) : Polynomial (Polynomial ℝ))
        * ((xVar * yVar) + (1 - xVar) * (1 - yVar)) ^ (n - 2*k)
        * ((xVar * yVar) * ((1 - xVar) * (1 - yVar))) ^ k else 0) := by
    intro k _
    rw [kernelA_eq, kernelBC_eq]
  rw [Finset.sum_congr rfl hcongr]
  exact (legendre_row_identity (xVar * yVar) ((1 - xVar) * (1 - yVar)) n).symm

/-- **(2)** The double-source kernel value formula: the bivariate moment functional of the
Legendre kernel coefficient is the Bernstein coefficient purity. -/
theorem bivariateMomentFunctional_legendreKernelCoeff (m : ℕ → ℝ) (n : ℕ) :
    bivariateMomentFunctional m (legendreKernelCoeff n) = bernsteinCoefficientPurity m n := by
  rw [← bernsteinRowKernel_eq_legendreKernelCoeff, bivariateMomentFunctional_bernsteinRowKernel]

/-! ### The kernel as a value function, its reflections and its conjugate factorization -/

variable {R : Type*} [CommRing R]

/-- `A(x,y) = 1 - x - y + 2xy`. -/
def kernelAOf (x y : R) : R := 1 - x - y + 2 * (x * y)

/-- `D(x,y) = 1 - x - y`. -/
def kernelDOf (x y : R) : R := 1 - x - y

/-- `b(x,y)c(x,y) = x(1-y)(1-x)y`. -/
def kernelBCOf (x y : R) : R := (x * (1 - y)) * ((1 - x) * y)

/-- The `t^n` coefficient of the Legendre double-source kernel, as a value. -/
def legendreKernelCoeffOf (n : ℕ) (x y : R) : R :=
  ∑ k ∈ Finset.range (n + 1),
    (if 2 * k ≤ n then ((n.choose (2*k) * (2*k).choose k : ℕ) : R)
      * (kernelAOf x y) ^ (n - 2*k) * (kernelBCOf x y) ^ k else 0)

/-- The Bernstein row kernel as a value. -/
def bernsteinRowKernelOf (n : ℕ) (x y : R) : R :=
  ∑ i ∈ Finset.range (n + 1), ((n.choose i ^ (2 : ℕ) : ℕ) : R)
    * (x * y) ^ i * ((1 - x) * (1 - y)) ^ (n - i)

/-- **(6)** at the level of values. -/
theorem bernsteinRowKernelOf_eq (n : ℕ) (x y : R) :
    bernsteinRowKernelOf n x y = legendreKernelCoeffOf n x y := by
  rw [bernsteinRowKernelOf, legendreKernelCoeffOf]
  have hA : ∀ k ∈ Finset.range (n + 1),
      (if 2 * k ≤ n then ((n.choose (2*k) * (2*k).choose k : ℕ) : R)
        * (kernelAOf x y) ^ (n - 2*k) * (kernelBCOf x y) ^ k else 0)
      = (if 2 * k ≤ n then ((n.choose (2*k) * (2*k).choose k : ℕ) : R)
        * ((x * y) + (1 - x) * (1 - y)) ^ (n - 2*k)
        * ((x * y) * ((1 - x) * (1 - y))) ^ k else 0) := by
    intro k _
    have h1 : kernelAOf x y = (x * y) + (1 - x) * (1 - y) := by rw [kernelAOf]; ring
    have h2 : kernelBCOf x y = (x * y) * ((1 - x) * (1 - y)) := by rw [kernelBCOf]; ring
    rw [h1, h2]
  rw [Finset.sum_congr rfl hA]
  exact (legendre_row_identity (x * y) ((1 - x) * (1 - y)) n).symm

/-- **(7)** `A² - 4bc = D²`. -/
theorem kernelA_sq_sub (x y : R) :
    (kernelAOf x y) ^ (2 : ℕ) - 4 * kernelBCOf x y = (kernelDOf x y) ^ (2 : ℕ) := by
  rw [kernelAOf, kernelBCOf, kernelDOf]; ring

/-- **(8)** The kernel is symmetric in its two sources. -/
theorem legendreKernelCoeffOf_symm (n : ℕ) (x y : R) :
    legendreKernelCoeffOf n x y = legendreKernelCoeffOf n y x := by
  rw [legendreKernelCoeffOf, legendreKernelCoeffOf]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : kernelAOf x y = kernelAOf y x := by rw [kernelAOf, kernelAOf]; ring
  have h2 : kernelBCOf x y = kernelBCOf y x := by rw [kernelBCOf, kernelBCOf]; ring
  rw [h1, h2]

/-- **(8)** The kernel is invariant under simultaneous complement reflection. -/
theorem legendreKernelCoeffOf_compl (n : ℕ) (x y : R) :
    legendreKernelCoeffOf n x y = legendreKernelCoeffOf n (1 - x) (1 - y) := by
  rw [legendreKernelCoeffOf, legendreKernelCoeffOf]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : kernelAOf x y = kernelAOf (1 - x) (1 - y) := by rw [kernelAOf, kernelAOf]; ring
  have h2 : kernelBCOf x y = kernelBCOf (1 - x) (1 - y) := by rw [kernelBCOf, kernelBCOf]; ring
  rw [h1, h2]

theorem kernelDOf_compl (x y : R) : kernelDOf (1 - x) (1 - y) = -(kernelDOf x y) := by
  rw [kernelDOf, kernelDOf]; ring

/-! ### The conjugate reflected specialization -/

theorem kernelAOf_conj (u : ℂ) :
    kernelAOf u ((starRingEnd ℂ) u) = ((‖u‖ ^ (2 : ℕ) + ‖1 - u‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  have h1 : u * (starRingEnd ℂ) u = ((Complex.normSq u : ℝ) : ℂ) := Complex.mul_conj u
  have h2 : u + (starRingEnd ℂ) u = ((2 * u.re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
  have h3 : ‖u‖ ^ (2 : ℕ) = Complex.normSq u := Complex.sq_norm u
  have h4 : ‖1 - u‖ ^ (2 : ℕ) = Complex.normSq (1 - u) := Complex.sq_norm (1 - u)
  have h5 : Complex.normSq (1 - u) = 1 - 2 * u.re + Complex.normSq u := by
    simp [Complex.normSq_apply]
    ring
  rw [kernelAOf, h3, h4, h5]
  push_cast
  rw [show (1 : ℂ) - u - (starRingEnd ℂ) u + 2 * (u * (starRingEnd ℂ) u)
      = 1 - (u + (starRingEnd ℂ) u) + 2 * (u * (starRingEnd ℂ) u) by ring, h1, h2]
  push_cast
  ring

theorem kernelDOf_conj_sq (u : ℂ) :
    (kernelDOf u ((starRingEnd ℂ) u)) ^ (2 : ℕ) = (((‖u‖ ^ (2 : ℕ) - ‖1 - u‖ ^ (2 : ℕ)) ^ (2 : ℕ) : ℝ) : ℂ) := by
  have h2 : u + (starRingEnd ℂ) u = ((2 * u.re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
  have h3 : ‖u‖ ^ (2 : ℕ) = Complex.normSq u := Complex.sq_norm u
  have h4 : ‖1 - u‖ ^ (2 : ℕ) = Complex.normSq (1 - u) := Complex.sq_norm (1 - u)
  have h5 : Complex.normSq (1 - u) = 1 - 2 * u.re + Complex.normSq u := by
    simp [Complex.normSq_apply]
    ring
  rw [kernelDOf, h3, h4, h5]
  rw [show (1 : ℂ) - u - (starRingEnd ℂ) u = 1 - (u + (starRingEnd ℂ) u) by ring, h2]
  push_cast
  ring

/-- `B₊(u) = ‖u‖ + ‖1-u‖`. -/
def reflectedAmplitudePlus (u : ℂ) : ℝ := ‖u‖ + ‖1 - u‖

/-- `B₋(u) = ‖u‖ - ‖1-u‖`. -/
def reflectedAmplitudeMinus (u : ℂ) : ℝ := ‖u‖ - ‖1 - u‖

/-- **(9)** The exact conjugate-reflected factorization of the quadratic under the radical. -/
theorem reflected_quadratic_factorization (u : ℂ) (t : ℝ) :
    1 - 2 * t * (‖u‖ ^ (2 : ℕ) + ‖1 - u‖ ^ (2 : ℕ)) + t ^ (2 : ℕ) * ((‖u‖ ^ (2 : ℕ) - ‖1 - u‖ ^ (2 : ℕ)) ^ (2 : ℕ))
      = (1 - reflectedAmplitudePlus u ^ (2 : ℕ) * t) * (1 - reflectedAmplitudeMinus u ^ (2 : ℕ) * t) := by
  rw [reflectedAmplitudePlus, reflectedAmplitudeMinus]
  ring

/-- **(10)** The first positive branch point of the reflected atom kernel is `B₊(u)^{-2}`. -/
theorem reflected_quadratic_pos_of_lt (u : ℂ) (hB : 0 < reflectedAmplitudePlus u) {t : ℝ}
    (ht0 : 0 ≤ t) (htB : t < 1 / reflectedAmplitudePlus u ^ (2 : ℕ)) :
    0 < 1 - 2 * t * (‖u‖ ^ (2 : ℕ) + ‖1 - u‖ ^ (2 : ℕ)) + t ^ (2 : ℕ) * ((‖u‖ ^ (2 : ℕ) - ‖1 - u‖ ^ (2 : ℕ)) ^ (2 : ℕ)) := by
  rw [reflected_quadratic_factorization]
  have hBsq : 0 < reflectedAmplitudePlus u ^ (2 : ℕ) := by positivity
  have h1 : reflectedAmplitudePlus u ^ (2 : ℕ) * t < 1 := by
    have := (lt_div_iff₀ hBsq).mp htB
    linarith [this]
  have hmono : reflectedAmplitudeMinus u ^ (2 : ℕ) ≤ reflectedAmplitudePlus u ^ (2 : ℕ) := by
    rw [reflectedAmplitudePlus, reflectedAmplitudeMinus]
    nlinarith [norm_nonneg u, norm_nonneg (1 - u)]
  have h2 : reflectedAmplitudeMinus u ^ (2 : ℕ) * t < 1 := by
    have := mul_le_mul_of_nonneg_right hmono ht0
    linarith
  have hp1 : 0 < 1 - reflectedAmplitudePlus u ^ (2 : ℕ) * t := by linarith
  have hp2 : 0 < 1 - reflectedAmplitudeMinus u ^ (2 : ℕ) * t := by linarith
  positivity

/-- **(10)** and the branch point is attained. -/
theorem reflected_quadratic_eq_zero (u : ℂ) (hB : 0 < reflectedAmplitudePlus u) :
    1 - 2 * (1 / reflectedAmplitudePlus u ^ (2 : ℕ)) * (‖u‖ ^ (2 : ℕ) + ‖1 - u‖ ^ (2 : ℕ))
        + (1 / reflectedAmplitudePlus u ^ (2 : ℕ)) ^ (2 : ℕ) * ((‖u‖ ^ (2 : ℕ) - ‖1 - u‖ ^ (2 : ℕ)) ^ (2 : ℕ)) = 0 := by
  rw [reflected_quadratic_factorization]
  have hBsq : (reflectedAmplitudePlus u : ℝ) ^ (2 : ℕ) ≠ 0 := by positivity
  rw [show reflectedAmplitudePlus u ^ (2 : ℕ) * (1 / reflectedAmplitudePlus u ^ (2 : ℕ)) = 1 by
    field_simp]
  ring

/-! ### The prime--Gamma specialization and the exact-radius splice -/

/-- **(2) for the endpoint source.**  The complete Abel susceptibility coefficient is an
unconditional double source evaluation of the Legendre kernel. -/
theorem bivariateMomentFunctional_legendreKernelCoeff_primeArch (n : ℕ) :
    bivariateMomentFunctional
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment)
        (legendreKernelCoeff n)
      = primeArchEndpointBernsteinPurity n :=
  bivariateMomentFunctional_legendreKernelCoeff _ n

theorem reflectedAmplitudePlus_eq_atomAmplitudeBase (q : XiZeroCopy) :
    reflectedAmplitudePlus (xiEndpointNormalizedReciprocalSquare q)
      = xiEndpointBernsteinAtomAmplitudeBase q := rfl

/-- **The exact-radius splice.**  Under false RH the Abel critical radius is exactly the first
reflected-kernel branch point of a maximizing endpoint divisor atom. -/
theorem abelCriticalRadius_eq_reflectedPinch_of_not_rh (hRH : ¬ RiemannHypothesis) :
    ∃ (B : ℝ) (q : XiZeroCopy),
      xiEndpointBernsteinAtomAmplitudeBase q = B ∧
      reflectedAmplitudePlus (xiEndpointNormalizedReciprocalSquare q) = B ∧
      PrimeArchEndpointBernsteinAttainedExactThreshold B ∧
      PrimeArchEndpointBernsteinAbelCriticalRadius (1 / B ^ (2 : ℕ)) ∧
      (1 - 2 * (1 / B ^ (2 : ℕ))
          * (‖xiEndpointNormalizedReciprocalSquare q‖ ^ (2 : ℕ)
            + ‖1 - xiEndpointNormalizedReciprocalSquare q‖ ^ (2 : ℕ))
        + (1 / B ^ (2 : ℕ)) ^ (2 : ℕ)
          * ((‖xiEndpointNormalizedReciprocalSquare q‖ ^ (2 : ℕ)
            - ‖1 - xiEndpointNormalizedReciprocalSquare q‖ ^ (2 : ℕ)) ^ (2 : ℕ)) = 0) := by
  obtain ⟨B, hthr, hrad⟩ :=
    exists_attained_primeArchEndpointBernsteinAbelCriticalRadius_of_not_rh hRH
  obtain ⟨hB1, hB2, ⟨q, hq⟩, hB4, hB5⟩ := id hthr
  have hBamp : reflectedAmplitudePlus (xiEndpointNormalizedReciprocalSquare q) = B := by
    rw [reflectedAmplitudePlus_eq_atomAmplitudeBase, hq]
  have hBpos : 0 < reflectedAmplitudePlus (xiEndpointNormalizedReciprocalSquare q) := by
    rw [hBamp]; linarith
  refine ⟨B, q, hq, hBamp, hthr, hrad, ?_⟩
  have h := reflected_quadratic_eq_zero (xiEndpointNormalizedReciprocalSquare q) hBpos
  rwa [hBamp] at h

end

end RHTower
