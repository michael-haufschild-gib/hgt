import GaloisForLFunctions.HTGeometry.GevreyFormalSeries
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Linear differential operators in Euler form and their shift polynomials

Write `θ = t d/dt` for the Euler operator on formal power series.  It is diagonal on monomials,
`θ (t^n) = n t^n`, so a linear differential operator

```text
L = ∑_{j ≤ m} B_j θ^j ,   B_j ∈ ℂ[[t]] ,
```

acts on coefficients by a single convolution: the coefficient of `t^n` in `L F` is

```text
∑_{k ≤ n} Φ_{n-k}(k) · f_k ,      Φ_μ(N) = ∑_{j ≤ m} (coeff_μ B_j) N^j .
```

The polynomials `Φ_μ` are the *shift polynomials* of `L`.  They carry the whole Newton polygon: the
pairs `(deg Φ_μ, μ)` are lattice points, so every slope of the polygon is a ratio of integers.  The
displayed formula is also the recursion that governs the growth of a formal solution, since its
`k = n` term is `Φ_0(n) f_n`.
-/

open PowerSeries
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### The Euler operator -/

/-- The Euler operator `θ = t d/dt`, diagonal on monomials. -/
noncomputable def formalEulerOp (F : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (n : ℂ) * PowerSeries.coeff n F

@[simp] theorem coeff_formalEulerOp (F : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (formalEulerOp F) = (n : ℂ) * PowerSeries.coeff n F :=
  PowerSeries.coeff_mk _ _

/-- Every power of the Euler operator is diagonal. -/
theorem coeff_formalEulerOp_iterate (F : PowerSeries ℂ) (j n : ℕ) :
    PowerSeries.coeff n (formalEulerOp^[j] F) = (n : ℂ) ^ j * PowerSeries.coeff n F := by
  induction j generalizing F with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply, ih, coeff_formalEulerOp]
      ring

/-- The Euler operator preserves the Gevrey classes. -/
theorem IsGevreySeries.formalEulerOp {r : ℝ} {F : PowerSeries ℂ} (hF : IsGevreySeries r F) :
    IsGevreySeries r (GaloisForLFunctions.HTGeometry.formalEulerOp F) := by
  obtain ⟨C, A, hC, hA, hbound⟩ := hF
  obtain ⟨C₃, hC₃1, hC₃⟩ :=
    exists_pow_le_const_mul_pow 1 (by norm_num : (1 : ℝ) < 2)
  refine ⟨C * C₃, 2 * A, by positivity, by positivity, fun n => ?_⟩
  have hn : ‖((n : ℂ))‖ = (n : ℝ) := by
    rw [show ((n : ℂ)) = (((n : ℝ) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  have hpoly : (n : ℝ) ≤ C₃ * 2 ^ n := by
    have h := hC₃ n
    simpa using h
  calc ‖PowerSeries.coeff n (GaloisForLFunctions.HTGeometry.formalEulerOp F)‖
      = (n : ℝ) * ‖PowerSeries.coeff n F‖ := by
        rw [coeff_formalEulerOp, norm_mul, hn]
    _ ≤ (C₃ * 2 ^ n) * (C * A ^ n * (n ! : ℝ) ^ r) := by
        refine mul_le_mul hpoly (hbound n) (norm_nonneg _) (by positivity)
    _ = C * C₃ * (2 * A) ^ n * (n ! : ℝ) ^ r := by
        rw [mul_pow]
        ring

/-! ### Linear operators and their shift polynomials -/

/-- A linear differential operator of order at most `m`, written in the Euler basis. -/
noncomputable def eulerLinearOp {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ) (F : PowerSeries ℂ) :
    PowerSeries ℂ :=
  ∑ j : Fin (m + 1), B j * formalEulerOp^[(j : ℕ)] F

/-- The shift polynomial of `L` at shift `μ`: the polynomial `N ↦ ∑_j (coeff_μ B_j) N^j`. -/
noncomputable def shiftPolynomial {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ) (μ : ℕ) :
    Polynomial ℂ :=
  ∑ j : Fin (m + 1), Polynomial.C (PowerSeries.coeff μ (B j)) * Polynomial.X ^ (j : ℕ)

theorem eval_shiftPolynomial {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ) (μ : ℕ) (z : ℂ) :
    (shiftPolynomial B μ).eval z
      = ∑ j : Fin (m + 1), PowerSeries.coeff μ (B j) * z ^ (j : ℕ) := by
  rw [shiftPolynomial, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- The degree of a shift polynomial is at most the order of the operator. -/
theorem natDegree_shiftPolynomial_le {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ) (μ : ℕ) :
    (shiftPolynomial B μ).natDegree ≤ m := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  simp only [Polynomial.natDegree_C, zero_add]
  refine le_trans (Polynomial.natDegree_pow_le) ?_
  simp only [Polynomial.natDegree_X, mul_one]
  exact Nat.lt_succ_iff.mp j.isLt

/-! ### The coefficient recursion -/

/-- **The action of a linear operator on coefficients is a single convolution against its shift
polynomials.** -/
theorem coeff_eulerLinearOp {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ) (F : PowerSeries ℂ)
    (n : ℕ) :
    PowerSeries.coeff n (eulerLinearOp B F)
      = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          (shiftPolynomial B p.1).eval ((p.2 : ℕ) : ℂ) * PowerSeries.coeff p.2 F := by
  classical
  rw [eulerLinearOp, map_sum]
  have hswap : ∀ j : Fin (m + 1),
      PowerSeries.coeff n (B j * formalEulerOp^[(j : ℕ)] F)
        = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
            PowerSeries.coeff p.1 (B j) * (((p.2 : ℕ) : ℂ) ^ (j : ℕ) * PowerSeries.coeff p.2 F) := by
    intro j
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [coeff_formalEulerOp_iterate]
  rw [Finset.sum_congr rfl fun j _ => hswap j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [eval_shiftPolynomial, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The same convolution, indexed by the coefficient level. -/
theorem coeff_eulerLinearOp_range {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ) (F : PowerSeries ℂ)
    (n : ℕ) :
    PowerSeries.coeff n (eulerLinearOp B F)
      = ∑ k ∈ Finset.range (n + 1),
          (shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k F := by
  classical
  rw [coeff_eulerLinearOp]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (fun p : ℕ × ℕ => (shiftPolynomial B p.1).eval ((p.2 : ℕ) : ℂ) * PowerSeries.coeff p.2 F) n]
  have hrefl := Finset.sum_range_reflect
    (fun k : ℕ => (shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k F) (n + 1)
  rw [← hrefl]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : n + 1 - 1 - k = n - k := by omega
  have h2 : n - (n - k) = k := by omega
  rw [h1, h2]

/-- **The recursion satisfied by the coefficients.**  The top term of the convolution isolates the
`n`-th coefficient against the shift polynomial at shift zero. -/
theorem shiftPolynomial_zero_mul_coeff {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ)
    (F : PowerSeries ℂ) (n : ℕ) :
    (shiftPolynomial B 0).eval ((n : ℕ) : ℂ) * PowerSeries.coeff n F
      = PowerSeries.coeff n (eulerLinearOp B F)
        - ∑ k ∈ Finset.range n,
            (shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k F := by
  have h := coeff_eulerLinearOp_range B F n
  rw [Finset.sum_range_succ, Nat.sub_self] at h
  linear_combination -h

end GaloisForLFunctions.HTGeometry
