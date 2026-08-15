import GaloisForLFunctions.HTGeometry.EulerShiftOperatorAlgebra
import GaloisForLFunctions.HTGeometry.ShiftPolynomialBounds

/-!
# The shift polynomials of a convergent operator, weighted by their own degree

The bound `‖Φ_μ(k)‖ ≤ C ρ^μ (k+1)^m` charges every shift the full order `m` of the operator.  That
is too crude for a Newton-polygon comparison: what decides which shift dominates a coefficient
recursion is the **weighted level** `deg Φ_μ − s μ`, so the estimate has to see the actual degree of
each shift polynomial.

It does, and for the same reason: the value of a polynomial at a nonnegative integer is bounded by
the number of its coefficients times their common bound times `(k+1)` to its own degree.  Combined
with the geometric decay of the coefficients of a convergent series this gives

```text
‖Φ_μ(k)‖ ≤ C ρ^μ (k+1)^{deg Φ_μ} .
```
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

/-- **The shift polynomials of a convergent operator are bounded by their own degree.** -/
theorem exists_bound_shiftPolynomial_natDegree {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ)
    (hB : ∀ j, IsGevreySeries 0 (B j)) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ∀ (μ k : ℕ),
      ‖(shiftPolynomial B μ).eval ((k : ℕ) : ℂ)‖
        ≤ C * ρ ^ μ * ((k : ℝ) + 1) ^ (shiftPolynomial B μ).natDegree := by
  classical
  choose C A hC hA hbound using hB
  set Cmax : ℝ := ∑ j : Fin (m + 1), C j with hCmax
  set ρ : ℝ := (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty A with hρ
  have hρpos : 0 < ρ := by
    obtain ⟨j⟩ : Nonempty (Fin (m + 1)) := ⟨⟨0, Nat.succ_pos m⟩⟩
    exact lt_of_lt_of_le (hA j) (Finset.le_sup' A (Finset.mem_univ j))
  have hAle : ∀ j, A j ≤ ρ := fun j => Finset.le_sup' A (Finset.mem_univ j)
  have hCmax0 : (0 : ℝ) ≤ Cmax := Finset.sum_nonneg fun j _ => le_of_lt (hC j)
  have hCpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) * (Cmax + 1) := by
    have h1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    nlinarith [hCmax0]
  refine ⟨((m + 1 : ℕ) : ℝ) * (Cmax + 1), ρ, hCpos, hρpos, fun μ k => ?_⟩
  have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  set d : ℕ := (shiftPolynomial B μ).natDegree with hd
  have hdm : d ≤ m := natDegree_shiftPolynomial_le B μ
  -- every coefficient of a shift polynomial is a coefficient of one of the operator's terms
  have hcoeff : ∀ i : ℕ, i ≤ m →
      ‖(shiftPolynomial B μ).coeff i‖ ≤ (Cmax + 1) * ρ ^ μ := by
    intro i hi
    set j : Fin (m + 1) := ⟨i, Nat.lt_succ_of_le hi⟩ with hj
    have hji : ((j : ℕ)) = i := rfl
    have heq : (shiftPolynomial B μ).coeff i = PowerSeries.coeff μ (B j) := by
      rw [← hji, coeff_shiftPolynomial B μ j]
    have h1 : ‖PowerSeries.coeff μ (B j)‖ ≤ C j * A j ^ μ := by
      have := hbound j μ
      simpa using this
    have hCj : C j ≤ Cmax := by
      rw [hCmax]
      exact Finset.single_le_sum (f := fun i : Fin (m + 1) => C i)
        (fun i _ => le_of_lt (hC i)) (Finset.mem_univ j)
    have hAρ : A j ^ μ ≤ ρ ^ μ := pow_le_pow_left₀ (le_of_lt (hA j)) (hAle j) μ
    calc ‖(shiftPolynomial B μ).coeff i‖ = ‖PowerSeries.coeff μ (B j)‖ := by rw [heq]
      _ ≤ C j * A j ^ μ := h1
      _ ≤ (Cmax + 1) * ρ ^ μ := by
          refine mul_le_mul (by linarith) hAρ (le_of_lt (pow_pos (hA j) μ)) (by linarith)
  have hterm : ∀ i ∈ Finset.range (d + 1),
      ‖(shiftPolynomial B μ).coeff i * ((k : ℕ) : ℂ) ^ i‖
        ≤ (Cmax + 1) * ρ ^ μ * ((k : ℝ) + 1) ^ d := by
    intro i hi
    have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    refine mul_le_mul (hcoeff i (le_trans hid hdm)) ?_ (by positivity) (by positivity)
    calc (k : ℝ) ^ i ≤ ((k : ℝ) + 1) ^ i := pow_le_pow_left₀ hknn (by linarith) _
      _ ≤ ((k : ℝ) + 1) ^ d := pow_le_pow_right₀ (by linarith) hid
  calc ‖(shiftPolynomial B μ).eval ((k : ℕ) : ℂ)‖
      = ‖∑ i ∈ Finset.range (d + 1), (shiftPolynomial B μ).coeff i * ((k : ℕ) : ℂ) ^ i‖ := by
        rw [Polynomial.eval_eq_sum_range, ← hd]
    _ ≤ ∑ i ∈ Finset.range (d + 1),
          ‖(shiftPolynomial B μ).coeff i * ((k : ℕ) : ℂ) ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (d + 1), (Cmax + 1) * ρ ^ μ * ((k : ℝ) + 1) ^ d :=
        Finset.sum_le_sum hterm
    _ = ((d : ℝ) + 1) * ((Cmax + 1) * ρ ^ μ * ((k : ℝ) + 1) ^ d) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ((m + 1 : ℕ) : ℝ) * (Cmax + 1) * ρ ^ μ * ((k : ℝ) + 1) ^ d := by
        have hdle : ((d : ℝ) + 1) ≤ ((m + 1 : ℕ) : ℝ) := by
          have : (d : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hdm
          push_cast
          linarith
        have hrest : (0 : ℝ) ≤ (Cmax + 1) * ρ ^ μ * ((k : ℝ) + 1) ^ d := by positivity
        nlinarith [hrest, hdle]

end GaloisForLFunctions.HTGeometry
