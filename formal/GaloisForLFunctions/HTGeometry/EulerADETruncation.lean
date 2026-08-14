import GaloisForLFunctions.HTGeometry.EulerADELinearization
import GaloisForLFunctions.HTGeometry.FormalAnalyticADE

/-!
# Truncating a formal solution

Linearizing an algebraic differential equation along a formal solution produces coefficients that
are only formal.  Linearizing along a **truncation** of it produces polynomials, hence convergent
coefficients, and the error committed is divisible by a high power of the variable.

Three facts make the reduction work, for a solution `F` truncated at order `N`:

* the truncation is a polynomial, so it and all its `θ`-jets are convergent;
* the tail is divisible by `t^{N+1}`, so the Taylor defect is divisible by `t^{2N+2}`;
* the value of the equation at the truncation is itself divisible by `t^{N+1}`, because it equals
  minus the linearized term and the defect, both of which are.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The truncation of a formal series -/

/-- The truncation of a formal series at order `N`, as a formal series. -/
def truncSeries (N : ℕ) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => if n ≤ N then PowerSeries.coeff n F else 0

@[simp] theorem coeff_truncSeries (N : ℕ) (F : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (truncSeries N F)
      = if n ≤ N then PowerSeries.coeff n F else 0 :=
  PowerSeries.coeff_mk _ _

/-- A truncation is convergent. -/
theorem isGevreySeries_zero_truncSeries (N : ℕ) (F : PowerSeries ℂ) :
    IsGevreySeries 0 (truncSeries N F) := by
  classical
  refine ⟨1 + ∑ k ∈ Finset.range (N + 1), ‖PowerSeries.coeff k F‖, 1, by positivity, one_pos,
    fun n => ?_⟩
  have hsum0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (N + 1), ‖PowerSeries.coeff k F‖ :=
    Finset.sum_nonneg fun k _ => norm_nonneg _
  rw [coeff_truncSeries]
  by_cases hn : n ≤ N
  · rw [if_pos hn]
    have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hle : ‖PowerSeries.coeff n F‖ ≤ ∑ k ∈ Finset.range (N + 1), ‖PowerSeries.coeff k F‖ :=
      Finset.single_le_sum (f := fun k : ℕ => ‖PowerSeries.coeff k F‖)
        (fun k _ => norm_nonneg _) hmem
    simp only [one_pow, mul_one, Real.rpow_zero]
    linarith
  · rw [if_neg hn, norm_zero]
    simp only [one_pow, mul_one, Real.rpow_zero]
    linarith

/-- The tail of a truncation is divisible by the corresponding power of the variable. -/
theorem X_pow_dvd_sub_truncSeries (N : ℕ) (F : PowerSeries ℂ) :
    (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ F - truncSeries N F := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro n hn
  rw [map_sub, coeff_truncSeries, if_pos (by omega : n ≤ N), sub_self]

theorem truncSeries_add_tail (N : ℕ) (F : PowerSeries ℂ) :
    truncSeries N F + (F - truncSeries N F) = F := by ring

/-! ### Convergence of the linearization at a truncation -/

theorem isGevreySeries_eulerOp_iterate {r : ℝ} {F : PowerSeries ℂ} (hF : IsGevreySeries r F) :
    ∀ j : ℕ, IsGevreySeries r ((GaloisForLFunctions.HTGeometry.eulerOp)^[j] F)
  | 0 => by simpa using hF
  | (j + 1) => by
      rw [Function.iterate_succ_apply']
      exact IsGevreySeries.eulerOp (isGevreySeries_eulerOp_iterate hF j)

/-- **A differential polynomial with analytic coefficients does not leave the Gevrey class of its
argument**, in the Euler basis. -/
theorem isGevreySeries_aeval_eulerJetVector {r : ℝ} (hr : 0 ≤ r) {m : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (hP : IsAnalyticDifferentialPolynomial P)
    {Y : PowerSeries ℂ} (hY : IsGevreySeries r Y) :
    IsGevreySeries r (MvPolynomial.aeval (eulerJetVector (m := m) Y) P) := by
  classical
  have hjet : ∀ j : Fin (m + 1), IsGevreySeries r (eulerJetVector (m := m) Y j) :=
    fun j => isGevreySeries_eulerOp_iterate hY (j : ℕ)
  have hEval : MvPolynomial.aeval (eulerJetVector (m := m) Y) P
      = ∑ d ∈ P.support, MvPolynomial.coeff d P
        * ∏ i ∈ d.support, eulerJetVector (m := m) Y i ^ d i := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    simp
  rw [hEval]
  refine isGevreySeries_finsetSum _ _ fun d _ => ?_
  refine IsGevreySeries.mul hr ((hP d).mono hr) ?_
  exact isGevreySeries_finsetProd hr _ _ fun i _ => (hjet i).pow hr _

/-- The partial derivatives of an analytic differential polynomial are analytic. -/
theorem isAnalyticDifferentialPolynomial_pderiv {m : ℕ}
    {P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ)} (hP : IsAnalyticDifferentialPolynomial P)
    (j : Fin (m + 1)) : IsAnalyticDifferentialPolynomial (MvPolynomial.pderiv j P) := by
  classical
  intro σ
  have hCnat : (((σ j + 1 : ℕ) : ℂ⟦X⟧)) = PowerSeries.C (((σ j + 1 : ℕ) : ℂ)) :=
    (map_natCast (PowerSeries.C : ℂ →+* ℂ⟦X⟧) (σ j + 1)).symm
  have hform : MvPolynomial.coeff σ (MvPolynomial.pderiv j P)
      = PowerSeries.C (((σ j + 1 : ℕ) : ℂ)) * MvPolynomial.coeff (σ + Finsupp.single j 1) P := by
    rw [MvPolynomial.coeff_pderiv, ← hCnat]
    push_cast
    ring
  obtain ⟨C, A, hC, hA, hbound⟩ := hP (σ + Finsupp.single j 1)
  refine ⟨((σ j + 1 : ℕ) : ℝ) * C + 1, A, by positivity, hA, fun n => ?_⟩
  have hnorm : ‖PowerSeries.coeff n (MvPolynomial.coeff σ (MvPolynomial.pderiv j P))‖
      = ((σ j + 1 : ℕ) : ℝ)
        * ‖PowerSeries.coeff n (MvPolynomial.coeff (σ + Finsupp.single j 1) P)‖ := by
    rw [hform, PowerSeries.coeff_C_mul, norm_mul, Complex.norm_natCast]
  rw [hnorm]
  have hb := hbound n
  have hnn : (0 : ℝ) ≤ ((σ j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpos : (0 : ℝ) < A ^ n * (Nat.factorial n : ℝ) ^ (0 : ℝ) := by
    simp only [Real.rpow_zero, mul_one]
    exact pow_pos hA n
  nlinarith [hb, hnn, hpos]

/-- **The linearization at a truncation has convergent coefficients.** -/
theorem isGevreySeries_zero_linearizationCoeff {m N : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ)) (hP : IsAnalyticDifferentialPolynomial P)
    (F : PowerSeries ℂ) (j : Fin (m + 1)) :
    IsGevreySeries 0 (linearizationCoeff P (truncSeries N F) j) :=
  isGevreySeries_aeval_eulerJetVector le_rfl _ (isAnalyticDifferentialPolynomial_pderiv hP j)
    (isGevreySeries_zero_truncSeries N F)

/-- **The value of the equation at a truncation is convergent.** -/
theorem isGevreySeries_zero_aeval_truncSeries {m N : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ)) (hP : IsAnalyticDifferentialPolynomial P)
    (F : PowerSeries ℂ) :
    IsGevreySeries 0 (MvPolynomial.aeval (eulerJetVector (m := m) (truncSeries N F)) P) :=
  isGevreySeries_aeval_eulerJetVector le_rfl P hP (isGevreySeries_zero_truncSeries N F)

/-- **The value of the equation at a truncation of a solution vanishes to the order of the
truncation.** -/
theorem X_pow_dvd_aeval_truncSeries {m N : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ)) {F : PowerSeries ℂ}
    (hsol : IsFormalEulerADESolution P F) :
    (PowerSeries.X : PowerSeries ℂ) ^ (N + 1)
      ∣ MvPolynomial.aeval (eulerJetVector (m := m) (truncSeries N F)) P := by
  classical
  set Y : PowerSeries ℂ := truncSeries N F with hY
  set H : PowerSeries ℂ := F - truncSeries N F with hH
  have hYH : Y + H = F := by rw [hY, hH]; ring
  have hdvdH : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ H := X_pow_dvd_sub_truncSeries N F
  have hsol' : IsFormalEulerADESolution P (Y + H) := by rw [hYH]; exact hsol
  have heq := eulerLinearOp_linearization_eq P Y H hsol'
  -- the linearized term is divisible
  have hlin : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1)
      ∣ eulerLinearOp (linearizationCoeff P Y) H := by
    rw [eulerLinearOp]
    refine Finset.dvd_sum fun j _ => ?_
    exact Dvd.dvd.mul_left (X_pow_dvd_eulerOp_iterate (j : ℕ) hdvdH) _
  -- and so is the defect
  have hdef : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1)
      ∣ taylorDefect (eulerJetVector (m := m) Y) (eulerJetVector (m := m) H) P := by
    have hmem := taylorDefect_mem_sq_X_pow (k := N + 1) P Y H hdvdH
    have hsub : (Ideal.span {(PowerSeries.X : PowerSeries ℂ) ^ (N + 1)}) ^ 2
        ≤ Ideal.span {(PowerSeries.X : PowerSeries ℂ) ^ (N + 1)} :=
      Ideal.pow_le_self (by norm_num)
    have := hsub hmem
    rwa [Ideal.mem_span_singleton] at this
  have hval : MvPolynomial.aeval (eulerJetVector (m := m) Y) P
      = -(eulerLinearOp (linearizationCoeff P Y) H)
        - taylorDefect (eulerJetVector (m := m) Y) (eulerJetVector (m := m) H) P := by
    linear_combination heq
  rw [hval]
  exact dvd_sub (dvd_neg.mpr hlin) hdef

end

end GaloisForLFunctions.HTGeometry
