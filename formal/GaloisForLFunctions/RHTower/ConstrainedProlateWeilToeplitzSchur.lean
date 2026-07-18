import GaloisForLFunctions.RHTower.RadialLeakageArcsineMeasure

/-!
# The adjacent regular-Weil Toeplitz moment and its Schur survivor

For the fixed-mode constrained-prolate exterior tails, the paper cross-mode calculation produces
the first two Toeplitz moments

```text
D₀ = (1/π) ∑_{k≥1} arcsin(1/k)/k,
D₁ = (1/π) ∑_{k≥2} (k²-2)√(k²-1)/k⁵.
```

This file formalizes the concrete adjacent coefficient and the exact two-channel Schur correction.
It proves `0 < D₁ < D₀`, the stronger floor `1/2 ≤ D₀-D₁`, and therefore

```text
1/2 < D₀-D₁²/D₀.
```

The last inequality is the first non-diagonal positive survivor of the regular Weil--prolate
comparison.  The analytic assertion that the true exterior pairings converge to these constants,
and the intact polar--prime critical-Mellin graph estimate needed for the full closed Weil form,
remain paper-level inputs; no such input is assumed here.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The `k=n+1` contribution to the diagonal Toeplitz moment `D₀`. -/
def constrainedProlateWeilToeplitzZeroTerm (n : ℕ) : ℝ :=
  let x : ℝ := 1 / ((n : ℝ) + 1)
  x * Real.arcsin x / Real.pi

/-- The `k=n+1` contribution to the adjacent Toeplitz moment `D₁`.

For `k≥2`, this is exactly
`(k²-2)√(k²-1)/(π k⁵)`; at `k=1` the expression vanishes. -/
def constrainedProlateWeilToeplitzAdjacentTerm (n : ℕ) : ℝ :=
  let x : ℝ := 1 / ((n : ℝ) + 1)
  x ^ 2 * (1 - 2 * x ^ 2) * Real.sqrt (1 - x ^ 2) / Real.pi

theorem constrainedProlateWeilToeplitzZeroTerm_eq_archTerm_div_pi (n : ℕ) :
    constrainedProlateWeilToeplitzZeroTerm n =
      GaloisForLFunctions.constrainedProlateArchSeriesTerm n / Real.pi := by
  unfold constrainedProlateWeilToeplitzZeroTerm
    GaloisForLFunctions.constrainedProlateArchSeriesTerm
  ring

theorem constrainedProlateWeilToeplitzZeroTerm_nonneg (n : ℕ) :
    0 ≤ constrainedProlateWeilToeplitzZeroTerm n := by
  rw [constrainedProlateWeilToeplitzZeroTerm_eq_archTerm_div_pi]
  exact div_nonneg
    (GaloisForLFunctions.constrainedProlateArchSeriesTerm_nonneg n)
    Real.pi_pos.le

theorem constrainedProlateWeilToeplitzAdjacentTerm_nonneg (n : ℕ) :
    0 ≤ constrainedProlateWeilToeplitzAdjacentTerm n := by
  rcases n with _ | n
  · simp [constrainedProlateWeilToeplitzAdjacentTerm]
  · let x : ℝ := 1 / (((n + 1 : ℕ) : ℝ) + 1)
    have hk : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      push_cast
      linarith
    have hx0 : 0 ≤ x := by positivity
    have hxhalf : x ≤ 1 / 2 := by
      dsimp [x]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (((n + 1 : ℕ) : ℝ) + 1))]
      nlinarith
    have hfactor : 0 ≤ 1 - 2 * x ^ 2 := by
      nlinarith [sq_nonneg x]
    change 0 ≤ x ^ 2 * (1 - 2 * x ^ 2) * Real.sqrt (1 - x ^ 2) / Real.pi
    positivity

/-- The adjacent cross moment is dominated by the diagonal moment term by term. -/
theorem constrainedProlateWeilToeplitzAdjacentTerm_le_zeroTerm (n : ℕ) :
    constrainedProlateWeilToeplitzAdjacentTerm n ≤
      constrainedProlateWeilToeplitzZeroTerm n := by
  rcases n with _ | n
  · simp [constrainedProlateWeilToeplitzAdjacentTerm,
      constrainedProlateWeilToeplitzZeroTerm, Real.arcsin_one]
    positivity
  · let x : ℝ := 1 / (((n + 1 : ℕ) : ℝ) + 1)
    have hk : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      push_cast
      linarith
    have hx0 : 0 ≤ x := by positivity
    have hxhalf : x ≤ 1 / 2 := by
      dsimp [x]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (((n + 1 : ℕ) : ℝ) + 1))]
      nlinarith
    have hx1 : x ≤ 1 := hxhalf.trans (by norm_num)
    have hxSq : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    have hinside0 : 0 ≤ 1 - x ^ 2 := by linarith
    have ha0 : 0 ≤ 1 - 2 * x ^ 2 := by nlinarith [sq_nonneg x]
    have ha1 : 1 - 2 * x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    have hb0 : 0 ≤ Real.sqrt (1 - x ^ 2) := Real.sqrt_nonneg _
    have hb1 : Real.sqrt (1 - x ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      nlinarith [sq_nonneg x]
    have hab : (1 - 2 * x ^ 2) * Real.sqrt (1 - x ^ 2) ≤ 1 := by
      calc
        (1 - 2 * x ^ 2) * Real.sqrt (1 - x ^ 2)
            ≤ 1 * Real.sqrt (1 - x ^ 2) :=
              mul_le_mul_of_nonneg_right ha1 hb0
        _ ≤ 1 := by simpa using hb1
    have hprod :
        x ^ 2 * (1 - 2 * x ^ 2) * Real.sqrt (1 - x ^ 2) ≤ x ^ 2 := by
      calc
        x ^ 2 * (1 - 2 * x ^ 2) * Real.sqrt (1 - x ^ 2) =
            x ^ 2 * ((1 - 2 * x ^ 2) * Real.sqrt (1 - x ^ 2)) := by ring
        _ ≤ x ^ 2 * 1 := mul_le_mul_of_nonneg_left hab (sq_nonneg x)
        _ = x ^ 2 := by ring
    have harc0 : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.mpr hx0
    have hxarc : x ≤ Real.arcsin x := by
      have hsin := Real.sin_le harc0
      rw [Real.sin_arcsin (by linarith) hx1] at hsin
      exact hsin
    have hdiag : x ^ 2 ≤ x * Real.arcsin x := by
      nlinarith
    change
      x ^ 2 * (1 - 2 * x ^ 2) * Real.sqrt (1 - x ^ 2) / Real.pi ≤
        x * Real.arcsin x / Real.pi
    exact div_le_div_of_nonneg_right (hprod.trans hdiag) Real.pi_pos.le

theorem summable_constrainedProlateWeilToeplitzZeroTerm :
    Summable constrainedProlateWeilToeplitzZeroTerm := by
  apply (GaloisForLFunctions.summable_constrainedProlateArchSeriesTerm.div_const
    Real.pi).congr
  intro n
  exact constrainedProlateWeilToeplitzZeroTerm_eq_archTerm_div_pi n |>.symm

theorem summable_constrainedProlateWeilToeplitzAdjacentTerm :
    Summable constrainedProlateWeilToeplitzAdjacentTerm := by
  exact summable_constrainedProlateWeilToeplitzZeroTerm.of_nonneg_of_le
    constrainedProlateWeilToeplitzAdjacentTerm_nonneg
    constrainedProlateWeilToeplitzAdjacentTerm_le_zeroTerm

/-- The diagonal regular-Weil Toeplitz moment. -/
def constrainedProlateWeilToeplitzD0 : ℝ :=
  ∑' n : ℕ, constrainedProlateWeilToeplitzZeroTerm n

/-- The first adjacent regular-Weil Toeplitz moment. -/
def constrainedProlateWeilToeplitzD1 : ℝ :=
  ∑' n : ℕ, constrainedProlateWeilToeplitzAdjacentTerm n

theorem constrainedProlateWeilToeplitzD0_pos :
    0 < constrainedProlateWeilToeplitzD0 := by
  unfold constrainedProlateWeilToeplitzD0
  refine summable_constrainedProlateWeilToeplitzZeroTerm.tsum_pos
    constrainedProlateWeilToeplitzZeroTerm_nonneg 0 ?_
  simp [constrainedProlateWeilToeplitzZeroTerm, Real.arcsin_one, Real.pi_pos]

theorem constrainedProlateWeilToeplitzD1_pos :
    0 < constrainedProlateWeilToeplitzD1 := by
  unfold constrainedProlateWeilToeplitzD1
  refine summable_constrainedProlateWeilToeplitzAdjacentTerm.tsum_pos
    constrainedProlateWeilToeplitzAdjacentTerm_nonneg 1 ?_
  norm_num [constrainedProlateWeilToeplitzAdjacentTerm]
  positivity

/-- The exact `k=1` half-identity slice remains after subtracting the adjacent moment. -/
theorem half_le_constrainedProlateWeilToeplitzD0_sub_D1 :
    (1 : ℝ) / 2 ≤
      constrainedProlateWeilToeplitzD0 - constrainedProlateWeilToeplitzD1 := by
  rw [constrainedProlateWeilToeplitzD0, constrainedProlateWeilToeplitzD1,
    ← summable_constrainedProlateWeilToeplitzZeroTerm.tsum_sub
      summable_constrainedProlateWeilToeplitzAdjacentTerm]
  have hsum :=
    (summable_constrainedProlateWeilToeplitzZeroTerm.sub
      summable_constrainedProlateWeilToeplitzAdjacentTerm).sum_le_tsum {0}
      (fun n _ => sub_nonneg.mpr
        (constrainedProlateWeilToeplitzAdjacentTerm_le_zeroTerm n))
  have hhalf : Real.pi / 2 / Real.pi = (1 : ℝ) / 2 := by
    field_simp [Real.pi_ne_zero]
  simpa [constrainedProlateWeilToeplitzZeroTerm,
    constrainedProlateWeilToeplitzAdjacentTerm, Real.arcsin_one,
    Real.pi_ne_zero, hhalf] using hsum

theorem constrainedProlateWeilToeplitzD1_lt_D0 :
    constrainedProlateWeilToeplitzD1 < constrainedProlateWeilToeplitzD0 := by
  linarith [half_le_constrainedProlateWeilToeplitzD0_sub_D1]

/-- **Concrete Schur survivor.**  Eliminating the adjacent Toeplitz channel retains more than one
half of the leading diagonal coefficient. -/
theorem constrainedProlateWeilToeplitzSchurCoefficient_gt_half :
    (1 : ℝ) / 2 <
      constrainedProlateWeilToeplitzD0 -
        constrainedProlateWeilToeplitzD1 ^ 2 / constrainedProlateWeilToeplitzD0 := by
  have hD0 := constrainedProlateWeilToeplitzD0_pos
  have hD1 := constrainedProlateWeilToeplitzD1_pos
  have hlt := constrainedProlateWeilToeplitzD1_lt_D0
  have hdiv :
      constrainedProlateWeilToeplitzD1 ^ 2 / constrainedProlateWeilToeplitzD0 <
        constrainedProlateWeilToeplitzD1 := by
    rw [div_lt_iff₀ hD0]
    nlinarith
  linarith [half_le_constrainedProlateWeilToeplitzD0_sub_D1]

/-- The leading two-channel regular-Weil quadratic form in source amplitudes `a₀,a₁`. -/
def constrainedProlateWeilTwoModeLeadingForm
    (D0 D1 a0 a1 x y : ℝ) : ℝ :=
  D0 * (a0 * x) ^ 2 + 2 * D1 * (a0 * x) * (a1 * y) + D0 * (a1 * y) ^ 2

/-- The unique adjacent-channel coefficient that cancels the second coordinate of the leading
Toeplitz block. -/
def constrainedProlateWeilTwoModeSchurCorrection
    (D0 D1 a0 a1 : ℝ) : ℝ :=
  -(D1 * a0) / (D0 * a1)

theorem constrainedProlateWeilTwoModeSchurCorrection_cancels
    {D0 D1 a0 a1 : ℝ} (hD0 : D0 ≠ 0) (ha1 : a1 ≠ 0) :
    D1 * a0 * a1 + D0 * a1 ^ 2 *
      constrainedProlateWeilTwoModeSchurCorrection D0 D1 a0 a1 = 0 := by
  unfold constrainedProlateWeilTwoModeSchurCorrection
  field_simp
  ring

/-- Exact Feshbach/Schur value of the corrected source vector. -/
theorem constrainedProlateWeilTwoModeLeadingForm_schurCorrection
    {D0 D1 a0 a1 : ℝ} (hD0 : D0 ≠ 0) (ha1 : a1 ≠ 0) :
    constrainedProlateWeilTwoModeLeadingForm D0 D1 a0 a1 1
        (constrainedProlateWeilTwoModeSchurCorrection D0 D1 a0 a1) =
      a0 ^ 2 * (D0 - D1 ^ 2 / D0) := by
  unfold constrainedProlateWeilTwoModeLeadingForm
    constrainedProlateWeilTwoModeSchurCorrection
  field_simp
  ring

/-- The first CCM scale quotient in the Schur correction:
`(8/11)/(176/211)=211/242`. -/
theorem constrainedProlateWeilFirstSchurScaleRatio :
    ((8 : ℝ) / 11) / ((176 : ℝ) / 211) = 211 / 242 := by
  norm_num

/-- Source-level capstone: the concrete adjacent correction has the exact Schur value and its
coefficient is strictly larger than `1/2`. -/
theorem constrainedProlateWeilConcreteTwoModeSchurSurvivor
    {a0 a1 : ℝ} (ha1 : a1 ≠ 0) :
    constrainedProlateWeilTwoModeLeadingForm
        constrainedProlateWeilToeplitzD0 constrainedProlateWeilToeplitzD1
        a0 a1 1
        (constrainedProlateWeilTwoModeSchurCorrection
          constrainedProlateWeilToeplitzD0 constrainedProlateWeilToeplitzD1 a0 a1) =
      a0 ^ 2 *
        (constrainedProlateWeilToeplitzD0 -
          constrainedProlateWeilToeplitzD1 ^ 2 / constrainedProlateWeilToeplitzD0) ∧
      (1 : ℝ) / 2 <
        constrainedProlateWeilToeplitzD0 -
          constrainedProlateWeilToeplitzD1 ^ 2 / constrainedProlateWeilToeplitzD0 := by
  exact ⟨constrainedProlateWeilTwoModeLeadingForm_schurCorrection
      constrainedProlateWeilToeplitzD0_pos.ne' ha1,
    constrainedProlateWeilToeplitzSchurCoefficient_gt_half⟩

end

end RHTower
