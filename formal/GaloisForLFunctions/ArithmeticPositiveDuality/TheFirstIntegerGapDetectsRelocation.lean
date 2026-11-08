import GaloisForLFunctions.ArithmeticPositiveDuality.NormalizedRelocationHasASignedDensity
import GaloisForLFunctions.ArithmeticPositiveDuality.TheIntegerJumpsOfRelocationDensities
import GaloisForLFunctions.RHTower.ThetaRenewalFeedbackLoop

/-!
# The first integer gap detects a normalized relocation

The density vanishes below one and starts with derivative equal to its quadratic
trace. A negative trace therefore produces a negative interval immediately after
one. Every finite ordinary Dirichlet filter with constant coefficient one preserves
this interval: its nonconstant dilations sample the zero region below one.
-/

noncomputable section
set_option autoImplicit false

open Complex Set

namespace GaloisForLFunctions.ArithmeticPositiveDuality

theorem quartetDensity_zero_of_lt_one (γ₁ γ₂ c : ℝ) {Y : ℝ} (hY : Y < 1) :
    quartetDensity γ₁ γ₂ c Y = 0 := by
  have hf : ⌊Y⌋₊ = 0 := Nat.floor_eq_zero.mpr hY
  simp [quartetDensity, criticalPairDensity, integerPowerDensity, hf]

/-- Subtracting the empty cell removes the zeta value, for arbitrary donor ordinates. -/
def quartetFirstCell (γ₁ γ₂ c θ : ℝ) : ℝ :=
  quartetCellDefect γ₁ γ₂ c 1 θ - quartetCellDefect γ₁ γ₂ c 0 (1 + θ)

theorem quartetDensity_eq_firstCell (γ₁ γ₂ c : ℝ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    quartetDensity γ₁ γ₂ c (1 + θ) = quartetFirstCell γ₁ γ₂ c θ := by
  have hf : ⌊1 + θ⌋₊ = 1 := by
    apply (Nat.floor_eq_iff (by positivity : 0 ≤ 1 + θ)).mpr
    norm_num
    exact ⟨hθ0, by linarith only [hθ1]⟩
  have he (s : ℂ) : integerPowerDensity s (1 + θ) =
      zeroPowerSumCellKernel s 1 θ - zeroPowerSumCellKernel s 0 (1 + θ) := by
    norm_num [integerPowerDensity, zeroPowerSumCellKernel, hf]
    ring
  have hp (γ : ℝ) : criticalPairDensity γ (1 + θ) =
      criticalPairCellKernel γ 1 θ - criticalPairCellKernel γ 0 (1 + θ) := by
    rw [criticalPairDensity, he, Complex.sub_im, sub_div]
    rfl
  rw [quartetDensity, quartetFirstCell, quartetCellDefect, quartetCellDefect, hp, hp]
  ring

/-- The literal first cell starts at zero with derivative equal to the quadratic trace. -/
theorem quartetFirstCell_hasDerivAt {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂) (c : ℝ) :
    quartetFirstCell γ₁ γ₂ c 0 = 0 ∧ HasDerivAt (quartetFirstCell γ₁ γ₂ c) c 0 := by
  have hdiff (N : ℕ) (θ : ℝ) (hθ : 0 < (N : ℝ) + θ) :
      DifferentiableAt ℝ (quartetCellDefect γ₁ γ₂ c N) θ := by
    have h₁ := (hasDerivAt_criticalPairCellKernel γ₁ N θ hθ).differentiableAt
    have h₂ := (hasDerivAt_criticalPairCellKernel γ₂ N θ hθ).differentiableAt
    unfold quartetCellDefect
    exact (((h₂.const_mul (γ₂ ^ 2 + 1 / 4)).sub
      (h₁.const_mul (γ₁ ^ 2 + 1 / 4))).const_mul (c / (γ₂ ^ 2 - γ₁ ^ 2)))
  have hleft := (hdiff 1 0 (by norm_num)).hasDerivAt
  have hright0 : HasDerivAt (quartetCellDefect γ₁ γ₂ c 0)
      (deriv (quartetCellDefect γ₁ γ₂ c 0) 1) (1 + (0 : ℝ)) := by
    simpa only [add_zero] using (hdiff 0 1 (by norm_num)).hasDerivAt
  have hright := hright0.comp 0
    ((hasDerivAt_id (0 : ℝ)).const_add 1)
  have hj : deriv (quartetCellDefect γ₁ γ₂ c 1) 0 -
      deriv (quartetCellDefect γ₁ γ₂ c 0) 1 = c := by
    simpa using quartetCellDefect_derivative_jump hγ₁ hγ₂ c 0
  constructor
  · unfold quartetFirstCell
    simpa only [Nat.zero_add, add_zero, sub_eq_zero] using quartetCellDefect_glue γ₁ γ₂ c 0
  · unfold quartetFirstCell
    simpa only [Function.comp_def, Pi.sub_def, mul_one, hj] using hleft.sub hright

/-- A negative trace is detected within the first gap, without passing to large integers. -/
theorem exists_first_gap_negative_quartetDensity {γ₁ γ₂ c : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂) (hc : c < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ Y ∈ Ioo 1 (1 + ε), quartetDensity γ₁ γ₂ c Y < 0 := by
  obtain ⟨h0, hd⟩ := quartetFirstCell_hasDerivAt hγ₁ hγ₂ c
  obtain ⟨ε, hε, hb⟩ := RHTower.exists_Ioo_neg_of_hasDerivAt_neg hd h0 hc
  refine ⟨min ε 1, by positivity, min_le_right _ _, ?_⟩
  intro Y hY
  have hθ0 : 0 < Y - 1 := sub_pos.mpr hY.1
  have hθε : Y - 1 < ε := by linarith only [hY.2, min_le_left ε 1]
  have hθ1 : Y - 1 < 1 := by linarith only [hY.2, min_le_right ε 1]
  have he := quartetDensity_eq_firstCell γ₁ γ₂ c hθ0.le hθ1
  rw [show 1 + (Y - 1) = Y by ring] at he
  rw [he]
  exact hb (Y - 1) ⟨hθ0, hθε⟩

/-- The continuous density obtained by multiplying a Mellin transform by a finite
ordinary Dirichlet polynomial with constant coefficient one. -/
def finiteIntegerDilationDensity (S : Finset ℕ) (a : ℕ → ℝ) (f : ℝ → ℝ) (Y : ℝ) : ℝ :=
  f Y + ∑ n ∈ S, a n / (n : ℝ) * f (Y / (n : ℝ))

/-- Every nonconstant integer dilation is invisible throughout the first gap. -/
theorem finiteIntegerDilationDensity_quartet_first_gap (γ₁ γ₂ c : ℝ)
    (S : Finset ℕ) (a : ℕ → ℝ) (hS : ∀ n ∈ S, 2 ≤ n) {Y : ℝ} (hY : Y < 2) :
    finiteIntegerDilationDensity S a (quartetDensity γ₁ γ₂ c) Y =
      quartetDensity γ₁ γ₂ c Y := by
  unfold finiteIntegerDilationDensity
  have hz : ∀ n ∈ S, a n / (n : ℝ) * quartetDensity γ₁ γ₂ c (Y / (n : ℝ)) = 0 := by
    intro n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hS n hn
    have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hn2
    rw [quartetDensity_zero_of_lt_one γ₁ γ₂ c
      ((div_lt_one hn0).mpr (hY.trans_le hn2)), mul_zero]
  rw [Finset.sum_eq_zero hz, add_zero]

/-- Actual donor zeros give a negative interval which survives every finite ordinary
Dirichlet filter with constant coefficient one, even when its other coefficients are signed. -/
theorem exists_normalizedRelocation_first_gap_obstruction :
    ∃ γ₁ γ₂ ε : ℝ, 1 < γ₁ ∧ γ₁ < γ₂ ∧
      riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0 ∧
      riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0 ∧ 0 < ε ∧ ε ≤ 1 ∧
      ∀ (S : Finset ℕ) (a : ℕ → ℝ), (∀ n ∈ S, 2 ≤ n) →
        ∀ Y ∈ Ioo 1 (1 + ε), finiteIntegerDilationDensity S a
          (quartetDensity γ₁ γ₂ (normalizedRelocationTrace γ₁ γ₂)) Y < 0 := by
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hz₁, hz₂⟩ := exists_two_critical_donor_ordinates
  obtain ⟨ε, hε, hε1, hb⟩ := exists_first_gap_negative_quartetDensity
    (lt_trans zero_lt_one hγ₁) hγ₂
    (normalizedRelocationTrace_neg hγ₁ (hγ₁.trans hγ₂))
  refine ⟨γ₁, γ₂, ε, hγ₁, hγ₂, hz₁, hz₂, hε, hε1, ?_⟩
  intro S a hS Y hY
  rw [finiteIntegerDilationDensity_quartet_first_gap γ₁ γ₂ _ S a hS
    (by linarith only [hY.2, hε1])]
  exact hb Y hY

#print axioms quartetFirstCell_hasDerivAt
#print axioms finiteIntegerDilationDensity_quartet_first_gap
#print axioms exists_normalizedRelocation_first_gap_obstruction

end GaloisForLFunctions.ArithmeticPositiveDuality
