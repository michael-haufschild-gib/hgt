import GaloisForLFunctions.HTGeometry.PolynomialODE.HeunFormalTermination

/-!
# The normalized nonresonant formal Heun solution

The coefficient recurrence constructs an actual formal solution for every
parameter outside the negative integers. Its constant coefficient determines
it uniquely. In the nonnegative real-part range, the spectral tuning and
terminal coefficient give the exact polynomial termination criterion.
-/

open scoped PowerSeries
noncomputable section
namespace GaloisForLFunctions.HTGeometry.Heun

/-- The normalized three-term recurrence, with division interpreted in the coefficient field. -/
def normalizedCoefficient (α β γ q : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => q / (1 + α)
  | n + 2 => ((β * ((n + 1 : ℕ) : ℂ) + q) * normalizedCoefficient α β γ q (n + 1) +
      (2 * ((n + 1 : ℕ) : ℂ) + α - γ) * normalizedCoefficient α β γ q n) /
        (((n + 2 : ℕ) : ℂ) * (((n + 2 : ℕ) : ℂ) + α))

/-- No positive coefficient index collides with the exponent parameter. -/
def Nonresonant (α : ℂ) : Prop := ∀ r : ℕ, 0 < r → (r : ℂ) + α ≠ 0

/-- Nonnegative real part excludes every formal coefficient collision. -/
theorem nonresonant_of_nonneg_re {α : ℂ} (hα : 0 ≤ α.re) : Nonresonant α := by
  intro r hr h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hre
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  linarith only [hre, hα, hr']

/-- The literal recursively defined coefficients solve every recurrence equation in the nonresonant range. -/
theorem normalizedCoefficient_recurrence (α β γ q : ℂ) (hα : Nonresonant α) :
    CoefficientRecurrence α β γ q (normalizedCoefficient α β γ q) := by
  have h1 : 1 + α ≠ 0 := by
    simpa only [Nat.cast_one] using hα 1 Nat.zero_lt_one
  constructor
  · simp only [normalizedCoefficient, mul_one]
    exact (mul_comm _ _).trans (div_mul_cancel₀ q h1)
  · intro n
    rw [normalizedCoefficient]
    have hn : ((n + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    have hden := mul_ne_zero hn (hα (n + 2) (by omega))
    exact (mul_comm _ _).trans (div_mul_cancel₀ _ hden)

/-- A nonresonant solution sequence is determined by its constant coefficient. -/
theorem recurrence_unique (α β γ q : ℂ) (hα : Nonresonant α)
    (d e : ℕ → ℂ) (hd : CoefficientRecurrence α β γ q d)
    (he : CoefficientRecurrence α β γ q e) (h0 : d 0 = e 0) : d = e := by
  funext r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rcases r with _ | r
    · exact h0
    · rcases r with _ | n
      · have h1 : (1 : ℂ) + α ≠ 0 := by
          simpa only [Nat.cast_one] using hα 1 Nat.zero_lt_one
        apply mul_left_cancel₀ h1
        rw [hd.1, he.1, h0]
      · have hn : ((n + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
        apply mul_left_cancel₀ (mul_ne_zero hn (hα (n + 2) (by omega)))
        rw [hd.2 n, he.2 n, ih (n + 1) (by omega), ih n (by omega)]

/-- The normalized formal solution in the coefficient ring, without a convergence claim. -/
def normalizedFormalSolution (α β γ q : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk (normalizedCoefficient α β γ q)

/-- The explicitly constructed normalized series is an actual formal solution. -/
theorem normalizedFormalSolution_solves (α β γ q : ℂ) (hα : Nonresonant α) :
    formalAction α β γ q (normalizedFormalSolution α β γ q) = 0 ∧
      PowerSeries.coeff 0 (normalizedFormalSolution α β γ q) = 1 := by
  constructor
  · apply (formalAction_eq_zero_iff α β γ q _).mpr
    simpa only [normalizedFormalSolution, PowerSeries.coeff_mk] using
      normalizedCoefficient_recurrence α β γ q hα
  · simp only [normalizedFormalSolution, PowerSeries.coeff_mk, normalizedCoefficient]

/-- The nonresonant initial-value problem has precisely the constructed normalized solution. -/
theorem normalizedFormalSolution_unique_iff (α β γ q : ℂ) (hα : Nonresonant α) (f : ℂ⟦X⟧) :
    (formalAction α β γ q f = 0 ∧ PowerSeries.coeff 0 f = 1) ↔
      f = normalizedFormalSolution α β γ q := by
  constructor
  · rintro ⟨hf, h0⟩
    have h := recurrence_unique α β γ q hα
      (fun n => PowerSeries.coeff n f) (normalizedCoefficient α β γ q)
      ((formalAction_eq_zero_iff α β γ q f).mp hf)
      (normalizedCoefficient_recurrence α β γ q hα) h0
    apply PowerSeries.ext
    intro n
    simpa only [normalizedFormalSolution, PowerSeries.coeff_mk] using congrFun h n
  · rintro rfl
    exact normalizedFormalSolution_solves α β γ q hα

/-- The canonical solution terminates in exact degree `N` precisely at the spectral and terminal-coefficient conditions. -/
theorem normalizedFormalSolution_termination_iff (α β γ q : ℂ) (hα : 0 ≤ α.re)
    (N : ℕ) (hN : normalizedCoefficient α β γ q N ≠ 0) :
    normalizedFormalSolution α β γ q =
        (PowerSeries.trunc (N + 1) (normalizedFormalSolution α β γ q) : ℂ⟦X⟧) ↔
      γ = α + 2 * N + 2 ∧ normalizedCoefficient α β γ q (N + 1) = 0 := by
  have hN' : PowerSeries.coeff N (normalizedFormalSolution α β γ q) ≠ 0 := by
    simpa only [normalizedFormalSolution, PowerSeries.coeff_mk] using hN
  simpa only [normalizedFormalSolution, PowerSeries.coeff_mk] using
    formal_solution_eq_trunc_iff_of_nonneg_re α β γ q N _
      (normalizedFormalSolution_solves α β γ q (nonresonant_of_nonneg_re hα)).1 hN' hα

#print axioms normalizedFormalSolution_solves
#print axioms normalizedFormalSolution_unique_iff
#print axioms normalizedFormalSolution_termination_iff
end GaloisForLFunctions.HTGeometry.Heun
