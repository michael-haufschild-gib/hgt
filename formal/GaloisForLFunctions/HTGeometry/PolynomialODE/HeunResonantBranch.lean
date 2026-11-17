import GaloisForLFunctions.HTGeometry.PolynomialODE.HeunNormalizedSeries

/-!
# Exact uniqueness boundary for the formal Heun equation

At every negative-integer exponent, a free formal branch starts at the
collided coefficient and has zero constant term. Adding this branch prevents
unique normalized solvability. Together with the explicit nonresonant
construction, this proves the exact uniqueness boundary for all parameters.
-/

open scoped PowerSeries
noncomputable section
namespace GaloisForLFunctions.HTGeometry.Heun

/-- The free branch at the collision index `m + 1`, with leading coefficient one. -/
def resonantCoefficient (m : ℕ) (β γ q : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => if m = 0 then 1 else 0
  | n + 2 => if n + 2 < m + 1 then 0 else if n + 2 = m + 1 then 1 else
      ((β * ((n + 1 : ℕ) : ℂ) + q) * resonantCoefficient m β γ q (n + 1) +
        (2 * ((n + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ) - γ) * resonantCoefficient m β γ q n) /
          (((n + 2 : ℕ) : ℂ) * (((n + 2 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)))

private theorem resonantCoefficient_below (m : ℕ) (β γ q : ℂ) (r : ℕ)
    (hr : r < m + 1) : resonantCoefficient m β γ q r = 0 := by
  rcases r with _ | r
  · rfl
  · rcases r with _ | n
    · simp only [resonantCoefficient, if_neg (by omega : m ≠ 0)]
    · rw [resonantCoefficient, if_pos hr]

/-- The resonant branch begins at precisely the collided coefficient. -/
theorem resonantCoefficient_leading (m : ℕ) (β γ q : ℂ) :
    resonantCoefficient m β γ q (m + 1) = 1 := by
  cases m with
  | zero => simp [resonantCoefficient]
  | succ m =>
    rw [show m + 1 + 1 = m + 2 by omega, resonantCoefficient,
      if_neg (by omega : ¬ m + 2 < m + 1 + 1), if_pos (by omega : m + 2 = m + 1 + 1)]

/-- The free branch solves every equation, including the zero-denominator collision itself. -/
theorem resonantCoefficient_recurrence (m : ℕ) (β γ q : ℂ) :
    CoefficientRecurrence (-((m + 1 : ℕ) : ℂ)) β γ q (resonantCoefficient m β γ q) := by
  constructor
  · by_cases hm : m = 0
    · subst m
      simp [resonantCoefficient]
    · simp only [resonantCoefficient, if_neg hm, mul_zero]
  · intro n
    by_cases hlt : n + 2 < m + 1
    · rw [resonantCoefficient, if_pos hlt,
        resonantCoefficient_below m β γ q (n + 1) (by omega),
        resonantCoefficient_below m β γ q n (by omega)]
      simp only [mul_zero, zero_add]
    · by_cases heq : n + 2 = m + 1
      · rw [resonantCoefficient, if_neg hlt, if_pos heq,
          resonantCoefficient_below m β γ q (n + 1) (by omega),
          resonantCoefficient_below m β γ q n (by omega), heq]
        simp only [add_neg_cancel, mul_zero, mul_one, zero_add]
      · rw [resonantCoefficient, if_neg hlt, if_neg heq]
        have hn : ((n + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
        have hd : ((n + 2 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ) ≠ 0 :=
          sub_ne_zero.mpr (by exact_mod_cast heq)
        simp only [sub_eq_add_neg]
        exact (mul_comm _ _).trans (div_mul_cancel₀ _ (mul_ne_zero hn hd))

/-- An actual formal solution with zero constant term at every negative-integer exponent. -/
def resonantFormalBranch (m : ℕ) (β γ q : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk (resonantCoefficient m β γ q)

theorem resonantFormalBranch_solves (m : ℕ) (β γ q : ℂ) :
    formalAction (-((m + 1 : ℕ) : ℂ)) β γ q (resonantFormalBranch m β γ q) = 0 ∧
      PowerSeries.coeff 0 (resonantFormalBranch m β γ q) = 0 ∧
      PowerSeries.coeff (m + 1) (resonantFormalBranch m β γ q) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · apply (formalAction_eq_zero_iff _ _ _ _ _).mpr
    simpa only [resonantFormalBranch, PowerSeries.coeff_mk] using
      resonantCoefficient_recurrence m β γ q
  · simp only [resonantFormalBranch, PowerSeries.coeff_mk, resonantCoefficient]
  · simpa only [resonantFormalBranch, PowerSeries.coeff_mk] using
      resonantCoefficient_leading m β γ q

private theorem formalAction_add (α β γ q : ℂ) (f g : ℂ⟦X⟧) :
    formalAction α β γ q (f + g) = formalAction α β γ q f + formalAction α β γ q g := by
  simp only [formalAction, _root_.RHTower.hypergeometricEulerOperator, map_add, mul_add]
  ring

/-- Unique normalized formal solvability has the exact boundary of no negative-integer resonance. -/
theorem existsUnique_normalized_iff (α β γ q : ℂ) :
    (∃! f : ℂ⟦X⟧, formalAction α β γ q f = 0 ∧ PowerSeries.coeff 0 f = 1) ↔ Nonresonant α := by
  constructor
  · rintro ⟨f, hf, huniq⟩
    by_contra hN
    change ¬ (∀ r : ℕ, 0 < r → (r : ℂ) + α ≠ 0) at hN
    push Not at hN
    obtain ⟨r, hr, hα⟩ := hN
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    have ha : α = -((m + 1 : ℕ) : ℂ) := by linear_combination hα
    subst α
    have hb := resonantFormalBranch_solves m β γ q
    have hsum : f + resonantFormalBranch m β γ q = f := huniq _ ⟨by
      rw [formalAction_add, hf.1, hb.1, add_zero], by rw [map_add, hf.2, hb.2.1, add_zero]⟩
    have hz : resonantFormalBranch m β γ q = 0 := add_left_cancel (by
      simpa only [add_zero] using hsum)
    have hh := congrArg (PowerSeries.coeff (m + 1)) hz
    rw [hb.2.2, map_zero] at hh
    exact one_ne_zero hh
  · intro hα
    refine ⟨normalizedFormalSolution α β γ q, normalizedFormalSolution_solves α β γ q hα, ?_⟩
    intro f hf
    exact (normalizedFormalSolution_unique_iff α β γ q hα f).mp hf

#print axioms resonantFormalBranch_solves
#print axioms existsUnique_normalized_iff
end GaloisForLFunctions.HTGeometry.Heun
