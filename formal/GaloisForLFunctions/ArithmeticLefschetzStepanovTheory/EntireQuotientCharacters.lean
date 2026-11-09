import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.PrimeOrbitEqualDivisors
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.EntirePrimeOrbitValue

/-!
# Entire quotients of prime-orbit polynomials are characters

An entire nonvanishing quotient with subquadratic proximity has an affine
logarithm. Unit modulus on the real axis makes its slope purely imaginary,
so the quotient restricts to one unimodular character.
-/

open Filter Topology Complex Set
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

/-- An order-one entire quotient of unit modulus on the real axis is a character. -/
theorem entire_quotient_eq_character {N D : ℂ → ℂ}
    (hN : AnalyticOnNhd ℂ N Set.univ) (hD : AnalyticOnNhd ℂ D Set.univ)
    (hDr : ∀ t : ℝ, D t ≠ 0)
    (horder : ∀ z, analyticOrderAt N z = analyticOrderAt D z)
    (hproxN : ValueDistribution.proximity N ⊤ =o[atTop] fun r : ℝ => r ^ (2 : ℕ))
    (hproxD : ValueDistribution.proximity D ⊤ =o[atTop] fun r : ℝ => r ^ (2 : ℕ))
    (hunit : ∀ t : ℝ, ‖N t / D t‖ = 1) :
    ∃ γ : ℝ, ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ t : ℝ, N t = c * expChar γ t * D t := by
  have hN0 : N 0 ≠ 0 := by
    intro he
    have hu := hunit 0
    simp only [Complex.ofReal_zero, he, zero_div, norm_zero] at hu
    exact zero_ne_one hu
  have hD0 : D 0 ≠ 0 := by simpa only [Complex.ofReal_zero] using hDr 0
  obtain ⟨H, hH, hHne, hfac⟩ := EntireQuotient.exists_entire_nonvanishing_quotient
    hN hD (entire_order_ne_top_of_ne_zero hN hN0) horder hD0
  have hNo (z : ℂ) : meromorphicOrderAt N z ≠ ⊤ := by
    rw [entire_meromorphicOrder_eq_natOrder hN hN0 z]
    exact WithTop.coe_ne_top
  have hDo (z : ℂ) : meromorphicOrderAt D z ≠ ⊤ := by
    rw [entire_meromorphicOrder_eq_natOrder hD hD0 z]
    exact WithTop.coe_ne_top
  obtain ⟨a, b, hex⟩ := _root_.RHTower.OrderOneRigidity.exists_expAffine_of_entire_quotient
    (fun z => (hD z trivial).differentiableAt)
    (fun z => (hN z trivial).differentiableAt) hH hDo hNo hHne hfac hproxD hproxN
  have hhunit (t : ℝ) : ‖Complex.exp (a * t + b)‖ = 1 := by
    rw [← hex]
    have hu := hunit t
    rw [hfac, mul_div_cancel_right₀ _ (hDr t)] at hu
    exact hu
  have hb : b.re = 0 := by
    have hu := hhunit 0
    simpa only [Complex.ofReal_zero, mul_zero, zero_add, Complex.norm_exp,
      Real.exp_eq_one_iff] using hu
  have ha : a.re = 0 := by
    have hu := hhunit 1
    simpa only [Complex.ofReal_one, mul_one, Complex.norm_exp,
      Real.exp_eq_one_iff, Complex.add_re, hb, add_zero] using hu
  have ha' : a = (a.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [ha]
  refine ⟨a.im, Complex.exp b, ?_, fun t => ?_⟩
  · simpa only [Complex.ofReal_zero, mul_zero, zero_add] using hhunit 0
  · have he : Complex.exp ((a.im : ℂ) * Complex.I * (t : ℂ)) = expChar a.im t := by
      unfold expChar
      congr 1
      push_cast
      ring
    conv_lhs => rw [hfac, hex, ha', Complex.exp_add, he]
    ring

#print axioms entire_quotient_eq_character
end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
