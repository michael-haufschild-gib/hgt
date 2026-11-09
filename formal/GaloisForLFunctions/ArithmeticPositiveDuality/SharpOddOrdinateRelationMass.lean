import GaloisForLFunctions.ArithmeticPositiveDuality.OddCyclePhaseEnergy
import GaloisForLFunctions.ArithmeticPositiveDuality.OddOrdinateRelationsForceFrequencyCost

/-!
# Sharp mass obstruction from an odd ordinate relation

A zero-sum list of ordinates makes each monomial's phases close into a cycle.
The odd-cycle spectral floor, integrated against positive coefficients, bounds
joint cancellation accuracy independently of logarithmic bandwidth.
-/

noncomputable section
set_option autoImplicit false

open Complex Finset
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

/-- Every odd zero-sum ordinate list imposes the cycle spectral mass bound. -/
theorem odd_ordinate_relation_sharp_mass_bound {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {q : ℕ} [NeZero q]
    (hq : Odd q) (h3 : 3 ≤ q) (β ε : ℝ) (γ : ZMod q → ℝ)
    (hs : ∑ j, γ j = 0)
    (he : ∀ j, ‖dirichletEval (harmonicPacketPoint β (γ j) 1) P‖ ≤ ε) :
    1 - ε ≤ Real.cos (Real.pi / q) * dirichletTailMass P β := by
  have hp (d : Fin 2 →₀ ℕ) : (∏ j, monomialPhase (γ j) d) = 1 := by
    simp only [monomialPhase]
    rw [← Complex.exp_sum, ← Finset.sum_mul, ← Finset.mul_sum,
      ← Complex.ofReal_sum, hs, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero]
  have hphase (d : Fin 2 →₀ ℕ) := odd_unit_product_phase_energy hq h3
    (fun j => monomialPhase (γ j) d) (fun j => norm_monomialPhase (γ j) d) (hp d)
  let w : (Fin 2 →₀ ℕ) → ℝ := fun d =>
    ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β)
  have hw (d : Fin 2 →₀ ℕ) : 0 ≤ w d :=
    mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos _).le
  have henergy : 2 * (q : ℝ) * (1 - Real.cos (Real.pi / q)) * dirichletTailMass P β ≤
      2 * q * (dirichletTailMass P β - 1 + ε) := by
    calc
      _ = ∑ d ∈ P.support.erase 0, w d *
          (2 * (q : ℝ) * (1 - Real.cos (Real.pi / q))) := by
        rw [← Finset.sum_mul]
        change _ = dirichletTailMass P β * _
        ring
      _ ≤ ∑ d ∈ P.support.erase 0, w d * ∑ j, ‖monomialPhase (γ j) d + 1‖ ^ 2 :=
        Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hphase d) (hw d)
      _ = ∑ j, 2 * (dirichletTailMass P β - 1 +
          (dirichletEval (harmonicPacketPoint β (γ j) 1) P).re) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => ordinate_phase_energy hP β (γ j)
      _ ≤ ∑ _j : ZMod q, 2 * (dirichletTailMass P β - 1 + ε) := by
        apply Finset.sum_le_sum
        intro j _
        have hr := (Complex.re_le_norm _).trans (he j)
        linarith only [hr]
      _ = _ := by simp; ring
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  apply le_of_mul_le_mul_left (a := (q : ℝ)) _ hqR
  nlinarith only [henergy]

#print axioms odd_ordinate_relation_sharp_mass_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
