import GaloisForLFunctions.HTGeometry.TanhSubstitution
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# All-order activation jets from arXiv:2609.03768
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def tanhDerivativePolynomial : ℕ → Polynomial ℝ
  | 0 => Polynomial.X
  | q + 1 => (1 - Polynomial.X ^ (2 : ℕ)) * (tanhDerivativePolynomial q).derivative

def tanhHighJet (q : ℕ) (x : ℝ) : ℝ :=
  (tanhDerivativePolynomial q).eval (Real.tanh x)

@[simp] theorem tanhHighJet_zero (x : ℝ) : tanhHighJet 0 x = Real.tanh x := by
  simp [tanhHighJet, tanhDerivativePolynomial]

theorem hasDerivAt_tanhHighJet (q : ℕ) (x : ℝ) :
    HasDerivAt (tanhHighJet q) (tanhHighJet (q + 1) x) x := by
  have h := ((tanhDerivativePolynomial q).hasDerivAt (Real.tanh x)).comp x
    (HTGeometry.hasDerivAt_tanh x)
  apply h.congr_deriv
  rw [← HTGeometry.one_sub_tanh_sq]
  simp [tanhHighJet, tanhDerivativePolynomial, Polynomial.eval_mul, Polynomial.eval_sub]
  ring

def polynomialUnitBound (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ p.support, |p.coeff i|

theorem abs_tanhHighJet_le_unitBound (q : ℕ) (x : ℝ) :
    |tanhHighJet q x| ≤ polynomialUnitBound (tanhDerivativePolynomial q) := by
  rw [tanhHighJet, Polynomial.eval_eq_sum, polynomialUnitBound]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul, abs_pow]
  have ht : |Real.tanh x| ^ i ≤ 1 := by
    exact (pow_le_one₀ (abs_nonneg _) (Real.abs_tanh_lt_one x).le)
  exact mul_le_of_le_one_right (abs_nonneg _) ht

def sinHighJet (q : ℕ) (x : ℝ) : ℝ :=
  Real.sin (x + (q : ℝ) * Real.pi / 2)

@[simp] theorem sinHighJet_zero (x : ℝ) : sinHighJet 0 x = Real.sin x := by
  simp [sinHighJet]

theorem hasDerivAt_sinHighJet (q : ℕ) (x : ℝ) :
    HasDerivAt (sinHighJet q) (sinHighJet (q + 1) x) x := by
  have hinner : HasDerivAt (fun y : ℝ => y + (q : ℝ) * Real.pi / 2) 1 x := by
    simpa using (hasDerivAt_id x).add_const ((q : ℝ) * Real.pi / 2)
  have h := (Real.hasDerivAt_sin (x + (q : ℝ) * Real.pi / 2)).comp x hinner
  apply h.congr_deriv
  rw [sinHighJet, show x + ((q + 1 : ℕ) : ℝ) * Real.pi / 2 =
      (x + (q : ℝ) * Real.pi / 2) + Real.pi / 2 by
        push_cast
        ring,
    Real.sin_add_pi_div_two]
  ring

theorem abs_sinHighJet_le_one (q : ℕ) (x : ℝ) : |sinHighJet q x| ≤ 1 := by
  exact Real.abs_sin_le_one _

end

end GaloisForLFunctions.HTGeometry
