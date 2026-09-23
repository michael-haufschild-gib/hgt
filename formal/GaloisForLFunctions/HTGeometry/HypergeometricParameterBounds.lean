import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Uniform Pochhammer bounds that retain terminating numerator parameters. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Split the actual coefficient product at a finite denominator prefix. -/
theorem pochhammer_eval_add {K : Type*} [CommRing K] (a : K) (N m : ℕ) :
    (ascPochhammer K (N+m)).eval a =
      (ascPochhammer K N).eval a * (ascPochhammer K m).eval (a+N) := by
  rw [← ascPochhammer_mul]
  simp only [Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_natCast]

theorem pochhammer_norm_le {a : ℂ} {B : ℝ} (hB : 0 < B) (ha : ‖a‖ ≤ B) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval a‖ ≤ (ascPochhammer ℝ n).eval B := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval,ascPochhammer_succ_eval,norm_mul]
    have hn : ‖a+(n : ℂ)‖ ≤ B+n := by
      calc
        _ ≤ ‖a‖+‖(n : ℂ)‖ := norm_add_le _ _
        _ ≤ B+n := by simpa only [Complex.norm_natCast] using add_le_add ha (le_refl (n : ℝ))
    exact mul_le_mul ih hn (norm_nonneg _) (ascPochhammer_pos n B hB).le

theorem pochhammer_norm_lower {c : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ j : ℕ, δ ≤ ‖c+j‖) (n : ℕ) :
    δ^n ≤ ‖(ascPochhammer ℂ n).eval c‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval,norm_mul,pow_succ]
    exact mul_le_mul ih (hc n) hδ.le (norm_nonneg _)

theorem pochhammer_norm_factorial {c : ℂ} (hc : 1 ≤ c.re) (n : ℕ) :
    (n.factorial : ℝ) ≤ ‖(ascPochhammer ℂ n).eval c‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ,Nat.cast_mul,ascPochhammer_succ_eval,norm_mul]
    have hn : ((n+1 : ℕ) : ℝ) ≤ ‖c+(n : ℂ)‖ := by
      have hr := Complex.re_le_norm (c+(n : ℂ))
      simp only [Complex.add_re,Complex.natCast_re] at hr
      push_cast
      linarith
    simpa only [mul_comm] using mul_le_mul ih hn (Nat.cast_nonneg (n+1) : (0 : ℝ) ≤ (n+1 : ℕ)) (norm_nonneg _)

theorem hypergeometricCoefficient_norm (a b c : ℂ) (n : ℕ) :
    ‖ordinaryHypergeometricCoefficient a b c n‖ =
      ‖(ascPochhammer ℂ n).eval a‖*‖(ascPochhammer ℂ n).eval b‖/
        ((n.factorial : ℝ)*‖(ascPochhammer ℂ n).eval c‖) := by
  simp only [ordinaryHypergeometricCoefficient,norm_mul,norm_inv,Complex.norm_natCast]
  ring

def positiveGaussCoefficient (B : ℝ) (n : ℕ) : ℝ := ordinaryHypergeometricCoefficient B B 1 n

theorem positiveGaussCoefficient_eq (B : ℝ) (n : ℕ) :
    positiveGaussCoefficient B n = ((ascPochhammer ℝ n).eval B)^(2 : ℕ)/(n.factorial : ℝ)^(2 : ℕ) := by
  simp only [positiveGaussCoefficient,ordinaryHypergeometricCoefficient,ascPochhammer_eval_one]
  ring

theorem positiveGaussCoefficient_nonneg (B : ℝ) (n : ℕ) : 0 ≤ positiveGaussCoefficient B n := by
  rw [positiveGaussCoefficient_eq]
  positivity

/-- A positive real Gauss series controls the whole smaller radial disk. -/
theorem positiveGaussCoefficient_summable {B r : ℝ} (hB : 0 < B) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => positiveGaussCoefficient B n*r^n) := by
  let p := ordinaryHypergeometricSeries ℝ B B 1
  have hp : p.radius = 1 := ordinaryHypergeometricSeries_radius_eq_one ℝ B B 1 (fun n => by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    refine ⟨?_,?_,?_⟩ <;> linarith)
  let rnn : NNReal := ⟨r,hr⟩
  have hrad : (rnn : ENNReal) < p.radius := by
    rw [hp]
    exact_mod_cast hr1
  have hs := p.summable_norm_mul_pow (r := rnn) hrad
  simp only [p,ordinaryHypergeometricSeries,FormalMultilinearSeries.ofScalars_norm,Real.norm_eq_abs] at hs
  change Summable (fun n : ℕ => |positiveGaussCoefficient B n| * r^n) at hs
  simpa only [abs_of_nonneg (positiveGaussCoefficient_nonneg B _)] using hs

end
end GaloisForLFunctions.HTGeometry
