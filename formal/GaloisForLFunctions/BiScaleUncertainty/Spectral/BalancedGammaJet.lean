import GaloisForLFunctions.BiScaleUncertainty.Spectral.BetaPhaseSpaceTraces
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# Balanced Gamma products have no linear jet

The numerator and denominator have the same total Gamma scale. Their
first derivatives at the origin cancel exactly, independently of Euler's
constant. This clears the double pole of triangular phase-space traces
without introducing a simple pole.
-/

open scoped BigOperators
open Complex Filter Topology
namespace GaloisForLFunctions.BiScaleUncertainty.Spectral
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gamma ratio with its origin poles removed by the recurrence. -/
def balancedGammaRatio (a : ι → ℂ) (s : ℂ) : ℂ :=
  (∏ i, Complex.Gamma (1+a i*s)) / Complex.Gamma (1+(∑ i, a i)*s)

omit [DecidableEq ι] in
lemma balancedGammaRatio_zero (a : ι → ℂ) : balancedGammaRatio a 0 = 1 := by
  simp only [balancedGammaRatio, mul_zero, add_zero, Complex.Gamma_one,
    Finset.prod_const_one, div_one]

private lemma gamma_affine_deriv_zero (a : ℂ) :
    HasDerivAt (fun s : ℂ => Complex.Gamma (1+a*s)) (deriv Complex.Gamma 1 * a) 0 := by
  have hG : DifferentiableAt ℂ Complex.Gamma 1 :=
    Complex.differentiableAt_Gamma 1 (by
      intro n h
      have hr := congrArg Complex.re h
      simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hr
      linarith only [hr, Nat.cast_nonneg (α := ℝ) n])
  have ha : HasDerivAt (fun s : ℂ => 1+a*s) a 0 := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id (0 : ℂ)).const_mul a).const_add 1
  have hG' : HasDerivAt Complex.Gamma (deriv Complex.Gamma 1) (1+a*(0:ℂ)) := by
    simpa only [mul_zero, add_zero] using hG.hasDerivAt
  convert! hG'.comp 0 ha using 1

/-- Every finite balanced Gamma ratio has vanishing first derivative at zero. -/
theorem balancedGammaRatio_hasDerivAt_zero (a : ι → ℂ) :
    HasDerivAt (balancedGammaRatio a) 0 0 := by
  have hp := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun i _ => gamma_affine_deriv_zero (a i))
  simp only [mul_zero, add_zero, Complex.Gamma_one, Finset.prod_const_one,
    one_smul, ← Finset.mul_sum] at hp
  have hq := hp.fun_div (gamma_affine_deriv_zero (∑ i, a i)) (by simp)
  convert! hq using 1
  simp only [mul_zero, add_zero, Complex.Gamma_one, Finset.prod_const_one,
    mul_one, one_mul, sub_self, zero_div]

/-- A finite-difference formulation of the absent linear term. -/
theorem balancedGammaRatio_no_linear_term (a : ι → ℂ) :
    Tendsto (fun s : ℂ => (balancedGammaRatio a s - 1)/s) (𝓝[≠] 0) (𝓝 0) := by
  have h := (balancedGammaRatio_hasDerivAt_zero a).tendsto_slope_zero
  simpa only [balancedGammaRatio_zero, zero_add, sub_zero, smul_eq_mul, div_eq_mul_inv,
    mul_comm] using h

/-- The meromorphic continuation of the triangular phase-space trace. -/
def triangularGammaTrace (a b c : ℝ) (s : ℂ) : ℂ :=
  Complex.Gamma ((Real.exp a : ℂ)*s) * Complex.Gamma ((Real.exp b : ℂ)*s) *
    Complex.Gamma ((Real.exp c : ℂ)*s) /
      Complex.Gamma (((Real.exp a + Real.exp b + Real.exp c : ℝ) : ℂ)*s)

/-- Positive dilation of the right-half-plane shape coordinates. -/
lemma positiveMellinShape_dilate (a : ℝ) (t : ℝ × ℝ) :
    positiveMellinShape (a+t.1, Real.exp a*t.2) = (Real.exp a : ℂ)*positiveMellinShape t := by
  unfold positiveMellinShape
  simp only [Real.exp_add, Complex.ofReal_mul]
  ring

/-- On its convergence domain the Gamma continuation is the actual phase-plane integral. -/
theorem triangularGammaTrace_phase_integral (a b c : ℝ) (t : ℝ × ℝ) :
    triangularGammaTrace a b c (positiveMellinShape t) =
      triangularPhaseTrace (positiveMellinShape (a+t.1, Real.exp a*t.2))
        (positiveMellinShape (b+t.1, Real.exp b*t.2))
        (positiveMellinShape (c+t.1, Real.exp c*t.2)) := by
  rw [triangularPhaseTrace_gamma]
  simp only [positiveMellinShape_dilate, triangularGammaTrace]
  have he : ((Real.exp a+Real.exp b+Real.exp c : ℝ) : ℂ)*positiveMellinShape t =
      (Real.exp a : ℂ)*positiveMellinShape t + (Real.exp b : ℂ)*positiveMellinShape t +
        (Real.exp c : ℂ)*positiveMellinShape t := by
    push_cast
    ring
  rw [he]

/-- Its double-pole coefficient, positive for every real shape parameter. -/
def triangularPoleCoefficient (a b c : ℝ) : ℝ :=
  (Real.exp a + Real.exp b + Real.exp c) / (Real.exp a * Real.exp b * Real.exp c)

def triangularGammaRegular (a b c : ℝ) (s : ℂ) : ℂ :=
  (triangularPoleCoefficient a b c : ℂ) *
    balancedGammaRatio (![Real.exp a, Real.exp b, Real.exp c] : Fin 3 → ℂ) s

lemma triangularGammaRegular_zero (a b c : ℝ) :
    triangularGammaRegular a b c 0 = triangularPoleCoefficient a b c := by
  rw [triangularGammaRegular, balancedGammaRatio_zero, mul_one]

/-- Gamma recurrence identifies the pole-cleared actual trace away from zero. -/
theorem triangularGammaTrace_regularization (a b c : ℝ) (s : ℂ) :
    s^2 * triangularGammaTrace a b c s =
      if s = 0 then 0 else triangularGammaRegular a b c s := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [if_neg hs]
    have ha : (Real.exp a : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero a
    have hb : (Real.exp b : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero b
    have hc : (Real.exp c : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero c
    have hA : ((Real.exp a + Real.exp b + Real.exp c : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show Real.exp a + Real.exp b + Real.exp c ≠ 0 by positivity)
    unfold triangularGammaTrace triangularGammaRegular balancedGammaRatio triangularPoleCoefficient
    simp only [Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add]
    rw [add_comm 1 ((Real.exp a : ℂ)*s), Complex.Gamma_add_one _ (mul_ne_zero ha hs),
      add_comm 1 ((Real.exp b : ℂ)*s), Complex.Gamma_add_one _ (mul_ne_zero hb hs),
      add_comm 1 ((Real.exp c : ℂ)*s), Complex.Gamma_add_one _ (mul_ne_zero hc hs)]
    have hAs : ((Real.exp a : ℂ)+(Real.exp b : ℂ)+(Real.exp c : ℂ))*s ≠ 0 := by
      exact mul_ne_zero (by simpa only [Complex.ofReal_add] using hA) hs
    rw [add_comm 1 _, Complex.Gamma_add_one _ hAs]
    by_cases hg : Complex.Gamma (((Real.exp a : ℂ)+(Real.exp b : ℂ)+(Real.exp c : ℂ))*s) = 0
    · simp only [hg, mul_zero, div_zero, mul_zero]
    · have hsum : (Real.exp a : ℂ)+Real.exp b+Real.exp c ≠ 0 := by
        simpa only [Complex.ofReal_add] using hA
      field_simp [ha, hb, hc, hs, hg, hsum]

/-- The regular part has zero derivative: the triangular trace has no simple-pole term. -/
theorem triangularGammaRegular_hasDerivAt_zero (a b c : ℝ) :
    HasDerivAt (triangularGammaRegular a b c) 0 0 := by
  have h := (balancedGammaRatio_hasDerivAt_zero
      (![Real.exp a, Real.exp b, Real.exp c] : Fin 3 → ℂ)).const_mul
        (triangularPoleCoefficient a b c : ℂ)
  convert! h using 1
  simp only [mul_zero]

/-- The double-pole coefficient is nonzero, so the leading pole cannot cancel. -/
theorem triangularPoleCoefficient_pos (a b c : ℝ) : 0 < triangularPoleCoefficient a b c := by
  unfold triangularPoleCoefficient
  positivity

/-- The pole-cleared trace tends to its explicit leading coefficient. -/
theorem triangularGammaTrace_double_pole (a b c : ℝ) :
    Tendsto (fun s : ℂ => s^2 * triangularGammaTrace a b c s) (𝓝[≠] 0)
      (𝓝 (triangularPoleCoefficient a b c : ℂ)) := by
  have ht : Tendsto (triangularGammaRegular a b c) (𝓝[≠] 0)
      (𝓝 (triangularGammaRegular a b c 0)) :=
    (triangularGammaRegular_hasDerivAt_zero a b c).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  rw [triangularGammaRegular_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change s ≠ 0 at hs
  rw [triangularGammaTrace_regularization, if_neg hs]

/-- Subtracting the double pole leaves no residue at the origin. -/
theorem triangularGammaTrace_no_simple_pole (a b c : ℝ) :
    Tendsto (fun s : ℂ => s*(triangularGammaTrace a b c s -
      (triangularPoleCoefficient a b c : ℂ)/s^2)) (𝓝[≠] 0) (𝓝 0) := by
  have ht := (triangularGammaRegular_hasDerivAt_zero a b c).tendsto_slope_zero
  simp only [triangularGammaRegular_zero, zero_add, smul_eq_mul] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change s ≠ 0 at hs
  have h := triangularGammaTrace_regularization a b c s
  rw [if_neg hs] at h
  rw [← h]
  field_simp

#print axioms triangularGammaTrace_phase_integral
#print axioms balancedGammaRatio_hasDerivAt_zero
#print axioms triangularGammaTrace_regularization
#print axioms triangularGammaTrace_double_pole
#print axioms triangularGammaTrace_no_simple_pole

end
end GaloisForLFunctions.BiScaleUncertainty.Spectral
