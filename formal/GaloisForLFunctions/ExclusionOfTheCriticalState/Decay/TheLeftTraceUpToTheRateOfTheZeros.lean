import GaloisForLFunctions.ExclusionOfTheCriticalState.Decay.LogarithmicMomentsOnTheReflectedLines
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateHasSquaredLogarithmicEnergyOnTheLinesOfItsDecay
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheExplicitFormulaHoldsOnTheEnergyDomainAgainstProbes
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroCauchyTransformIsSquareIntegrableUpToALogarithm

/-!
# The left trace up to the rate of the zeros

On the reflected zero-free strip the continued state is the sum of the reflected
Euler multiplier, the two wall terms, and the truncated prime tail. Each term
has finite square mass with respect to unweighted Lebesgue measure.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The squared absolute value of the Cauchy kernel on an off-centre line is a
constant multiple of the Poisson kernel. -/
private theorem memLp_div_line {f : ℝ → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ t, ‖f t‖ ≤ C) {b : ℝ} (hb : b ≠ 0) :
    MemLp (fun t : ℝ => f t / ((b:ℂ)+(t:ℂ)*I)) 2 volume := by
  have hn (t : ℝ) : (b:ℂ)+(t:ℂ)*I ≠ 0 := by
    intro e
    exact hb (by simpa using congrArg Complex.re e)
  have hm : Continuous fun t : ℝ => f t / ((b:ℂ)+(t:ℂ)*I) := hf.div (by fun_prop) hn
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hb' := abs_pos.mpr hb
  apply (((integrable_halfPlanePoisson hb').const_mul (Real.pi/|b|)).const_mul (C^2)).mono'
    (hm.norm.pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  change ‖‖f t / ((b:ℂ)+(t:ℂ)*I)‖^2‖ ≤ C^2 * (Real.pi/|b| * halfPlanePoisson |b| t)
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_div, div_pow, pi_div_mul_halfPlanePoisson hb',
    sq_abs, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_I_re, Complex.mul_I_im, neg_zero, add_zero, zero_add]
  rw [div_eq_mul_inv, ← sq, ← sq]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC t) 2) (by positivity)

/-- On `Θ - 1/2 < c < 1/2`, the continuation at `-8-c+it` has an ordinary
square-integrable trace. No heat factor or reciprocal logarithm is needed. -/
theorem integrable_norm_sq_stateMeromorphic_reflected_line {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ}
    (hc : zetaZeroAbscissa - 1/2 < c) (hc2 : c < 1/2) :
    Integrable fun t : ℝ =>
      ‖stateMeromorphic W₀ F (((-c:ℝ):ℂ)+(t:ℂ)*I-8)‖^2 := by
  let κ := zetaZeroAbscissa - 1/2
  have hκ : 0 ≤ κ := sub_nonneg.mpr half_le_zetaZeroAbscissa
  have hc0 : 0 < c := lt_of_le_of_lt hκ hc
  have hz (q : XiZeroCopy) : (centredZero q).re ≤ κ := by
    simpa [centredZero, κ] using sub_le_sub_right
      (re_le_zetaZeroAbscissa (riemannZeta_xiZeroCopy_eq_zero q)) (1/2)
  let p := fun t : ℝ => ((-c:ℝ):ℂ)+(t:ℂ)*I
  let r := fun t : ℝ => (c:ℂ)-(t:ℂ)*I
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hr : Continuous r := by dsimp [r]; fun_prop
  have hpR (t) : (p t).re = -c := by simp [p]
  have hrR (t) : (r t).re = c := by simp [r]
  have hpr (t) : -p t = r t := by dsimp [p, r]; push_cast; ring
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  let L := negativeHalfLineLaplace (cx F)
  have hL : Continuous fun t => L (p t) := continuous_iff_continuousAt.mpr fun t =>
    (differentiableAt_laplace hd (by rw [hpR]; linarith)).continuousAt.comp hp.continuousAt
  have hN : Continuous fun t => zetaRegularLogDeriv (1/2+r t) :=
    continuous_iff_continuousAt.mpr fun t =>
      (differentiableAt_zetaRegularLogDeriv_half_add hκ hz (by rwa [hrR] : κ < (r t).re)
        ).continuousAt.comp hr.continuousAt
  have euler := (memLp_two_iff_integrable_sq_norm (hN.mul hL).aestronglyMeasurable).mpr
    (integrable_norm_sq_reflected_euler_mul_laplace hW ht hF hc (by linarith))
  have hJ : Continuous fun t => levyHeadTerm F (p t) :=
    (differentiableOn_levyHeadTerm hd).continuousOn.comp_continuous hp fun t =>
      (by change (p t).re < _; rw [hpR]; linarith)
  have hT : Continuous fun t => stateTail F (p t) :=
    (differentiableOn_stateTail_strip hd).continuousOn.comp_continuous hp fun t =>
      (by change -4 < (p t).re; rw [hpR]; linarith)
  have head := (memLp_two_iff_integrable_sq_norm hJ.aestronglyMeasurable).mpr
    (integrable_norm_sq_levyHeadTerm_line hd (neg_lt_zero.mpr hc0))
  have tail := (memLp_two_iff_integrable_sq_norm hT.aestronglyMeasurable).mpr
    (integrable_norm_sq_stateTail_line_of_neg_four_lt hd (by linarith : -4 < -c))
  have slope := memLp_div_line (hL.sub continuous_const)
    (C := transformMass F (-c) + ‖L (-(1/2))‖)
    (fun t => (norm_sub_le _ _).trans (add_le_add_right
      (norm_laplace_le_transformMass hd (by linarith : -4 < -c) (hpR t).ge) _))
    (b := -c+1/2) (by linarith)
  have pole := memLp_div_line (continuous_const (y := L (1/2))) (fun _ => le_rfl)
    (b := -c-1/2) (by linarith)
  have hsum := (((euler.neg.sub slope).add head).sub tail).add pole
  have heq (t : ℝ) : stateMeromorphic W₀ F (p t - 8) =
      (-((-(zetaRegularLogDeriv (1/2+r t)*L (p t)) -
        (L (p t)-L (-(1/2)))/(((-c+1/2:ℝ):ℂ)+(t:ℂ)*I) + levyHeadTerm F (p t) -
        stateTail F (p t)) + L (1/2)/(((-c-1/2:ℝ):ℂ)+(t:ℂ)*I))) /
        criticalAliasCoefficient W₀ := by
    have hs : (p t) ≠ -(1/2) := by
      intro e
      have h := congrArg Complex.re e
      rw [hpR] at h
      norm_num at h
      linarith
    have e : 1/2 - p t = 1/2+r t := by rw [sub_eq_add_neg, hpr]
    have hxi : xi (1/2 + p t) ≠ 0 := by
      rw [← xi_half_sub_eq, e]
      intro h
      obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h
      have he : centredZero q = r t := by unfold centredZero; rw [hq]; ring
      have hu := hz q
      rw [he, hrR] at hu
      exact hc.not_ge hu
    unfold stateMeromorphic
    rw [sub_add_cancel, globalRemainder_eq_stripRemainder hd
      (by rw [hpR]; linarith) (by rw [hpR]; linarith) hxi]
    unfold stripRemainder
    rw [e, logDeriv_zetaEntire_half_add_eq hκ hz (by rwa [hrR]) (by rwa [hrR]),
      dslope_of_ne _ hs, slope_def_field]
    dsimp [L, p]
    push_cast
    ring_nf
  have htrace := hsum.neg.const_mul ((criticalAliasCoefficient W₀ : ℂ))⁻¹
  refine ((memLp_two_iff_integrable_sq_norm htrace.aestronglyMeasurable).mp htrace).congr
    (Eventually.of_forall fun t => ?_)
  change ‖_ * (-_)‖^2 = ‖stateMeromorphic W₀ F (p t-8)‖^2
  rw [heq, div_eq_mul_inv, mul_comm]

#print axioms integrable_norm_sq_stateMeromorphic_reflected_line

end GaloisForLFunctions.ExclusionOfTheCriticalState
