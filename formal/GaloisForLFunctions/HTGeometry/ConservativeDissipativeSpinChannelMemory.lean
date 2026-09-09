import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinInstrumentPinching
import GaloisForLFunctions.HTGeometry.MarkovianReturnRecovery

/-!
# Information revival in one complete spin instrument

Application of Schaffer–Exl, arXiv:2609.04530, to the existing quantum dynamical
semigroup framework. The previously constructed two-outcome spin filter has forgotten
coherence `cos(t)/cosh(a²t)`. It erases an explicit pair of physical states at a
quarter turn and restores their distinction at a half turn. Thus even arbitrary
postprocessing, and in particular a dynamical semigroup, cannot implement this
particular forgotten-outcome family. The obstruction concerns this completion;
an amplitude-damping completion of the conditional trajectory is constructed separately.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- The explicit channel obtained by forgetting the two spin-filter outcomes. -/
def spinForgottenChannel (a t : ℝ) : FiniteRectangularKrausChannel 2 2 (Fin 2) :=
  spinFilterChannel (Complex.exp (spinPlaneRate a * (t : ℂ)))

/-- The coherence of the forgotten channel in elementary real functions. -/
theorem spinFilterCoherence_flow (a t : ℝ) :
    spinFilterCoherence (Complex.exp (spinPlaneRate a * (t : ℂ))) =
      2 * Real.exp (-a ^ 2 * t) * Real.cos t / (1 + Real.exp (-2 * a ^ 2 * t)) := by
  have hn : ‖Complex.exp (spinPlaneRate a * (t : ℂ))‖ ^ 2 = Real.exp (-2 * a ^ 2 * t) := by
    simpa only [spinPlaneFlow, mul_one, norm_one, one_pow] using spinPlaneFlow_norm_sq a 1 t
  have hr : (spinPlaneRate a * (t : ℂ)).re = -a ^ 2 * t := by
    simp only [spinPlaneRate, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.I_re, Complex.sub_im, Complex.ofReal_im, Complex.I_im]
    ring
  have hi : (spinPlaneRate a * (t : ℂ)).im = -t := by
    simp only [spinPlaneRate, Complex.mul_im, Complex.sub_re, Complex.ofReal_re,
      Complex.I_re, Complex.sub_im, Complex.ofReal_im, Complex.I_im]
    ring
  rw [spinFilterCoherence_eq, hn, Complex.exp_re, hr, hi, Real.cos_neg]
  ring

/-- Hyperbolic/circular factorization of the complete channel's memory profile. -/
theorem spinFilterCoherence_flow_cosh (a t : ℝ) :
    spinFilterCoherence (Complex.exp (spinPlaneRate a * (t : ℂ))) =
      Real.cos t / Real.cosh (a ^ 2 * t) := by
  rw [spinFilterCoherence_flow, Real.cosh_eq]
  have he := Real.exp_ne_zero (a ^ 2 * t)
  have htwo : Real.exp (-2 * a ^ 2 * t) = (Real.exp (a ^ 2 * t))⁻¹ ^ 2 := by
    rw [show -2 * a ^ 2 * t = -(a ^ 2 * t + a ^ 2 * t) by ring,
      Real.exp_neg, Real.exp_add]
    simp only [_root_.mul_inv_rev, pow_two]
  rw [htwo, show -a ^ 2 * t = -(a ^ 2 * t) by ring, Real.exp_neg]
  have hd : Real.exp (a ^ 2 * t) + (Real.exp (a ^ 2 * t))⁻¹ ≠ 0 := by positivity
  have hd' : 1 + (Real.exp (a ^ 2 * t))⁻¹ ^ 2 ≠ 0 := by positivity
  field_simp

/-- At a quarter precession turn the complete channel is exactly the existing pinching. -/
theorem spinForgottenChannel_quarter_turn (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinForgottenChannel a (Real.pi / 2)).evolveMatrix ρ = spinZPinch ρ := by
  rw [spinForgottenChannel, spinFilterChannel_dephasing, spinFilterCoherence_flow_cosh,
    Real.cos_pi_div_two, zero_div, Complex.ofReal_zero, zero_smul, sub_zero, one_smul, zero_add]

/-- At a half turn the restored coherence multiplier is strictly negative for every damping amplitude. -/
theorem spinForgottenChannel_half_turn_coherence_neg (a : ℝ) :
    spinFilterCoherence (Complex.exp (spinPlaneRate a * (Real.pi : ℂ))) < 0 := by
  rw [spinFilterCoherence_flow_cosh, Real.cos_pi]
  exact div_neg_of_neg_of_pos (by linarith) (Real.cosh_pos _)

/-- The two equatorial pure densities have the same measured populations. -/
theorem spinChartDensity_equatorial_pinch : spinZPinch (spinChartDensity 1) =
    spinZPinch (spinChartDensity (-1)) := by
  rw [spinZPinch_entries, spinZPinch_entries, spinChartDensity_entries, spinChartDensity_entries]
  simp [Matrix.smul_apply]

/-- An exactly erased physical input distinction reappears at the half turn. -/
theorem spinForgottenChannel_half_turn_separates (a : ℝ) :
    (spinForgottenChannel a Real.pi).evolveMatrix (spinChartDensity 1) ≠
      (spinForgottenChannel a Real.pi).evolveMatrix (spinChartDensity (-1)) := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  simp only [spinForgottenChannel, spinFilterChannel_entries] at he
  rw [spinChartDensity_entries, spinChartDensity_entries] at he
  have hq := spinForgottenChannel_half_turn_coherence_neg a
  have hzero : (spinFilterCoherence (Complex.exp (spinPlaneRate a * (Real.pi : ℂ))) : ℂ) = 0 := by
    simp [Matrix.smul_apply] at he
    linear_combination he
  have hr : spinFilterCoherence (Complex.exp (spinPlaneRate a * (Real.pi : ℂ))) = 0 := by
    exact_mod_cast hzero
  linarith

/-- Even arbitrary deterministic postprocessing cannot reconstruct the later channel from the erased stage. -/
theorem spinForgottenChannel_no_postprocessing (a : ℝ) :
    ¬ ∃ F : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ,
      ∀ z : ℂ, F ((spinForgottenChannel a (Real.pi / 2)).evolveMatrix (spinChartDensity z)) =
        (spinForgottenChannel a Real.pi).evolveMatrix (spinChartDensity z) := by
  rintro ⟨F, hF⟩
  apply spinForgottenChannel_half_turn_separates a
  rw [← hF 1, ← hF (-1), spinForgottenChannel_quarter_turn,
    spinForgottenChannel_quarter_turn, spinChartDensity_equatorial_pinch]

/-- The forgotten channel family cannot be any quantum dynamical semigroup on its physical inputs. -/
theorem spinForgottenChannel_no_dynamicalSemigroup (a : ℝ) :
    ¬ ∃ S : DynamicalSemigroup (Fin 2),
      ∀ (t : NNReal) (z : ℂ), (S.ch t).map (spinChartDensity z) =
        (spinForgottenChannel a t).evolveMatrix (spinChartDensity z) := by
  rintro ⟨S, hS⟩
  let q : NNReal := ⟨Real.pi / 2, le_of_lt (by positivity)⟩
  have ht : ((q + q : NNReal) : ℝ) = Real.pi := by
    change Real.pi / 2 + Real.pi / 2 = Real.pi
    ring
  apply spinForgottenChannel_no_postprocessing a
  refine ⟨(S.ch q).map, fun z => ?_⟩
  have hq : (q : ℝ) = Real.pi / 2 := rfl
  rw [← hq, ← hS q z]
  change ((S.ch q * S.ch q).map (spinChartDensity z)) = _
  rw [← S.ch_add, hS, ht]

end
end GaloisForLFunctions.HTGeometry.SchafferExl
