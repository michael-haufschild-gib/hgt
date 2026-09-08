import GaloisForLFunctions.RHTower.SelbergMaassTraceEnergy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A periodic phase test for scalar-norm energy reconstruction

Explicit smooth period-one complex fields have identical scalar squared norms but
strictly different actual derivative energies. Their scalar-amplitude derivative is
zero while the discarded phase energy is exact. This disproves norm-only energy
reconstruction for smooth periodic fields.

These toy fields are not claimed to be Maass eigenforms or cusp forms. In particular,
this theorem does not contradict the actual Maass identity that recovers gradient
energy from trace derivatives together with the eigenvalue. The source-specific
positive survivor is the exact radial/residual decomposition in SelbergMaassTraceRadial.
-/

open Complex
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergScalarPhaseToy
open SelbergMaassTraceEnergy
noncomputable section

/-- An explicit complex pure-phase chart with real frequency. -/
def phaseField (c : ℝ) (z : ℂ) : ℂ := Complex.exp (Complex.I * ((c * z.re : ℝ) : ℂ))

/-- The explicit pure-phase field is smooth. -/
theorem phaseField_contDiff (c : ℝ) : ContDiff ℝ ⊤ (phaseField c) := by
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul Complex.reCLM.contDiff))).cexp

/-- Every pure-phase field has the same constant squared norm. -/
theorem phaseField_normSq (c : ℝ) (z : ℂ) : normSq (phaseField c z) = 1 := by
  rw [phaseField, normSq_eq_norm_sq, norm_exp_I_mul_ofReal]
  norm_num

/-- The actual horizontal phase derivative retains its frequency. -/
theorem phaseField_dir (c : ℝ) (z : ℂ) :
    dir 1 (phaseField c) z = Complex.I * (c : ℂ) * phaseField c z := by
  have hR := (Complex.reCLM.hasFDerivAt (x := z)).const_mul c
  have hC := Complex.ofRealCLM.hasFDerivAt.comp z hR
  have h := (hC.const_mul Complex.I).cexp
  have hv := congrArg (fun L => L 1) h.fderiv
  change dir 1 (phaseField c) z = _ at hv
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    Function.comp_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply, one_re, mul_one] at hv
  rw [hv]
  unfold phaseField
  ring

/-- The actual horizontal derivative energy is exactly the squared frequency. -/
theorem phaseField_energy (c : ℝ) (z : ℂ) : normSq (dir 1 (phaseField c) z) = c ^ 2 := by
  rw [phaseField_dir, normSq_mul, normSq_mul, normSq_I, normSq_ofReal, phaseField_normSq]
  ring

/-- The entire scalar-amplitude function is constant. -/
theorem phaseField_scalar_amplitude (c : ℝ) :
    (fun z => Real.sqrt (normSq (phaseField c z))) = (fun _ => (1 : ℝ)) := by
  funext z
  rw [phaseField_normSq, Real.sqrt_one]

/-- The actual scalar-amplitude derivative is identically zero. -/
theorem phaseField_amplitude_dir (c : ℝ) (z : ℂ) :
    dir 1 (fun w => Real.sqrt (normSq (phaseField c w))) z = 0 := by
  rw [phaseField_scalar_amplitude]
  simp [dir]

/-- Integral frequency gives actual period one in the horizontal coordinate. -/
theorem integer_phase_periodic (n : ℤ) (z : ℂ) :
    phaseField (2 * Real.pi * n) (z + 1) = phaseField (2 * Real.pi * n) z := by
  unfold phaseField
  have he : Complex.I * (((2 * Real.pi * (n : ℝ)) * (z + 1).re : ℝ) : ℂ) =
      Complex.I * (((2 * Real.pi * (n : ℝ)) * z.re : ℝ) : ℂ) +
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp only [add_re, one_re]
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Closed smooth periodic counterexample to energy reconstruction from the scalar squared norm alone. -/
theorem scalar_trace_does_not_determine_energy :
    ∃ F G : ℂ → ℂ, ContDiff ℝ ⊤ F ∧ ContDiff ℝ ⊤ G ∧
      (∀ z, F (z + 1) = F z) ∧ (∀ z, G (z + 1) = G z) ∧
      (∀ z, normSq (F z) = normSq (G z)) ∧
      (∀ z, normSq (dir 1 F z) < normSq (dir 1 G z)) := by
  refine ⟨phaseField (2 * Real.pi * (0 : ℤ)), phaseField (2 * Real.pi * (1 : ℤ)),
    phaseField_contDiff _, phaseField_contDiff _, integer_phase_periodic 0,
    integer_phase_periodic 1, ?_, ?_⟩
  · intro z
    rw [phaseField_normSq, phaseField_normSq]
  · intro z
    rw [phaseField_energy, phaseField_energy]
    simpa only [Int.cast_zero, Int.cast_one, mul_zero, mul_one, zero_pow (by norm_num : 2 ≠ 0)] using
      (sq_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos))

end
end GaloisForLFunctions.RHTower.SelbergScalarPhaseToy
