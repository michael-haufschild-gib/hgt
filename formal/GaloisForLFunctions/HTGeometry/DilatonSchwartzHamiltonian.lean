import GaloisForLFunctions.HTGeometry.DilatonSchwartzTransform
import GaloisForLFunctions.HTGeometry.SchwartzSmoothMultiplierApproximation

/-!
# A polynomial family of dilaton Hamiltonians on Schwartz space

For the effective potential of arXiv:2608.21406v1, equation (20), construct
continuous differential operators on complex Schwartz space and prove the
factorization into mutually adjoint first-order operators. Integration by parts
is discharged by the actual Schwartz functions. The energy is a squared L2
norm, so every polynomial log-weight excludes a neutral growing eigenmode.
The conclusion also holds for the original weighted radial equation through
the exact half-density conjugation. All mode claims concern this Schwartz domain.
-/

noncomputable section
open Polynomial MeasureTheory
open scoped SchwartzMap
namespace GaloisForLFunctions.HTGeometry

private theorem dilatonPolynomial_temperate (H : ℝ[X]) :
    Function.HasTemperateGrowth (fun x : ℝ => ((H.eval x : ℝ) : ℂ)) := by
  exact Complex.ofRealCLM.hasTemperateGrowth.comp (SchwartzMap.polynomial_eval_hasTemperateGrowth H)

def dilatonDriftCLM (H : ℝ[X]) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (1 / 2 : ℂ) • SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => ((H.derivative.eval x : ℝ) : ℂ))

def dilatonSuperchargeCLM (H : ℝ[X]) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := derivSCLM - dilatonDriftCLM H

def dilatonAdjointChargeCLM (H : ℝ[X]) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := -derivSCLM - dilatonDriftCLM H

def dilatonHamiltonianCLM (H : ℝ[X]) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (dilatonAdjointChargeCLM H).comp (dilatonSuperchargeCLM H)

theorem dilatonDriftCLM_apply (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatonDriftCLM H ψ x = ((H.derivative.eval x : ℝ) : ℂ) / 2 * ψ x := by
  rw [dilatonDriftCLM, _root_.smul_apply, _root_.smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply (dilatonPolynomial_temperate H.derivative)]
  simp only [smul_eq_mul]
  ring

theorem dilatonSuperchargeCLM_apply (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatonSuperchargeCLM H ψ x = deriv ψ x - ((H.derivative.eval x : ℝ) : ℂ) / 2 * ψ x := by
  change derivSCLM ψ x - dilatonDriftCLM H ψ x = _
  rw [derivSCLM_apply, dilatonDriftCLM_apply]

theorem dilatonAdjointChargeCLM_apply (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatonAdjointChargeCLM H ψ x = -deriv ψ x - ((H.derivative.eval x : ℝ) : ℂ) / 2 * ψ x := by
  change -derivSCLM ψ x - dilatonDriftCLM H ψ x = _
  rw [derivSCLM_apply, dilatonDriftCLM_apply]

theorem dilatonSuperchargeCLM_derivative (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (dilatonSuperchargeCLM H ψ : ℝ → ℂ)
      (deriv (deriv ψ) x - ((H.derivative.derivative.eval x : ℝ) : ℂ) / 2 * ψ x -
        ((H.derivative.eval x : ℝ) : ℂ) / 2 * deriv ψ x) x := by
  have hd : HasDerivAt (deriv ψ) (deriv (deriv ψ) x) x :=
    (SchwartzMap.derivCLM ℂ ℂ ψ).hasDerivAt x
  have h := hd.sub (((H.derivative.hasDerivAt x).ofReal_comp.div_const 2).mul (ψ.hasDerivAt x))
  rw [show (dilatonSuperchargeCLM H ψ : ℝ → ℂ) = _ from funext (dilatonSuperchargeCLM_apply H ψ)]
  exact h.congr_deriv (by ring)

theorem dilatonHamiltonianCLM_apply (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatonHamiltonianCLM H ψ x = -deriv (deriv ψ) x + (dilatonPotential H x : ℂ) * ψ x := by
  rw [dilatonHamiltonianCLM, ContinuousLinearMap.comp_apply, dilatonAdjointChargeCLM_apply,
    (dilatonSuperchargeCLM_derivative H ψ x).deriv, dilatonSuperchargeCLM_apply]
  simp only [dilatonPotential, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  ring

theorem dilatonSuperchargeCLM_conj (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) :
    SchwartzMap.conjSLM (dilatonSuperchargeCLM H ψ) = dilatonSuperchargeCLM H (SchwartzMap.conjSLM ψ) := by
  have hb : SchwartzMap.conjSLM (dilatonDriftCLM H ψ) = dilatonDriftCLM H (SchwartzMap.conjSLM ψ) := by
    ext x
    simp only [SchwartzMap.conjSLM_apply, dilatonDriftCLM_apply, map_mul, map_div₀,
      Complex.conj_ofReal, map_ofNat]
  change SchwartzMap.conjSLM (derivSCLM ψ - dilatonDriftCLM H ψ) =
    derivSCLM (SchwartzMap.conjSLM ψ) - dilatonDriftCLM H (SchwartzMap.conjSLM ψ)
  rw [map_sub, conjSLM_derivSCLM, hb]

theorem dilatonCharges_pair_adjoint (H : ℝ[X]) (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair f (dilatonAdjointChargeCLM H g) = schwartzPair (dilatonSuperchargeCLM H f) g := by
  have hd : schwartzPair f (derivSCLM g) = -schwartzPair (derivSCLM f) g := by
    simpa only [schwartzPair_eq_integral, derivSCLM_apply] using
      SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul f g
  have hb : schwartzPair f (dilatonDriftCLM H g) = schwartzPair (dilatonDriftCLM H f) g := by
    rw [schwartzPair_eq_integral, schwartzPair_eq_integral]
    apply integral_congr_ae
    filter_upwards with x
    simp only [dilatonDriftCLM_apply]
    ring
  change schwartzPair f (-derivSCLM g - dilatonDriftCLM H g) =
    schwartzPair (derivSCLM f - dilatonDriftCLM H f) g
  rw [show -derivSCLM g - dilatonDriftCLM H g =
      (-1 : ℂ) • derivSCLM g + (-1 : ℂ) • dilatonDriftCLM H g by module,
    show derivSCLM f - dilatonDriftCLM H f =
      derivSCLM f + (-1 : ℂ) • dilatonDriftCLM H f by module,
    schwartzPair_add_right, schwartzPair_add_left, schwartzPair_smul_right,
    schwartzPair_smul_right, schwartzPair_smul_left, hd, hb]
  ring

/-- Every polynomial dilaton potential has an exact nonnegative Schwartz energy. -/
theorem dilatonHamiltonian_energy (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) :
    schwartzPair (SchwartzMap.conjSLM ψ) (dilatonHamiltonianCLM H ψ) =
      ((‖(dilatonSuperchargeCLM H ψ).toLp 2 (volume : Measure ℝ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [dilatonHamiltonianCLM, ContinuousLinearMap.comp_apply, dilatonCharges_pair_adjoint,
    ← dilatonSuperchargeCLM_conj, schwartzPair_conj_self]

/-- No polynomial dilaton weight creates a neutral growing mode on this Schwartz domain. -/
theorem dilatonHamiltonian_no_growing_mode (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (u s : ℝ) :
    dilatonHamiltonianCLM H ψ = growingFrequency u s ^ 2 • ψ ↔ ψ = 0 := by
  constructor
  · intro h
    have hp := congrArg (fun f => schwartzPair (SchwartzMap.conjSLM ψ) f) h
    rw [dilatonHamiltonian_energy, schwartzPair_smul_right, schwartzPair_conj_self] at hp
    have hz := (growingFrequency_energy_balance u s
      ‖(dilatonSuperchargeCLM H ψ).toLp 2 (volume : Measure ℝ)‖
      ‖ψ.toLp 2 (volume : Measure ℝ)‖ 0).mp (by simpa using hp)
    apply SchwartzMap.injective_toLp 2 (volume : Measure ℝ)
    have hzero := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_zero
    rw [SchwartzMap.toLpCLM_apply] at hzero
    exact (norm_eq_zero.mp hz.2).trans hzero.symm
  · rintro rfl
    simp

/-- Frequency exclusion transported back to the actual weighted radial equation. -/
theorem dilaton_neutral_radial_no_growing_mode (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) (u s : ℝ) :
    (∀ x, dilatonRadialOperator H (dilatonUndressed H ψ) x +
      growingFrequency u s ^ 2 * dilatonUndressed H ψ x = 0) ↔ ψ = 0 := by
  constructor
  · intro h
    apply (dilatonHamiltonian_no_growing_mode H ψ u s).mp
    ext x
    have hx := h x
    rw [dilatonRadialOperator_conjugation, dilatonUndressed] at hx
    have hn : dilatonGauge H x *
        (-dilatonHamiltonianCLM H ψ x + growingFrequency u s ^ 2 * ψ x) = 0 := by
      rw [dilatonHamiltonianCLM_apply]
      convert hx using 1
      ring
    have hz := (mul_eq_zero.mp hn).resolve_left (dilatonGauge_ne_zero H x)
    change dilatonHamiltonianCLM H ψ x = growingFrequency u s ^ 2 * ψ x
    linear_combination -hz
  · rintro rfl x
    rw [show dilatonUndressed H 0 = 0 by funext y; simp [dilatonUndressed]]
    simp [dilatonRadialOperator]

end GaloisForLFunctions.HTGeometry
