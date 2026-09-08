import GaloisForLFunctions.HTGeometry.FokasLenellsPlaneWaves

/-!
# Charged-wave Wronskians and actual Noether flux

Applies equations (23)--(30) and Appendix A of arXiv:2608.21406v1 to the
corpus's FDNLS phases, Fokas--Lenells plane waves, and retimed NLS plane wave.
The current and Wronskian use actual Lean derivatives. Exact two-channel
waves solve the radial wave equation, their interference cancels from the
current, and the current is constant for arbitrary complex channel amplitudes.
These identities do not assume a scattering solution or boundary data.
-/

noncomputable section
open Complex Real
namespace GaloisForLFunctions.HTGeometry

/-- The spatial Noether flux, with its derivative taken by Lean. -/
def complexRadialFlux (ψ : ℝ → ℂ) (x : ℝ) : ℝ :=
  ((starRingEnd ℂ) (ψ x) * deriv ψ x).im

def complexRadialWronskian (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) (ψ x) * deriv ψ x - ψ x * (starRingEnd ℂ) (deriv ψ x)

/-- Equation (24) and Appendix A: the Wronskian is twice `i` times the real current. -/
theorem complexRadialWronskian_eq_flux (ψ : ℝ → ℂ) (x : ℝ) :
    complexRadialWronskian ψ x = 2 * I * (complexRadialFlux ψ x : ℂ) := by
  apply Complex.ext <;> simp [complexRadialWronskian, complexRadialFlux, Complex.mul_re, Complex.mul_im]
  ring

/-- Opposite-frequency interference contributes no net current. -/
theorem complexOppositeChannelFlux (u v : ℂ) (k : ℝ) :
    ((starRingEnd ℂ) (u + v) * (I * (k : ℂ) * (v - u))).im = k * (normSq v - normSq u) := by
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- Exact incoming and outgoing channels in the corpus's FDNLS phase convention. -/
def chargedChannelWave (a b : ℂ) (k x : ℝ) : ℂ :=
  a * FDNLS.staggerPhase k x + b * FDNLS.staggerPhase (-k) x

theorem chargedChannelWave_derivative (a b : ℂ) (k x : ℝ) :
    HasDerivAt (chargedChannelWave a b k)
      (I * (k : ℂ) * (b * FDNLS.staggerPhase (-k) x - a * FDNLS.staggerPhase k x)) x := by
  have h := ((FDNLS.hasDerivAt_staggerPhase k x).const_mul a).add
    ((FDNLS.hasDerivAt_staggerPhase (-k) x).const_mul b)
  apply h.congr_deriv
  simp only [Complex.ofReal_neg]
  ring

theorem chargedChannelWave_second_derivative (a b : ℂ) (k x : ℝ) :
    HasDerivAt (deriv (chargedChannelWave a b k))
      (-(k : ℂ) ^ 2 * chargedChannelWave a b k x) x := by
  have he : deriv (chargedChannelWave a b k) = fun y =>
      I * (k : ℂ) * (b * FDNLS.staggerPhase (-k) y - a * FDNLS.staggerPhase k y) :=
    funext (fun y => (chargedChannelWave_derivative a b k y).deriv)
  rw [he]
  have h := (((FDNLS.hasDerivAt_staggerPhase (-k) x).const_mul b).sub
    ((FDNLS.hasDerivAt_staggerPhase k x).const_mul a)).const_mul (I * (k : ℂ))
  apply h.congr_deriv
  simp only [chargedChannelWave, Complex.ofReal_neg]
  linear_combination (I_sq) * ((k : ℂ) ^ 2 * (a * FDNLS.staggerPhase k x + b * FDNLS.staggerPhase (-k) x))

/-- The channels solve the actual constant-coefficient radial wave equation. -/
theorem chargedChannelWave_wave_equation (a b : ℂ) (k x : ℝ) :
    deriv (deriv (chargedChannelWave a b k)) x + (k : ℂ) ^ 2 * chargedChannelWave a b k x = 0 := by
  rw [(chargedChannelWave_second_derivative a b k x).deriv]
  ring

/-- Equation (29), with arbitrary complex incident and reflected amplitudes. -/
theorem chargedChannelWave_flux (a b : ℂ) (k x : ℝ) :
    complexRadialFlux (chargedChannelWave a b k) x = k * (‖b‖ ^ 2 - ‖a‖ ^ 2) := by
  rw [complexRadialFlux, (chargedChannelWave_derivative a b k x).deriv, chargedChannelWave,
    complexOppositeChannelFlux]
  simp only [normSq_eq_norm_sq, norm_mul, FDNLS.norm_staggerPhase, mul_one]

theorem chargedChannelWave_wronskian (a b : ℂ) (k x : ℝ) :
    complexRadialWronskian (chargedChannelWave a b k) x =
      2 * I * ((k * (‖b‖ ^ 2 - ‖a‖ ^ 2) : ℝ) : ℂ) := by
  rw [complexRadialWronskian_eq_flux, chargedChannelWave_flux]

theorem chargedChannelWave_flux_conserved (a b : ℂ) (k x : ℝ) :
    HasDerivAt (complexRadialFlux (chargedChannelWave a b k)) 0 x := by
  simp only [funext (chargedChannelWave_flux a b k)]
  exact hasDerivAt_const x _

/-- Actual Fokas--Lenells waves carry the expected positive momentum current. -/
theorem fokasLenells_planeWave_radialFlux (a κ t x : ℝ) :
    complexRadialFlux (FokasLenells.planeWave a κ t) x = Real.exp κ * a ^ 2 := by
  have he : FokasLenells.planeWave a κ t =
      chargedChannelWave ((a : ℂ) * FDNLS.staggerPhase (FokasLenells.waveFrequency a κ) t) 0 (-Real.exp κ) := by
    funext y
    simp only [FokasLenells.planeWave, FokasLenells.waveNumber, chargedChannelWave, zero_mul, add_zero]
    ring
  rw [he, chargedChannelWave_flux]
  simp [FDNLS.norm_staggerPhase, sq_abs]

/-- The retimed NLS plane wave inherits the same unit current. -/
theorem retimed_nls_planeWave_radialFlux (t x : ℝ) :
    complexRadialFlux (fun y => DispersivePDE.nlsPlaneWave (-2 * t) y) x = 1 := by
  have he : (fun y => DispersivePDE.nlsPlaneWave (-2 * t) y) = FokasLenells.planeWave 1 0 t :=
    funext (fun y => (FokasLenells.planeWave_eq_retimed_nls t y).symm)
  rw [he, fokasLenells_planeWave_radialFlux]
  norm_num

end GaloisForLFunctions.HTGeometry
