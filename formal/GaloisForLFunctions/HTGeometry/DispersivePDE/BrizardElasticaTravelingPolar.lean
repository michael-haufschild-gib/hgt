import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaNLS
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Traveling polar reduction of NLS

Paper equations (43)--(46) are formalized as a reusable compiler.  A twice-differentiable real
amplitude and phase generate a derivative-certified complex traveling jet.  Its NLS residual splits
exactly into the paper's real and imaginary scalar balances.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Scalar profile data needed by the traveling Hasimoto ansatz. -/
structure TravelingPolarProfile where
  amplitude : ℝ → ℝ
  amplitude₁ : ℝ → ℝ
  amplitude₂ : ℝ → ℝ
  phase : ℝ → ℝ
  phase₁ : ℝ → ℝ
  phase₂ : ℝ → ℝ
  amplitude_deriv : ∀ z, HasDerivAt amplitude (amplitude₁ z) z
  amplitude₁_deriv : ∀ z, HasDerivAt amplitude₁ (amplitude₂ z) z
  phase_deriv : ∀ z, HasDerivAt phase (phase₁ z) z
  phase₁_deriv : ∀ z, HasDerivAt phase₁ (phase₂ z) z

noncomputable def polarPhase (P : TravelingPolarProfile) (z : ℝ) : ℂ :=
  Complex.exp (Complex.I * (P.phase z : ℂ))

noncomputable def polarProfile (P : TravelingPolarProfile) (z : ℝ) : ℂ :=
  (P.amplitude z : ℂ) * polarPhase P z

noncomputable def polarProfile₁ (P : TravelingPolarProfile) (z : ℝ) : ℂ :=
  polarPhase P z *
    ((P.amplitude₁ z : ℂ) +
      Complex.I * (P.amplitude z * P.phase₁ z : ℝ))

noncomputable def polarProfile₂ (P : TravelingPolarProfile) (z : ℝ) : ℂ :=
  polarPhase P z *
    (((P.amplitude₂ z - P.amplitude z * P.phase₁ z ^ 2 : ℝ) : ℂ) +
      Complex.I *
        ((2 * P.amplitude₁ z * P.phase₁ z +
          P.amplitude z * P.phase₂ z : ℝ) : ℂ))

theorem norm_polarPhase (P : TravelingPolarProfile) (z : ℝ) :
    ‖polarPhase P z‖ = 1 := by
  rw [polarPhase, Complex.norm_exp]
  simp

theorem norm_polarProfile_sq (P : TravelingPolarProfile) (z : ℝ) :
    ‖polarProfile P z‖ ^ 2 = P.amplitude z ^ 2 := by
  rw [polarProfile, norm_mul, norm_polarPhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

theorem hasDerivAt_polarPhase (P : TravelingPolarProfile) (z : ℝ) :
    HasDerivAt (polarPhase P)
      (polarPhase P z * (Complex.I * (P.phase₁ z : ℂ))) z := by
  have hinner := (P.phase_deriv z).ofReal_comp.const_mul Complex.I
  have h := (Complex.hasDerivAt_exp (Complex.I * (P.phase z : ℂ))).scomp z hinner
  apply h.congr_deriv
  rw [polarPhase]
  ring

theorem hasDerivAt_polarProfile (P : TravelingPolarProfile) (z : ℝ) :
    HasDerivAt (polarProfile P) (polarProfile₁ P z) z := by
  have h := (P.amplitude_deriv z).ofReal_comp.mul (hasDerivAt_polarPhase P z)
  apply h.congr_deriv
  rw [polarProfile₁, polarPhase]
  push_cast
  ring

theorem hasDerivAt_polarProfile₁ (P : TravelingPolarProfile) (z : ℝ) :
    HasDerivAt (polarProfile₁ P) (polarProfile₂ P z) z := by
  have hproduct : HasDerivAt
      (fun x => P.amplitude x * P.phase₁ x)
      (P.amplitude₁ z * P.phase₁ z + P.amplitude z * P.phase₂ z) z :=
    (P.amplitude_deriv z).mul (P.phase₁_deriv z)
  have hcore := (P.amplitude₁_deriv z).ofReal_comp.add
    (hproduct.ofReal_comp.const_mul Complex.I)
  have h := (hasDerivAt_polarPhase P z).mul hcore
  apply h.congr_deriv
  rw [polarProfile₂]
  push_cast
  simp only [Pi.add_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Derivative-certified moving field `Ψ(x-ct)`. -/
noncomputable def travelingPolarJet (P : TravelingPolarProfile) (c : ℝ) :
    ComplexEvolutionJet2 where
  u := fun t x => polarProfile P (x - c * t)
  ut := fun t x => (-c : ℝ) * polarProfile₁ P (x - c * t)
  ux := fun t x => polarProfile₁ P (x - c * t)
  uxx := fun t x => polarProfile₂ P (x - c * t)
  hasDerivAt_time := by
    intro t x
    have hinner : HasDerivAt (fun s : ℝ => x - c * s) (-c) t := by
      simpa using! ((hasDerivAt_id t).const_mul c).const_sub x
    simpa only [Function.comp_def, Complex.real_smul] using
      (hasDerivAt_polarProfile P (x - c * t)).scomp t hinner
  hasDerivAt_space := by
    intro t x
    have hinner : HasDerivAt (fun y : ℝ => y - c * t) 1 x :=
      (hasDerivAt_id x).sub_const _
    simpa only [Function.comp_def, one_smul] using
      (hasDerivAt_polarProfile P (x - c * t)).scomp x hinner
  hasDerivAt_space_one := by
    intro t x
    have hinner : HasDerivAt (fun y : ℝ => y - c * t) 1 x :=
      (hasDerivAt_id x).sub_const _
    simpa only [Function.comp_def, one_smul] using
      (hasDerivAt_polarProfile₁ P (x - c * t)).scomp x hinner

/-- Pointwise complex residual equals phase times paper's two real scalar residuals. -/
theorem travelingPolar_residual_split
    (D c a a₁ a₂ p₁ p₂ : ℝ) (phase : ℂ) :
    Complex.I * ((-c : ℝ) *
        (phase * ((a₁ : ℂ) + Complex.I * (a * p₁ : ℝ)))) +
      (D : ℂ) *
        (phase * (((a₂ - a * p₁ ^ 2 : ℝ) : ℂ) +
          Complex.I * ((2 * a₁ * p₁ + a * p₂ : ℝ) : ℂ))) +
      (((D / 2) * a ^ 2 : ℝ) : ℂ) * ((a : ℂ) * phase) =
    phase *
      (((c * a * p₁ + D * (a₂ - a * p₁ ^ 2 + a ^ 3 / 2) : ℝ) : ℂ) +
        Complex.I * ((-c * a₁ + D * (2 * a₁ * p₁ + a * p₂) : ℝ) : ℂ)) := by
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Closed profile package for equations (44)--(45). -/
structure TravelingPolarNLSData extends TravelingPolarProfile where
  dispersion : ℝ
  speed : ℝ
  real_balance : ∀ z,
    speed * amplitude z * phase₁ z +
      dispersion *
        (amplitude₂ z - amplitude z * phase₁ z ^ 2 + amplitude z ^ 3 / 2) = 0
  imaginary_balance : ∀ z,
    -speed * amplitude₁ z +
      dispersion * (2 * amplitude₁ z * phase₁ z + amplitude z * phase₂ z) = 0

/-- Every scalar polar balance package compiles to an exact Brizard NLS solution. -/
theorem travelingPolarNLSData_solves (P : TravelingPolarNLSData) :
    SolvesNLS P.dispersion (travelingPolarJet P.toTravelingPolarProfile P.speed) := by
  intro t x
  let z := x - P.speed * t
  change Complex.I * ((-P.speed : ℝ) * polarProfile₁ P.toTravelingPolarProfile z) +
      (P.dispersion : ℂ) * polarProfile₂ P.toTravelingPolarProfile z +
      (((P.dispersion / 2) * ‖polarProfile P.toTravelingPolarProfile z‖ ^ 2 : ℝ) : ℂ) *
        polarProfile P.toTravelingPolarProfile z = 0
  rw [norm_polarProfile_sq]
  rw [polarProfile, polarProfile₁, polarProfile₂,
    travelingPolar_residual_split]
  rw [P.real_balance z, P.imaginary_balance z]
  simp

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
