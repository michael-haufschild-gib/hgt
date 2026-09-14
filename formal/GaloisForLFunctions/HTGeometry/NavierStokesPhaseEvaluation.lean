import GaloisForLFunctions.HTGeometry.NavierStokesFiniteTorusInverse
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Chain rules for Navier--Stokes auxiliary-phase evaluation

Equation (6.4) of the supplied Navier--Stokes paper replaces physical derivatives
after phase evaluation by directional derivatives in an auxiliary torus.  This file
proves that mechanism on the torus's vector model for arbitrary differentiable
scalar phases, then specializes it to affine time phases and real-power radial phases.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry.NavierStokesPhaseEvaluation

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- An auxiliary orbit driven by a scalar phase. -/
def auxiliaryPhasePath (base velocity : d → ℝ) (phase : ℝ → ℝ) (t : ℝ) : d → ℝ :=
  base + phase t • velocity

def auxiliaryAffinePath (base velocity : d → ℝ) (t : ℝ) : d → ℝ :=
  auxiliaryPhasePath base velocity id t

def auxiliaryRadialPowerPath (base velocity : d → ℝ) (exponent r : ℝ) : d → ℝ :=
  auxiliaryPhasePath base velocity (fun s => s ^ exponent) r

omit [Fintype d] [DecidableEq d] in
theorem auxiliaryPhasePath_hasDerivAt
    (base velocity : d → ℝ) {phase : ℝ → ℝ} {phase' t : ℝ}
    (hphase : HasDerivAt phase phase' t) :
    HasDerivAt (auxiliaryPhasePath base velocity phase) (phase' • velocity) t := by
  apply hasDerivAt_pi.mpr
  intro i
  change HasDerivAt (fun s : ℝ => base i + phase s * velocity i) (phase' * velocity i) t
  simpa using (hphase.mul_const (velocity i)).const_add (base i)

omit [Fintype d] [DecidableEq d] in
theorem auxiliaryAffinePath_hasDerivAt (base velocity : d → ℝ) (t : ℝ) :
    HasDerivAt (auxiliaryAffinePath base velocity) velocity t := by
  change HasDerivAt (auxiliaryPhasePath base velocity id) velocity t
  simpa using auxiliaryPhasePath_hasDerivAt base velocity (hasDerivAt_id t)

/-- A Fréchet derivative evaluated on a vector is the corresponding sum of coordinate
partial derivatives. -/
theorem fderiv_apply_eq_transportDerivative
    (G : (d → ℝ) → ℂ) (x velocity : d → ℝ) :
    fderiv ℝ G x velocity =
      NavierStokesFiniteTorusInverse.transportDerivative velocity G x := by
  unfold NavierStokesFiniteTorusInverse.transportDerivative pderiv
  rw [← Finset.univ_sum_single velocity, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsingle : Pi.single i (velocity i) = velocity i • Pi.single i (1 : ℝ) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hsingle, map_smul]
  simp [Complex.real_smul]

/-- General phase-evaluation chain rule behind equation (6.4). -/
theorem deriv_comp_auxiliaryPhasePath
    {G : (d → ℝ) → ℂ} {base velocity : d → ℝ} {phase : ℝ → ℝ} {phase' t : ℝ}
    (hG : DifferentiableAt ℝ G (auxiliaryPhasePath base velocity phase t))
    (hphase : HasDerivAt phase phase' t) :
    deriv (fun s => G (auxiliaryPhasePath base velocity phase s)) t =
      (phase' : ℂ) * NavierStokesFiniteTorusInverse.transportDerivative velocity G
        (auxiliaryPhasePath base velocity phase t) := by
  have hcomp := hG.hasFDerivAt.comp_hasDerivAt t
    (auxiliaryPhasePath_hasDerivAt base velocity hphase)
  change deriv (G ∘ auxiliaryPhasePath base velocity phase) t = _
  rw [hcomp.deriv, map_smul, fderiv_apply_eq_transportDerivative]
  simp [Complex.real_smul]

/-- Affine-time specialization of the phase-evaluation chain rule. -/
theorem deriv_comp_auxiliaryAffinePath
    {G : (d → ℝ) → ℂ} {base velocity : d → ℝ} {t : ℝ}
    (hG : DifferentiableAt ℝ G (auxiliaryAffinePath base velocity t)) :
    deriv (fun s => G (auxiliaryAffinePath base velocity s)) t =
      NavierStokesFiniteTorusInverse.transportDerivative velocity G
        (auxiliaryAffinePath base velocity t) := by
  have hcomp := hG.hasFDerivAt.comp_hasDerivAt t
    (auxiliaryAffinePath_hasDerivAt base velocity t)
  change deriv (G ∘ auxiliaryAffinePath base velocity) t = _
  rw [hcomp.deriv, fderiv_apply_eq_transportDerivative]

/-- Real-power radial specialization, giving the `d_r r^(d_r-1)` coefficient in (6.4). -/
theorem deriv_comp_auxiliaryRadialPowerPath
    {G : (d → ℝ) → ℂ} {base velocity : d → ℝ} {exponent r : ℝ}
    (hG : DifferentiableAt ℝ G (auxiliaryRadialPowerPath base velocity exponent r))
    (hr : r ≠ 0) :
    deriv (fun s => G (auxiliaryRadialPowerPath base velocity exponent s)) r =
      ((exponent * r ^ (exponent - 1) : ℝ) : ℂ) *
        NavierStokesFiniteTorusInverse.transportDerivative velocity G
          (auxiliaryRadialPowerPath base velocity exponent r) := by
  change deriv (fun s => G (auxiliaryPhasePath base velocity
    (fun x => x ^ exponent) s)) r = _
  simpa [auxiliaryRadialPowerPath] using deriv_comp_auxiliaryPhasePath hG
    (Real.hasDerivAt_rpow_const (Or.inl hr))

end

end GaloisForLFunctions.HTGeometry.NavierStokesPhaseEvaluation
