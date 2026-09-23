import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith

/-!
# Finite-mode energy identity

This file isolates the Hilbert-space algebra behind equation (7.22) of the supplied
Navier–Stokes paper.  For a mode satisfying `u' = forcing - d • u`, the derivative of its
kinetic energy is the work of the forcing minus the exact quadratic damping term.
-/

noncomputable section

open RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry.NavierStokesEnergyIdentity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Half the squared Hilbert norm, matching the kinetic-energy normalization in (7.22). -/
def kineticEnergy (u : E) : ℝ := ‖u‖ ^ (2 : ℕ) / 2

/-- The chain rule `d(‖u‖²/2)/dt = ⟨u,u'⟩`. -/
theorem hasDerivAt_kineticEnergy {u : ℝ → E} {u' : E} {t : ℝ}
    (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => kineticEnergy (u s)) (inner ℝ (u t) u') t := by
  simpa [kineticEnergy] using hu.norm_sq.div_const (2 : ℝ)

/-- Equation (7.22), abstracted from the cylindrical coordinates: forcing contributes the
signed transfer `-transfer`, while scalar damping contributes exactly `-d ‖u‖²`. -/
theorem hasDerivAt_kineticEnergy_of_damped_mode
    {u : ℝ → E} {u' forcing : E} {d transfer t : ℝ}
    (hu : HasDerivAt u u' t)
    (hode : u' = forcing - d • u t)
    (htransfer : inner ℝ (u t) forcing = -transfer) :
    HasDerivAt (fun s => kineticEnergy (u s))
      (-transfer - d * ‖u t‖ ^ (2 : ℕ)) t := by
  convert hasDerivAt_kineticEnergy hu using 1
  rw [hode, inner_sub_right, inner_smul_right, htransfer,
    real_inner_self_eq_norm_sq]

/-- Nonnegative transfer and damping make the instantaneous kinetic-energy derivative
nonpositive.  This is the dissipative consequence used after (7.22). -/
theorem kineticEnergy_deriv_nonpos_of_damped_mode
    {u : ℝ → E} {u' forcing : E} {d transfer t : ℝ}
    (hu : HasDerivAt u u' t)
    (hode : u' = forcing - d • u t)
    (htransfer : inner ℝ (u t) forcing = -transfer)
    (hd : 0 ≤ d) (htransfer_nonneg : 0 ≤ transfer) :
    deriv (fun s => kineticEnergy (u s)) t ≤ 0 := by
  rw [(hasDerivAt_kineticEnergy_of_damped_mode hu hode htransfer).deriv]
  have hdis : 0 ≤ d * ‖u t‖ ^ (2 : ℕ) := mul_nonneg hd (sq_nonneg _)
  linarith

end GaloisForLFunctions.HTGeometry.NavierStokesEnergyIdentity
