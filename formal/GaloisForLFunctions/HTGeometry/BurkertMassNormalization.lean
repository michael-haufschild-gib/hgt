import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Burkert radial mass and its normalization

The density in arXiv:2608.23600v1, equation (4), has the exact primitive proved here.
At unit halo scale, its enclosed mass has coefficient `2 * pi * centralDensity`.
The coefficient `4 * pi * centralDensity` printed in the same equation produces
exactly twice the required density flux. Positive radii and central densities are
parameterized exponentially; no differentiability or integrability is assumed.
-/

noncomputable section
open Real Set
namespace GaloisForLFunctions.HTGeometry

def burkertDensity (r : ℝ) : ℝ := 1 / ((1 + r) * (1 + r ^ (2 : ℕ)))
def burkertPrimitive (r : ℝ) : ℝ :=
  Real.log (1 + r ^ (2 : ℕ)) / 2 + Real.log (1 + r) - Real.arctan r

theorem burkertPrimitive_derivative (t : ℝ) :
    HasDerivAt burkertPrimitive
      (2 * (Real.exp t) ^ (2 : ℕ) * burkertDensity (Real.exp t)) (Real.exp t) := by
  have h1 : 1 + Real.exp t ≠ 0 := by positivity
  have h2 : 1 + (Real.exp t) ^ (2 : ℕ) ≠ 0 := by positivity
  have h := (((((hasDerivAt_id (Real.exp t)).pow 2).const_add 1).log h2).div_const 2).add
    (((hasDerivAt_id (Real.exp t)).const_add 1).log h1)
  apply (h.sub (Real.hasDerivAt_arctan (Real.exp t))).congr_deriv
  dsimp [burkertDensity]
  field_simp
  ring

theorem integral_burkert_radial_mass (t : ℝ) :
    (∫ r in (0 : ℝ)..Real.exp t, r ^ (2 : ℕ) * burkertDensity r) =
      burkertPrimitive (Real.exp t) / 2 := by
  have hd : ∀ r ∈ uIcc (0 : ℝ) (Real.exp t),
      HasDerivAt (fun x => burkertPrimitive x / 2) (r ^ (2 : ℕ) * burkertDensity r) r := by
    intro r hr
    have hr0 : 0 ≤ r := (uIcc_of_le (Real.exp_pos t).le ▸ hr).1
    have h1 : 1 + r ≠ 0 := by positivity
    have h2 : 1 + r ^ (2 : ℕ) ≠ 0 := by positivity
    have h := ((((((hasDerivAt_id r).pow 2).const_add 1).log h2).div_const 2).add
      (((hasDerivAt_id r).const_add 1).log h1)).sub (Real.hasDerivAt_arctan r)
    apply (h.div_const 2).congr_deriv
    dsimp [burkertDensity]
    field_simp
    ring
  have hc : ContinuousOn (fun r => r ^ (2 : ℕ) * burkertDensity r) (uIcc (0 : ℝ) (Real.exp t)) := by
    apply ContinuousOn.mul (continuous_pow 2).continuousOn
    apply ContinuousOn.div continuousOn_const
      ((continuous_const.add continuous_id).mul
        (continuous_const.add (continuous_pow 2))).continuousOn
    intro r hr
    have hr0 : 0 ≤ r := (uIcc_of_le (Real.exp_pos t).le ▸ hr).1
    dsimp
    positivity
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  simpa [burkertPrimitive] using h

def burkertEnclosedMass (d r : ℝ) : ℝ :=
  2 * Real.pi * Real.exp d * burkertPrimitive r

def burkertPrintedMass (d r : ℝ) : ℝ :=
  4 * Real.pi * Real.exp d * burkertPrimitive r

theorem burkertEnclosedMass_derivative (d t : ℝ) :
    HasDerivAt (burkertEnclosedMass d)
      (4 * Real.pi * Real.exp d * (Real.exp t) ^ (2 : ℕ) * burkertDensity (Real.exp t))
      (Real.exp t) := by
  apply ((burkertPrimitive_derivative t).const_mul (2 * Real.pi * Real.exp d)).congr_deriv
  ring

theorem burkertPrintedMass_derivative (d t : ℝ) :
    HasDerivAt (burkertPrintedMass d)
      (8 * Real.pi * Real.exp d * (Real.exp t) ^ (2 : ℕ) * burkertDensity (Real.exp t))
      (Real.exp t) := by
  apply ((burkertPrimitive_derivative t).const_mul (4 * Real.pi * Real.exp d)).congr_deriv
  ring

theorem burkertPrintedMass_violates_density_flux (d t : ℝ) :
    deriv (burkertPrintedMass d) (Real.exp t) ≠
      4 * Real.pi * Real.exp d * (Real.exp t) ^ (2 : ℕ) * burkertDensity (Real.exp t) := by
  rw [(burkertPrintedMass_derivative d t).deriv]
  have hp : 0 < 4 * Real.pi * Real.exp d * (Real.exp t) ^ (2 : ℕ) * burkertDensity (Real.exp t) := by
    unfold burkertDensity
    positivity
  linarith

theorem burkertPrintedMass_eq_twice (d r : ℝ) :
    burkertPrintedMass d r = 2 * burkertEnclosedMass d r := by
  unfold burkertPrintedMass burkertEnclosedMass
  ring

end GaloisForLFunctions.HTGeometry
