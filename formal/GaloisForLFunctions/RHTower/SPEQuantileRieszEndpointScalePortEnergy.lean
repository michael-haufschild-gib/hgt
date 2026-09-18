import GaloisForLFunctions.RHTower.SPEQuantileRieszEndpointRayGraphEnergy

/-!
# Exact graph energy of the literal SP-E endpoint scale port

The SP-E endpoint profile is not a single Route-P ray: it is its literal continuous scale
superposition over `[1/2, 1]`.  This module computes the positive-half-line Route-P graph energy
of that exact source port.  The answer is `1/6`.

This is an analytic normalization fact.  It does not identify this energy with any separately
normalized Route-E threshold, construct the missing signed free-word lift, or bound the
RH-equivalent completed SP-E current.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-- The literal continuous scale superposition defining the normalized SP-E endpoint ray port. -/
def primeGammaCauchyCubicEndpointScalePort (u : ℝ) : ℂ :=
  (∫ s in (1 / 2 : ℝ)..1, primeGammaCauchyCubicRayFeature s u : ℝ)

/-- **Exact endpoint-port energy.** The full normalized SP-E endpoint scale superposition has
Route-P graph energy `1/6`. -/
theorem routePBurnolApertureEnergy_primeGammaCauchyCubicEndpointScalePort :
    routePBurnolApertureEnergy primeGammaCauchyCubicEndpointScalePort = 1 / 6 := by
  let f1 : ℝ → ℝ := fun u => Real.exp ((-1 : ℝ) * u)
  let f2 : ℝ → ℝ := fun u => Real.exp ((-3 / 2 : ℝ) * u)
  let f3 : ℝ → ℝ := fun u => Real.exp ((-2 : ℝ) * u)
  have hnorm (u : ℝ) :
      ‖primeGammaCauchyCubicEndpointScalePort u‖ ^ 2 =
        f1 u - 2 * f2 u + f3 u := by
    unfold primeGammaCauchyCubicEndpointScalePort
    rw [integral_primeGammaCauchyCubicRayFeature_half_one]
    dsimp only [f1, f2, f3]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hfirst : Real.exp (-(u / 2)) ^ 2 = Real.exp ((-1 : ℝ) * u) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hcross : Real.exp (-(u / 2)) * Real.exp (-u) =
        Real.exp ((-3 / 2 : ℝ) * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hlast : Real.exp (-u) ^ 2 = Real.exp ((-2 : ℝ) * u) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      (Real.exp (-(u / 2)) - Real.exp (-u)) ^ 2 =
          Real.exp (-(u / 2)) ^ 2 -
            2 * (Real.exp (-(u / 2)) * Real.exp (-u)) + Real.exp (-u) ^ 2 := by ring
      _ = _ := by rw [hfirst, hcross, hlast]
  have hint1 : IntegrableOn f1 (Ioi 0) := by
    dsimp only [f1]
    exact integrableOn_exp_mul_Ioi (by norm_num) 0
  have hint2 : IntegrableOn f2 (Ioi 0) := by
    dsimp only [f2]
    exact integrableOn_exp_mul_Ioi (by norm_num) 0
  have hint3 : IntegrableOn f3 (Ioi 0) := by
    dsimp only [f3]
    exact integrableOn_exp_mul_Ioi (by norm_num) 0
  have hval1 : (∫ u : ℝ in Ioi 0, f1 u) = 1 := by
    dsimp only [f1]
    rw [integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0]
    norm_num
  have hval2 : (∫ u : ℝ in Ioi 0, f2 u) = 2 / 3 := by
    dsimp only [f2]
    rw [integral_exp_mul_Ioi (by norm_num : (-3 / 2 : ℝ) < 0) 0]
    norm_num
  have hval3 : (∫ u : ℝ in Ioi 0, f3 u) = 1 / 2 := by
    dsimp only [f3]
    rw [integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0]
    norm_num
  have hconst2 :
      (∫ u : ℝ in Ioi 0, 2 * f2 u) =
        2 * ∫ u : ℝ in Ioi 0, f2 u :=
    MeasureTheory.integral_const_mul 2 _
  have hsub2 :
      (∫ u : ℝ in Ioi 0, f1 u - 2 * f2 u) =
        (∫ u : ℝ in Ioi 0, f1 u) -
          2 * ∫ u : ℝ in Ioi 0, f2 u := by
    calc
      (∫ u : ℝ in Ioi 0, f1 u - 2 * f2 u) =
          (∫ u : ℝ in Ioi 0, f1 u) -
            ∫ u : ℝ in Ioi 0, 2 * f2 u :=
        MeasureTheory.integral_sub hint1 (hint2.const_mul 2)
      _ = _ := by rw [hconst2]
  unfold routePBurnolApertureEnergy
  simp_rw [hnorm]
  change (∫ u : ℝ in Ioi 0, (f1 u - 2 * f2 u) + f3 u) = 1 / 6
  calc
    (∫ u : ℝ in Ioi 0, (f1 u - 2 * f2 u) + f3 u) =
        (∫ u : ℝ in Ioi 0, f1 u - 2 * f2 u) +
          ∫ u : ℝ in Ioi 0, f3 u := by
          exact MeasureTheory.integral_add (hint1.sub (hint2.const_mul 2)) hint3
    _ = (∫ u : ℝ in Ioi 0, f1 u) -
          2 * (∫ u : ℝ in Ioi 0, f2 u) +
            (∫ u : ℝ in Ioi 0, f3 u) := by
          rw [hsub2]
    _ = 1 / 6 := by
      linarith [hval1, hval2, hval3]

end GaloisForLFunctions.HTGeometry
