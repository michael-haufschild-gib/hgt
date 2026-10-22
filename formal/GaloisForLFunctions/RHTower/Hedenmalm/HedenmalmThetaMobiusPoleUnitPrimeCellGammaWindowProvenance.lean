import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPoleUnitPrimeCellGammaPythagoreanBudget
import GaloisForLFunctions.RHTower.BurnolCoPoissonConormalReflectionCover

/-!
# Burnol-window provenance of the Route-P Gamma scattering clock

P-G49 identifies a forced nonlinear Gamma rapidity but leaves its source provenance open.  This
module closes that gate.  Twice the forced rapidity is the length of a literal Burnol co-Poisson
exponential window.  Its lower endpoint has an exact rational expression in the running Euler odds
and thermal ratio, lies strictly between zero and one, and the corpus's existing Mellin theorem
evaluates the resulting source vector.

This proves source realizability of the P-G49 clock.  It does not turn the conservative
Euler--Gamma budget into Julia saturation.
-/

open Complex Filter Set Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Literal Burnol-window length forced by one Euler Julia cell. -/
def thermalBernoulliGammaWindowLength (q k T : ℝ) : ℝ :=
  2 * Real.artanh (thermalBernoulliCoPoissonCayley q k T)

/-- Rational lower endpoint of the forced Burnol window. -/
def thermalBernoulliGammaWindowAperture (q k T : ℝ) : ℝ :=
  (1 + thermalBernoulliRunningOdds q k) /
    (2 * T + thermalBernoulliRunningOdds q k - 1)

theorem thermalBernoulliGammaWindowLength_pos
    {q k T : ℝ} (hq : 0 < q) (hT : 1 < T) :
    0 < thermalBernoulliGammaWindowLength q k T := by
  rw [thermalBernoulliGammaWindowLength]
  exact mul_pos (by norm_num) (Real.artanh_pos
    (thermalBernoulliCoPoissonCayley_mem_Ioo_zero_one hq hT))

theorem thermalBernoulliGammaWindowAperture_mem_Ioo
    {q k T : ℝ} (hq : 0 < q) (hT : 1 < T) :
    thermalBernoulliGammaWindowAperture q k T ∈ Ioo 0 1 := by
  have ha : 0 < thermalBernoulliRunningOdds q k :=
    thermalBernoulliRunningOdds_pos hq
  rw [thermalBernoulliGammaWindowAperture]
  constructor
  · exact div_pos (by linarith) (by linarith)
  · rw [div_lt_one (by linarith)]
    linarith

/-- Exact window-endpoint law: the rational aperture is the exponential of minus forced length. -/
theorem exp_neg_thermalBernoulliGammaWindowLength_eq_aperture
    {q k T : ℝ} (hq : 0 < q) (hT : 1 < T) :
    Real.exp (-thermalBernoulliGammaWindowLength q k T) =
      thermalBernoulliGammaWindowAperture q k T := by
  let C := thermalBernoulliCoPoissonCayley q k T
  have hC := thermalBernoulliCoPoissonCayley_mem_Ioo_zero_one (k := k) hq hT
  have hC' : C ∈ Ioo (-1 : ℝ) 1 := ⟨lt_trans (by norm_num) hC.1, hC.2⟩
  have hratio : 0 ≤ (1 + C) / (1 - C) :=
    div_nonneg (by linarith [hC'.1]) (by linarith [hC'.2])
  rw [thermalBernoulliGammaWindowLength]
  change Real.exp (-(2 * Real.artanh C)) = _
  rw [show -(2 * Real.artanh C) = -(Real.artanh C + Real.artanh C) by ring,
    Real.exp_neg, Real.exp_add, ← pow_two,
    Real.exp_artanh hC', Real.sq_sqrt hratio]
  dsimp [C]
  rw [thermalBernoulliGammaWindowAperture, thermalBernoulliCoPoissonCayley]
  have ha : 0 < thermalBernoulliRunningOdds q k :=
    thermalBernoulliRunningOdds_pos hq
  field_simp
  ring

/-- The forced exponential window is an actual corpus co-Poisson source with exact Mellin
evaluation. -/
theorem integral_Ioi_burnolCoPoisson_thermalBernoulliGammaWindow
    {q k T : ℝ} (hq : 0 < q) (hT : 1 < T) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    (∫ t in Set.Ioi (0 : ℝ),
        RHTower.burnolCoPoissonRightSum
          (RHTower.coPoissonSubWindowSeed
            (Real.exp (-thermalBernoulliGammaWindowLength q k T)) 1) t *
          (t : ℂ) ^ (-w)) =
      RHTower.burnolCoPoissonExpWindowZetaMellinGerm
        (thermalBernoulliGammaWindowLength q k T) w := by
  exact RHTower.integral_Ioi_burnolCoPoisson_expWindow_cpow
    (thermalBernoulliGammaWindowLength_pos hq hT) hw0 hw1

/-- Rational and exponential descriptions define the same literal co-Poisson seed. -/
theorem thermalBernoulliGammaWindowAperture_eq_exp_neg
    {q k T : ℝ} (hq : 0 < q) (hT : 1 < T) :
    RHTower.coPoissonSubWindowSeed
        (thermalBernoulliGammaWindowAperture q k T) 1 =
      RHTower.coPoissonSubWindowSeed
        (Real.exp (-thermalBernoulliGammaWindowLength q k T)) 1 := by
  rw [exp_neg_thermalBernoulliGammaWindowLength_eq_aperture hq hT]

end

end RHTower.HedenmalmThetaSource
