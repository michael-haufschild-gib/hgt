import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspCutoffMean
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Actual quadratic cusp indicial powers and their sharp native integrability chambers.

This leaf proves the displayed source or cusp identity. Causal continuation,
left-QNM evaluation and Hawking-clock extinction remain separate obligations.
-/

open MeasureTheory Set Filter Topology
namespace RHTower.D4BMCuspProjection
open D4BMAngularSeries D4BMGlobalAngularResponse D4BMQuadraticMixedSource
noncomputable section

/-- The squared norm density of a literal cusp height power in native hyperbolic measure. -/
def powerDensity (p : ℂ) (y : ℝ) : ℝ := ‖(y:ℂ)^p‖^(2 : ℕ)/y^(2 : ℕ)

private theorem powerDensity_eq (p : ℂ) {y : ℝ} (hy : 0 < y) :
    powerDensity p y = y^(2*p.re-2) := by
  rw [powerDensity,Complex.norm_cpow_eq_rpow_re_of_pos hy,Real.rpow_sub hy,
    show 2*p.re=p.re*2 by ring,Real.rpow_mul hy.le]
  norm_num

/-- The exact native cusp integrability threshold, with its endpoint excluded. -/
theorem powerDensity_integrable_iff (p : ℂ) :
    IntegrableOn (powerDensity p) (Ioi (2:ℝ)) ↔ p.re < 1/2 := by
  have he : EqOn (powerDensity p) (fun y : ℝ => y^(2*p.re-2)) (Ioi (2:ℝ)) := by
    intro y hy
    exact powerDensity_eq p (by change 2 < y at hy; linarith)
  rw [integrableOn_congr_fun he measurableSet_Ioi,integrableOn_Ioi_rpow_iff (by norm_num : (0:ℝ)<2)]
  constructor <;> intro h <;> linarith

/-- Both actual height powers solve the homogeneous cusp equation for the
original quadratic doubled-time parameter. -/
theorem indicial_power_equations (w : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (fun a : Fin 2 → ℝ => (a 1:ℂ)^(w+2)) z =
      (w+1)*(w+2)*(z 1:ℂ)^(w+2) ∧
    hyperbolicLaplacian (fun a : Fin 2 → ℝ => (a 1:ℂ)^(-w-1)) z =
      (w+1)*(w+2)*(z 1:ℂ)^(-w-1) := by
  constructor <;> rw [height_cpow_hyperbolicLaplacian _ z hz] <;> ring

/-- The two holomorphic indicial branches have opposite native integrability chambers. -/
theorem indicial_power_integrability (w : ℂ) :
    (IntegrableOn (powerDensity (w+2)) (Ioi (2:ℝ)) ↔ w.re < -3/2) ∧
    (IntegrableOn (powerDensity (-w-1)) (Ioi (2:ℝ)) ↔ -3/2 < w.re) := by
  norm_num [powerDensity_integrable_iff,Complex.add_re,Complex.sub_re,Complex.neg_re,
    Complex.natCast_re,Complex.one_re]
  constructor <;> constructor <;> intro h <;> linarith

/-- Doubled time rate of either actual Xi source branch. -/
def physicalRate (q : XiZeroCopy) (branch : Bool) : ℂ :=
  if branch then 2*((q.1:ℂ)-2) else 2*(-(q.1:ℂ)-1)

/-- This is the literal source parameter, with no change of spectral coordinate. -/
theorem physicalRate_parameter (q : XiZeroCopy) (branch : Bool) :
    parameter q branch = (physicalRate q branch+1)*(physicalRate q branch+2) := by
  cases branch <;> rfl

/-- Both physical Xi rates lie strictly on the left of the cusp threshold line. -/
theorem physicalRate_re_bounds (q : XiZeroCopy) (branch : Bool) :
    -4 < (physicalRate q branch).re ∧ (physicalRate q branch).re < -2 := by
  have hq := xi_divisor_support_re_mem_open_unit q.1
  cases branch <;> norm_num [physicalRate,Complex.mul_re,Complex.sub_re,Complex.neg_re]
  all_goals constructor <;> linarith [hq.1,hq.2]

/-- Native finite cusp mass at every actual Xi occurrence selects the branch
opposite to the one integrable on the right-hand parameter chamber. -/
theorem physical_indicial_selection (q : XiZeroCopy) (branch : Bool) :
    IntegrableOn (powerDensity (physicalRate q branch+2)) (Ioi (2:ℝ)) ∧
      ¬ IntegrableOn (powerDensity (-physicalRate q branch-1)) (Ioi (2:ℝ)) := by
  have hp := (physicalRate_re_bounds q branch).2
  rw [(indicial_power_integrability _).1,(indicial_power_integrability _).2]
  constructor <;> linarith

end
end RHTower.D4BMCuspProjection
