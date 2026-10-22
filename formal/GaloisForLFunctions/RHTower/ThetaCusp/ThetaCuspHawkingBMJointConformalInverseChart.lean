import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointConformalChartJets
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-! Explicit inverse and physical chart domains for the joint Euclidean coordinate map. -/
open scoped ContDiff
namespace RHTower.D4BMJointConformal
open D4BMJointSource
noncomputable section

def inverseChart (q : Point3) : Point3 :=
  ![-Real.arsinh (q 0/q 1),q 2,Real.sqrt ((q 0)^(2 : ℕ)+(q 1)^(2 : ℕ))]

theorem chart_radius (p : Point3) : (chart p 0)^(2 : ℕ)+(chart p 1)^(2 : ℕ) = (p 2)^(2 : ℕ) := by
  dsimp [chart]
  linear_combination (p 2)^(2 : ℕ)*(warp_relation (p 0))

theorem chart_ratio (p : Point3) (hp : 0 < p 2) :
    chart p 0/chart p 1 = -Real.sinh (p 0) := by
  have hy := ne_of_gt hp
  have hc := ne_of_gt (Real.cosh_pos (p 0))
  dsimp [chart,radialUnit,warp]
  field_simp

/-- The proposed inverse recovers all original physical coordinates. -/
theorem inverseChart_chart (p : Point3) (hp : 0 < p 2) : inverseChart (chart p) = p := by
  ext i
  fin_cases i
  · change -Real.arsinh (chart p 0/chart p 1) = p 0
    rw [chart_ratio p hp,Real.arsinh_neg,Real.arsinh_sinh,neg_neg]
  · rfl
  · change Real.sqrt ((chart p 0)^(2 : ℕ)+(chart p 1)^(2 : ℕ)) = p 2
    rw [chart_radius,Real.sqrt_sq hp.le]

private theorem radius_pos (q : Point3) (hq : 0 < q 1) :
    0 < Real.sqrt ((q 0)^(2 : ℕ)+(q 1)^(2 : ℕ)) :=
  Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (q 0)])

private theorem sqrt_ratio (q : Point3) (hq : 0 < q 1) :
    Real.sqrt (1+(q 0/q 1)^(2 : ℕ)) = Real.sqrt ((q 0)^(2 : ℕ)+(q 1)^(2 : ℕ))/q 1 := by
  have hy := ne_of_gt hq
  rw [show 1+(q 0/q 1)^(2 : ℕ) = ((q 0)^(2 : ℕ)+(q 1)^(2 : ℕ))/(q 1)^(2 : ℕ) by field_simp; ring,
    Real.sqrt_div,Real.sqrt_sq hq.le]
  positivity

/-- The explicit inverse covers the entire upper-Y chart, including the physical quadrant. -/
theorem chart_inverseChart (q : Point3) (hq : 0 < q 1) : chart (inverseChart q) = q := by
  have hy := ne_of_gt hq
  have hr := ne_of_gt (radius_pos q hq)
  ext i
  fin_cases i
  · dsimp [chart,inverseChart,radialUnit]
    rw [Real.sinh_neg,Real.cosh_neg,Real.sinh_arsinh,Real.cosh_arsinh,sqrt_ratio q hq]
    field_simp
  · dsimp [chart,inverseChart,warp]
    rw [Real.cosh_neg,Real.cosh_arsinh,sqrt_ratio q hq]
    field_simp
  · rfl

theorem chart_physical (p : Point3) (ht : p 0 < 0) (hy : 0 < p 2) :
    0 < chart p 0 ∧ 0 < chart p 1 :=
  ⟨mul_pos hy (radialUnit_bounds (p 0) ht).1,mul_pos hy (warp_pos _)⟩

theorem inverseChart_physical (q : Point3) (hX : 0 < q 0) (hY : 0 < q 1) :
    inverseChart q 0 < 0 ∧ 0 < inverseChart q 2 := by
  constructor
  · change -Real.arsinh (q 0/q 1) < 0
    exact neg_neg_of_pos (Real.arsinh_pos_iff.mpr (div_pos hX hY))
  · exact radius_pos q hY

/-- The explicit inverse is smooth on its actual positive-Y domain. -/
theorem inverseChart_smooth (q : Point3) (hY : 0 < q 1) : ContDiffAt ℝ ∞ inverseChart q := by
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun p : Point3 => p i) :=
    (ContinuousLinearMap.proj i : Point3 →L[ℝ] ℝ).contDiff
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact (Real.contDiff_arsinh.contDiffAt.comp q
      ((hc 0).contDiffAt.div (hc 1).contDiffAt (ne_of_gt hY))).neg
  · exact (hc 2).contDiffAt
  · exact (((hc 0).contDiffAt.pow 2).add ((hc 1).contDiffAt.pow 2)).sqrt
      (ne_of_gt (by nlinarith [sq_nonneg (q 0)] : 0 < (q 0)^(2 : ℕ)+(q 1)^(2 : ℕ)))

end
end RHTower.D4BMJointConformal
