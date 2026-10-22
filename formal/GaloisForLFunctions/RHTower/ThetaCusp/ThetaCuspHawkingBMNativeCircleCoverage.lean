import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCircleChart
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
The native polar chart is globally onto the upper half-plane, not merely a local
coordinate computation.  This is the coverage gate needed before its exact
Jacobian can be used in the literal cyclic Peierls cap pairing.
-/
namespace RHTower.D4BMNativeCircle
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse
open Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem exists_angle_of_sq_add_sq_eq_one {u v : ℝ} (h : u ^ (2 : ℕ) + v ^ (2 : ℕ) = 1) :
    ∃ theta : ℝ, Real.sin theta = u ∧ Real.cos theta = v := by
  let z : Circle := ⟨(v : ℂ) + (u : ℂ) * Complex.I, by
    have hn : ‖(v : ℂ) + (u : ℂ) * Complex.I‖ ^ (2 : ℕ) = 1 := by
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_im, mul_one, Complex.I_re,
        mul_zero, sub_zero, Complex.add_im, Complex.mul_im, add_zero]
      nlinarith
    have hsq : ‖(v : ℂ) + (u : ℂ) * Complex.I‖ ^ (2 : ℕ) = (1 : ℝ) ^ (2 : ℕ) := by
      simpa using hn
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with hnorm | hnorm
    · exact mem_sphere_zero_iff_norm.mpr hnorm
    · have hnonneg : 0 ≤ ‖(v : ℂ) + (u : ℂ) * Complex.I‖ := norm_nonneg _
      rw [hnorm] at hnonneg
      linarith⟩
  obtain ⟨theta, htheta⟩ := Circle.exp_surjective z
  refine ⟨theta, ?_, ?_⟩
  · have him := congrArg Complex.im (congrArg (fun w : Circle => (w : ℂ)) htheta)
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I] at him
    dsimp [z] at him
    norm_num at him
    exact him
  · have hre := congrArg Complex.re (congrArg (fun w : Circle => (w : ℂ)) htheta)
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I] at hre
    dsimp [z] at hre
    norm_num at hre
    exact hre

/-- Every positive-height coordinate pair is reached by the literal circle chart based at `I`. -/
theorem circle_coverage (x y : ℝ) (hy : 0 < y) :
    ∃ d theta : ℝ, 0 ≤ d ∧ circle d theta ![0, 1] = ![x, y] := by
  let R : ℝ := (x ^ (2 : ℕ) + y ^ (2 : ℕ) + 1) / (2 * y)
  have hR : 1 ≤ R := by
    dsimp [R]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg x, sq_nonneg (y - 1)]
  by_cases hbase : x = 0 ∧ y = 1
  · rcases hbase with ⟨rfl, rfl⟩
    refine ⟨0, 0, le_rfl, ?_⟩
    ext i
    fin_cases i <;> norm_num [circle, offset, height, denominator]
  have hR_ne : R ≠ 1 := by
    intro heq
    have heq' : (x ^ (2 : ℕ) + y ^ (2 : ℕ) + 1) / (2 * y) = 1 := by simpa [R] using heq
    have hxy : x = 0 ∧ y = 1 := by
      rw [div_eq_iff (by positivity : (2 * y) ≠ 0)] at heq'
      constructor <;> nlinarith [sq_nonneg x, sq_nonneg (y - 1)]
    exact hbase hxy
  have hR_gt : 1 < R := lt_of_le_of_ne hR (Ne.symm hR_ne)
  let D : ℝ := √(R ^ (2 : ℕ) - 1)
  have hDsq_pos : 0 < R ^ (2 : ℕ) - 1 := by nlinarith
  have hDpos : 0 < D := Real.sqrt_pos.2 hDsq_pos
  have hDne : D ≠ 0 := hDpos.ne'
  have hDsq : D ^ (2 : ℕ) = R ^ (2 : ℕ) - 1 := Real.sq_sqrt (le_of_lt hDsq_pos)
  let u : ℝ := (x / y) / D
  let v : ℝ := (R - y⁻¹) / D
  have hcircle : (x / y) ^ (2 : ℕ) + (R - y⁻¹) ^ (2 : ℕ) = R ^ (2 : ℕ) - 1 := by
    dsimp [R]
    field_simp [hy.ne']
    ring
  have hcircleMul : x ^ (2 : ℕ) + (R * y - 1) ^ (2 : ℕ) = D ^ (2 : ℕ) * y ^ (2 : ℕ) := by
    have h := hcircle
    field_simp [hy.ne'] at h
    nlinarith [h, hDsq]
  have huvsq : u ^ (2 : ℕ) + v ^ (2 : ℕ) = 1 := by
    dsimp [u, v]
    field_simp [hDne, hy.ne']
    nlinarith [hcircleMul]
  obtain ⟨theta, hsin, hcos⟩ := exists_angle_of_sq_add_sq_eq_one huvsq
  refine ⟨Real.arcosh R, theta, Real.arcosh_nonneg hR, ?_⟩
  have hcosh : Real.cosh (Real.arcosh R) = R := Real.cosh_arcosh hR
  have hsinh : Real.sinh (Real.arcosh R) = D := by rw [Real.sinh_arcosh hR]
  have hden : denominator (Real.arcosh R) theta = y⁻¹ := by
    rw [denominator, hcosh, hsinh, hcos]
    dsimp [v]
    field_simp [hDne]
    ring
  have hoff : offset (Real.arcosh R) theta = x := by
    rw [offset, hsinh, hsin, hden]
    dsimp [u]
    field_simp [hDne, hy.ne']
  have hheight : height (Real.arcosh R) theta = y := by
    rw [height, hden]
    field_simp [hy.ne']
  ext i
  fin_cases i
  · simpa [circle] using hoff
  · simpa [circle] using hheight

/-- The literal chart about every positive-height base point covers every positive-height point. -/
theorem circle_coverage_scaled (z : Point) (hz : 0 < z 1) (x y : ℝ) (hy : 0 < y) :
    ∃ d theta : ℝ, 0 ≤ d ∧ circle d theta z = ![x, y] := by
  let X : ℝ := (x - z 0) / z 1
  let Y : ℝ := y / z 1
  have hY : 0 < Y := div_pos hy hz
  obtain ⟨d, theta, hd, hcircle⟩ := circle_coverage X Y hY
  have hoff : offset d theta = X := by
    have h := congrFun hcircle 0
    simpa [circle] using h
  have hheight : height d theta = Y := by
    have h := congrFun hcircle 1
    simpa [circle] using h
  refine ⟨d, theta, hd, ?_⟩
  ext i
  fin_cases i
  · rw [circle, hoff]
    dsimp [X]
    field_simp [hz.ne']
    ring
  · rw [circle, hheight]
    dsimp [Y]
    field_simp [hz.ne']

end
end RHTower.D4BMNativeCircle
