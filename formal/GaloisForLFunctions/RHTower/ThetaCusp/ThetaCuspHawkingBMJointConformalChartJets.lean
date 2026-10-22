import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointConformalCoordinateLines
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointConformalWarpJets

/-! Actual first and second coordinate derivatives of the joint Euclidean chart. -/
open scoped ContDiff
namespace RHTower.D4BMJointConformal
open D4BMJointSource
noncomputable section
abbrev Point3 := Fin 3 → ℝ

def chart (p : Point3) : Point3 := ![p 2*radialUnit (p 0),p 2*warp (p 0),p 1]

def chartFirst (p : Point3) (i : Fin 3) : Point3 :=
  ![![-p 2*warp (p 0)^(2 : ℕ),p 2*warp (p 0)*radialUnit (p 0),0],
    ![0,0,1],![radialUnit (p 0),warp (p 0),0]] i

def chartSecond (p : Point3) (i : Fin 3) : Point3 :=
  ![![-2*p 2*warp (p 0)^(2 : ℕ)*radialUnit (p 0),
    p 2*warp (p 0)*(2*radialUnit (p 0)^(2 : ℕ)-1),0],0,0] i

theorem chart_smooth : ContDiff ℝ ∞ chart := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj 2 : Point3 →L[ℝ] ℝ).contDiff.mul
      (radialUnit_smooth.comp (ContinuousLinearMap.proj 0 : Point3 →L[ℝ] ℝ).contDiff)
  · exact (ContinuousLinearMap.proj 2 : Point3 →L[ℝ] ℝ).contDiff.mul
      (warp_smooth.comp (ContinuousLinearMap.proj 0 : Point3 →L[ℝ] ℝ).contDiff)
  · exact (ContinuousLinearMap.proj 1 : Point3 →L[ℝ] ℝ).contDiff

theorem chartCurve_hasDerivAt (p : Point3) (i : Fin 3) (s : ℝ) :
    HasDerivAt (fun x => chart (coordinateLine p i x)) (chartFirst (coordinateLine p i s) i) s := by
  fin_cases i <;> apply hasDerivAt_pi.mpr <;> intro j <;> fin_cases j
  · simpa [chart,chartFirst,coordinateLine,mul_neg,neg_mul] using
      (radialUnit_warp_derivative s).const_mul (p 2)
  · simpa [chart,chartFirst,coordinateLine,mul_assoc] using (warp_hasDerivAt s).const_mul (p 2)
  · simpa [chart,chartFirst,coordinateLine] using hasDerivAt_const s (p 1)
  · simpa [chart,chartFirst,coordinateLine] using hasDerivAt_const s (p 2*radialUnit (p 0))
  · simpa [chart,chartFirst,coordinateLine] using hasDerivAt_const s (p 2*warp (p 0))
  · simpa [chart,chartFirst,coordinateLine,id_eq] using! hasDerivAt_id s
  · simpa [chart,chartFirst,coordinateLine] using (hasDerivAt_id s).mul_const (radialUnit (p 0))
  · simpa [chart,chartFirst,coordinateLine] using (hasDerivAt_id s).mul_const (warp (p 0))
  · simpa [chart,chartFirst,coordinateLine] using hasDerivAt_const s (p 1)

theorem chartFirstCurve_hasDerivAt (p : Point3) (i : Fin 3) (s : ℝ) :
    HasDerivAt (fun x => chartFirst (coordinateLine p i x) i)
      (chartSecond (coordinateLine p i s) i) s := by
  fin_cases i <;> apply hasDerivAt_pi.mpr <;> intro j <;> fin_cases j
  · have h := ((warp_hasDerivAt s).pow 2).const_mul (-p 2)
    have hd : (-p 2)*(2*warp s^(2-1)*(warp s*radialUnit s)) =
        -2*p 2*warp s^(2 : ℕ)*radialUnit s := by ring
    simpa [chartFirst,chartSecond,coordinateLine] using h.congr_deriv hd
  · simpa [chartFirst,chartSecond,coordinateLine,mul_assoc] using
      (warpFirst_hasDerivAt s).const_mul (p 2)
  · simpa [chartFirst,chartSecond,coordinateLine] using hasDerivAt_const s (0:ℝ)
  · simpa [chartFirst,chartSecond,coordinateLine] using hasDerivAt_const s (0:ℝ)
  · simpa [chartFirst,chartSecond,coordinateLine] using hasDerivAt_const s (0:ℝ)
  · simpa [chartFirst,chartSecond,coordinateLine] using hasDerivAt_const s (1:ℝ)
  · simpa [chartFirst,chartSecond,coordinateLine] using hasDerivAt_const s (radialUnit (p 0))
  · simpa [chartFirst,chartSecond,coordinateLine] using hasDerivAt_const s (warp (p 0))
  · simpa [chartFirst,chartSecond,coordinateLine] using hasDerivAt_const s (0:ℝ)

/-- Both chart jets are derivatives of the actual coordinate map. -/
theorem chartCurve_derivatives (p : Point3) (i : Fin 3) :
    deriv (fun x => chart (coordinateLine p i x)) (p i) = chartFirst p i ∧
      deriv (deriv (fun x => chart (coordinateLine p i x))) (p i) = chartSecond p i := by
  have h : deriv (fun x => chart (coordinateLine p i x)) =
      fun x => chartFirst (coordinateLine p i x) i :=
    funext (fun x => (chartCurve_hasDerivAt p i x).deriv)
  constructor
  · simpa [coordinateLine_base] using (chartCurve_hasDerivAt p i (p i)).deriv
  · rw [h]
    simpa [coordinateLine_base] using (chartFirstCurve_hasDerivAt p i (p i)).deriv

end
end RHTower.D4BMJointConformal
