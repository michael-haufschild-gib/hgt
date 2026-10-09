import GaloisForLFunctions.HTGeometry.CircleRootPaths

open Complex Topology
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A d-th-root phase along one positive circle. -/
def powerRootCirclePhase (d : ℕ) : C(I, ℂ) where
  toFun t := circleMap 0 1 ((2 * Real.pi * (t : ℝ)) / (d : ℝ))
  continuous_toFun := by unfold circleMap; fun_prop

@[simp] theorem powerRootCirclePhase_zero (d : ℕ) : powerRootCirclePhase d 0 = 1 := by
  simp [powerRootCirclePhase, circleMap]

@[simp] theorem norm_powerRootCirclePhase (d : ℕ) (t : I) :
    ‖powerRootCirclePhase d t‖ = 1 := by
  change ‖circleMap 0 1 _‖ = 1
  simp only [norm_circleMap_zero, abs_one]

theorem powerRootCirclePhase_ne_zero (d : ℕ) (t : I) : powerRootCirclePhase d t ≠ 0 := by
  intro h
  have hn := norm_powerRootCirclePhase d t
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

/-- Taking the d-th power recovers the positive target circle exactly. -/
theorem powerRootCirclePhase_pow (d : ℕ) (hd : 0 < d) (t : I) :
    powerRootCirclePhase d t ^ d = positiveCirclePath 0 1 t := by
  change circleMap 0 1 ((2 * Real.pi * (t : ℝ)) / (d : ℝ)) ^ d =
    circleMap 0 1 (2 * Real.pi * (t : ℝ))
  rw [circleMap_zero_pow, one_pow]
  congr 1
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp [hd']

/-- The endpoint multiplier is the canonical primitive root of unity. -/
theorem powerRootCirclePhase_one (d : ℕ) :
    powerRootCirclePhase d 1 = Complex.exp (2 * Real.pi * Complex.I / (d : ℂ)) := by
  change circleMap 0 1 ((2 * Real.pi * (1 : ℝ)) / (d : ℝ)) = _
  simp only [mul_one,
    circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
  congr 1
  ring

end
end GaloisForLFunctions.HTGeometry
