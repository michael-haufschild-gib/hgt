import GaloisForLFunctions.HTGeometry.FokasLenellsSmallScattering
import GaloisForLFunctions.HTGeometry.FokasLenellsSingularPhase

/-!
# Uniform-in-time coercivity for constructed scattering data

The angle in (5.1) of Yan–Zhang–Zhu, arXiv:2607.19649v1, supplies the
space-time factors of the actual scattering quotients. The two factors have
opposite signs as in (5.4); their product and individual moduli are preserved.

For the explicitly rescaled Schwartz potentials, the jump determinant stays
one and the `5/9` coercivity bound holds at every real position and time,
uniformly throughout the prescribed positive spectral band.

This proves persistence of the jump estimate for the prescribed scattering
evolution. It does not reconstruct a nonlinear PDE solution.
-/

open Complex Matrix
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The space-time phase in equation (5.1). -/
def scatteringAngle (κ t x : ℝ) : ℝ :=
  (Real.exp κ)^(2 : ℕ)*x-t/(4*(Real.exp κ)^(2 : ℕ))

/-- Lower-left reflection coefficient, including the signs of (3.3) and (5.4). -/
def spaceTimeReflection (q : SchwartzMap ℝ ℂ) (κ t x : ℝ) : ℂ :=
  FDNLS.staggerPhase 2 (scatteringAngle κ t x)*reflectionCoefficient q κ

def spaceTimeReverseReflection (q : SchwartzMap ℝ ℂ) (κ t x : ℝ) : ℂ :=
  FDNLS.staggerPhase (-2) (scatteringAngle κ t x)*reverseReflectionCoefficient q κ

theorem spaceTimeReflection_norm (q : SchwartzMap ℝ ℂ) (κ t x : ℝ) :
    ‖spaceTimeReflection q κ t x‖ = ‖reflectionCoefficient q κ‖ := by
  simp [spaceTimeReflection, FDNLS.norm_staggerPhase]

theorem spaceTimeReverseReflection_norm (q : SchwartzMap ℝ ℂ) (κ t x : ℝ) :
    ‖spaceTimeReverseReflection q κ t x‖ = ‖reverseReflectionCoefficient q κ‖ := by
  simp [spaceTimeReverseReflection, FDNLS.norm_staggerPhase]

/-- The time factor for `r` is the positive exponential in (5.4). -/
theorem spaceTimeReflection_time_factor (q : SchwartzMap ℝ ℂ) (κ t x : ℝ) :
    spaceTimeReflection q κ t x =
      phase (-t) ((Real.exp κ)^(2 : ℕ))*spaceTimeReflection q κ 0 x := by
  unfold spaceTimeReflection FDNLS.staggerPhase scatteringAngle phase
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_ofNat, zero_div, sub_zero]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The reverse reflection carries the opposite time factor. -/
theorem spaceTimeReverseReflection_time_factor (q : SchwartzMap ℝ ℂ) (κ t x : ℝ) :
    spaceTimeReverseReflection q κ t x =
      phase t ((Real.exp κ)^(2 : ℕ))*spaceTimeReverseReflection q κ 0 x := by
  unfold spaceTimeReverseReflection FDNLS.staggerPhase scatteringAngle phase
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_ofNat, zero_div, sub_zero]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem spaceTimeReflection_product (q : SchwartzMap ℝ ℂ) (κ t x : ℝ) :
    spaceTimeReflection q κ t x*spaceTimeReverseReflection q κ t x =
      reflectionCoefficient q κ*reverseReflectionCoefficient q κ := by
  unfold spaceTimeReflection spaceTimeReverseReflection
  have hp : FDNLS.staggerPhase 2 (scatteringAngle κ t x)*
      FDNLS.staggerPhase (-2) (scatteringAngle κ t x) = 1 := by
    simp [FDNLS.staggerPhase, ← Complex.exp_add]
  calc
    _ = (FDNLS.staggerPhase 2 (scatteringAngle κ t x)*
      FDNLS.staggerPhase (-2) (scatteringAngle κ t x))*
      (reflectionCoefficient q κ*reverseReflectionCoefficient q κ) := by ring
    _ = _ := by rw [hp, one_mul]

def spaceTimeJump (q : SchwartzMap ℝ ℂ) (κ t x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  jump (spaceTimeReflection q κ t x) (spaceTimeReverseReflection q κ t x)

theorem spaceTimeJump_det (q : SchwartzMap ℝ ℂ) (κ t x : ℝ) :
    (spaceTimeJump q κ t x).det = 1 := det_jump _ _

/-- The quantitative jump bound persists for every real position and time in (5.1). -/
theorem smallScatteringPotential_spaceTime_coercivity (q : SchwartzMap ℝ ℂ)
    (K s t x : ℝ) (u v : ℂ) :
    (5/9 : ℝ)*(normSq u+normSq v) ≤
      energy (spaceTimeReflection (smallScatteringPotential q K) (K-|s|) t x)
        (spaceTimeReverseReflection (smallScatteringPotential q K) (K-|s|) t x) u v := by
  let a := spaceTimeReflection (smallScatteringPotential q K) (K-|s|) t x
  let b := spaceTimeReverseReflection (smallScatteringPotential q K) (K-|s|) t x
  have h := smallScatteringPotential_reflection_bounds q K s
  have ha : ‖a‖ ≤ 1/3 := by simpa only [a, spaceTimeReflection_norm] using h.1
  have hb : ‖b‖ ≤ 1/3 := by simpa only [b, spaceTimeReverseReflection_norm] using h.2
  have hab : ‖a‖*‖b‖ ≤ 1/9 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1/3-‖a‖) (norm_nonneg b)]
  have h1 : 5/9 ≤ 1-(‖a‖+‖b‖)/2 := by linarith
  have h2 : 5/9 ≤ 1-‖a‖*‖b‖-(‖a‖+‖b‖)/2 := by linarith
  calc
    (5/9 : ℝ)*(normSq u+normSq v) = (5/9 : ℝ)*normSq u+(5/9 : ℝ)*normSq v := by ring
    _ ≤ (1-(‖a‖+‖b‖)/2)*normSq u+(1-‖a‖*‖b‖-(‖a‖+‖b‖)/2)*normSq v :=
      add_le_add (mul_le_mul_of_nonneg_right h1 (normSq_nonneg u))
        (mul_le_mul_of_nonneg_right h2 (normSq_nonneg v))
    _ ≤ _ := energy_norm_lower_bound a b u v

end
end GaloisForLFunctions.HTGeometry.FokasLenells
