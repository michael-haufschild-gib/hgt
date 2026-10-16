import GaloisForLFunctions.RHTower.PaperThetaNativeMomentIdentity
import GaloisForLFunctions.RHTower.CHMDCompactGraphCutoffs
import Mathlib.Analysis.Normed.Algebra.Exponential

/-! # A compact source channel transverse to every theta character

Modulating one fixed nonnegative compact smooth source cancels the character
exactly. Its moment is one positive constant throughout the complex plane.
The modulation is entire in the original uniform Banach space.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile CHMDDoobGraph

def nativeClampedCoordinate (x : ℝ) : ℝ := max (-2) (min 2 x)

theorem nativeClampedCoordinate_bound (x : ℝ) : |nativeClampedCoordinate x| ≤ 2 := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem nativeClampedCoordinate_eq {x : ℝ} (hx : x ∈ Icc (-2 : ℝ) 2) :
    nativeClampedCoordinate x = x := by
  simp only [nativeClampedCoordinate, min_eq_right hx.2, max_eq_right hx.1]

def nativeCoordinateBCF : NativeContinuousSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (nativeClampedCoordinate x : ℂ))
    (by unfold nativeClampedCoordinate; fun_prop) 2
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using nativeClampedCoordinate_bound x)

def nativeCounterSeed : NativeContinuousSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (baseCutoff x : ℂ))
    (Complex.continuous_ofReal.comp baseCutoff.continuous) 1 (fun x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg baseCutoff.nonneg] using
        (baseCutoff.le_one : baseCutoff x ≤ 1))

private def nativeEvalRingHom (x : ℝ) : NativeContinuousSpace →+* ℂ where
  toFun f := f x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A single entire, compactly supported channel works at every resonance. -/
def nativeCounterSource (z : ℂ) : NativeContinuousSpace :=
  nativeCounterSeed * NormedSpace.exp ((-I*z) • nativeCoordinateBCF)

theorem nativeCounterSource_apply (z : ℂ) (x : ℝ) :
    nativeCounterSource z x = exp (-(I*z)*(x : ℂ))*(baseCutoff x : ℂ) := by
  have he := NormedSpace.map_exp (nativeEvalRingHom x)
    (BoundedContinuousFunction.evalCLM ℂ x).continuous ((-I*z) • nativeCoordinateBCF)
  change (NormedSpace.exp ((-I*z) • nativeCoordinateBCF)) x =
    NormedSpace.exp ((-I*z)*(nativeClampedCoordinate x : ℂ)) at he
  rw [← Complex.exp_eq_exp_ℂ] at he
  change (baseCutoff x : ℂ)*(NormedSpace.exp ((-I*z) • nativeCoordinateBCF)) x = _
  rw [he]
  by_cases hx : x ∈ Icc (-2 : ℝ) 2
  · rw [nativeClampedCoordinate_eq hx]
    rw [show (-I*z)*(x : ℂ) = -(I*z)*(x : ℂ) by ring]
    exact mul_comm _ _
  · have hb : baseCutoff x = 0 := by
      apply baseCutoff.zero_of_le_dist
      change 2 ≤ dist x 0
      rw [Real.dist_eq, sub_zero]
      have h := not_and_or.mp hx
      rcases h with h | h
      · exact (neg_le_abs x).trans' (by linarith [not_le.mp h])
      · exact (le_abs_self x).trans' (le_of_lt (not_le.mp h))
    simp only [hb, Complex.ofReal_zero, zero_mul, mul_zero]

theorem differentiable_nativeCounterSource : Differentiable ℂ nativeCounterSource := by
  have he : Differentiable ℂ (NormedSpace.exp : NativeContinuousSpace → NativeContinuousSpace) :=
    fun x => (NormedSpace.exp_analytic (𝕂 := ℂ) x).differentiableAt
  exact (differentiable_const nativeCounterSeed).mul
    (he.comp (((differentiable_const (-I)).mul differentiable_id).smul_const nativeCoordinateBCF))

theorem nativeCounterSource_contDiff (z : ℂ) : ContDiff ℝ 2 (nativeCounterSource z) := by
  have he : (nativeCounterSource z : ℝ → ℂ) =
      fun x : ℝ => exp (-(I*z)*(x : ℂ))*(baseCutoff x : ℂ) := funext (nativeCounterSource_apply z)
  rw [he]
  exact (((show ContDiff ℝ 2 (fun _ : ℝ => -(I*z)) from contDiff_const).mul
    (Complex.ofRealCLM.contDiff : ContDiff ℝ 2 (fun x : ℝ => (x : ℂ)))).cexp).mul
    (Complex.ofRealCLM.contDiff.comp (baseCutoff.contDiff : ContDiff ℝ 2 baseCutoff))

theorem nativeCounterSource_hasCompactSupport (z : ℂ) : HasCompactSupport (nativeCounterSource z) := by
  have hs : HasCompactSupport (fun x : ℝ => (baseCutoff x : ℂ)) :=
    baseCutoff.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have he : (nativeCounterSource z : ℝ → ℂ) =
      fun x : ℝ => exp (-(I*z)*(x : ℂ))*(baseCutoff x : ℂ) := funext (nativeCounterSource_apply z)
  rw [he]
  exact hs.mul_left

def nativeCounterMass : ℝ := ∫ x, thetaSource.normalized x*baseCutoff x

theorem nativeCounterMass_pos : 0 < nativeCounterMass := by
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((thetaSource.continuous_k.div_const thetaSource.mass).mul baseCutoff.continuous)
    baseCutoff.hasCompactSupport.mul_left
    (fun x => mul_nonneg (thetaSource.normalized_pos x).le baseCutoff.nonneg) (x := 0)
  change thetaSource.normalized 0*baseCutoff 0 ≠ 0
  rw [baseCutoff.one_of_mem_closedBall (by norm_num [baseCutoff]), mul_one]
  exact (thetaSource.normalized_pos 0).ne'

theorem nativeCounterSource_moment (z : ℂ) :
    boundedThetaMomentCLM z (nativeCounterSource z) = (nativeCounterMass : ℂ) := by
  change (∫ x, flatCharDensity z x*nativeCounterSource z x) = _
  have he (x : ℝ) : flatCharDensity z x*nativeCounterSource z x =
      ((thetaSource.normalized x*baseCutoff x : ℝ) : ℂ) := by
    rw [nativeCounterSource_apply]
    dsimp [flatCharDensity, sourceChar]
    rw [show -(I*z)*(x : ℂ) = -(I*z*(x : ℂ)) by ring]
    rw [show (thetaSource.normalized x : ℂ)*exp (I*z*(x : ℂ))*
      (exp (-(I*z*(x : ℂ)))*(baseCutoff x : ℂ)) =
      (thetaSource.normalized x : ℂ)*(exp (I*z*(x : ℂ))*exp (-(I*z*(x : ℂ))))*
        (baseCutoff x : ℂ) by ring, ← exp_add, add_neg_cancel, exp_zero, mul_one]
    exact (Complex.ofReal_mul _ _).symm
  simp_rw [he]
  exact integral_complex_ofReal

end RHTower.PaperThetaEndpoint
