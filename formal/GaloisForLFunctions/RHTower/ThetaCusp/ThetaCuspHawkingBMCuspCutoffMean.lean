import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMHeightLaplacian
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspSourceMean
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalCuspCutoff

/-!
# The complete source mean, including the literal cutoff height derivatives.

This leaf proves the displayed source or cusp identity. Causal continuation,
left-QNM evaluation and Hawking-clock extinction remain separate obligations.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMCuspProjection
open D4BMAngularSeries D4BMGlobalAngularResponse D4BMModularCore
noncomputable section

/-- The original cutoff response as its actual one-dimensional height function. -/
def cutoffHeight (q : XiZeroCopy) (branch : Bool) (y : ℝ) : ℂ :=
  cutoffResponse q branch ![0,y]

theorem cutoffResponse_eq_height (q : XiZeroCopy) (branch : Bool) (z : Fin 2 → ℝ) :
    cutoffResponse q branch z = cutoffHeight q branch (z 1) := rfl

/-- The actual height cutoff is globally smooth, also through nonpositive height. -/
theorem cutoffHeight_smooth (q : XiZeroCopy) (branch : Bool) :
    ContDiff ℝ ∞ (cutoffHeight q branch) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : 1 < y
  · have hz : ![0,y] ∈ domain := by change 0 < y; linarith
    have hf := (cutoffResponse_contDiffOn q branch).contDiffAt
      ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)
    have hc : ContDiff ℝ ∞ (fun t : ℝ => (![0,t] : Fin 2 → ℝ)) := by
      apply contDiff_pi.mpr
      intro i
      fin_cases i
      · exact contDiff_const
      · exact contDiff_id
    exact hf.comp y hc.contDiffAt
  · have he : cutoffHeight q branch =ᶠ[𝓝 y] (fun _ => 0) := by
      have h2 : y < 2 := by linarith
      filter_upwards [isOpen_Iio.mem_nhds h2] with t ht
      exact cutoffResponse_zero q branch ![0,t] ht.le
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- All original cutoff derivatives reduce to the actual second height derivative. -/
theorem cutoffResponse_laplacian (q : XiZeroCopy) (branch : Bool) (z : Fin 2 → ℝ) :
    hyperbolicLaplacian (cutoffResponse q branch) z =
      (z 1:ℂ)^(2 : ℕ)*deriv (deriv (cutoffHeight q branch)) (z 1) := by
  have he : cutoffResponse q branch = fun w => cutoffHeight q branch (w 1) := rfl
  rw [he]
  exact height_laplacian _ (cutoffHeight_smooth q branch) z

/-- The complete scalar square retains its two principal powers and the infinite paired-mode sum. -/
theorem mean_scalar_sq (u : ℂ) {y : ℝ} (hy : 0 < y) :
    mean (fun x => scalar u ![x,y] ^(2 : ℕ)) = principal u ![0,y] ^(2 : ℕ)+
      8*∑' N, amplitude u y N^(2 : ℕ) := by
  have ht : Continuous (fun x => tail u ![x,y]) := by
    have he : (fun x => tail u ![x,y]) = fun x => 2*series (amplitude u y) x :=
      funext (tail_eq_series u hy)
    rw [he]
    exact continuous_const.mul (series_continuous _ (amplitude_norm_summable u hy))
  have hr : Continuous (fun x => squareRemainder u ![x,y]) := by
    have he : (fun x => squareRemainder u ![x,y]) =
      fun x => 2*(principal u ![0,y]*tail u ![x,y])+tail u ![x,y] ^(2 : ℕ) := by
      funext x
      exact squareRemainder_eq u ![x,y]
    rw [he]
    exact (continuous_const.mul (continuous_const.mul ht)).add (ht.pow 2)
  have he : (fun x => scalar u ![x,y] ^(2 : ℕ)) =
    fun x => principal u ![0,y] ^(2 : ℕ)+squareRemainder u ![x,y] := by
    funext x
    change _ = principal u ![x,y] ^(2 : ℕ)+(scalar u ![x,y] ^(2 : ℕ)-principal u ![x,y] ^(2 : ℕ))
    ring
  rw [he]
  change (∫ x in Ioc (-1/2:ℝ) (1/2), principal u ![0,y] ^(2 : ℕ)+squareRemainder u ![x,y])=_
  rw [integral_add (integrable_const _) hr.integrableOn_Ioc]
  change (∫ _x in Ioc (-1/2:ℝ) (1/2), principal u ![0,y] ^(2 : ℕ))+
    mean (fun x => squareRemainder u ![x,y])=_
  rw [mean_squareRemainder u hy]
  norm_num

/-- Full projected forcing through the transition region: the complete cutoff
second derivative and original amplitude are retained explicitly. -/
theorem mean_forcing (q : XiZeroCopy) (branch : Bool) {y : ℝ} (hy : 0 < y) :
    mean (fun x => forcing q branch ![x,y]) =
      (parameter q branch/2)*(principal (center q) ![0,y] ^(2 : ℕ)+
        8*∑' N, amplitude (center q) y N^(2 : ℕ))-
      ((y:ℂ)^(2 : ℕ)*deriv (deriv (cutoffHeight q branch)) y-
        parameter q branch*cutoffHeight q branch y) := by
  have hs : Continuous (fun x => scalar (center q) ![x,y]) := by
    have hc : Continuous (fun x : ℝ => (![x,y] : Fin 2 → ℝ)) := by fun_prop
    exact (cuspLeg_contDiffOn .scalar (center q)).continuousOn.comp_continuous hc (fun _ => hy)
  have he (x : ℝ) : forcing q branch ![x,y] =
      (parameter q branch/2)*scalar (center q) ![x,y] ^(2 : ℕ)-
      ((y:ℂ)^(2 : ℕ)*deriv (deriv (cutoffHeight q branch)) y-
        parameter q branch*cutoffHeight q branch y) := by
    rw [forcing,cutoffResponse_laplacian,cutoffResponse_eq_height]
    rfl
  simp_rw [he]
  have hi : IntegrableOn (fun x => (parameter q branch/2)*scalar (center q) ![x,y] ^(2 : ℕ))
      (Ioc (-1/2:ℝ) (1/2)) := (continuous_const.mul (hs.pow 2)).integrableOn_Ioc
  change (∫ x in Ioc (-1/2:ℝ) (1/2), _-_) = _
  rw [integral_sub hi (integrable_const _),integral_const_mul]
  change (parameter q branch/2)*mean (fun x => scalar (center q) ![x,y] ^(2 : ℕ))-_= _
  rw [mean_scalar_sq _ hy]
  norm_num

end
end RHTower.D4BMCuspProjection
