import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeSquareResidualMellinReduction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspCutoffMean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The actual unfolded source mean retains the complete paired Fourier series and full cutoff orbit sum. -/
open Set Filter Topology MeasureTheory UpperHalfPlane
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries D4BMCuspProjection
noncomputable section

/-- The actual mean of the complete cutoff periodization, including all nonparabolic images. -/
def squareCutoffStripMean (q : XiZeroCopy) (y : ℝ) : ℂ :=
  ∫ x in Ico (0:ℝ) 1, periodize (squareCutoffSeed q) (ofComplex (⟨x,y⟩:ℂ))

private theorem horizontalPoint_continuous {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => ofComplex (⟨x,y⟩:ℂ)) := by
  have hm : Continuous (fun x : ℝ => (⟨x,y⟩:ℂ)) := by
    have he : (fun x : ℝ => (⟨x,y⟩:ℂ)) = (fun x : ℝ => (x:ℂ)+(y:ℂ)*Complex.I) := by
      funext x
      apply Complex.ext <;> simp
    rw [he]
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (contMDiffAt_ofComplex (n := 0) (by simpa using hy)).continuousAt.comp hm.continuousAt

private theorem scalarSquare_unit_mean (q : XiZeroCopy) {y : ℝ} (hy : 0 < y) :
    (∫ x in Ico (0:ℝ) 1, scalar (center q) ![x,y] ^2) =
      principal (center q) ![0,y] ^2+8*∑' N, amplitude (center q) y N^2 := by
  have hp : Function.Periodic (fun x : ℝ => scalar (center q) ![x,y] ^2) 1 := by
    intro x
    have he : scalar (center q) ![x+1,y] = scalar (center q) ![x,y] := by
      simpa [scalar] using d4BM_completedEisensteinCuspLeg_scalar_periodic (center q) y x
    dsimp only
    rw [he]
  have hs := hp.intervalIntegral_add_eq 0 (-1/2)
  have hs' : (∫ x in (0:ℝ)..1, scalar (center q) ![x,y] ^2) =
      ∫ x in (-1/2:ℝ)..(1/2:ℝ), scalar (center q) ![x,y] ^2 := by
    convert hs using 1 <;> norm_num
  rw [intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num),
    intervalIntegral.integral_of_le (show (-1/2:ℝ)≤1/2 by norm_num)] at hs'
  rw [integral_Ico_eq_integral_Ioc,hs']
  exact mean_scalar_sq (center q) hy

/-- Exact full source mean; the cutoff orbit correction is retained before the Mellin integral. -/
theorem residualStripMean_eq_fourier (q : XiZeroCopy) {y : ℝ} (hy : 0 < y) :
    residualStripMean q y = principal (center q) ![0,y] ^2/2+
      4*(∑' N, amplitude (center q) y N^2)-squareCutoffStripMean q y := by
  let F (x : ℝ) := scalar (center q) ![x,y] ^2
  let G (x : ℝ) := globalSquareResidual q (ofComplex (⟨x,y⟩:ℂ))
  let H (x : ℝ) := periodize (squareCutoffSeed q) (ofComplex (⟨x,y⟩:ℂ))
  have hF : Continuous F :=
    ((cuspLeg_contDiffOn .scalar (center q)).continuousOn.comp_continuous
      (by fun_prop) (fun _ => hy)).pow 2
  have hG : Continuous G := (globalSquareResidual_smooth q).continuous.comp (horizontalPoint_continuous hy)
  have he (x : ℝ) : G x = F x/2-H x := by
    dsimp [F,G,H]
    rw [globalSquareResidual_eq_periodized]
    rw [ofComplex_apply_of_im_pos (by simpa using hy)]
    dsimp [fullSquarePotential,coordinates]
    ring
  have hH : Continuous H := by
    have hh : H = fun x => F x/2-G x := by
      funext x
      rw [he x]
      ring
    rw [hh]
    exact (hF.div_const 2).sub hG
  change (∫ x in Ico (0:ℝ) 1, G x) = _
  simp_rw [he]
  rw [integral_sub ((hF.div_const 2).integrableOn_Icc.mono_set Ico_subset_Icc_self)
    (hH.integrableOn_Icc.mono_set Ico_subset_Icc_self)]
  have hdiv : (∫ x in Ico (0:ℝ) 1, F x/2) = (∫ x in Ico (0:ℝ) 1, F x)/2 := by
    simp only [div_eq_mul_inv,integral_mul_const]
  rw [hdiv]
  change (∫ x in Ico (0:ℝ) 1, scalar (center q) ![x,y] ^2)/2-squareCutoffStripMean q y = _
  rw [scalarSquare_unit_mean q hy]
  ring

/-- The native period has its derived complete Fourier--Mellin integrand, with all cutoff images retained. -/
theorem scalarResidualPeriod_eq_full_fourier_mellin (q : XiZeroCopy)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    scalarResidualPeriod q (P.s-1/2) = reflectedCompletedLambda (2*P.s)*
      ∫ y in Ioi (0:ℝ), (y:ℂ)^(P.s-2)*
        (principal (center q) ![0,y] ^2/2+4*(∑' N, amplitude (center q) y N^2)-
          squareCutoffStripMean q y) := by
  rw [scalarResidualPeriod_eq_mellin]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  rw [residualStripMean_eq_fourier q hy]

end
end RHTower.D4BMJointSource
