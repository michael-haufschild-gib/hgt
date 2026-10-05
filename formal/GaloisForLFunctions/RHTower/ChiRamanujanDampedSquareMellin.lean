import GaloisForLFunctions.HTGeometry.MellinTestFunctionPerron
import GaloisForLFunctions.RHTower.LogPhasePhysicalWindow
import Mathlib.Analysis.MellinInversion

/-!
# Mellin inversion and arbitrary strip decay for the actual BAG window

Repeated Euler differentiation proves every polynomial decay order uniformly
on a fixed vertical strip. The literal physical height window supplies its
own smoothness, positive-axis support, entire transform, and inversion.
These are the window inputs to the joint damping-height contour transfer.
-/

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology ContDiff Asymptotics
open GaloisForLFunctions.HTGeometry.TestFunctionPerron
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

private theorem test_mellin_norm_pow_bound (n : ℕ) (R : ℝ) :
    ∀ {f : ℝ → ℂ} {a b : ℝ}, IsTest f a b →
    ∃ C ≥ 0, ∀ s : ℂ, |s.re-1| ≤ R → ‖s‖^n*‖mellin f s‖ ≤ C := by
  induction n with
  | zero =>
    intro f a b hf
    obtain ⟨B,hB,hbound⟩ := hf.exists_bound
    refine ⟨(b-a)*Real.exp (R*IsTest.logScale a b)*B,?_,?_⟩
    · have := sub_nonneg.mpr hf.le
      positivity
    · intro s hs
      simpa only [pow_zero,one_mul] using hf.norm_mellin_le hbound hs
  | succ n ih =>
    intro f a b hf
    obtain ⟨C,hC,hbound⟩ := ih hf.eulerDeriv
    refine ⟨C,hC,?_⟩
    intro s hs
    have h := hbound s hs
    rw [hf.mellin_eulerDeriv,norm_mul,norm_neg] at h
    simpa only [pow_succ,mul_assoc] using h

private theorem test_mellin_rapidDecay {f : ℝ → ℂ} {a b : ℝ} (hf : IsTest f a b)
    (n : ℕ) (R : ℝ) : ∃ C > 0, ∀ s : ℂ, |s.re-1| ≤ R →
      ‖mellin f s‖ ≤ C/(1+|s.im|)^n := by
  obtain ⟨B,hB,hBn⟩ := test_mellin_norm_pow_bound n R hf
  obtain ⟨A,hA,hA0⟩ := test_mellin_norm_pow_bound 0 R hf
  refine ⟨2^n*(A+B+1),by positivity,?_⟩
  intro s hs
  have h0 : ‖mellin f s‖ ≤ A := by simpa using hA0 s hs
  have hn := hBn s hs
  have hab : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  rw [le_div_iff₀ (by positivity)]
  by_cases hi : |s.im| ≤ 1
  · calc ‖mellin f s‖*(1+|s.im|)^n ≤ A*2^n := by gcongr; linarith
      _ ≤ 2^n*(A+B+1) := by nlinarith [pow_pos (by norm_num : (0 : ℝ)<2) n]
  · have hi' : 1 ≤ |s.im| := le_of_lt (lt_of_not_ge hi)
    calc ‖mellin f s‖*(1+|s.im|)^n ≤ ‖mellin f s‖*(2*‖s‖)^n := by gcongr; linarith
      _ = 2^n*(‖s‖^n*‖mellin f s‖) := by rw [mul_pow]; ring
      _ ≤ 2^n*B := mul_le_mul_of_nonneg_left hn (by positivity)
      _ ≤ 2^n*(A+B+1) := by gcongr; linarith

private theorem physical_window_isTest :
    IsTest (fun x : ℝ => (bagPhysicalHeightWindow x : ℂ)) 1 2 := by
  refine ⟨by norm_num,by norm_num,Complex.ofRealCLM.contDiff.comp bagPhysicalHeightWindow.contDiff,?_⟩
  intro x hx
  have hne : bagPhysicalHeightWindow x ≠ 0 := by simpa using hx
  have hm : x ∈ Metric.ball (3/2 : ℝ) bagPhysicalHeightWindow.rOut := by
    rw [← bagPhysicalHeightWindow.support_eq]
    exact hne
  have hb : |x-3/2| < (1/2 : ℝ) := by simpa only [Metric.mem_ball,Real.dist_eq,bagPhysicalHeightWindow] using hm
  constructor <;> linarith [(abs_lt.mp hb).1,(abs_lt.mp hb).2]

def dampedSquareWindowMellin (s : ℂ) : ℂ :=
  mellin (fun x : ℝ => (bagPhysicalHeightWindow x : ℂ)) s

theorem differentiable_dampedSquareWindowMellin : Differentiable ℂ dampedSquareWindowMellin :=
  physical_window_isTest.differentiableAt_mellin

theorem exists_dampedSquareWindowMellin_rapidDecay (n : ℕ) (R : ℝ) :
    ∃ C > 0, ∀ s : ℂ, |s.re-1| ≤ R →
      ‖dampedSquareWindowMellin s‖ ≤ C/(1+|s.im|)^n :=
  test_mellin_rapidDecay physical_window_isTest n R

theorem integrable_dampedSquareWindowMellin_vertical (σ : ℝ) :
    Integrable (fun t : ℝ => dampedSquareWindowMellin ((σ : ℂ)+t*I)) :=
  physical_window_isTest.verticalIntegrable σ

theorem mellinConvergent_dampedSquareWindow (s : ℂ) :
    MellinConvergent (fun x : ℝ => (bagPhysicalHeightWindow x : ℂ)) s := by
  apply mellinConvergent_of_isBigO_rpow
    (a := s.re+1) (b := s.re-1)
    (physical_window_isTest.continuous.locallyIntegrable.locallyIntegrableOn _)
  · refine Filter.EventuallyEq.trans_isBigO ?_ (Asymptotics.isBigO_zero _ _)
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    exact physical_window_isTest.eq_zero_of_ge hx.le
  · linarith
  · refine Filter.EventuallyEq.trans_isBigO ?_ (Asymptotics.isBigO_zero _ _)
    filter_upwards [(eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds] with x hx
    exact physical_window_isTest.eq_zero_of_le hx.le
  · linarith

theorem mellinInv_dampedSquareWindowMellin (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ dampedSquareWindowMellin x = (bagPhysicalHeightWindow x : ℂ) := by
  apply mellinInv_mellin_eq σ _ hx (mellinConvergent_dampedSquareWindow σ)
    (integrable_dampedSquareWindowMellin_vertical σ)
  exact physical_window_isTest.continuous.continuousAt

end RHTower.BAGTrace
