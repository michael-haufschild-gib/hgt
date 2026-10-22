import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerMellinStripControl
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGaussianStripRegularization
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogFrechet
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Gaussian removal in the original all-weight source topology

Vertical Mellin inversion bounds every source gauge by an integrable line
trace. Dominated convergence therefore removes Gaussian damping in all
weights and derivative orders, without changing the underlying source.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology

theorem deningerMeyerInverseMellinSource_source (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerInverseMellinSource (deningerMeyerStrongLogMellin g)
      (deningerMeyerStrongLogMellin_entireRegular g) = g := by
  apply deningerMeyerStrongLogMellin_injective
  exact funext (deningerMeyerInverseMellinSource_mellin
    (deningerMeyerStrongLogMellin_entireRegular g))

theorem deningerMeyerInverseMellinSource_gauge_le
    {F : ℂ → ℂ} (hF : DeningerEntireMellinRegular F) (n : ℕ) (k : ℤ) :
    ‖deningerMeyerStrongLogGauge n k (deningerMeyerInverseMellinSource F hF)‖ ≤
      (1/(2*Real.pi))*∫ y : ℝ, ‖(-((k:ℂ)+y*I))^n*F ((k:ℂ)+y*I)‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro t
  change ‖((Real.exp t^(k:ℝ):ℝ):ℂ)*
    iteratedDeriv n (deningerMeyerInverseMellinProfile F) t‖ ≤ _
  rw [iteratedDeriv_deningerMeyerInverseMellinProfile hF,
    deningerMeyerInverseMellinProfile, (hF.signedPow n).inverse_line_eq 1 (k:ℝ) t,
    norm_mul, Complex.norm_real,
    Real.norm_eq_abs (Real.exp t^(k:ℝ)),
    abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos t) _)]
  have hb := GaloisForLFunctions.HTGeometry.norm_mellinInv_le
    (Ψ := fun s => (-s)^n*F s) (k:ℝ) (Real.exp_pos t)
  have hc : Real.exp t^(k:ℝ)*Real.exp t^(-(k:ℝ)) = 1 := by
    rw [← Real.rpow_add (Real.exp_pos t), add_neg_cancel, Real.rpow_zero]
  calc Real.exp t^(k:ℝ)*‖mellinInv (k:ℝ) (fun s => (-s)^n*F s) (Real.exp t)‖
      ≤ Real.exp t^(k:ℝ)*((1/(2*Real.pi))*Real.exp t^(-(k:ℝ))*
        ∫ y : ℝ, ‖(-(((k:ℝ):ℂ)+y*I))^n*F (((k:ℝ):ℂ)+y*I)‖) := by
          exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      push_cast
      calc Real.exp t^(k:ℝ)*((1/(2*Real.pi))*Real.exp t^(-(k:ℝ))*
          ∫ y : ℝ, ‖(-((k:ℂ)+y*I))^n*F ((k:ℂ)+y*I)‖)
          = (Real.exp t^(k:ℝ)*Real.exp t^(-(k:ℝ)))*
            ((1/(2*Real.pi))*∫ y : ℝ, ‖(-((k:ℂ)+y*I))^n*F ((k:ℂ)+y*I)‖) := by ring
        _ = _ := by rw [hc, one_mul]

/-- All weighted derivatives are controlled by their own vertical Mellin line. -/
theorem deningerMeyerStrongLogGauge_le_mellin
    (g : DeningerMeyerStrongLogTarget) (n : ℕ) (k : ℤ) :
    ‖deningerMeyerStrongLogGauge n k g‖ ≤
      (1/(2*Real.pi))*∫ y : ℝ,
        ‖(-((k:ℂ)+y*I))^n*deningerMeyerStrongLogMellin g ((k:ℂ)+y*I)‖ := by
  simpa only [deningerMeyerInverseMellinSource_source] using
    deningerMeyerInverseMellinSource_gauge_le (deningerMeyerStrongLogMellin_entireRegular g) n k

theorem deningerMeyerStrongLogMellin_gaussianRegular
    (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) :
    DeningerEntireMellinRegular
      (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g)) := by
  apply deningerGaussianMellinRegularization_entireRegular
    (deningerMeyerStrongLogMellin_entireRegular g).differentiable _ hε
  intro a b
  obtain ⟨C, hC, hc⟩ := deningerMeyerStrongLogMellin_strip_bound g a b
  exact ⟨C, 0, hC, le_rfl, fun s ha hb => by simpa using hc s ha hb⟩

def deningerMeyerGaussianSource (g : DeningerMeyerStrongLogTarget) (m : ℕ) :
    DeningerMeyerStrongLogTarget :=
  deningerMeyerInverseMellinSource
    (deningerGaussianMellinRegularization (1/((m:ℝ)+1)) (deningerMeyerStrongLogMellin g))
    (deningerMeyerStrongLogMellin_gaussianRegular g (by positivity))

theorem deningerMeyerGaussianSource_mellin
    (g : DeningerMeyerStrongLogTarget) (m : ℕ) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerGaussianSource g m) s =
      Complex.exp (((1/((m:ℝ)+1):ℝ):ℂ)*s^2)*deningerMeyerStrongLogMellin g s :=
  deningerMeyerInverseMellinSource_mellin _ s

private theorem gaussian_multiplier_le {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (s : ℂ) :
    ‖Complex.exp ((ε:ℂ)*s^2)‖ ≤ Real.exp (s.re^2) := by
  rw [Complex.norm_exp]
  have he : ((ε:ℂ)*s^2).re = ε*(s.re^2-s.im^2) := by
    simp [pow_two, Complex.mul_re, Complex.mul_im]
  rw [he]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hε (sq_nonneg s.im),
    mul_le_mul_of_nonneg_right hε₁ (sq_nonneg s.re)]

private theorem gaussian_line_error_tendsto
    (g : DeningerMeyerStrongLogTarget) (n : ℕ) (k : ℤ) :
    Tendsto (fun m : ℕ => ∫ y : ℝ,
      ‖(Complex.exp (((1/((m:ℝ)+1):ℝ):ℂ)*((k:ℂ)+y*I)^2)-1)*
        ((-((k:ℂ)+y*I))^n*deningerMeyerStrongLogMellin g ((k:ℂ)+y*I))‖)
      atTop (𝓝 0) := by
  let P : ℂ → ℂ := fun s => (-s)^n*deningerMeyerStrongLogMellin g s
  have hP := (deningerMeyerStrongLogMellin_entireRegular g).signedPow n
  have hi := (hP ((k:ℝ)-1) ((k:ℝ)+1)).integrable_line
    (c := (k:ℝ)) (by linarith) (by linarith)
  have hPc : Continuous P := hP.differentiable.continuous
  have hε : Tendsto (fun m : ℕ => ((1/((m:ℝ)+1):ℝ):ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hd := tendsto_integral_of_dominated_convergence
    (fun y : ℝ => (Real.exp ((k:ℝ)^2)+1)*‖P ((k:ℂ)+y*I)‖)
    (f := fun _ => (0:ℝ))
    (F := fun (m : ℕ) (y : ℝ) => ‖(Complex.exp (((1/((m:ℝ)+1):ℝ):ℂ)*((k:ℂ)+y*I)^2)-1)*
      P ((k:ℂ)+y*I)‖)
    (fun m => (show Continuous (fun y : ℝ =>
      ‖(Complex.exp (((1/((m:ℝ)+1):ℝ):ℂ)*((k:ℂ)+y*I)^2)-1)*P ((k:ℂ)+y*I)‖)
      from by fun_prop).aestronglyMeasurable)
    (by simpa only [Complex.ofReal_intCast] using hi.norm.const_mul (Real.exp ((k:ℝ)^2)+1))
    (fun m => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_norm, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hb := gaussian_multiplier_le (by positivity : 0 ≤ 1/((m:ℝ)+1))
        (by apply (div_le_one (by positivity)).mpr; linarith [Nat.cast_nonneg (α := ℝ) m])
        ((k:ℂ)+y*I)
      have hr : (((k:ℂ)+y*I):ℂ).re = (k:ℝ) := by simp
      rw [hr] at hb
      exact (norm_sub_le _ _).trans (by simpa using add_le_add_right hb 1))
    (Eventually.of_forall fun y => by
      have he := (Complex.continuous_exp.continuousAt.tendsto.comp
        (hε.mul_const (((k:ℂ)+y*I)^2))).sub_const 1
      simpa using (he.mul_const (P ((k:ℂ)+y*I))).norm)
  simpa [P] using hd

/-- Gaussian removal converges in every source gauge simultaneously. -/
theorem deningerMeyerGaussianSource_tendsto (g : DeningerMeyerStrongLogTarget) :
    Tendsto (deningerMeyerGaussianSource g) atTop (𝓝 g) := by
  have herr : Tendsto (fun m => deningerMeyerGaussianSource g m - g) atTop (𝓝 0) := by
    change Tendsto _ _ (@nhds _ (⨅ i : ℕ × ℤ, TopologicalSpace.induced
      (deningerMeyerStrongLogGaugeLinear i.1 i.2) inferInstance) 0)
    rw [nhds_iInf, tendsto_iInf]
    intro i
    rw [nhds_induced, map_zero, tendsto_comap_iff, tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (g := fun m : ℕ => (1/(2*Real.pi))*∫ y : ℝ,
      ‖(Complex.exp (((1/((m:ℝ)+1):ℝ):ℂ)*((i.2:ℂ)+y*I)^2)-1)*
        ((-((i.2:ℂ)+y*I))^i.1*deningerMeyerStrongLogMellin g ((i.2:ℂ)+y*I))‖)
      (fun _ => norm_nonneg _)
    · intro m
      have hb := deningerMeyerStrongLogGauge_le_mellin
        (deningerMeyerGaussianSource g m-g) i.1 i.2
      change ‖deningerMeyerStrongLogGauge i.1 i.2 (deningerMeyerGaussianSource g m-g)‖ ≤ _
      refine hb.trans_eq ?_
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      have he (s : ℂ) : deningerMeyerStrongLogMellin
          (deningerMeyerGaussianSource g m-g : DeningerMeyerStrongLogTarget) s =
          (Complex.exp (((1/((m:ℝ)+1):ℝ):ℂ)*s^2)-1)*deningerMeyerStrongLogMellin g s := by
        change deningerMeyerStrongLogMellinLM s (deningerMeyerGaussianSource g m-g) = _
        rw [map_sub]
        change deningerMeyerStrongLogMellin (deningerMeyerGaussianSource g m) s -
          deningerMeyerStrongLogMellin g s = _
        rw [deningerMeyerGaussianSource_mellin]
        ring
      rw [he]
      congr 1
      ring
    · simpa using (gaussian_line_error_tendsto g i.1 i.2).const_mul (1/(2*Real.pi))
  simpa only [sub_add_cancel, zero_add] using herr.add_const g

end
end RHTower
