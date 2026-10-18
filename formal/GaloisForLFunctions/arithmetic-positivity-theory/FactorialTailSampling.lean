import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailDiskSampling
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailStripEnergy
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCorrectedSampling
import GaloisForLFunctions.RHTower.WeilDeletionZeroSide
import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailSmoothing

/-! Absolute square sampling of the literal factorial tail and every normalized
smoothing. Local holomorphy, global zero counts, and the arithmetic Fourier
budget are discharged; no Weil positivity or zero-location premise is used. -/

open MeasureTheory Set Metric
open _root_.Zeta23 _root_.RHTower
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
namespace GaloisForLFunctions.ArithmeticPositivityTheory
noncomputable section
set_option autoImplicit false

private theorem readout_ball_integrable (n : ℕ) (q : XiZeroCopy) :
    IntegrableOn (fun s : ℂ => ‖factorialTailReadout n s‖^2)
      (Metric.ball (q.1 : ℂ) (1/4)) := by
  have hc : ContinuousOn (fun s : ℂ => ‖factorialTailReadout n s‖^2)
      (Metric.closedBall (q.1 : ℂ) (1/4)) := by
    apply ((factorialTailReadout_analyticOnNhd n).continuousOn.mono ?_).norm.pow 2
    intro s hs
    have hd : ‖s-(q.1 : ℂ)‖ ≤ (1/4 : ℝ) := by
      simpa only [Metric.mem_closedBall,dist_eq_norm] using hs
    have hz := xi_divisor_support_re_mem_open_unit q.1
    have hr := (abs_le.mp (Complex.abs_re_le_norm (s-(q.1 : ℂ)))).1
    simp only [Complex.sub_re] at hr
    change -1 < s.re
    linarith
  exact (hc.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall

private theorem finite_copy_sampling_le (n : ℕ) (C : ℝ)
    (hC : ∀ (F : Finset XiZeroCopy) (s : ℂ), zeroDiskOverlap F s ≤
      zeroSamplingStrip.indicator (fun z : ℂ => C*(1+Real.log (2+|z.im|))) s)
    (F : Finset XiZeroCopy) :
    (Real.pi/16)*(∑ q ∈ F,‖factorialTailReadout n (q.1 : ℂ)‖^2) ≤
      C*(∫ s : ℂ,factorialTailStripDensity n s) := by
  classical
  let b : XiZeroCopy → ℂ → ℝ := fun q => (Metric.ball (q.1 : ℂ) (1/4)).indicator
    (fun s : ℂ => ‖factorialTailReadout n s‖^2)
  have hb (q : XiZeroCopy) : Integrable (b q) :=
    (integrable_indicator_iff measurableSet_ball).mpr (readout_ball_integrable n q)
  have hpoint (s : ℂ) : (∑ q ∈ F,b q s) =
      zeroDiskOverlap F s*‖factorialTailReadout n s‖^2 := by
    rw [zeroDiskOverlap,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hs : s ∈ Metric.ball (q.1 : ℂ) (1/4)
    · simp only [b,indicator_of_mem hs,if_pos hs,one_mul]
    · simp only [b,indicator_of_notMem hs,if_neg hs,zero_mul]
  have hbound (s : ℂ) : (∑ q ∈ F,b q s) ≤ C*factorialTailStripDensity n s := by
    rw [hpoint]
    have h := mul_le_mul_of_nonneg_right (hC F s) (sq_nonneg ‖factorialTailReadout n s‖)
    apply h.trans_eq
    by_cases hs : s ∈ zeroSamplingStrip
    · simp only [factorialTailStripDensity,indicator_of_mem hs]
      ring
    · simp only [factorialTailStripDensity,indicator_of_notMem hs,zero_mul,mul_zero]
  calc
    (Real.pi/16)*(∑ q ∈ F,‖factorialTailReadout n (q.1 : ℂ)‖^2) =
        ∑ q ∈ F,(Real.pi/16)*‖factorialTailReadout n (q.1 : ℂ)‖^2 := Finset.mul_sum ..
    _ ≤ ∑ q ∈ F,∫ s in Metric.ball (q.1 : ℂ) (1/4),‖factorialTailReadout n s‖^2 := by
      apply Finset.sum_le_sum
      intro q hq
      have hz := xi_divisor_support_re_mem_open_unit q.1
      exact factorialTailReadout_disk_mean_square n ⟨q.1,hz.1.le,hz.2.le⟩
    _ = ∑ q ∈ F,∫ s : ℂ,b q s := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (integral_indicator measurableSet_ball).symm
    _ = ∫ s : ℂ,∑ q ∈ F,b q s := (integral_finsetSum F (fun q _ => hb q)).symm
    _ ≤ ∫ s : ℂ,C*factorialTailStripDensity n s :=
      integral_mono (integrable_finsetSum F (fun q _ => hb q))
        ((factorialTailStrip_integrable n).const_mul C) hbound
    _ = C*(∫ s : ℂ,factorialTailStripDensity n s) := integral_const_mul C _

private theorem finite_carrier_sampling_le (n : ℕ) (B : ℝ)
    (hB : ∀ F : Finset XiZeroCopy,∑ q ∈ F,‖factorialTailReadout n (q.1 : ℂ)‖^2 ≤ B)
    (S : Finset zetaZeroConfig.carrier) :
    (∑ ρ ∈ S,zetaZeroSquareSummand (fun x => (factorialMuntzCorrectedTail n x : ℂ)) ρ) ≤ B := by
  classical
  let e : zetaZeroConfig.carrier → {ρ : ℂ // IsNontrivialZero ρ} := fun ρ => ⟨ρ,ρ.2⟩
  have he : Function.Injective e := by
    intro a b hab
    exact Subtype.ext (congrArg Subtype.val hab)
  have hinj : Set.InjOn (WeilDeletion.toSupport ∘ e) (S : Set _) :=
    (WeilDeletion.toSupport_injective.comp he).injOn
  let V := S.image (WeilDeletion.toSupport ∘ e)
  let Q : Finset XiZeroCopy := V.sigma (fun ρ => Finset.univ)
  have hid : (∑ ρ ∈ S,zetaZeroSquareSummand
      (fun x => (factorialMuntzCorrectedTail n x : ℂ)) ρ) =
      ∑ q ∈ Q,‖factorialTailReadout n (q.1 : ℂ)‖^2 := by
    rw [show (∑ q ∈ Q,‖factorialTailReadout n (q.1 : ℂ)‖^2) =
      ∑ ρ ∈ V,(xiSupportMultiplicity ρ : ℝ)*‖factorialTailReadout n (ρ : ℂ)‖^2 from
        WeilDeletion.sum_copies V (fun s => ‖factorialTailReadout n s‖^2)]
    dsimp only [V]
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [Function.comp_def]
    rw [← WeilDeletion.zeroMult_eq_xiSupportMultiplicity,WeilDeletion.toSupport_coe]
    unfold zetaZeroSquareSummand
    rw [factorialTailReadout_eq_paperFT]
    rfl
  rw [hid]
  exact hB Q

/-- A scale-independent bound for the raw tail's entire multiplicity-weighted square sum.
The theorem includes summability, so the totalized infinite sum cannot hide divergence. -/
theorem exists_factorialTail_zeroSquare_bound :
    ∃ C : ℝ,0 < C ∧ ∀ n : ℕ,
      Summable (zetaZeroSquareSummand (fun x => (factorialMuntzCorrectedTail n x : ℂ))) ∧
      zetaZeroSquareMass (fun x => (factorialMuntzCorrectedTail n x : ℂ)) ≤
        C*(1+Real.log (n+1 : ℝ))/(n+1 : ℝ) := by
  obtain ⟨D,hD,hcount⟩ := exists_zeroDiskOverlap_log_bound
  let C := (24/Real.pi)*D*factorialTailVerticalConstant
  have hC : 0 < C := mul_pos (mul_pos (div_pos (by norm_num) Real.pi_pos) hD)
    factorialTailVerticalConstant_pos
  refine ⟨C,hC,fun n => ?_⟩
  have hf (F : Finset XiZeroCopy) : (∑ q ∈ F,‖factorialTailReadout n (q.1 : ℂ)‖^2) ≤
      C*(1+Real.log (n+1 : ℝ))/(n+1 : ℝ) := by
    have h := (finite_copy_sampling_le n D hcount F).trans
      (mul_le_mul_of_nonneg_left (factorialTailStrip_integral_le n) hD.le)
    have hp : 0 < Real.pi/16 := by positivity
    apply le_of_mul_le_mul_left (a := Real.pi/16) (a0 := hp)
    apply h.trans_eq
    dsimp [C]
    field_simp
    ring
  have hnonneg (ρ : zetaZeroConfig.carrier) :
      0 ≤ zetaZeroSquareSummand (fun x => (factorialMuntzCorrectedTail n x : ℂ)) ρ :=
    mul_nonneg (by positivity) (sq_nonneg _)
  have hfinite := finite_carrier_sampling_le n _ hf
  exact ⟨summable_of_sum_le hnonneg hfinite,Real.tsum_le_of_sum_le hnonneg hfinite⟩

theorem factorialTail_zeroSquare_summable (n : ℕ) :
    Summable (zetaZeroSquareSummand (fun x => (factorialMuntzCorrectedTail n x : ℂ))) := by
  obtain ⟨C,hC,h⟩ := exists_factorialTail_zeroSquare_bound
  exact (h n).1

private theorem smoothed_tail_summand_le (n k : ℕ) (ρ : zetaZeroConfig.carrier) :
    zetaZeroSquareSummand (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) ρ ≤
      (Real.exp 1)^2*zetaZeroSquareSummand (fun x => (factorialMuntzCorrectedTail n x : ℂ)) ρ := by
  have hρ := zetaZeroConfig.strip (ρ : ℂ) ρ.2
  have hread : paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (gammaOf ρ) =
      factorialMuntzKernelReadout k ρ*factorialTailReadout n ρ := by
    have he : paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (gammaOf ρ) =
        ∫ x : ℝ,Complex.exp (((ρ : ℂ)-1/2)*(x : ℂ))*(factorialMuntzSmoothedTail n k x : ℂ) := by
      simp only [paperFT,gammaOf,mul_div_cancel₀ _ Complex.I_ne_zero,mul_comm]
    rw [he]
    exact (factorialMuntzSmoothedTail_readout n k ρ (by linarith only [hρ.1])).2
  have hk := (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos 1).le).mpr
    (factorialMuntzKernelReadout_bound k hρ.1 hρ.2)
  unfold zetaZeroSquareSummand
  rw [hread,norm_mul,mul_pow,← factorialTailReadout_eq_paperFT]
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hk (sq_nonneg _)) (Nat.cast_nonneg _)).trans_eq (by ring)

/-- Every normalized smoothing preserves absolute square summability. -/
theorem factorialSmoothedTail_zeroSquare_summable (n k : ℕ) :
    Summable (zetaZeroSquareSummand (fun x => (factorialMuntzSmoothedTail n k x : ℂ))) := by
  apply Summable.of_nonneg_of_le (fun ρ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (smoothed_tail_summand_le n k)
    ((factorialTail_zeroSquare_summable n).mul_left ((Real.exp 1)^2))

/-- The raw and smoothed tail budgets share one constant for every arithmetic and smoothing scale. -/
theorem exists_factorialTail_raw_and_smoothed_zeroSquare_bound :
    ∃ C : ℝ,0 < C ∧ ∀ n k : ℕ,
      zetaZeroSquareMass (fun x => (factorialMuntzCorrectedTail n x : ℂ))+
        zetaZeroSquareMass (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) ≤
          C*(1+Real.log (n+1 : ℝ))/(n+1 : ℝ) := by
  obtain ⟨D,hD,hbound⟩ := exists_factorialTail_zeroSquare_bound
  refine ⟨(1+(Real.exp 1)^2)*D,by positivity,fun n k => ?_⟩
  have hs : zetaZeroSquareMass (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) ≤
      (Real.exp 1)^2*zetaZeroSquareMass (fun x => (factorialMuntzCorrectedTail n x : ℂ)) := by
    unfold zetaZeroSquareMass
    rw [← tsum_mul_left]
    exact (factorialSmoothedTail_zeroSquare_summable n k).tsum_le_tsum
      (smoothed_tail_summand_le n k)
      ((factorialTail_zeroSquare_summable n).mul_left ((Real.exp 1)^2))
  calc
    _ ≤ (1+(Real.exp 1)^2)*zetaZeroSquareMass
        (fun x => (factorialMuntzCorrectedTail n x : ℂ)) := by linarith only [hs]
    _ ≤ (1+(Real.exp 1)^2)*(D*(1+Real.log (n+1 : ℝ))/(n+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hbound n).2 (by positivity)
    _ = _ := by ring

end
end GaloisForLFunctions.ArithmeticPositivityTheory
