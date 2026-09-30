import GaloisForLFunctions.RHTower.LiClockPairedEtaArithmeticCancellation
import GaloisForLFunctions.RHTower.LiClockPairedEtaContiguousMovingClock

/-!
# Joint finite paired-eta arithmetic cancellation

One common family of actual central circles supports every smaller positive
logarithmic clock window. Along arbitrary diverging prefix and real-clock
sequences in such a window, the completed finite response approximates the
actual complete clock without normalization. Its completion-scaled limit is
zero; both the literal finite eta clock and the actual-to-contiguous gap clock
have scaled limit `-1/5`, completion ratio `-1`, and real part tending to minus
infinity. Finite circle regularity follows eventually from the arithmetic
source floor. No clock-sign or zero-location premise is imposed.
-/

open GaloisForLFunctions RiemannGaussian Complex Set Metric Filter Topology
namespace RHTower
noncomputable section

private theorem joint_exp_neg_tendsto_zero (τ : ℕ → ℝ) (hτ : Tendsto τ atTop atTop) :
    Tendsto (fun l : ℕ => (Real.exp (-(2/5)*(τ l)) : ℂ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun l : ℕ => (2/5)*(τ l)) atTop atTop :=
    hτ.const_mul_atTop (by norm_num : (0 : ℝ) < 2/5)
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have hc := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp he
  simpa only [Function.comp_def,neg_mul,Complex.ofReal_zero] using hc

private theorem joint_clock_error_tendsto_zero {r c : ℝ} (hc : 0 < c) (hcr : c < r/4)
    (hu : ∀ c : ℝ, 0 < c → c < r/4 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ t : ℂ, ‖t‖ ≤ c*Real.log (2*(N:ℝ)+1) →
        ‖liClockPairedEtaFiniteClockResponse N r t-liEvenCrossActualComplexClockResponse t‖ < ε)
    (ν : ℕ → ℕ) (τ : ℕ → ℝ) (hν : Tendsto ν atTop atTop)
    (hwindow : ∀ᶠ l : ℕ in atTop, 0 ≤ τ l ∧ τ l ≤ c*Real.log (2*(ν l:ℝ)+1)) :
    Tendsto (fun l : ℕ => liClockPairedEtaFiniteClockResponse (ν l) r (τ l:ℂ)-
      liEvenCrossActualComplexClockResponse (τ l:ℂ)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun l => ha.trans_le (norm_nonneg _))
  · intro ε hε
    have hfinite := hν.eventually (hu c hc hcr ε hε)
    filter_upwards [hfinite,hwindow] with l hl hw
    apply hl (τ l:ℂ)
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw.1] using hw.2

private theorem joint_circle_regular {r : ℝ} (hrsmall : r ≤ 1/128)
    (ν : ℕ → ℕ) (hν : Tendsto ν atTop atTop) :
    ∀ᶠ l : ℕ in atTop, 0 < ν l ∧
      ∀ z ∈ sphere (0:ℂ) r, pairedEtaCorePartialSum (ν l) (1/2+z*I) ≠ 0 := by
  have hs := hν.eventually liClockPairedEta_eventually_valueTail_le_one_sixteenth
  filter_upwards [hs,hν.eventually_gt_atTop (0:ℕ)] with l hl hn
  refine ⟨hn,?_⟩
  intro z hz hzero
  have hzsmall : ‖z‖ ≤ 1/128 := (show ‖z‖=r by
    simpa only [mem_sphere_iff_norm,sub_zero] using hz).le.trans hrsmall
  have hf := liClockPairedEtaFiniteCore_re_gt_one_sixteenth (ν l) hl hzsmall
  norm_num [hzero] at hf

private theorem joint_ratio_tendsto {r : ℝ} (hr : 0 < r) (hrhalf : r < 1/2)
    (τ : ℕ → ℝ) (hτ : Tendsto τ atTop atTop) (X : ℕ → ℂ)
    (hX : Tendsto (fun l : ℕ => (Real.exp (-(2/5)*(τ l)):ℂ)*X l)
      atTop (𝓝 (-1/5:ℂ))) :
    Tendsto (fun l : ℕ => X l/liClockPairedEtaCompletionClockResponse r (τ l:ℂ))
      atTop (𝓝 (-1:ℂ)) := by
  have hC := (liClockPairedEtaCompletionClockResponse_exp_neg_mul_tendsto hr hrhalf).comp hτ
  have hh := hX.div hC (by norm_num : (1/5:ℂ) ≠ 0)
  have hh' : Tendsto (fun l : ℕ =>
      ((Real.exp (-(2/5)*(τ l)):ℂ)*X l)/
      ((Real.exp (-(2/5)*(τ l)):ℂ)*liClockPairedEtaCompletionClockResponse r (τ l:ℂ)))
      atTop (𝓝 (-1:ℂ)) := by norm_num at hh ⊢; exact hh
  apply hh'.congr'
  filter_upwards [] with l
  have he : (Real.exp (-(2/5)*(τ l)):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  exact mul_div_mul_left _ _ he

private theorem joint_re_tendsto_atBot (τ : ℕ → ℝ) (hτ : Tendsto τ atTop atTop)
    (X : ℕ → ℂ)
    (hX : Tendsto (fun l : ℕ => (Real.exp (-(2/5)*(τ l)):ℂ)*X l)
      atTop (𝓝 (-1/5:ℂ))) :
    Tendsto (fun l : ℕ => (X l).re) atTop atBot := by
  have hre : Tendsto (fun l : ℕ => Real.exp (-(2/5)*(τ l))*(X l).re)
      atTop (𝓝 (-1/5:ℝ)) := by
    have hh := (Complex.continuous_re.tendsto (-1/5:ℂ)).comp hX
    simp only [Function.comp_def,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero] at hh
    norm_num at hh
    simpa only [neg_mul,neg_div] using hh
  have he : Tendsto (fun l : ℕ => Real.exp ((2/5)*(τ l))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (hτ.const_mul_atTop (by norm_num : (0:ℝ)<2/5))
  have hm := hre.neg_mul_atTop (by norm_num) he
  convert hm using 1
  funext l
  have hexp : Real.exp (-(2/5)*(τ l))*Real.exp ((2/5)*(τ l))=1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc
    (X l).re = (X l).re*1 := by ring
    _ = (X l).re*(Real.exp (-(2/5)*(τ l))*Real.exp ((2/5)*(τ l))) := by rw [hexp]
    _ = _ := by ring

/-- A common actual central radius supports joint finite arithmetic cancellation
on every smaller logarithmic window. Both sequences may vary without monotonicity. -/
theorem exists_liClockPairedEtaFiniteArithmeticJointCancellation_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∀ c : ℝ, 0 < c → c < r/4 → ∀ ν : ℕ → ℕ, ∀ τ : ℕ → ℝ,
      Tendsto ν atTop atTop → Tendsto τ atTop atTop →
      (∀ᶠ l : ℕ in atTop, 0 ≤ τ l ∧ τ l ≤ c*Real.log (2*(ν l:ℝ)+1)) →
      Tendsto (fun l : ℕ => liClockPairedEtaFiniteClockResponse (ν l) r (τ l:ℂ)-
        liEvenCrossActualComplexClockResponse (τ l:ℂ)) atTop (𝓝 0) ∧
      Tendsto (fun l : ℕ => (Real.exp (-(2/5)*(τ l)):ℂ)*
        liClockPairedEtaFiniteClockResponse (ν l) r (τ l:ℂ)) atTop (𝓝 0) ∧
      Tendsto (fun l : ℕ => (Real.exp (-(2/5)*(τ l)):ℂ)*
        liClockPairedEtaFiniteArithmeticClockResponse (ν l) r (τ l:ℂ)) atTop (𝓝 (-1/5:ℂ)) ∧
      Tendsto (fun l : ℕ => (Real.exp (-(2/5)*(τ l)):ℂ)*
        liClockPairedEtaFiniteGapClockResponse (ν l) r (τ l:ℂ)) atTop (𝓝 (-1/5:ℂ)) ∧
      Tendsto (fun l : ℕ => liClockPairedEtaFiniteArithmeticClockResponse (ν l) r (τ l:ℂ)/
        liClockPairedEtaCompletionClockResponse r (τ l:ℂ)) atTop (𝓝 (-1:ℂ)) ∧
      Tendsto (fun l : ℕ => liClockPairedEtaFiniteGapClockResponse (ν l) r (τ l:ℂ)/
        liClockPairedEtaCompletionClockResponse r (τ l:ℂ)) atTop (𝓝 (-1:ℂ)) ∧
      Tendsto (fun l : ℕ => (liClockPairedEtaFiniteArithmeticClockResponse (ν l) r (τ l:ℂ)).re)
        atTop atBot ∧
      Tendsto (fun l : ℕ => (liClockPairedEtaFiniteGapClockResponse (ν l) r (τ l:ℂ)).re)
        atTop atBot := by
  obtain ⟨r₀,hr₀,hr₀small,huniform⟩ := exists_liClockPairedEtaFiniteClockResponse_uniform_windows
  refine ⟨r₀,hr₀,hr₀small,?_⟩
  intro r hr hrr c hc hcr ν τ hν hτ hwindow
  have hrs : r ≤ 1/128 := hrr.le.trans hr₀small
  have hrhalf : r < 1/2 := lt_of_le_of_lt hrs (by norm_num)
  have hcsmall : c < 1/16 := by linarith
  have herror := joint_clock_error_tendsto_zero hc hcr (huniform r hr hrr).1 ν τ hν hwindow
  have hscale := joint_exp_neg_tendsto_zero τ hτ
  have hactual := liEvenCrossActualComplexClockResponse_exp_neg_two_fifths_tendsto_zero.comp hτ
  have hfinite : Tendsto (fun l : ℕ => (Real.exp (-(2/5)*(τ l)):ℂ)*
      liClockPairedEtaFiniteClockResponse (ν l) r (τ l:ℂ)) atTop (𝓝 0) := by
    have hh := (hscale.mul herror).add hactual
    convert hh using 1
    · funext l
      simp only [Function.comp_def]
      ring
    · simp
  have hregular := joint_circle_regular hrs ν hν
  have hC := (liClockPairedEtaCompletionClockResponse_exp_neg_mul_tendsto hr hrhalf).comp hτ
  have heta : Tendsto (fun l : ℕ => (Real.exp (-(2/5)*(τ l)):ℂ)*
      liClockPairedEtaFiniteArithmeticClockResponse (ν l) r (τ l:ℂ)) atTop (𝓝 (-1/5:ℂ)) := by
    have hh := hfinite.sub hC
    have hh' : Tendsto (fun l : ℕ => (Real.exp (-(2/5)*(τ l)):ℂ)*
        liClockPairedEtaFiniteClockResponse (ν l) r (τ l:ℂ)-
        (Real.exp (-(2/5)*(τ l)):ℂ)*liClockPairedEtaCompletionClockResponse r (τ l:ℂ))
        atTop (𝓝 (-1/5:ℂ)) := by norm_num at hh ⊢; exact hh
    apply hh'.congr'
    filter_upwards [hregular] with l hl
    rw [liClockPairedEtaFiniteClockResponse_eq_arithmetic_add_completion (ν l) hr hrhalf hl.2]
    ring
  have hwindowComplex : ∀ᶠ l : ℕ in atTop,
      ‖(τ l:ℂ)‖ ≤ c*Real.log (2*(ν l:ℝ)+1) := by
    filter_upwards [hwindow] with l hl
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hl.1] using hl.2
  have hK := liClockPairedEtaContiguousClock_moving_logWindow_tendsto_zero hc hcsmall ν
    (fun l => (τ l:ℂ)) hν hwindowComplex
  have hgap : Tendsto (fun l : ℕ => (Real.exp (-(2/5)*(τ l)):ℂ)*
      liClockPairedEtaFiniteGapClockResponse (ν l) r (τ l:ℂ)) atTop (𝓝 (-1/5:ℂ)) := by
    have hh := heta.add (hscale.mul hK)
    have hh' : Tendsto (fun l : ℕ => (Real.exp (-(2/5)*(τ l)):ℂ)*
        liClockPairedEtaFiniteArithmeticClockResponse (ν l) r (τ l:ℂ)+
        (Real.exp (-(2/5)*(τ l)):ℂ)*
          liClockPairedEtaContiguousClock (Real.log (2*(ν l:ℝ))) (τ l:ℂ))
        atTop (𝓝 (-1/5:ℂ)) := by simpa only [mul_zero,add_zero] using hh
    apply hh'.congr'
    filter_upwards [hregular] with l hl
    rw [liClockPairedEtaFiniteGapClockResponse_eq_arithmetic_add_contiguous hl.1 hr hrhalf hl.2]
    ring
  exact ⟨herror,hfinite,heta,hgap,joint_ratio_tendsto hr hrhalf τ hτ _ heta,
    joint_ratio_tendsto hr hrhalf τ hτ _ hgap,joint_re_tendsto_atBot τ hτ _ heta,
    joint_re_tendsto_atBot τ hτ _ hgap⟩

end
end RHTower
