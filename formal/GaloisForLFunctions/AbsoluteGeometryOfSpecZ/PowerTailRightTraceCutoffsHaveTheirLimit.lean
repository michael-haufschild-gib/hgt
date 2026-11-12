import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailZeroTraceIsAbsolutelySummable
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailRightZeroCutoffs
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailZeroConvolutionModes

/-!
# Height cutoffs retain the constant part of the zero convolution

The constant power-integral terms have summable reciprocal-ordinate
majorants. Each right-band zero eventually enters its height cutoff.
When the boundary line is empty, every oscillating mode vanishes under
the summable contact-amplitude majorant, without a common depth deficit.
-/

noncomputable section

open Complex Finset Filter Topology Set
open _root_.RHTower

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ZeroConfigurationGeometry

/-- The constant power-integral term of a retained zero mode. -/
def powerTailRightZeroConstant (a σ : ℝ) (q : XiZeroCopy) : ℂ :=
  if σ ≤ (q.1 : ℂ).re then
    1 / (((q.1 : ℂ) - (a : ℂ)) * (1 - ((q.1 : ℂ) + (a : ℂ)))) else 0

/-- Both real shifts retain the ordinate in their denominator; one
reciprocal ordinate already dominates the constant term. -/
theorem norm_powerTailRightZeroConstant_le (a σ : ℝ) (q : XiZeroCopy) :
    ‖powerTailRightZeroConstant a σ q‖ ≤ rightSubstripOrdinateWeight σ q := by
  by_cases hq : σ ≤ (q.1 : ℂ).re
  · have hγ : 0 < |xiCopyOrdinate q| := by
      have hh := four_lt_abs_xiCopyOrdinate q
      linarith only [hh]
    have hd : |xiCopyOrdinate q| ≤ ‖1 - ((q.1 : ℂ) + (a : ℂ))‖ := by
      simpa only [Complex.sub_im, Complex.one_im, Complex.add_im, Complex.ofReal_im,
        add_zero, zero_sub, abs_neg, xiCopyOrdinate] using
        Complex.abs_im_le_norm (1 - ((q.1 : ℂ) + (a : ℂ)))
    have hd1 : 1 ≤ ‖1 - ((q.1 : ℂ) + (a : ℂ))‖ := by
      have hh := four_lt_abs_xiCopyOrdinate q
      linarith only [hh, hd]
    have hp : |xiCopyOrdinate q| ≤
        ‖(q.1 : ℂ) - (a : ℂ)‖ * ‖1 - ((q.1 : ℂ) + (a : ℂ))‖ :=
      (abs_ordinate_le_norm_zero_sub_real q a).trans
        (le_mul_of_one_le_right (norm_nonneg _) hd1)
    rw [powerTailRightZeroConstant, if_pos hq, norm_div, norm_one, norm_mul,
      rightSubstripOrdinateWeight, if_pos hq, ← one_div]
    exact div_le_div_of_nonneg_left zero_le_one hγ hp
  · simp only [powerTailRightZeroConstant, rightSubstripOrdinateWeight, if_neg hq,
      norm_zero, le_refl]

/-- The full constant contribution is absolutely summable in every fixed
right substrip, including all multiplicity copies. -/
theorem summable_powerTailRightZeroConstant {σ : ℝ} (hσ : 1 / 2 < σ) (a : ℝ) :
    Summable (powerTailRightZeroConstant a σ) :=
  Summable.of_norm_bounded (summable_rightSubstripOrdinateWeight hσ)
    (norm_powerTailRightZeroConstant_le a σ)

/-- Every fixed right-band zero eventually belongs to the exact height cutoff. -/
theorem eventually_mem_powerTailRightZeroCutoff {σ : ℝ} (q : XiZeroCopy)
    (hq : σ ≤ (q.1 : ℂ).re) :
    ∀ᶠ N : ℕ in atTop, q ∈ powerTailRightZeroCutoff σ (N : ℝ) := by
  filter_upwards [eventually_ge_atTop ⌈|xiCopyOrdinate q|⌉₊] with N hN
  apply (mem_powerTailRightZeroCutoff σ N q).mpr
  exact ⟨hq, (Nat.le_ceil _).trans (by exact_mod_cast hN)⟩

/-- The finite constant terms tend to their complete absolutely convergent sum. -/
theorem tendsto_sum_powerTailRightZeroConstant {σ : ℝ} (hσ : 1 / 2 < σ) (a : ℝ) :
    Tendsto (fun N : ℕ => ∑ q ∈ powerTailRightZeroCutoff σ (N : ℝ),
      powerTailRightZeroConstant a σ q) atTop (𝓝 (∑' q, powerTailRightZeroConstant a σ q)) := by
  classical
  let g := fun (N : ℕ) (q : XiZeroCopy) =>
    if q ∈ powerTailRightZeroCutoff σ (N : ℝ) then powerTailRightZeroConstant a σ q else 0
  have hs := summable_powerTailRightZeroConstant hσ a
  have hpt (q : XiZeroCopy) :
      Tendsto (fun N : ℕ => g N q) atTop (𝓝 (powerTailRightZeroConstant a σ q)) := by
    by_cases hq : σ ≤ (q.1 : ℂ).re
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_mem_powerTailRightZeroCutoff q hq] with N hN
      simp only [g, if_pos hN]
    · simpa only [g, powerTailRightZeroConstant, if_neg hq, ite_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ q : XiZeroCopy,
      ‖g N q‖ ≤ ‖powerTailRightZeroConstant a σ q‖ := by
    exact Filter.Eventually.of_forall fun N q => by
      dsimp only [g]
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg (powerTailRightZeroConstant a σ q)
  have hh := tendsto_tsum_of_dominated_convergence hs.norm hpt hdom
  refine hh.congr fun N => ?_
  rw [tsum_eq_sum (s := powerTailRightZeroCutoff σ (N : ℝ))
    (fun q hq => (show g N q = 0 from if_neg hq))]
  exact Finset.sum_congr rfl fun q hq => if_pos hq

/-- With no boundary zeros, even the moving finite oscillatory cutoff
vanishes under the summable residue-amplitude majorant. -/
theorem tendsto_sum_powerTailRightZeroWave_log_zero {a σ : ℝ}
    (hs : Summable (fun q => ‖powerTailRightZeroAmplitude a σ q‖))
    (hne : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 - a) :
    Tendsto (fun N : ℕ => ∑ q ∈ powerTailRightZeroCutoff σ (N : ℝ),
      powerTailRightZeroWave a σ (Real.log N) q) atTop (𝓝 0) := by
  classical
  let g := fun (N : ℕ) (q : XiZeroCopy) =>
    if q ∈ powerTailRightZeroCutoff σ (N : ℝ) then
      powerTailRightZeroWave a σ (Real.log N) q else 0
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpt (q : XiZeroCopy) : Tendsto (fun N : ℕ => g N q) atTop (𝓝 0) := by
    have hw := (tendsto_powerTailRightZeroWave_zero (a := a) (σ := σ) q (hne q)).comp hlog
    have hwn : Tendsto (fun N : ℕ => ‖powerTailRightZeroWave a σ (Real.log N) q‖)
        atTop (𝓝 0) := by simpa only [Function.comp_def, norm_zero] using hw.norm
    refine squeeze_zero_norm' (Filter.Eventually.of_forall fun N => ?_) hwn
    dsimp only [g]
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (powerTailRightZeroWave a σ (Real.log N) q)
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ q : XiZeroCopy,
      ‖g N q‖ ≤ ‖powerTailRightZeroAmplitude a σ q‖ := by
    filter_upwards [eventually_ge_atTop 1] with N hN q
    dsimp only [g]
    split_ifs
    · exact norm_powerTailRightZeroWave_le (Real.log_nonneg (by exact_mod_cast hN)) q
    · simpa only [norm_zero] using norm_nonneg (powerTailRightZeroAmplitude a σ q)
  have hh := tendsto_tsum_of_dominated_convergence hs hpt hdom
  simp only [tsum_zero] at hh
  refine hh.congr fun N => ?_
  rw [tsum_eq_sum (s := powerTailRightZeroCutoff σ (N : ℝ))
    (fun q hq => (show g N q = 0 from if_neg hq))]
  exact Finset.sum_congr rfl fun q hq => if_pos hq

/-- The positive zero-convolution mode has the negative contact wave and
the constant power-integral term, with the exact logarithmic phase. -/
theorem powerTailZeroConvolutionMain_eq_neg_wave_add_constant {a σ : ℝ}
    {N : ℕ} (hN : 1 ≤ N) (q : XiZeroCopy)
    (hq : σ ≤ (q.1 : ℂ).re) (hqβ : (q.1 : ℂ).re ≤ 1 - a) :
    powerTailZeroConvolutionMain a N q =
      -powerTailRightZeroWave a σ (Real.log N) q + powerTailRightZeroConstant a σ q := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hphase : ((N : ℝ) : ℂ) ^ ((q.1 : ℂ) - ((1 - a : ℝ) : ℂ)) =
      Complex.exp (((q.1 : ℂ) - ((1 - a : ℝ) : ℂ)) * ((Real.log N : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hNp.ne'),
      ← Complex.ofReal_log hNp.le]
    congr 1
    ring
  rw [powerTailZeroConvolutionMain, powerTailRightZeroWave, powerTailRightZeroAmplitude,
    if_pos ⟨hq, hqβ⟩, powerTailRightZeroConstant, if_pos hq, hphase]
  ring

/-- With no boundary zeros, the full finite main part tends exactly to
the absolutely summable constant contribution. -/
theorem tendsto_sum_powerTailZeroConvolutionMain {a σ : ℝ} (hσ : 1 / 2 < σ)
    (hs : Summable (fun q => ‖powerTailRightZeroAmplitude a σ q‖))
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re < 1 - a) :
    Tendsto (fun N : ℕ => ∑ q ∈ powerTailRightZeroCutoff σ (N : ℝ),
      powerTailZeroConvolutionMain a N q) atTop (𝓝 (∑' q, powerTailRightZeroConstant a σ q)) := by
  have hlim := (tendsto_sum_powerTailRightZeroWave_log_zero hs (fun q => (hβ q).ne)).neg.add
    (tendsto_sum_powerTailRightZeroConstant hσ a)
  simp only [neg_zero, zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  exact (powerTailZeroConvolutionMain_eq_neg_wave_add_constant hN q
    ((mem_powerTailRightZeroCutoff σ N q).mp hq).1 (hβ q).le).symm

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
