import GaloisForLFunctions.RHTower.CCMFirstClockLandauHead

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Global reciprocal-square domination of every literal first-clock Xi atom. -/
theorem norm_ccmFirstClockRationalKernel_xiSpectralPoint_le_global
    {L : ℝ} (hL : 0 ≤ L) (q : XiZeroCopy) :
    ‖ccmFirstClockRationalKernel L (xiSpectralPoint q)‖ ≤
      (ccmFirstClockHeadReciprocalSquareConstant +
        (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1)) /
        ‖xiSpectralPoint q‖ ^ 2 := by
  by_cases hhead : L ≤ Real.pi / 2
  · calc
      ‖ccmFirstClockRationalKernel L (xiSpectralPoint q)‖ ≤
          ccmFirstClockHeadReciprocalSquareConstant /
            ‖xiSpectralPoint q‖ ^ 2 :=
        norm_ccmFirstClockRationalKernel_xiSpectralPoint_le_head hL hhead q
      _ ≤ (ccmFirstClockHeadReciprocalSquareConstant +
          (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1)) /
          ‖xiSpectralPoint q‖ ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact le_add_of_nonneg_right (by positivity)
  · have htail : Real.pi / 2 ≤ L := le_of_not_ge hhead
    calc
      ‖ccmFirstClockRationalKernel L (xiSpectralPoint q)‖ ≤
          (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1) /
            ‖xiSpectralPoint q‖ ^ 2 :=
        norm_ccmFirstClockRationalKernel_xiSpectralPoint_le htail q
      _ ≤ (ccmFirstClockHeadReciprocalSquareConstant +
          (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1)) /
          ‖xiSpectralPoint q‖ ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact le_add_of_nonneg_left
          ccmFirstClockHeadReciprocalSquareConstant_nonneg

/-- Literal complete first-clock divisor is absolutely summable at every nonnegative aperture,
not only on the large-aperture physical tail. -/
theorem summable_ccmFirstClockRationalKernel_xiSpectralPoint_global
    {L : ℝ} (hL : 0 ≤ L) :
    Summable (fun q : XiZeroCopy =>
      ccmFirstClockRationalKernel L (xiSpectralPoint q)) := by
  apply Summable.of_norm_bounded
    (xiSpectralPoint_inv_sq_summable.mul_left
      (ccmFirstClockHeadReciprocalSquareConstant +
        (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1)))
  intro q
  calc
    ‖ccmFirstClockRationalKernel L (xiSpectralPoint q)‖ ≤
        (ccmFirstClockHeadReciprocalSquareConstant +
          (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1)) /
          ‖xiSpectralPoint q‖ ^ 2 :=
      norm_ccmFirstClockRationalKernel_xiSpectralPoint_le_global hL q
    _ = (ccmFirstClockHeadReciprocalSquareConstant +
          (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1)) *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring

theorem measurable_ccmFirstClockRationalKernel
    (z : ℂ) :
    Measurable (fun L : ℝ => ccmFirstClockRationalKernel L z) := by
  unfold ccmFirstClockRationalKernel
  fun_prop

theorem measurable_ccmFirstClockXiRationalDivisor :
    Measurable ccmFirstClockXiRationalDivisor := by
  unfold ccmFirstClockXiRationalDivisor
  exact Measurable.tsum fun q =>
    measurable_ccmFirstClockRationalKernel (xiSpectralPoint q)

/-- Global norm envelope for the literal multiplicity-exact divisor. -/
theorem norm_ccmFirstClockXiRationalDivisor_le
    {L : ℝ} (hL : 0 ≤ L) :
    ‖ccmFirstClockXiRationalDivisor L‖ ≤
      (ccmFirstClockHeadReciprocalSquareConstant +
        (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1)) *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
  let C : ℝ :=
    ccmFirstClockHeadReciprocalSquareConstant +
      (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1)
  have hsum :=
    summable_ccmFirstClockRationalKernel_xiSpectralPoint_global hL
  have hmajor := xiSpectralPoint_inv_sq_summable.mul_left C
  rw [ccmFirstClockXiRationalDivisor]
  calc
    ‖∑' q : XiZeroCopy,
        ccmFirstClockRationalKernel L (xiSpectralPoint q)‖ ≤
        ∑' q : XiZeroCopy,
          ‖ccmFirstClockRationalKernel L (xiSpectralPoint q)‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' q : XiZeroCopy, C * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
      exact hsum.norm.tsum_le_tsum (fun q => by
        calc
          ‖ccmFirstClockRationalKernel L (xiSpectralPoint q)‖ ≤
              C / ‖xiSpectralPoint q‖ ^ 2 := by
            simpa only [C] using
              norm_ccmFirstClockRationalKernel_xiSpectralPoint_le_global hL q
          _ = C * (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring)
        hmajor
    _ = C * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
      rw [tsum_mul_left]
    _ = _ := rfl

/-- The literal complete divisor has an ordinary Laplace transform on the entire
unconditional half-plane `Re s > 1/2`. -/
theorem integrableOn_exp_mul_ccmFirstClockXiRationalDivisor
    {s : ℂ} (hsHalf : 1 / 2 < s.re) :
    IntegrableOn
      (fun L : ℝ =>
        Complex.exp (-s * (L : ℂ)) *
          ccmFirstClockXiRationalDivisor L) (Ioi 0) := by
  let M : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  let g : ℝ → ℝ := fun L =>
    M * (ccmFirstClockHeadReciprocalSquareConstant * Real.exp (-s.re * L) +
      (1 + 2 * Real.pi) *
        (Real.exp ((-s.re + 1 / 2) * L) + Real.exp (-s.re * L)))
  have hdecay0 : -s.re < 0 := by linarith
  have hdecay1 : -s.re + 1 / 2 < 0 := by linarith
  have hM0 : 0 ≤ M := by
    dsimp only [M]
    exact tsum_nonneg fun _ => by positivity
  have hgint : IntegrableOn g (Ioi 0) := by
    dsimp only [g]
    exact (((integrableOn_exp_mul_Ioi hdecay0 0).const_mul
      ccmFirstClockHeadReciprocalSquareConstant).add
        (((integrableOn_exp_mul_Ioi hdecay1 0).add
          (integrableOn_exp_mul_Ioi hdecay0 0)).const_mul
            (1 + 2 * Real.pi))).const_mul M
  apply Integrable.mono' hgint
  · exact ((by fun_prop : Measurable (fun L : ℝ =>
      Complex.exp (-s * (L : ℂ)))).aestronglyMeasurable.mul
        measurable_ccmFirstClockXiRationalDivisor.aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
    have hQ := norm_ccmFirstClockXiRationalDivisor_le hL.le
    have hexpRe : (-s * (L : ℂ)).re = -s.re * L := by
      simp [mul_re]
    rw [norm_mul, Complex.norm_exp, hexpRe]
    dsimp only [g, M]
    calc
      Real.exp (-s.re * L) * ‖ccmFirstClockXiRationalDivisor L‖ ≤
          Real.exp (-s.re * L) *
            ((ccmFirstClockHeadReciprocalSquareConstant +
              (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1)) *
                ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hQ (Real.exp_pos _).le
      _ = (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) *
          (ccmFirstClockHeadReciprocalSquareConstant *
              Real.exp (-s.re * L) +
            (1 + 2 * Real.pi) *
              (Real.exp ((-s.re + 1 / 2) * L) +
                Real.exp (-s.re * L))) := by
        rw [show (-s.re + 1 / 2) * L =
          -s.re * L + L / 2 by ring, Real.exp_add]
        ring

/-- **Infinite-divisor first-clock transform law.**  The literal multiplicity-exact CCM
first-clock divisor has Laplace transform equal to its normally convergent cubic continuation
throughout `Re s > 1/2`. -/
theorem integral_exp_mul_ccmFirstClockXiRationalDivisor_eq_continuation
    {s : ℂ} (hsHalf : 1 / 2 < s.re) :
    (∫ L : ℝ in Ioi 0,
      Complex.exp (-s * (L : ℂ)) *
        ccmFirstClockXiRationalDivisor L) =
      ccmFirstClockLaplaceContinuation s := by
  let F : XiZeroCopy → ℝ → ℂ := fun q L =>
    Complex.exp (-s * (L : ℂ)) *
      ccmFirstClockRationalKernel L (xiSpectralPoint q)
  let g : ℝ → ℝ := fun L =>
    ccmFirstClockHeadReciprocalSquareConstant * Real.exp (-s.re * L) +
      (1 + 2 * Real.pi) *
        (Real.exp ((-s.re + 1 / 2) * L) + Real.exp (-s.re * L))
  have hdecay0 : -s.re < 0 := by linarith
  have hdecay1 : -s.re + 1 / 2 < 0 := by linarith
  have hgint : IntegrableOn g (Ioi 0) := by
    dsimp only [g]
    exact ((integrableOn_exp_mul_Ioi hdecay0 0).const_mul
      ccmFirstClockHeadReciprocalSquareConstant).add
        (((integrableOn_exp_mul_Ioi hdecay1 0).add
          (integrableOn_exp_mul_Ioi hdecay0 0)).const_mul
            (1 + 2 * Real.pi))
  have hpointBound (q : XiZeroCopy) (L : ℝ) (hL : L ∈ Ioi (0 : ℝ)) :
      ‖F q L‖ ≤ g L * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    have hkernel :=
      norm_ccmFirstClockRationalKernel_xiSpectralPoint_le_global hL.le q
    have hexpRe : (-s * (L : ℂ)).re = -s.re * L := by
      simp [mul_re]
    dsimp only [F, g]
    rw [norm_mul, Complex.norm_exp, hexpRe]
    calc
      Real.exp (-s.re * L) *
          ‖ccmFirstClockRationalKernel L (xiSpectralPoint q)‖ ≤
        Real.exp (-s.re * L) *
          ((ccmFirstClockHeadReciprocalSquareConstant +
            (1 + 2 * Real.pi) * (Real.exp (L / 2) + 1)) /
              ‖xiSpectralPoint q‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hkernel (Real.exp_pos _).le
      _ = (ccmFirstClockHeadReciprocalSquareConstant *
            Real.exp (-s.re * L) +
          (1 + 2 * Real.pi) *
            (Real.exp ((-s.re + 1 / 2) * L) +
              Real.exp (-s.re * L))) *
          (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        rw [show (-s.re + 1 / 2) * L =
          -s.re * L + L / 2 by ring, Real.exp_add]
        ring
  have hFint : ∀ q : XiZeroCopy, IntegrableOn (F q) (Ioi 0) := by
    intro q
    have hmajor :
        IntegrableOn
          (fun L : ℝ => g L * (1 / ‖xiSpectralPoint q‖ ^ 2)) (Ioi 0) :=
      hgint.mul_const _
    apply Integrable.mono' hmajor
    · have hmeas : Measurable (F q) := by
        dsimp only [F]
        unfold ccmFirstClockRationalKernel
        fun_prop
      exact hmeas.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
      exact hpointBound q L hL
  have hnormSummable : Summable (fun q : XiZeroCopy =>
      ∫ L : ℝ in Ioi 0, ‖F q L‖) := by
    apply Summable.of_nonneg_of_le
      (fun q => integral_nonneg fun _ => norm_nonneg _)
      (fun q => ?_)
      (xiSpectralPoint_inv_sq_summable.mul_left
        (∫ L : ℝ in Ioi 0, g L))
    have hmajor :
        IntegrableOn
          (fun L : ℝ => g L * (1 / ‖xiSpectralPoint q‖ ^ 2)) (Ioi 0) :=
      hgint.mul_const _
    calc
      (∫ L : ℝ in Ioi 0, ‖F q L‖) ≤
          ∫ L : ℝ in Ioi 0,
            g L * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        apply integral_mono_ae (hFint q).norm hmajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
        exact hpointBound q L hL
      _ = (∫ L : ℝ in Ioi 0, g L) *
          (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        rw [integral_mul_const]
  have hswap :
      (∫ L : ℝ in Ioi 0, ∑' q : XiZeroCopy, F q L) =
        ∑' q : XiZeroCopy, ∫ L : ℝ in Ioi 0, F q L :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm
      hFint hnormSummable).symm
  calc
    (∫ L : ℝ in Ioi 0,
        Complex.exp (-s * (L : ℂ)) *
          ccmFirstClockXiRationalDivisor L) =
        ∫ L : ℝ in Ioi 0, ∑' q : XiZeroCopy, F q L := by
      apply integral_congr_ae
      filter_upwards with L
      rw [ccmFirstClockXiRationalDivisor, ← tsum_mul_left]
    _ = ∑' q : XiZeroCopy, ∫ L : ℝ in Ioi 0, F q L := hswap
    _ = ∑' q : XiZeroCopy,
        ccmFirstClockLaplaceContinuationAtom s (xiSpectralPoint q) := by
      apply tsum_congr
      intro q
      exact integral_exp_mul_ccmFirstClockRationalKernel_xiSpectralPoint
        q hsHalf
    _ = ccmFirstClockLaplaceContinuation s := rfl

end

end RHTower
