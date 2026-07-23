import GaloisForLFunctions.RHTower.CCMFirstClockLandauDyadic

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

private theorem xiDivisorSupport_countable_for_firstClockReflection :
    (Set.univ : Set XiDivisorSupport).Countable := by
  have hlocal : LocallyFiniteSupport
      (fun z : ℂ => MeromorphicOn.divisor xi Set.univ z) := by
    intro z
    exact (MeromorphicOn.divisor xi Set.univ).supportLocallyFiniteWithinDomain'
      z (Set.mem_univ z)
  apply hlocal.locallyFinite_support.countable_univ
  intro rho
  exact ⟨(rho : ℂ), rfl⟩

noncomputable local instance : Countable XiDivisorSupport :=
  Set.countable_univ_iff.mp
    xiDivisorSupport_countable_for_firstClockReflection

noncomputable local instance : Countable XiZeroCopy := inferInstance

/-- Fixed dilation kernel of the first physical CCM clock. -/
def ccmFirstClockDilationKernel (x : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) *
    Real.sin ((2 * Real.pi) * x)

/-- Dilation form of the universal first-clock Volterra law. -/
theorem ccmFirstClockXiRationalDivisor_eq_screw_add_dilation
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    ccmFirstClockXiRationalDivisor L =
      xiScrewDivisor L +
        ∫ x : ℝ in (0 : ℝ)..1,
          ccmFirstClockDilationKernel x * xiScrewDivisor (L * x) := by
  have hLpos : 0 < L :=
    lt_of_lt_of_le (by positivity : 0 < Real.pi / 2) hL
  rw [ccmFirstClockXiRationalDivisor_eq_screw_add_volterra hL]
  congr 1
  let F : ℝ → ℂ := fun t =>
    ((((2 * Real.pi / L : ℝ) : ℂ) *
      Real.sin ((2 * Real.pi / L) * t)) *
        xiScrewDivisor t)
  have hsub := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) F L
  have hsub' :
      L • (∫ x : ℝ in (0 : ℝ)..1, F (L * x)) =
        ∫ t : ℝ in (0 : ℝ)..L, F t := by
    simpa only [mul_zero, mul_one] using hsub
  rw [← hsub']
  rw [← intervalIntegral.integral_smul L]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only [F, ccmFirstClockDilationKernel]
  change
    (L : ℂ) *
        ((((2 * Real.pi / L : ℝ) : ℂ) *
          (Real.sin ((2 * Real.pi / L) * (L * x)) : ℂ)) *
            xiScrewDivisor (L * x)) =
      (((2 * Real.pi : ℝ) : ℂ) *
        (Real.sin ((2 * Real.pi) * x) : ℂ)) *
          xiScrewDivisor (L * x)
  have harg : (2 * Real.pi / L) * (L * x) =
      (2 * Real.pi) * x := by field_simp [hLpos.ne']
  rw [harg]
  push_cast
  field_simp [hLpos.ne']

/-- Complete literal first-clock divisor has every positive exponential moment. -/
def CCMFirstClockXiAllExponentialMoments : Prop :=
  ∀ a : ℝ, 0 < a →
    IntegrableOn (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)) *
        ccmFirstClockXiRationalDivisor L) (Ioi 0)

private theorem integrableOn_firstClock_head_at_positive
    {a : ℝ} (_ha : 0 < a) :
    IntegrableOn (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)) *
        ccmFirstClockXiRationalDivisor L)
      (Ioc (0 : ℝ) (Real.pi / 2)) := by
  let B : ℝ → ℂ := fun L =>
    Complex.exp (-(1 : ℂ) * (L : ℂ)) *
      ccmFirstClockXiRationalDivisor L
  let P : ℝ → ℂ := fun L =>
    Complex.exp (((1 - a : ℝ) : ℂ) * (L : ℂ))
  have hBglobal : IntegrableOn B (Ioi 0) := by
    exact integrableOn_exp_mul_ccmFirstClockXiRationalDivisor
      (s := (1 : ℂ)) (by norm_num)
  have hB : IntegrableOn B (Ioc (0 : ℝ) (Real.pi / 2)) :=
    hBglobal.mono_set (by
      intro L hL
      exact hL.1)
  have hPmeas : AEStronglyMeasurable P
      (volume.restrict (Ioc (0 : ℝ) (Real.pi / 2))) :=
    (by fun_prop : Continuous P).aestronglyMeasurable
  let C : ℝ := Real.exp (|1 - a| * (Real.pi / 2))
  have hPbound :
      ∀ᵐ L : ℝ ∂volume.restrict (Ioc (0 : ℝ) (Real.pi / 2)),
        ‖P L‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
    dsimp only [P, C]
    rw [Complex.norm_exp]
    have hre :
        ((((1 - a : ℝ) : ℂ) * (L : ℂ))).re = (1 - a) * L := by
      simp
    rw [hre]
    apply Real.exp_le_exp.mpr
    calc
      (1 - a) * L ≤ |1 - a| * |L| := by
        exact le_trans (le_abs_self ((1 - a) * L))
          (by rw [abs_mul])
      _ = |1 - a| * L := by rw [abs_of_pos hL.1]
      _ ≤ |1 - a| * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_left hL.2 (abs_nonneg _)
  have hPB : IntegrableOn (fun L => P L * B L)
      (Ioc (0 : ℝ) (Real.pi / 2)) :=
    hB.bdd_mul hPmeas hPbound
  apply hPB.congr
  filter_upwards with L
  dsimp only [P, B]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem ccmFirstClockXi_all_exponential_moments
    (hsource : CCMFirstClockPublishedSourceNonnegative) :
    CCMFirstClockXiAllExponentialMoments := by
  intro a ha
  have hhead := integrableOn_firstClock_head_at_positive ha
  have htailReal :=
    ccmFirstClockTailMomentsAbove_zero hsource a ha
  have htail : IntegrableOn (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)) *
        ccmFirstClockXiRationalDivisor L)
      (Ioi (Real.pi / 2)) := by
    have htailCast : IntegrableOn (fun L : ℝ =>
        (ccmFirstClockLandauDensity a L : ℂ))
        (Ioi (Real.pi / 2)) :=
      htailReal.ofReal
    apply htailCast.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
    have hreal :
        ccmFirstClockXiRationalDivisor L =
          ((ccmFirstClockXiRationalDivisor L).re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [ccmFirstClockXiRationalDivisor_im_eq_zero]
    rw [hreal]
    unfold ccmFirstClockLandauDensity
    rw [show -(a : ℂ) * (L : ℂ) = ((-a * L : ℝ) : ℂ) by
      push_cast
      ring]
    simp
  have hunion := hhead.union htail
  apply hunion.mono_set
  intro L hL
  by_cases hcut : L ≤ Real.pi / 2
  · exact Or.inl ⟨hL, hcut⟩
  · exact Or.inr (lt_of_not_ge hcut)

theorem norm_ccmFirstClockDilationKernel (x : ℝ) :
    ‖ccmFirstClockDilationKernel x‖ =
      (2 * Real.pi) * |Real.sin ((2 * Real.pi) * x)| := by
  unfold ccmFirstClockDilationKernel
  rw [norm_mul, Complex.norm_real, Complex.norm_real]
  simp only [Real.norm_eq_abs]
  rw [abs_of_pos (by positivity : 0 < 2 * Real.pi)]

theorem norm_ccmFirstClockDilationKernel_le_origin
    {x : ℝ} (hx : 0 ≤ x) :
    ‖ccmFirstClockDilationKernel x‖ ≤
      (2 * Real.pi) ^ 2 * x := by
  rw [norm_ccmFirstClockDilationKernel]
  have hsin :
      |Real.sin ((2 * Real.pi) * x)| ≤
        |(2 * Real.pi) * x| :=
    Real.abs_sin_le_abs
  rw [abs_of_nonneg (mul_nonneg (by positivity) hx)] at hsin
  calc
    (2 * Real.pi) * |Real.sin ((2 * Real.pi) * x)| ≤
        (2 * Real.pi) * ((2 * Real.pi) * x) :=
      mul_le_mul_of_nonneg_left hsin (by positivity)
    _ = (2 * Real.pi) ^ 2 * x := by ring

theorem norm_ccmFirstClockDilationKernel_le_endpoint
    {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ‖ccmFirstClockDilationKernel x‖ ≤
      (2 * Real.pi) ^ 2 * (1 - x) := by
  rw [norm_ccmFirstClockDilationKernel]
  have harg :
      2 * Real.pi - (2 * Real.pi) * x =
        (2 * Real.pi) * (1 - x) := by ring
  have hsinPeriod :
      |Real.sin ((2 * Real.pi) * x)| =
        |Real.sin ((2 * Real.pi) * (1 - x))| := by
    have hperiod :=
      Real.sin_two_pi_sub ((2 * Real.pi) * x)
    rw [harg] at hperiod
    rw [hperiod, abs_neg]
  rw [hsinPeriod]
  have hsin :
      |Real.sin ((2 * Real.pi) * (1 - x))| ≤
        |(2 * Real.pi) * (1 - x)| :=
    Real.abs_sin_le_abs
  rw [abs_of_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hx1))] at hsin
  calc
    (2 * Real.pi) * |Real.sin ((2 * Real.pi) * (1 - x))| ≤
        (2 * Real.pi) * ((2 * Real.pi) * (1 - x)) :=
      mul_le_mul_of_nonneg_left hsin (by positivity)
    _ = (2 * Real.pi) ^ 2 * (1 - x) := by ring

/-- Fixed contraction ratio used by dilation--Volterra reflection. -/
def ccmFirstClockReflectionRatio : ℝ := 15 / 16

theorem ccmFirstClockReflectionRatio_pos :
    0 < ccmFirstClockReflectionRatio := by
  norm_num [ccmFirstClockReflectionRatio]

theorem ccmFirstClockReflectionRatio_lt_one :
    ccmFirstClockReflectionRatio < 1 := by
  norm_num [ccmFirstClockReflectionRatio]

theorem ccmFirstClockMellinKernel_tail_bound
    {x : ℝ} (hxr : ccmFirstClockReflectionRatio ≤ x) (hx1 : x ≤ 1) :
    ‖ccmFirstClockDilationKernel x‖ / x ≤
      (1024 / 15 : ℝ) * (1 - x) := by
  have hx0 : 0 < x :=
    ccmFirstClockReflectionRatio_pos.trans_le hxr
  have hk :=
    norm_ccmFirstClockDilationKernel_le_endpoint hx0.le hx1
  have hpiSq : (2 * Real.pi) ^ 2 ≤ 64 := by
    have htwo : 2 * Real.pi ≤ 8 := by
      nlinarith [Real.pi_le_four]
    have hsquare : (2 * Real.pi) ^ 2 ≤ (8 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity : 0 ≤ 2 * Real.pi) htwo 2
    norm_num at hsquare ⊢
    exact hsquare
  have hxInv : 1 / x ≤ 16 / 15 := by
    rw [div_le_iff₀ hx0]
    dsimp only [ccmFirstClockReflectionRatio] at hxr
    nlinarith
  calc
    ‖ccmFirstClockDilationKernel x‖ / x ≤
        ((2 * Real.pi) ^ 2 * (1 - x)) / x := by
      exact div_le_div_of_nonneg_right hk hx0.le
    _ = (2 * Real.pi) ^ 2 * (1 / x) * (1 - x) := by ring
    _ ≤ 64 * (16 / 15) * (1 - x) := by
      gcongr
    _ = (1024 / 15 : ℝ) * (1 - x) := by ring

theorem integral_ccmFirstClockMellinKernel_tail_lt_one :
    (∫ x : ℝ in ccmFirstClockReflectionRatio..1,
      ‖ccmFirstClockDilationKernel x‖ / x) < 1 := by
  have hle :
      (∫ x : ℝ in ccmFirstClockReflectionRatio..1,
        ‖ccmFirstClockDilationKernel x‖ / x) ≤
      ∫ x : ℝ in ccmFirstClockReflectionRatio..1,
        (1024 / 15 : ℝ) * (1 - x) := by
    apply intervalIntegral.integral_mono_on
    · exact ccmFirstClockReflectionRatio_lt_one.le
    · have hkcont : Continuous
          (fun x : ℝ => ‖ccmFirstClockDilationKernel x‖) := by
          unfold ccmFirstClockDilationKernel
          fun_prop
      exact (hkcont.continuousOn.div continuousOn_id
        (fun x hx => ne_of_gt
          (ccmFirstClockReflectionRatio_pos.trans_le
            ((show x ∈ Icc ccmFirstClockReflectionRatio 1 by
              simpa [uIcc_of_le ccmFirstClockReflectionRatio_lt_one.le]
                using hx).1)))).intervalIntegrable
    · exact (by fun_prop : Continuous
        (fun x : ℝ => (1024 / 15 : ℝ) * (1 - x))).continuousOn
          |>.intervalIntegrable
    · intro x hx
      exact ccmFirstClockMellinKernel_tail_bound hx.1 hx.2
  calc
    (∫ x : ℝ in ccmFirstClockReflectionRatio..1,
      ‖ccmFirstClockDilationKernel x‖ / x) ≤
        ∫ x : ℝ in ccmFirstClockReflectionRatio..1,
          (1024 / 15 : ℝ) * (1 - x) := hle
    _ = 2 / 15 := by
      rw [intervalIntegral.integral_const_mul]
      have hderiv : ∀ x ∈
          uIcc ccmFirstClockReflectionRatio 1,
          HasDerivAt (fun y : ℝ => y - y ^ 2 / 2) (1 - x) x := by
        intro x hx
        convert (hasDerivAt_id x).sub
          (((hasDerivAt_id x).pow 2).div_const 2) using 1 <;>
            simp only [id_eq] <;> ring
      have hint : IntervalIntegrable (fun x : ℝ => 1 - x)
          volume ccmFirstClockReflectionRatio 1 :=
        (by fun_prop : Continuous (fun x : ℝ => 1 - x)).intervalIntegrable _ _
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      norm_num [ccmFirstClockReflectionRatio]
    _ < 1 := by norm_num

theorem measurable_xiScrewDivisor :
    Measurable xiScrewDivisor := by
  unfold xiScrewDivisor
  exact Measurable.tsum fun q => by
    unfold xiScrewDivisorTerm
    fun_prop

set_option maxHeartbeats 800000 in
theorem norm_xiScrewDivisor_le (t : ℝ) :
    ‖xiScrewDivisor t‖ ≤
      (Real.exp (|t| / 2) + 1) *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
  rw [xiScrewDivisor]
  calc
    ‖∑' q : XiZeroCopy, xiScrewDivisorTerm t q‖ ≤
        ∑' q : XiZeroCopy, ‖xiScrewDivisorTerm t q‖ :=
      norm_tsum_le_tsum_norm (xiScrewDivisorTerm_summable t).norm
    _ ≤ ∑' q : XiZeroCopy,
        (Real.exp (|t| / 2) + 1) /
          ‖xiSpectralPoint q‖ ^ 2 := by
      have hupper : Summable (fun q : XiZeroCopy =>
          (Real.exp (|t| / 2) + 1) /
            ‖xiSpectralPoint q‖ ^ 2) := by
        apply (xiSpectralPoint_inv_sq_summable.mul_left
          (Real.exp (|t| / 2) + 1)).congr
        intro q
        ring
      exact Summable.tsum_le_tsum
        (fun q => norm_xiScrewDivisorTerm_le t q)
        (xiScrewDivisorTerm_summable t).norm
        hupper
    _ = (Real.exp (|t| / 2) + 1) *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro q
      ring

private theorem intervalIntegrable_dilationKernel_mul_screw
    {L : ℝ} (hL : 0 ≤ L) :
    IntervalIntegrable (fun x : ℝ =>
      ccmFirstClockDilationKernel x * xiScrewDivisor (L * x))
      volume 0 1 := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ =>
      ccmFirstClockDilationKernel x * xiScrewDivisor (L * x))
      (volume.restrict (uIoc (0 : ℝ) 1)) := by
    exact ((by
      unfold ccmFirstClockDilationKernel
      fun_prop : Measurable ccmFirstClockDilationKernel).mul
        (measurable_xiScrewDivisor.comp
          (measurable_const.mul measurable_id))).aestronglyMeasurable
  rw [intervalIntegrable_iff,
    uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  let M : ℝ :=
    (2 * Real.pi) *
      (Real.exp (L / 2) + 1) *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  have hbound :
      ∀ᵐ x : ℝ ∂volume.restrict (Ioc (0 : ℝ) 1),
        ‖ccmFirstClockDilationKernel x *
          xiScrewDivisor (L * x)‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [norm_mul]
    have hk : ‖ccmFirstClockDilationKernel x‖ ≤ 2 * Real.pi := by
      rw [norm_ccmFirstClockDilationKernel]
      have hs :
          |Real.sin ((2 * Real.pi) * x)| ≤ 1 :=
        (abs_le.mpr (Real.sin_mem_Icc ((2 * Real.pi) * x)))
      nlinarith [Real.pi_pos]
    have hLx : |L * x| ≤ L := by
      rw [abs_mul, abs_of_nonneg hL, abs_of_pos hx.1]
      exact mul_le_of_le_one_right hL hx.2
    have hscrew := norm_xiScrewDivisor_le (L * x)
    have hexp : Real.exp (|L * x| / 2) ≤ Real.exp (L / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    dsimp only [M]
    calc
      ‖ccmFirstClockDilationKernel x‖ *
          ‖xiScrewDivisor (L * x)‖ ≤
        (2 * Real.pi) *
          ((Real.exp (|L * x| / 2) + 1) *
            ∑' q : XiZeroCopy,
              1 / ‖xiSpectralPoint q‖ ^ 2) := by gcongr
      _ ≤ (2 * Real.pi) *
          ((Real.exp (L / 2) + 1) *
            ∑' q : XiZeroCopy,
              1 / ‖xiSpectralPoint q‖ ^ 2) := by
        gcongr
      _ = _ := by ring
  exact IntegrableOn.of_bound measure_Ioc_lt_top
    (by simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hmeas)
    M hbound

theorem norm_screw_le_firstClock_add_dilationNorm
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    ‖xiScrewDivisor L‖ ≤
      ‖ccmFirstClockXiRationalDivisor L‖ +
        ∫ x : ℝ in (0 : ℝ)..1,
          ‖ccmFirstClockDilationKernel x‖ *
            ‖xiScrewDivisor (L * x)‖ := by
  have heq :=
    ccmFirstClockXiRationalDivisor_eq_screw_add_dilation hL
  have hL0 : 0 ≤ L :=
    (by positivity : 0 < Real.pi / 2).le.trans hL
  have hint := intervalIntegrable_dilationKernel_mul_screw hL0
  have hnorm :=
    intervalIntegral.norm_integral_le_integral_norm
      (μ := volume)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (f := fun x : ℝ =>
        ccmFirstClockDilationKernel x * xiScrewDivisor (L * x))
  have htri :
      ‖xiScrewDivisor L‖ ≤
        ‖ccmFirstClockXiRationalDivisor L‖ +
          ‖∫ x : ℝ in (0 : ℝ)..1,
            ccmFirstClockDilationKernel x *
              xiScrewDivisor (L * x)‖ := by
    have heq' :
        xiScrewDivisor L =
          ccmFirstClockXiRationalDivisor L -
            ∫ x : ℝ in (0 : ℝ)..1,
              ccmFirstClockDilationKernel x *
                xiScrewDivisor (L * x) :=
      eq_sub_of_add_eq heq.symm
    rw [heq']
    have := norm_sub_le
      (ccmFirstClockXiRationalDivisor L)
      (∫ x : ℝ in (0 : ℝ)..1,
        ccmFirstClockDilationKernel x * xiScrewDivisor (L * x))
    exact this
  calc
    ‖xiScrewDivisor L‖ ≤
        ‖ccmFirstClockXiRationalDivisor L‖ +
          ‖∫ x : ℝ in (0 : ℝ)..1,
            ccmFirstClockDilationKernel x *
              xiScrewDivisor (L * x)‖ := htri
    _ ≤ ‖ccmFirstClockXiRationalDivisor L‖ +
        ∫ x : ℝ in (0 : ℝ)..1,
          ‖ccmFirstClockDilationKernel x *
            xiScrewDivisor (L * x)‖ := by gcongr
    _ = _ := by
      apply congrArg (fun y : ℝ =>
        ‖ccmFirstClockXiRationalDivisor L‖ + y)
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [norm_mul]

def ccmXiScrewWeightedNorm (a L : ℝ) : ℝ :=
  Real.exp (-a * L) * ‖xiScrewDivisor L‖

def ccmFirstClockXiWeightedNorm (a L : ℝ) : ℝ :=
  Real.exp (-a * L) * ‖ccmFirstClockXiRationalDivisor L‖

theorem ccmXiScrewWeightedNorm_nonneg (a L : ℝ) :
    0 ≤ ccmXiScrewWeightedNorm a L := by
  unfold ccmXiScrewWeightedNorm
  positivity

theorem ccmFirstClockXiWeightedNorm_nonneg (a L : ℝ) :
    0 ≤ ccmFirstClockXiWeightedNorm a L := by
  unfold ccmFirstClockXiWeightedNorm
  positivity

theorem measurable_ccmXiScrewWeightedNorm (a : ℝ) :
    Measurable (ccmXiScrewWeightedNorm a) := by
  unfold ccmXiScrewWeightedNorm
  exact (by fun_prop : Measurable (fun L : ℝ => Real.exp (-a * L))).mul
    measurable_xiScrewDivisor.norm

theorem measurable_ccmFirstClockXiWeightedNorm (a : ℝ) :
    Measurable (ccmFirstClockXiWeightedNorm a) := by
  unfold ccmFirstClockXiWeightedNorm
  exact (by fun_prop : Measurable (fun L : ℝ => Real.exp (-a * L))).mul
    measurable_ccmFirstClockXiRationalDivisor.norm

theorem norm_exp_mul_xiScrewDivisor_eq_weightedNorm
    (a L : ℝ) :
    ‖Complex.exp (-(a : ℂ) * (L : ℂ)) *
      xiScrewDivisor L‖ = ccmXiScrewWeightedNorm a L := by
  rw [norm_mul, Complex.norm_exp]
  unfold ccmXiScrewWeightedNorm
  congr 2
  simp [mul_re]

theorem norm_exp_mul_firstClockXi_eq_weightedNorm
    (a L : ℝ) :
    ‖Complex.exp (-(a : ℂ) * (L : ℂ)) *
      ccmFirstClockXiRationalDivisor L‖ =
        ccmFirstClockXiWeightedNorm a L := by
  rw [norm_mul, Complex.norm_exp]
  unfold ccmFirstClockXiWeightedNorm
  congr 2
  simp [mul_re]

theorem integral_ccmXiScrewWeightedNorm_dilate
    {a x N : ℝ} (hx : 0 < x) :
    (∫ L : ℝ in (0 : ℝ)..N,
      Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖) =
      (1 / x) * ∫ u : ℝ in (0 : ℝ)..(N * x),
        ccmXiScrewWeightedNorm (a / x) u := by
  let F : ℝ → ℝ := fun u =>
    ccmXiScrewWeightedNorm (a / x) u
  have hsub := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := N) F x
  have hsub' :
      x * (∫ L : ℝ in (0 : ℝ)..N, F (x * L)) =
        ∫ u : ℝ in (0 : ℝ)..(N * x), F u := by
    simpa only [smul_eq_mul, mul_zero, mul_comm x N] using hsub
  have hpoint (L : ℝ) :
      F (x * L) =
        Real.exp (-a * L) * ‖xiScrewDivisor (x * L)‖ := by
    dsimp only [F, ccmXiScrewWeightedNorm]
    have hexp : -(a / x) * (x * L) = -a * L := by
      field_simp [hx.ne']
    rw [hexp]
  simp_rw [hpoint] at hsub'
  dsimp only [F] at hsub'
  have hresult :
      (∫ L : ℝ in (0 : ℝ)..N,
        Real.exp (-a * L) * ‖xiScrewDivisor (x * L)‖) =
        (1 / x) * ∫ u : ℝ in (0 : ℝ)..(N * x),
          ccmXiScrewWeightedNorm (a / x) u := by
    calc
      (∫ L : ℝ in (0 : ℝ)..N,
        Real.exp (-a * L) * ‖xiScrewDivisor (x * L)‖) =
          (1 / x) * (x * ∫ L : ℝ in (0 : ℝ)..N,
            Real.exp (-a * L) * ‖xiScrewDivisor (x * L)‖) := by
        rw [one_div, ← mul_assoc, inv_mul_cancel₀ hx.ne', one_mul]
      _ = (1 / x) * ∫ u : ℝ in (0 : ℝ)..(N * x),
          ccmXiScrewWeightedNorm (a / x) u := by rw [hsub']
  calc
    (∫ L : ℝ in (0 : ℝ)..N,
      Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖) =
        ∫ L : ℝ in (0 : ℝ)..N,
          Real.exp (-a * L) * ‖xiScrewDivisor (x * L)‖ := by
      apply intervalIntegral.integral_congr
      intro L hL
      dsimp only
      rw [mul_comm L x]
    _ = _ := hresult

theorem integrableOn_ccmXiScrewWeightedNorm
    {a : ℝ}
    (h : IntegrableOn (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)) *
        xiScrewDivisor L) (Ioi 0)) :
    IntegrableOn (ccmXiScrewWeightedNorm a) (Ioi 0) := by
  apply h.norm.congr
  filter_upwards with L
  exact norm_exp_mul_xiScrewDivisor_eq_weightedNorm a L

theorem integrableOn_ccmFirstClockXiWeightedNorm
    {a : ℝ}
    (h : IntegrableOn (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)) *
        ccmFirstClockXiRationalDivisor L) (Ioi 0)) :
    IntegrableOn (ccmFirstClockXiWeightedNorm a) (Ioi 0) := by
  apply h.norm.congr
  filter_upwards with L
  exact norm_exp_mul_firstClockXi_eq_weightedNorm a L

theorem ccmFirstClockMellinKernel_le_sixtyFour
    {x : ℝ} (hx : 0 < x) :
    ‖ccmFirstClockDilationKernel x‖ / x ≤ 64 := by
  have hk := norm_ccmFirstClockDilationKernel_le_origin hx.le
  have hpiSq : (2 * Real.pi) ^ 2 ≤ 64 := by
    have htwo : 2 * Real.pi ≤ 8 := by
      nlinarith [Real.pi_le_four]
    have hsquare : (2 * Real.pi) ^ 2 ≤ (8 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity : 0 ≤ 2 * Real.pi) htwo 2
    norm_num at hsquare ⊢
    exact hsquare
  calc
    ‖ccmFirstClockDilationKernel x‖ / x ≤
        ((2 * Real.pi) ^ 2 * x) / x :=
      div_le_div_of_nonneg_right hk hx.le
    _ = (2 * Real.pi) ^ 2 := by field_simp [hx.ne']
    _ ≤ 64 := hpiSq

theorem integral_ccmFirstClockMellinKernel_low_le :
    (∫ x : ℝ in (0 : ℝ)..ccmFirstClockReflectionRatio,
      ‖ccmFirstClockDilationKernel x‖ / x) ≤
        64 * ccmFirstClockReflectionRatio := by
  have hle :
      (∫ x : ℝ in (0 : ℝ)..ccmFirstClockReflectionRatio,
        ‖ccmFirstClockDilationKernel x‖ / x) ≤
      ∫ x : ℝ in (0 : ℝ)..ccmFirstClockReflectionRatio,
        (64 : ℝ) := by
    have hleft : IntervalIntegrable
        (fun x : ℝ => ‖ccmFirstClockDilationKernel x‖ / x)
        volume 0 ccmFirstClockReflectionRatio := by
      rw [intervalIntegrable_iff,
        uIoc_of_le ccmFirstClockReflectionRatio_pos.le]
      have hmeas : AEStronglyMeasurable
          (fun x : ℝ => ‖ccmFirstClockDilationKernel x‖ / x)
          (volume.restrict
            (Ioc (0 : ℝ) ccmFirstClockReflectionRatio)) :=
        ((by
          unfold ccmFirstClockDilationKernel
          fun_prop : Measurable (fun x : ℝ =>
            ‖ccmFirstClockDilationKernel x‖ / x))).aestronglyMeasurable
      have hbound :
          ∀ᵐ x : ℝ ∂volume.restrict
            (Ioc (0 : ℝ) ccmFirstClockReflectionRatio),
            ‖‖ccmFirstClockDilationKernel x‖ / x‖ ≤ (64 : ℝ) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact ccmFirstClockMellinKernel_le_sixtyFour hx.1
        · exact div_nonneg (norm_nonneg _) hx.1.le
      exact IntegrableOn.of_bound measure_Ioc_lt_top hmeas 64 hbound
    apply intervalIntegral.integral_mono_on
    · exact ccmFirstClockReflectionRatio_pos.le
    · exact hleft
    · exact intervalIntegrable_const
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ)
          ccmFirstClockReflectionRatio := by
        simpa [uIcc_of_le ccmFirstClockReflectionRatio_pos.le] using hx
      by_cases hzero : x = 0
      · simp [hzero]
      · exact ccmFirstClockMellinKernel_le_sixtyFour
          (lt_of_le_of_ne hx'.1 (Ne.symm hzero))
  calc
    (∫ x : ℝ in (0 : ℝ)..ccmFirstClockReflectionRatio,
      ‖ccmFirstClockDilationKernel x‖ / x) ≤
        ∫ x : ℝ in (0 : ℝ)..ccmFirstClockReflectionRatio,
          (64 : ℝ) := hle
    _ = 64 * ccmFirstClockReflectionRatio := by
      simp [mul_comm]

theorem intervalIntegrable_ccmFirstClockMellinKernel_low :
    IntervalIntegrable
      (fun x : ℝ => ‖ccmFirstClockDilationKernel x‖ / x)
      volume 0 ccmFirstClockReflectionRatio := by
  rw [intervalIntegrable_iff,
    uIoc_of_le ccmFirstClockReflectionRatio_pos.le]
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => ‖ccmFirstClockDilationKernel x‖ / x)
      (volume.restrict
        (Ioc (0 : ℝ) ccmFirstClockReflectionRatio)) :=
    ((by
      unfold ccmFirstClockDilationKernel
      fun_prop : Measurable (fun x : ℝ =>
        ‖ccmFirstClockDilationKernel x‖ / x))).aestronglyMeasurable
  have hbound :
      ∀ᵐ x : ℝ ∂volume.restrict
        (Ioc (0 : ℝ) ccmFirstClockReflectionRatio),
        ‖‖ccmFirstClockDilationKernel x‖ / x‖ ≤ (64 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact ccmFirstClockMellinKernel_le_sixtyFour hx.1
    · exact div_nonneg (norm_nonneg _) hx.1.le
  exact IntegrableOn.of_bound measure_Ioc_lt_top hmeas 64 hbound

theorem intervalIntegrable_ccmFirstClockMellinKernel_tail :
    IntervalIntegrable
      (fun x : ℝ => ‖ccmFirstClockDilationKernel x‖ / x)
      volume ccmFirstClockReflectionRatio 1 := by
  have hkcont : Continuous
      (fun x : ℝ => ‖ccmFirstClockDilationKernel x‖) := by
    unfold ccmFirstClockDilationKernel
    fun_prop
  exact (hkcont.continuousOn.div continuousOn_id
    (fun x hx => ne_of_gt
      (ccmFirstClockReflectionRatio_pos.trans_le
        ((show x ∈ Icc ccmFirstClockReflectionRatio 1 by
          simpa [uIcc_of_le ccmFirstClockReflectionRatio_lt_one.le]
            using hx).1)))).intervalIntegrable

private theorem integrable_weightedDilation_rectangle
    {a N : ℝ} (ha : 0 < a)
    (_hN : Real.pi / 2 ≤ N) :
    Integrable (fun p : ℝ × ℝ =>
      Real.exp (-a * p.1) *
        ‖ccmFirstClockDilationKernel p.2‖ *
          ‖xiScrewDivisor (p.1 * p.2)‖)
      ((volume.restrict (Ioc (Real.pi / 2) N)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))) := by
  let M : ℝ :=
    (2 * Real.pi) * (Real.exp (N / 2) + 1) *
      ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  have hfunMeas : Measurable (fun p : ℝ × ℝ =>
      Real.exp (-a * p.1) *
        ‖ccmFirstClockDilationKernel p.2‖ *
          ‖xiScrewDivisor (p.1 * p.2)‖) := by
    simpa only [Function.comp_apply, mul_assoc] using
      ((by fun_prop : Measurable (fun p : ℝ × ℝ =>
      Real.exp (-a * p.1))).mul
        ((by
          unfold ccmFirstClockDilationKernel
          fun_prop : Measurable (fun p : ℝ × ℝ =>
            ‖ccmFirstClockDilationKernel p.2‖)).mul
          (measurable_xiScrewDivisor.comp
            (measurable_fst.mul measurable_snd)).norm))
  apply Integrable.of_bound hfunMeas.aestronglyMeasurable M
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
    (measurableSet_le (Measurable.norm hfunMeas) measurable_const)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hLmem
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hxmem
  have hL0 : 0 ≤ L :=
    (by positivity : 0 < Real.pi / 2).le.trans hLmem.1.le
  have hLx : |L * x| ≤ N := by
    rw [abs_mul, abs_of_nonneg hL0, abs_of_pos hxmem.1]
    calc
      L * x ≤ L := mul_le_of_le_one_right hL0 hxmem.2
      _ ≤ N := hLmem.2
  have hexpA : Real.exp (-a * L) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr ha.le) hL0)
  have hk : ‖ccmFirstClockDilationKernel x‖ ≤ 2 * Real.pi := by
    rw [norm_ccmFirstClockDilationKernel]
    have hs :
        |Real.sin ((2 * Real.pi) * x)| ≤ 1 :=
      abs_le.mpr (Real.sin_mem_Icc ((2 * Real.pi) * x))
    nlinarith [Real.pi_pos]
  have hscrew := norm_xiScrewDivisor_le (L * x)
  have hexpN :
      Real.exp (|L * x| / 2) ≤ Real.exp (N / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  dsimp only [M]
  calc
    ‖Real.exp (-a * L) *
        ‖ccmFirstClockDilationKernel x‖ *
          ‖xiScrewDivisor (L * x)‖‖ =
      Real.exp (-a * L) *
        ‖ccmFirstClockDilationKernel x‖ *
          ‖xiScrewDivisor (L * x)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      positivity
    _ ≤ 1 * (2 * Real.pi) *
        ((Real.exp (|L * x| / 2) + 1) *
          ∑' q : XiZeroCopy,
            1 / ‖xiSpectralPoint q‖ ^ 2) := by gcongr
    _ ≤ 1 * (2 * Real.pi) *
        ((Real.exp (N / 2) + 1) *
          ∑' q : XiZeroCopy,
            1 / ‖xiSpectralPoint q‖ ^ 2) := by gcongr
    _ = _ := by ring

theorem integral_integral_weightedDilation_swap
    {a N : ℝ} (ha : 0 < a) (hN : Real.pi / 2 ≤ N) :
    (∫ L : ℝ in Real.pi / 2..N,
      ∫ x : ℝ in (0 : ℝ)..1,
        Real.exp (-a * L) *
          ‖ccmFirstClockDilationKernel x‖ *
            ‖xiScrewDivisor (L * x)‖) =
      ∫ x : ℝ in (0 : ℝ)..1,
        ∫ L : ℝ in Real.pi / 2..N,
          Real.exp (-a * L) *
            ‖ccmFirstClockDilationKernel x‖ *
              ‖xiScrewDivisor (L * x)‖ := by
  have hprod :=
    integrable_weightedDilation_rectangle ha hN
  have hswap :=
    MeasureTheory.integral_integral_swap
      (μ := volume.restrict (Ioc (Real.pi / 2) N))
      (ν := volume.restrict (Ioc (0 : ℝ) 1))
      (f := fun L x =>
        Real.exp (-a * L) *
          ‖ccmFirstClockDilationKernel x‖ *
            ‖xiScrewDivisor (L * x)‖)
      hprod
  simpa only [
    intervalIntegral.integral_of_le hN,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    using hswap

private theorem intervalIntegrable_ccmXiScrewWeightedNorm_Icc
    {a N : ℝ} (ha : 0 < a) (hN : 0 ≤ N) :
    IntervalIntegrable (ccmXiScrewWeightedNorm a) volume 0 N := by
  rw [intervalIntegrable_iff, uIoc_of_le hN]
  let M : ℝ :=
    (Real.exp (N / 2) + 1) *
      ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  have hbound :
      ∀ᵐ L : ℝ ∂volume.restrict (Ioc (0 : ℝ) N),
        ‖ccmXiScrewWeightedNorm a L‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
    rw [Real.norm_eq_abs,
      abs_of_nonneg (ccmXiScrewWeightedNorm_nonneg a L)]
    unfold ccmXiScrewWeightedNorm
    have hexpA : Real.exp (-a * L) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr ha.le) hL.1.le)
    have hscrew := norm_xiScrewDivisor_le L
    have hLabs : |L| ≤ N := by
      rw [abs_of_pos hL.1]
      exact hL.2
    have hexpN :
        Real.exp (|L| / 2) ≤ Real.exp (N / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    dsimp only [M]
    calc
      Real.exp (-a * L) * ‖xiScrewDivisor L‖ ≤
        1 * ((Real.exp (|L| / 2) + 1) *
          ∑' q : XiZeroCopy,
            1 / ‖xiSpectralPoint q‖ ^ 2) := by gcongr
      _ ≤ 1 * ((Real.exp (N / 2) + 1) *
          ∑' q : XiZeroCopy,
            1 / ‖xiSpectralPoint q‖ ^ 2) := by gcongr
      _ = _ := by ring
  exact IntegrableOn.of_bound measure_Ioc_lt_top
    (measurable_ccmXiScrewWeightedNorm a).aestronglyMeasurable
    M hbound

private theorem intervalIntegrable_exp_norm_screw_dilate
    {a x N : ℝ} (ha : 0 < a) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hN : 0 ≤ N) :
    IntervalIntegrable (fun L : ℝ =>
      Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖)
      volume 0 N := by
  rw [intervalIntegrable_iff, uIoc_of_le hN]
  let M : ℝ :=
    (Real.exp (N / 2) + 1) *
      ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  have hmeas : AEStronglyMeasurable (fun L : ℝ =>
      Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖)
      (volume.restrict (Ioc (0 : ℝ) N)) := by
    exact ((by fun_prop : Measurable (fun L : ℝ =>
      Real.exp (-a * L))).mul
        (measurable_xiScrewDivisor.comp
          (measurable_id.mul measurable_const)).norm).aestronglyMeasurable
  have hbound :
      ∀ᵐ L : ℝ ∂volume.restrict (Ioc (0 : ℝ) N),
        ‖Real.exp (-a * L) *
          ‖xiScrewDivisor (L * x)‖‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · have hexpA : Real.exp (-a * L) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr
          (mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr ha.le) hL.1.le)
      have hLx : |L * x| ≤ N := by
        rw [abs_mul, abs_of_pos hL.1, abs_of_pos hx0]
        calc
          L * x ≤ L := mul_le_of_le_one_right hL.1.le hx1
          _ ≤ N := hL.2
      have hscrew := norm_xiScrewDivisor_le (L * x)
      have hexpN :
          Real.exp (|L * x| / 2) ≤ Real.exp (N / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      dsimp only [M]
      calc
        Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖ ≤
          1 * ((Real.exp (|L * x| / 2) + 1) *
            ∑' q : XiZeroCopy,
              1 / ‖xiSpectralPoint q‖ ^ 2) := by gcongr
        _ ≤ 1 * ((Real.exp (N / 2) + 1) *
            ∑' q : XiZeroCopy,
              1 / ‖xiSpectralPoint q‖ ^ 2) := by gcongr
        _ = _ := by ring
    · positivity
  exact IntegrableOn.of_bound measure_Ioc_lt_top hmeas M hbound

private theorem integral_ccmXiScrewWeightedNorm_interval_le_global
    {b c T : ℝ} (hc : 0 < c) (hcb : c ≤ b) (hT : 0 ≤ T)
    (hglobal : IntegrableOn (ccmXiScrewWeightedNorm c) (Ioi 0)) :
    (∫ u : ℝ in (0 : ℝ)..T,
      ccmXiScrewWeightedNorm b u) ≤
      ∫ u : ℝ in Ioi 0, ccmXiScrewWeightedNorm c u := by
  have hb : 0 < b := hc.trans_le hcb
  have hbint :=
    intervalIntegrable_ccmXiScrewWeightedNorm_Icc hb hT
  have hcint :=
    intervalIntegrable_ccmXiScrewWeightedNorm_Icc hc hT
  rw [intervalIntegral.integral_of_le hT]
  have hlocal :
      (∫ u : ℝ in Ioc (0 : ℝ) T,
        ccmXiScrewWeightedNorm b u) ≤
      ∫ u : ℝ in Ioc (0 : ℝ) T,
        ccmXiScrewWeightedNorm c u := by
    apply integral_mono_ae hbint.1 hcint.1
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    unfold ccmXiScrewWeightedNorm
    have hmul : c * u ≤ b * u :=
      mul_le_mul_of_nonneg_right hcb hu.1.le
    have hexp : Real.exp (-b * u) ≤ Real.exp (-c * u) :=
      Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  refine hlocal.trans ?_
  apply MeasureTheory.integral_mono_measure
    (Measure.restrict_mono_set volume (by
      intro u hu
      exact hu.1))
  · filter_upwards with u
    exact ccmXiScrewWeightedNorm_nonneg c u
  · exact hglobal

private theorem weightedDilation_inner_low_le
    {a x N : ℝ} (ha : 0 < a) (hx0 : 0 < x)
    (hxr : x ≤ ccmFirstClockReflectionRatio)
    (hN : Real.pi / 2 ≤ N)
    (hseed : IntegrableOn
      (ccmXiScrewWeightedNorm
        (a / ccmFirstClockReflectionRatio)) (Ioi 0)) :
    (∫ L : ℝ in Real.pi / 2..N,
      Real.exp (-a * L) *
        ‖ccmFirstClockDilationKernel x‖ *
          ‖xiScrewDivisor (L * x)‖) ≤
      (‖ccmFirstClockDilationKernel x‖ / x) *
        ∫ u : ℝ in Ioi 0,
          ccmXiScrewWeightedNorm
            (a / ccmFirstClockReflectionRatio) u := by
  have hx1 : x ≤ 1 :=
    hxr.trans ccmFirstClockReflectionRatio_lt_one.le
  have hN0 : 0 ≤ N :=
    (by positivity : 0 < Real.pi / 2).le.trans hN
  have hint :=
    intervalIntegrable_exp_norm_screw_dilate ha hx0 hx1 hN0
  have hmono :
      (∫ L : ℝ in Real.pi / 2..N,
        Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖) ≤
      ∫ L : ℝ in (0 : ℝ)..N,
        Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖ := by
    apply intervalIntegral.integral_mono_interval
    · positivity
    · exact hN
    · exact le_rfl
    · filter_upwards with L
      positivity
    · exact hint
  have hrate :
      a / ccmFirstClockReflectionRatio ≤ a / x := by
    exact (div_le_div_iff₀
      ccmFirstClockReflectionRatio_pos hx0).2
        (mul_le_mul_of_nonneg_left hxr ha.le)
  have hNx : 0 ≤ N * x := mul_nonneg hN0 hx0.le
  have hweighted :=
    integral_ccmXiScrewWeightedNorm_interval_le_global
      (div_pos ha ccmFirstClockReflectionRatio_pos)
      hrate hNx hseed
  have hrearrange :
      (∫ L : ℝ in Real.pi / 2..N,
        Real.exp (-a * L) *
          ‖ccmFirstClockDilationKernel x‖ *
            ‖xiScrewDivisor (L * x)‖) =
      ‖ccmFirstClockDilationKernel x‖ *
        ∫ L : ℝ in Real.pi / 2..N,
          Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro L hL
    ring
  rw [hrearrange]
  calc
    ‖ccmFirstClockDilationKernel x‖ *
        (∫ L : ℝ in Real.pi / 2..N,
          Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖) ≤
      ‖ccmFirstClockDilationKernel x‖ *
        (∫ L : ℝ in (0 : ℝ)..N,
          Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖) :=
      mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
    _ = ‖ccmFirstClockDilationKernel x‖ *
        ((1 / x) * ∫ u : ℝ in (0 : ℝ)..(N * x),
          ccmXiScrewWeightedNorm (a / x) u) := by
      rw [integral_ccmXiScrewWeightedNorm_dilate hx0]
    _ = (‖ccmFirstClockDilationKernel x‖ / x) *
        (∫ u : ℝ in (0 : ℝ)..(N * x),
          ccmXiScrewWeightedNorm (a / x) u) := by ring
    _ ≤ (‖ccmFirstClockDilationKernel x‖ / x) *
        ∫ u : ℝ in Ioi 0,
          ccmXiScrewWeightedNorm
            (a / ccmFirstClockReflectionRatio) u :=
      mul_le_mul_of_nonneg_left hweighted
        (div_nonneg (norm_nonneg _) hx0.le)

private theorem integral_ccmXiScrewWeightedNorm_dilated_le_truncated
    {a x N : ℝ} (ha : 0 < a) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hN : 0 ≤ N) :
    (∫ u : ℝ in (0 : ℝ)..(N * x),
      ccmXiScrewWeightedNorm (a / x) u) ≤
      ∫ u : ℝ in (0 : ℝ)..N,
        ccmXiScrewWeightedNorm a u := by
  have hNx : 0 ≤ N * x := mul_nonneg hN hx0.le
  have hrate : a ≤ a / x := by
    exact (le_div_iff₀ hx0).2
      (mul_le_of_le_one_right ha.le hx1)
  have hleft :=
    intervalIntegrable_ccmXiScrewWeightedNorm_Icc
      (ha.trans_le hrate) hNx
  have hrightLocal :=
    intervalIntegrable_ccmXiScrewWeightedNorm_Icc ha hNx
  have hright :=
    intervalIntegrable_ccmXiScrewWeightedNorm_Icc ha hN
  have hpoint :
      (∫ u : ℝ in (0 : ℝ)..(N * x),
        ccmXiScrewWeightedNorm (a / x) u) ≤
      ∫ u : ℝ in (0 : ℝ)..(N * x),
        ccmXiScrewWeightedNorm a u := by
    apply intervalIntegral.integral_mono_on
    · exact hNx
    · exact hleft
    · exact hrightLocal
    · intro u hu
      have hu' : u ∈ Icc (0 : ℝ) (N * x) := by
        simpa [uIcc_of_le hNx] using hu
      unfold ccmXiScrewWeightedNorm
      have hmul : a * u ≤ (a / x) * u :=
        mul_le_mul_of_nonneg_right hrate hu'.1
      have hexp :
          Real.exp (-(a / x) * u) ≤ Real.exp (-a * u) :=
        Real.exp_le_exp.mpr (by linarith)
      exact mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  refine hpoint.trans ?_
  apply intervalIntegral.integral_mono_interval
  · exact le_rfl
  · exact hNx
  · exact mul_le_of_le_one_right hN hx1
  · filter_upwards with u
    exact ccmXiScrewWeightedNorm_nonneg a u
  · exact hright

private theorem weightedDilation_inner_tail_le
    {a x N : ℝ} (ha : 0 < a)
    (hxr : ccmFirstClockReflectionRatio ≤ x) (hx1 : x ≤ 1)
    (hN : Real.pi / 2 ≤ N) :
    (∫ L : ℝ in Real.pi / 2..N,
      Real.exp (-a * L) *
        ‖ccmFirstClockDilationKernel x‖ *
          ‖xiScrewDivisor (L * x)‖) ≤
      (‖ccmFirstClockDilationKernel x‖ / x) *
        ∫ u : ℝ in (0 : ℝ)..N,
          ccmXiScrewWeightedNorm a u := by
  have hx0 : 0 < x :=
    ccmFirstClockReflectionRatio_pos.trans_le hxr
  have hN0 : 0 ≤ N :=
    (by positivity : 0 < Real.pi / 2).le.trans hN
  have hint :=
    intervalIntegrable_exp_norm_screw_dilate ha hx0 hx1 hN0
  have hmono :
      (∫ L : ℝ in Real.pi / 2..N,
        Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖) ≤
      ∫ L : ℝ in (0 : ℝ)..N,
        Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖ := by
    apply intervalIntegral.integral_mono_interval
    · positivity
    · exact hN
    · exact le_rfl
    · filter_upwards with L
      positivity
    · exact hint
  have hweighted :=
    integral_ccmXiScrewWeightedNorm_dilated_le_truncated
      ha hx0 hx1 hN0
  have hrearrange :
      (∫ L : ℝ in Real.pi / 2..N,
        Real.exp (-a * L) *
          ‖ccmFirstClockDilationKernel x‖ *
            ‖xiScrewDivisor (L * x)‖) =
      ‖ccmFirstClockDilationKernel x‖ *
        ∫ L : ℝ in Real.pi / 2..N,
          Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro L hL
    ring
  rw [hrearrange]
  calc
    ‖ccmFirstClockDilationKernel x‖ *
        (∫ L : ℝ in Real.pi / 2..N,
          Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖) ≤
      ‖ccmFirstClockDilationKernel x‖ *
        (∫ L : ℝ in (0 : ℝ)..N,
          Real.exp (-a * L) * ‖xiScrewDivisor (L * x)‖) :=
      mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
    _ = ‖ccmFirstClockDilationKernel x‖ *
        ((1 / x) * ∫ u : ℝ in (0 : ℝ)..(N * x),
          ccmXiScrewWeightedNorm (a / x) u) := by
      rw [integral_ccmXiScrewWeightedNorm_dilate hx0]
    _ = (‖ccmFirstClockDilationKernel x‖ / x) *
        (∫ u : ℝ in (0 : ℝ)..(N * x),
          ccmXiScrewWeightedNorm (a / x) u) := by ring
    _ ≤ (‖ccmFirstClockDilationKernel x‖ / x) *
        ∫ u : ℝ in (0 : ℝ)..N,
          ccmXiScrewWeightedNorm a u :=
      mul_le_mul_of_nonneg_left hweighted
        (div_nonneg (norm_nonneg _) hx0.le)

private theorem integral_weightedDilation_le_low_add_tail
    {a N : ℝ} (ha : 0 < a) (hN : Real.pi / 2 ≤ N)
    (hseed : IntegrableOn
      (ccmXiScrewWeightedNorm
        (a / ccmFirstClockReflectionRatio)) (Ioi 0)) :
    (∫ L : ℝ in Real.pi / 2..N,
      ∫ x : ℝ in (0 : ℝ)..1,
        Real.exp (-a * L) *
          ‖ccmFirstClockDilationKernel x‖ *
            ‖xiScrewDivisor (L * x)‖) ≤
      (64 * ccmFirstClockReflectionRatio) *
        (∫ u : ℝ in Ioi 0,
          ccmXiScrewWeightedNorm
            (a / ccmFirstClockReflectionRatio) u) +
      (∫ x : ℝ in ccmFirstClockReflectionRatio..1,
        ‖ccmFirstClockDilationKernel x‖ / x) *
          (∫ u : ℝ in (0 : ℝ)..N,
            ccmXiScrewWeightedNorm a u) := by
  let H : ℝ → ℝ := fun x =>
    ∫ L : ℝ in Real.pi / 2..N,
      Real.exp (-a * L) *
        ‖ccmFirstClockDilationKernel x‖ *
          ‖xiScrewDivisor (L * x)‖
  let Eseed : ℝ :=
    ∫ u : ℝ in Ioi 0,
      ccmXiScrewWeightedNorm
        (a / ccmFirstClockReflectionRatio) u
  let AN : ℝ :=
    ∫ u : ℝ in (0 : ℝ)..N,
      ccmXiScrewWeightedNorm a u
  have hprod :=
    integrable_weightedDilation_rectangle ha hN
  have hHint : IntervalIntegrable H volume
      ccmFirstClockReflectionRatio 1 := by
    rw [intervalIntegrable_iff,
      uIoc_of_le ccmFirstClockReflectionRatio_lt_one.le]
    have hi := hprod.integral_prod_right
    have hiTail := hi.mono_measure
      (Measure.restrict_mono_set volume (show
        Ioc ccmFirstClockReflectionRatio 1 ⊆ Ioc (0 : ℝ) 1 by
        intro x (hx : x ∈ Ioc ccmFirstClockReflectionRatio 1)
        exact ⟨ccmFirstClockReflectionRatio_pos.trans hx.1,
          hx.2⟩))
    apply hiTail.congr
    filter_upwards with x
    dsimp only [H]
    rw [intervalIntegral.integral_of_le hN]
  have hHlow : IntervalIntegrable H volume 0
      ccmFirstClockReflectionRatio := by
    rw [intervalIntegrable_iff,
      uIoc_of_le ccmFirstClockReflectionRatio_pos.le]
    have hi := hprod.integral_prod_right
    have hiLow := hi.mono_measure
      (Measure.restrict_mono_set volume (show
        Ioc (0 : ℝ) ccmFirstClockReflectionRatio ⊆
          Ioc (0 : ℝ) 1 by
        intro x (hx : x ∈ Ioc (0 : ℝ)
          ccmFirstClockReflectionRatio)
        exact ⟨hx.1,
          hx.2.trans ccmFirstClockReflectionRatio_lt_one.le⟩))
    apply hiLow.congr
    filter_upwards with x
    dsimp only [H]
    rw [intervalIntegral.integral_of_le hN]
  have hEseed0 : 0 ≤ Eseed := by
    dsimp only [Eseed]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun u =>
        ccmXiScrewWeightedNorm_nonneg _ u)
  have hAN0 : 0 ≤ AN := by
    dsimp only [AN]
    exact intervalIntegral.integral_nonneg
      (show (0 : ℝ) ≤ N by
        exact (by positivity : 0 < Real.pi / 2).le.trans hN)
      (fun u hu => ccmXiScrewWeightedNorm_nonneg a u)
  have hlowRight : IntervalIntegrable
      (fun x : ℝ =>
        (‖ccmFirstClockDilationKernel x‖ / x) * Eseed)
      volume 0 ccmFirstClockReflectionRatio :=
    intervalIntegrable_ccmFirstClockMellinKernel_low.mul_const Eseed
  have htailRight : IntervalIntegrable
      (fun x : ℝ =>
        (‖ccmFirstClockDilationKernel x‖ / x) * AN)
      volume ccmFirstClockReflectionRatio 1 :=
    intervalIntegrable_ccmFirstClockMellinKernel_tail.mul_const AN
  have hlow :
      (∫ x : ℝ in (0 : ℝ)..ccmFirstClockReflectionRatio,
        H x) ≤
      (64 * ccmFirstClockReflectionRatio) * Eseed := by
    calc
      (∫ x : ℝ in (0 : ℝ)..ccmFirstClockReflectionRatio,
        H x) ≤
          ∫ x : ℝ in (0 : ℝ)..ccmFirstClockReflectionRatio,
            (‖ccmFirstClockDilationKernel x‖ / x) * Eseed := by
        apply intervalIntegral.integral_mono_on
        · exact ccmFirstClockReflectionRatio_pos.le
        · exact hHlow
        · exact hlowRight
        · intro x hx
          have hx' : x ∈ Icc (0 : ℝ)
              ccmFirstClockReflectionRatio := by
            simpa [uIcc_of_le
              ccmFirstClockReflectionRatio_pos.le] using hx
          by_cases hzero : x = 0
          · subst x
            dsimp only [H]
            simp [ccmFirstClockDilationKernel]
          · exact weightedDilation_inner_low_le ha
              (lt_of_le_of_ne hx'.1 (Ne.symm hzero))
              hx'.2 hN hseed
      _ = (∫ x : ℝ in (0 : ℝ)..ccmFirstClockReflectionRatio,
          ‖ccmFirstClockDilationKernel x‖ / x) * Eseed := by
        rw [intervalIntegral.integral_mul_const]
      _ ≤ (64 * ccmFirstClockReflectionRatio) * Eseed :=
        mul_le_mul_of_nonneg_right
          integral_ccmFirstClockMellinKernel_low_le hEseed0
  have htail :
      (∫ x : ℝ in ccmFirstClockReflectionRatio..1, H x) ≤
      (∫ x : ℝ in ccmFirstClockReflectionRatio..1,
        ‖ccmFirstClockDilationKernel x‖ / x) * AN := by
    calc
      (∫ x : ℝ in ccmFirstClockReflectionRatio..1, H x) ≤
          ∫ x : ℝ in ccmFirstClockReflectionRatio..1,
            (‖ccmFirstClockDilationKernel x‖ / x) * AN := by
        apply intervalIntegral.integral_mono_on
        · exact ccmFirstClockReflectionRatio_lt_one.le
        · exact hHint
        · exact htailRight
        · intro x hx
          have hx' : x ∈ Icc ccmFirstClockReflectionRatio 1 := by
            simpa [uIcc_of_le
              ccmFirstClockReflectionRatio_lt_one.le] using hx
          exact weightedDilation_inner_tail_le
            ha hx'.1 hx'.2 hN
      _ = _ := by rw [intervalIntegral.integral_mul_const]
  rw [integral_integral_weightedDilation_swap ha hN]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    hHlow hHint]
  dsimp only [Eseed, AN] at hlow htail ⊢
  linarith

private theorem truncated_ccmXiScrewWeightedNorm_uniform
    {a : ℝ} (ha : 0 < a)
    (hseed : IntegrableOn
      (ccmXiScrewWeightedNorm
        (a / ccmFirstClockReflectionRatio)) (Ioi 0))
    (hQ : IntegrableOn
      (ccmFirstClockXiWeightedNorm a) (Ioi 0)) :
    ∃ C : ℝ, ∀ N : ℝ, Real.pi / 2 ≤ N →
      (∫ L : ℝ in (0 : ℝ)..N,
        ccmXiScrewWeightedNorm a L) ≤ C := by
  let H0 : ℝ :=
    ∫ L : ℝ in (0 : ℝ)..Real.pi / 2,
      ccmXiScrewWeightedNorm a L
  let EQ : ℝ :=
    ∫ L : ℝ in Ioi 0,
      ccmFirstClockXiWeightedNorm a L
  let Eseed : ℝ :=
    ∫ L : ℝ in Ioi 0,
      ccmXiScrewWeightedNorm
        (a / ccmFirstClockReflectionRatio) L
  let kappa : ℝ :=
    ∫ x : ℝ in ccmFirstClockReflectionRatio..1,
      ‖ccmFirstClockDilationKernel x‖ / x
  let C0 : ℝ :=
    H0 + EQ +
      (64 * ccmFirstClockReflectionRatio) * Eseed
  have hH00 : 0 ≤ H0 := by
    dsimp only [H0]
    exact intervalIntegral.integral_nonneg
      (by positivity : (0 : ℝ) ≤ Real.pi / 2)
      (fun L hL => ccmXiScrewWeightedNorm_nonneg a L)
  have hEQ0 : 0 ≤ EQ := by
    dsimp only [EQ]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun L =>
        ccmFirstClockXiWeightedNorm_nonneg a L)
  have hEseed0 : 0 ≤ Eseed := by
    dsimp only [Eseed]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun L =>
        ccmXiScrewWeightedNorm_nonneg _ L)
  have hkappa0 : 0 ≤ kappa := by
    dsimp only [kappa]
    exact intervalIntegral.integral_nonneg
      ccmFirstClockReflectionRatio_lt_one.le
      (fun x hx => div_nonneg (norm_nonneg _)
        (ccmFirstClockReflectionRatio_pos.trans_le hx.1).le)
  have hkappa1 : kappa < 1 := by
    exact integral_ccmFirstClockMellinKernel_tail_lt_one
  have hC00 : 0 ≤ C0 := by
    dsimp only [C0]
    exact add_nonneg (add_nonneg hH00 hEQ0)
      (mul_nonneg
        (mul_nonneg (by norm_num)
          ccmFirstClockReflectionRatio_pos.le)
        hEseed0)
  refine ⟨C0 / (1 - kappa), ?_⟩
  intro N hN
  have hN0 : 0 ≤ N :=
    (by positivity : 0 < Real.pi / 2).le.trans hN
  have hSint :=
    intervalIntegrable_ccmXiScrewWeightedNorm_Icc ha hN0
  have hShead :=
    intervalIntegrable_ccmXiScrewWeightedNorm_Icc ha
      (by positivity : (0 : ℝ) ≤ Real.pi / 2)
  have hStail : IntervalIntegrable
      (ccmXiScrewWeightedNorm a) volume (Real.pi / 2) N :=
    (intervalIntegrable_iff.mpr
      ((intervalIntegrable_iff.mp hSint).mono_set (by
        intro L hL
        have hL' : L ∈ Ioc (Real.pi / 2) N := by
          simpa [uIoc_of_le hN] using hL
        have : L ∈ Ioc (0 : ℝ) N :=
          ⟨lt_trans (by positivity : 0 < Real.pi / 2) hL'.1,
            hL'.2⟩
        simpa [uIoc_of_le hN0] using this)))
  have hQint : IntervalIntegrable
      (ccmFirstClockXiWeightedNorm a) volume (Real.pi / 2) N := by
    rw [intervalIntegrable_iff, uIoc_of_le hN]
    exact hQ.mono_set (by
      intro L hL
      exact lt_trans (by positivity : 0 < Real.pi / 2) hL.1)
  have hprod :=
    integrable_weightedDilation_rectangle ha hN
  let D : ℝ → ℝ := fun L =>
    ∫ x : ℝ in (0 : ℝ)..1,
      Real.exp (-a * L) *
        ‖ccmFirstClockDilationKernel x‖ *
          ‖xiScrewDivisor (L * x)‖
  have hDint : IntervalIntegrable D volume (Real.pi / 2) N := by
    rw [intervalIntegrable_iff, uIoc_of_le hN]
    have hi := hprod.integral_prod_left
    apply hi.congr
    filter_upwards with L
    dsimp only [D]
    rw [intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ 1 by norm_num)]
  have hpoint : ∀ L ∈ Icc (Real.pi / 2) N,
      ccmXiScrewWeightedNorm a L ≤
        ccmFirstClockXiWeightedNorm a L + D L := by
    intro L hL
    have hs :=
      norm_screw_le_firstClock_add_dilationNorm hL.1
    unfold ccmXiScrewWeightedNorm ccmFirstClockXiWeightedNorm
    dsimp only [D]
    have hexp0 : 0 ≤ Real.exp (-a * L) := (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_left hs hexp0
    calc
      Real.exp (-a * L) * ‖xiScrewDivisor L‖ ≤
        Real.exp (-a * L) *
          (‖ccmFirstClockXiRationalDivisor L‖ +
            ∫ x : ℝ in (0 : ℝ)..1,
              ‖ccmFirstClockDilationKernel x‖ *
                ‖xiScrewDivisor (L * x)‖) := hmul
      _ = Real.exp (-a * L) *
          ‖ccmFirstClockXiRationalDivisor L‖ +
        ∫ x : ℝ in (0 : ℝ)..1,
          Real.exp (-a * L) *
            ‖ccmFirstClockDilationKernel x‖ *
              ‖xiScrewDivisor (L * x)‖ := by
        rw [mul_add]
        apply congrArg (fun y : ℝ =>
          Real.exp (-a * L) *
            ‖ccmFirstClockXiRationalDivisor L‖ + y)
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x hx
        ring
  have htail :
      (∫ L : ℝ in Real.pi / 2..N,
        ccmXiScrewWeightedNorm a L) ≤
      (∫ L : ℝ in Real.pi / 2..N,
        ccmFirstClockXiWeightedNorm a L) +
      ∫ L : ℝ in Real.pi / 2..N, D L := by
    rw [← intervalIntegral.integral_add hQint hDint]
    apply intervalIntegral.integral_mono_on
    · exact hN
    · exact hStail
    · exact hQint.add hDint
    · intro L hL
      exact hpoint L (by simpa [uIcc_of_le hN] using hL)
  have hQtail :
      (∫ L : ℝ in Real.pi / 2..N,
        ccmFirstClockXiWeightedNorm a L) ≤ EQ := by
    rw [intervalIntegral.integral_of_le hN]
    dsimp only [EQ]
    apply MeasureTheory.integral_mono_measure
      (Measure.restrict_mono_set volume (by
        intro L hL
        exact lt_trans (by positivity : 0 < Real.pi / 2) hL.1))
    · filter_upwards with L
      exact ccmFirstClockXiWeightedNorm_nonneg a L
    · exact hQ
  have hD :=
    integral_weightedDilation_le_low_add_tail ha hN hseed
  have hsplit :
      (∫ L : ℝ in (0 : ℝ)..N,
        ccmXiScrewWeightedNorm a L) =
      H0 + ∫ L : ℝ in Real.pi / 2..N,
        ccmXiScrewWeightedNorm a L := by
    dsimp only [H0]
    exact (intervalIntegral.integral_add_adjacent_intervals
      hShead hStail).symm
  let AN : ℝ :=
    ∫ L : ℝ in (0 : ℝ)..N,
      ccmXiScrewWeightedNorm a L
  have hAN0 : 0 ≤ AN := by
    dsimp only [AN]
    exact intervalIntegral.integral_nonneg hN0
      (fun L hL => ccmXiScrewWeightedNorm_nonneg a L)
  have hineq : AN ≤ C0 + kappa * AN := by
    have hD' :
        (∫ L : ℝ in Real.pi / 2..N, D L) ≤
          (64 * ccmFirstClockReflectionRatio) * Eseed +
            kappa * AN := by
      simpa only [D, Eseed, kappa, AN] using hD
    calc
      AN = H0 + ∫ L : ℝ in Real.pi / 2..N,
          ccmXiScrewWeightedNorm a L := hsplit
      _ ≤ H0 +
          ((∫ L : ℝ in Real.pi / 2..N,
            ccmFirstClockXiWeightedNorm a L) +
              ∫ L : ℝ in Real.pi / 2..N, D L) :=
        (by
          simpa only [add_comm] using
            (add_le_add_left htail H0))
      _ ≤ H0 + (EQ + ∫ L : ℝ in Real.pi / 2..N, D L) := by
        gcongr
      _ ≤ H0 + (EQ +
          ((64 * ccmFirstClockReflectionRatio) * Eseed +
            kappa * AN)) := by
        gcongr
      _ = C0 + kappa * AN := by
        dsimp only [C0]
        ring
  have hden : 0 < 1 - kappa := sub_pos.mpr hkappa1
  apply (le_div_iff₀ hden).2
  dsimp only [AN] at hineq ⊢
  nlinarith

private theorem intervalIntegrable_ccmXiScrewWeightedNorm_nonneg_interval
    {a A B : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hAB : A ≤ B) :
    IntervalIntegrable (ccmXiScrewWeightedNorm a) volume A B := by
  have hB : 0 ≤ B := hA.trans hAB
  have hAll :=
    intervalIntegrable_ccmXiScrewWeightedNorm_Icc ha hB
  rw [intervalIntegrable_iff, uIoc_of_le hAB]
  have hAll' := intervalIntegrable_iff.mp hAll
  exact hAll'.mono_set (by
    intro L hL
    have hL' : L ∈ Ioc A B := by
      simpa [uIoc_of_le hAB] using hL
    have : L ∈ Ioc (0 : ℝ) B :=
      ⟨lt_of_le_of_lt hA hL'.1, hL'.2⟩
    simpa [uIoc_of_le hB] using this)

private theorem integrableOn_ccmXiScrewWeightedNorm_of_uniform
    {a : ℝ} (ha : 0 < a)
    (huniform : ∃ C : ℝ, ∀ N : ℝ, Real.pi / 2 ≤ N →
      (∫ L : ℝ in (0 : ℝ)..N,
        ccmXiScrewWeightedNorm a L) ≤ C) :
    IntegrableOn (ccmXiScrewWeightedNorm a) (Ioi 0) := by
  obtain ⟨C, hC⟩ := huniform
  let shell : ℕ → Set ℝ := fun n =>
    Ioc (n : ℝ) ((n + 1 : ℕ) : ℝ)
  let mass : ℕ → ℝ := fun n =>
    ∫ L : ℝ in (n : ℝ)..((n + 1 : ℕ) : ℝ),
      ccmXiScrewWeightedNorm a L
  have hlocal (n : ℕ) :
      IntegrableOn (ccmXiScrewWeightedNorm a) (shell n) := by
    dsimp only [shell]
    have hint :=
      intervalIntegrable_ccmXiScrewWeightedNorm_nonneg_interval
        ha (Nat.cast_nonneg n)
        (by norm_num : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    rw [intervalIntegrable_iff,
      uIoc_of_le (by norm_num :
        (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ))] at hint
    exact hint
  have hmass0 (n : ℕ) : 0 ≤ mass n := by
    dsimp only [mass]
    exact intervalIntegral.integral_nonneg
      (by norm_num : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
      (fun L hL => ccmXiScrewWeightedNorm_nonneg a L)
  have hcum : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, mass i) =
        ∫ L : ℝ in (0 : ℝ)..(n : ℝ),
          ccmXiScrewWeightedNorm a L := by
    intro n
    induction n with
    | zero =>
        simp [mass]
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        have hleft :=
          intervalIntegrable_ccmXiScrewWeightedNorm_Icc
            ha (Nat.cast_nonneg n)
        have hright :=
          intervalIntegrable_ccmXiScrewWeightedNorm_nonneg_interval
            ha (Nat.cast_nonneg n)
            (by norm_num :
              (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
        have hadd :=
          intervalIntegral.integral_add_adjacent_intervals
            hleft hright
        dsimp only [mass]
        simpa only [Nat.cast_add, Nat.cast_one] using hadd
  have hsumBound (n : ℕ) :
      (∑ i ∈ Finset.range n, mass i) ≤ C := by
    rw [hcum n]
    let N : ℝ := (n : ℝ) + 2
    have hN0 : 0 ≤ N := by
      dsimp only [N]
      positivity
    have hnN : (n : ℝ) ≤ N := by
      dsimp only [N]
      linarith
    have hbig :=
      intervalIntegrable_ccmXiScrewWeightedNorm_Icc ha hN0
    have hmono :
        (∫ L : ℝ in (0 : ℝ)..(n : ℝ),
          ccmXiScrewWeightedNorm a L) ≤
        ∫ L : ℝ in (0 : ℝ)..N,
          ccmXiScrewWeightedNorm a L := by
      apply intervalIntegral.integral_mono_interval
      · exact le_rfl
      · exact Nat.cast_nonneg n
      · exact hnN
      · filter_upwards with L
        exact ccmXiScrewWeightedNorm_nonneg a L
      · exact hbig
    have hpiN : Real.pi / 2 ≤ N := by
      dsimp only [N]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [Real.pi_le_four]
    exact hmono.trans (hC N hpiN)
  have hmassSummable : Summable mass :=
    summable_of_sum_range_le hmass0 hsumBound
  have hnormMass : Summable (fun n : ℕ =>
      ∫ L : ℝ in shell n,
        ‖ccmXiScrewWeightedNorm a L‖) := by
    apply hmassSummable.congr
    intro n
    dsimp only [shell, mass]
    rw [intervalIntegral.integral_of_le
      (by norm_num :
        (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
    apply integral_congr_ae
    filter_upwards with L
    rw [Real.norm_eq_abs,
      abs_of_nonneg (ccmXiScrewWeightedNorm_nonneg a L)]
  have hunion : (⋃ n : ℕ, shell n) = Ioi (0 : ℝ) := by
    dsimp only [shell]
    have hbase : ∀ n : ℕ, ((0 : ℕ) : ℝ) ≤ (n : ℝ) :=
      fun n => by
        simpa only [Nat.cast_zero] using (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hunbounded :
        ¬ BddAbove (Set.range (fun n : ℕ => (n : ℝ))) := by
      intro hbounded
      obtain ⟨B, hB⟩ := hbounded
      obtain ⟨n, hn⟩ := exists_nat_gt B
      exact (not_le_of_gt hn) (hB ⟨n, rfl⟩)
    have hU := iUnion_Ioc_map_succ_eq_Ioi
      (f := fun n : ℕ => (n : ℝ)) hbase hunbounded
    change (⋃ n : ℕ,
      Ioc (n : ℝ) ((Nat.succ n : ℕ) : ℝ)) =
        Ioi ((0 : ℕ) : ℝ) at hU
    simpa only [Nat.cast_zero, Nat.cast_succ] using hU
  rw [← hunion]
  exact integrableOn_iUnion_of_summable_integral_norm
    hlocal hnormMass

/-- **One-step universal dilation--Volterra reflection.**  A screw moment at
`a / (15/16)` and the first-clock moment at `a` force the screw moment at `a`. -/
theorem integrableOn_exp_mul_xiScrewDivisor_reflect
    {a : ℝ} (ha : 0 < a)
    (hseed : IntegrableOn (fun L : ℝ =>
      Complex.exp (-((a / ccmFirstClockReflectionRatio : ℝ) : ℂ) *
        (L : ℂ)) * xiScrewDivisor L) (Ioi 0))
    (hQ : IntegrableOn (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)) *
        ccmFirstClockXiRationalDivisor L) (Ioi 0)) :
    IntegrableOn (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)) *
        xiScrewDivisor L) (Ioi 0) := by
  have hseedReal :=
    integrableOn_ccmXiScrewWeightedNorm hseed
  have hQReal :=
    integrableOn_ccmFirstClockXiWeightedNorm hQ
  have huniform :=
    truncated_ccmXiScrewWeightedNorm_uniform
      ha hseedReal hQReal
  have hreal :=
    integrableOn_ccmXiScrewWeightedNorm_of_uniform
      ha huniform
  have hmeas : AEStronglyMeasurable (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)) *
        xiScrewDivisor L) (volume.restrict (Ioi 0)) := by
    exact ((by fun_prop : Measurable (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)))).mul
        measurable_xiScrewDivisor).aestronglyMeasurable
  change Integrable (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)) *
        xiScrewDivisor L) (volume.restrict (Ioi 0))
  apply (integrable_norm_iff hmeas).1
  apply hreal.congr
  filter_upwards with L
  exact (norm_exp_mul_xiScrewDivisor_eq_weightedNorm a L).symm

theorem integrableOn_exp_mul_xiScrewDivisor_of_one_half_lt
    {a : ℝ} (ha : 1 / 2 < a) :
    IntegrableOn (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)) *
        xiScrewDivisor L) (Ioi 0) := by
  let M : ℝ :=
    ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  let g : ℝ → ℝ := fun L =>
    M * (Real.exp ((-a + 1 / 2) * L) +
      Real.exp (-a * L))
  have hdecay1 : -a + 1 / 2 < 0 := by linarith
  have hdecay2 : -a < 0 := by linarith
  have hg : IntegrableOn g (Ioi 0) := by
    exact ((integrableOn_exp_mul_Ioi hdecay1 0).add
      (integrableOn_exp_mul_Ioi hdecay2 0)).const_mul M
  apply hg.mono'
  · exact ((by fun_prop : Measurable (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)))).mul
        measurable_xiScrewDivisor).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
    rw [norm_mul, Complex.norm_exp]
    have hexpRe :
        (-(a : ℂ) * (L : ℂ)).re = -a * L := by
      simp [mul_re]
    rw [hexpRe]
    have hscrew := norm_xiScrewDivisor_le L
    rw [abs_of_pos hL] at hscrew
    have hM0 : 0 ≤ M := by
      dsimp only [M]
      exact tsum_nonneg fun _ => by positivity
    calc
      Real.exp (-a * L) * ‖xiScrewDivisor L‖ ≤
        Real.exp (-a * L) *
          ((Real.exp (L / 2) + 1) * M) :=
        mul_le_mul_of_nonneg_left hscrew (Real.exp_pos _).le
      _ = M * (Real.exp ((-a + 1 / 2) * L) +
          Real.exp (-a * L)) := by
        rw [show (-a + 1 / 2) * L =
          -a * L + L / 2 by ring, Real.exp_add]
        ring
      _ = g L := rfl

theorem integrableOn_exp_mul_xiScrewDivisor_mono
    {a b : ℝ} (_hb : 0 < b) (hba : b ≤ a)
    (h : IntegrableOn (fun L : ℝ =>
      Complex.exp (-(b : ℂ) * (L : ℂ)) *
        xiScrewDivisor L) (Ioi 0)) :
    IntegrableOn (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)) *
        xiScrewDivisor L) (Ioi 0) := by
  let P : ℝ → ℂ := fun L =>
    Complex.exp (-((a - b : ℝ) : ℂ) * (L : ℂ))
  let B : ℝ → ℂ := fun L =>
    Complex.exp (-(b : ℂ) * (L : ℂ)) *
      xiScrewDivisor L
  have hPmeas : AEStronglyMeasurable P
      (volume.restrict (Ioi 0)) :=
    (by fun_prop : Measurable P).aestronglyMeasurable
  have hPnorm :
      ∀ᵐ L : ℝ ∂volume.restrict (Ioi 0), ‖P L‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
    dsimp only [P]
    rw [Complex.norm_exp]
    have hre :
        (-((a - b : ℝ) : ℂ) * (L : ℂ)).re =
          -(a - b) * L := by simp [mul_re]
    rw [hre, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sub_nonneg.mpr hba)) hL.le)
  have hPB : IntegrableOn (fun L => P L * B L) (Ioi 0) :=
    h.bdd_mul hPmeas hPnorm
  apply hPB.congr
  filter_upwards with L
  dsimp only [P, B]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Reflection abscissa after `n` Mellin contractions. -/
def ccmFirstClockReflectionThreshold (n : ℕ) : ℝ :=
  ccmFirstClockReflectionRatio ^ n

theorem ccmFirstClockReflectionThreshold_pos (n : ℕ) :
    0 < ccmFirstClockReflectionThreshold n := by
  unfold ccmFirstClockReflectionThreshold
  exact pow_pos ccmFirstClockReflectionRatio_pos n

theorem ccmFirstClockReflectionThreshold_succ_div (n : ℕ) :
    ccmFirstClockReflectionThreshold (n + 1) /
      ccmFirstClockReflectionRatio =
        ccmFirstClockReflectionThreshold n := by
  unfold ccmFirstClockReflectionThreshold
  rw [pow_succ]
  field_simp [ccmFirstClockReflectionRatio_pos.ne']

theorem integrableOn_exp_mul_xiScrewDivisor_reflectionThreshold
    (hsource : CCMFirstClockPublishedSourceNonnegative) :
    ∀ n : ℕ, IntegrableOn (fun L : ℝ =>
      Complex.exp
        (-(ccmFirstClockReflectionThreshold n : ℂ) * (L : ℂ)) *
          xiScrewDivisor L) (Ioi 0) := by
  have hQall := ccmFirstClockXi_all_exponential_moments hsource
  intro n
  induction n with
  | zero =>
      simpa [ccmFirstClockReflectionThreshold] using
        (integrableOn_exp_mul_xiScrewDivisor_of_one_half_lt
          (show (1 / 2 : ℝ) < 1 by norm_num))
  | succ n ih =>
      have ha :=
        ccmFirstClockReflectionThreshold_pos (n + 1)
      have hQ :=
        hQall (ccmFirstClockReflectionThreshold (n + 1)) ha
      have hseed : IntegrableOn (fun L : ℝ =>
          Complex.exp
            (-((ccmFirstClockReflectionThreshold (n + 1) /
              ccmFirstClockReflectionRatio : ℝ) : ℂ) * (L : ℂ)) *
              xiScrewDivisor L) (Ioi 0) := by
        simpa only [ccmFirstClockReflectionThreshold_succ_div n]
          using ih
      exact integrableOn_exp_mul_xiScrewDivisor_reflect
        ha hseed hQ

/-- **Complete CCM Volterra reflection law.** Published-source nonnegativity forces
every positive exponential moment of the literal infinite CCM screw. -/
theorem ccmXiScrew_all_exponential_moments_of_firstClockSource
    (hsource : CCMFirstClockPublishedSourceNonnegative) :
    CCMXiScrewAllExponentialMoments := by
  intro a ha
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      ccmFirstClockReflectionRatio ^ n < a :=
    exists_pow_lt_of_lt_one ha
      ccmFirstClockReflectionRatio_lt_one
  have hthreshold :=
    integrableOn_exp_mul_xiScrewDivisor_reflectionThreshold
      hsource n
  exact integrableOn_exp_mul_xiScrewDivisor_mono
    (ccmFirstClockReflectionThreshold_pos n)
    (by
      unfold ccmFirstClockReflectionThreshold
      exact hn.le)
    hthreshold

/-- Published first-clock nonnegativity implies RH, with no truncation or
auxiliary analytic hypothesis. -/
theorem riemannHypothesis_of_ccmFirstClockPublishedSourceNonnegative
    (hsource : CCMFirstClockPublishedSourceNonnegative) :
    RiemannHypothesis :=
  riemannHypothesis_of_ccmXiScrew_all_exponential_moments
    (ccmXiScrew_all_exponential_moments_of_firstClockSource hsource)

/-- **CCM first-clock completeness theorem.** RH is exactly equivalent to
nonnegativity of the first physical published-source clock at every aperture
`L ≥ π/2`. -/
theorem ccmFirstClockPublishedSourceNonnegative_iff_rh :
    CCMFirstClockPublishedSourceNonnegative ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_ccmFirstClockPublishedSourceNonnegative
  · intro hRH L hL
    exact ccmPublishedSourceSineCoefficient_firstClock_nonneg_of_rh
      hRH hL

end

end RHTower
