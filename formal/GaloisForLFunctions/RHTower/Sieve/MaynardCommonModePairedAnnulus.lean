import GaloisForLFunctions.RHTower.Sieve.MaynardCommonCentralMode
import GaloisForLFunctions.RHTower.Sieve.MaynardPairedKernelBufferedHandoff
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedWidthPrimeGapRungCover

open Complex MeasureTheory Set
open Filter ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

/-!
# Cancellation-preserving common-mode annulus

The common-mode producer historically separated its reference and target high tails.  This file
keeps their difference intact, discards only an absolute far tail, and exposes the resulting
two-sided annulus to the canonical shell machinery.
-/

/-- The common-mode reference and buffered paired-kernel reference are definitionally the same
relative width. -/
theorem routeTCommonModeReferenceRelativeWidth_eq_pairedKernelReferenceRelativeWidth
    (x : ℝ) :
    routeTCommonModeReferenceRelativeWidth x =
      routeTPairedKernelReferenceRelativeWidth x := rfl

/-- Exact canonical normalization: after reparameterizing the source at shell height `T₁`, the
common reference base is one quarter of the height-matched support. -/
theorem routeTCommonModeReferenceRelativeWidth_eq_heightMatchedPairedReference
    {T₀ T₁ : ℝ} (hT₀ : 1 < T₀) (hT₁ : 1 < T₁) :
    routeTCommonModeReferenceRelativeWidth (routeTPrimeGapPacketBase T₀) =
      routeTPairedKernelReferenceRelativeWidth
        (T₁ ^ routeTHeightMatchedExponent T₀ (8 / 5 : ℝ) T₁ / 4) := by
  rw [rpow_routeTHeightMatchedExponent hT₀ hT₁]
  rfl

/-- The logarithmic order-50 tail denominator grows uniformly over every physical base in the
canonical dyadic block.  In particular it eventually absorbs the fixed common-mode density. -/
theorem eventually_routeTCommonMode_tailLogRatio_ge_densityInverse :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T),
        1 / routeTCommonModeReferenceDensity ≤
          1 + Real.log ((1 / 4) / routeTPrimeGapPacketWidth lambda) / Real.log 2 := by
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hpowTop : Tendsto
      (fun T : ℝ => routeTPrimeGapPacketBase T ^ (49 / 80 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 49 / 80)).comp hbaseTop
  have hscaledTop : Tendsto
      (fun T : ℝ => (1 / 4 : ℝ) * routeTPrimeGapPacketBase T ^ (49 / 80 : ℝ))
      atTop atTop := hpowTop.const_mul_atTop (by norm_num)
  have hlogTop : Tendsto
      (fun T : ℝ => Real.log
        ((1 / 4 : ℝ) * routeTPrimeGapPacketBase T ^ (49 / 80 : ℝ)))
      atTop atTop := Real.tendsto_log_atTop.comp hscaledTop
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdivTop : Tendsto
      (fun T : ℝ => Real.log
        ((1 / 4 : ℝ) * routeTPrimeGapPacketBase T ^ (49 / 80 : ℝ)) /
          Real.log 2) atTop atTop := hlogTop.atTop_div_const hlogTwo
  have hthreshold := hdivTop.eventually_ge_atTop
    (1 / routeTCommonModeReferenceDensity - 1)
  filter_upwards [hthreshold, hbaseTop.eventually_ge_atTop 1] with T hq hx1
  intro lambda hlambda
  have hx0 : 0 < routeTPrimeGapPacketBase T := zero_lt_one.trans_le hx1
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hwidth : routeTPrimeGapPacketWidth lambda ≤
      routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) := by
    unfold routeTPrimeGapPacketWidth
    exact Real.rpow_le_rpow_of_nonpos hx0 hlambda.1 (by norm_num)
  have hwidthX0 : 0 < routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) := by
    unfold routeTPrimeGapPacketWidth
    positivity
  have hwidthLambda0 : 0 < routeTPrimeGapPacketWidth lambda := by
    unfold routeTPrimeGapPacketWidth
    positivity
  have hratio : (1 / 4 : ℝ) /
        routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) ≤
      (1 / 4 : ℝ) / routeTPrimeGapPacketWidth lambda := by
    gcongr
  have hlog : Real.log ((1 / 4 : ℝ) /
        routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T)) ≤
      Real.log ((1 / 4 : ℝ) / routeTPrimeGapPacketWidth lambda) := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (div_pos (by norm_num) hwidthX0))
      (Set.mem_Ioi.mpr (div_pos (by norm_num) hwidthLambda0)) hratio
  have hbaseEq :
      (1 / 4 : ℝ) / routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) =
        (1 / 4 : ℝ) * routeTPrimeGapPacketBase T ^ (49 / 80 : ℝ) := by
    unfold routeTPrimeGapPacketWidth
    rw [Real.rpow_neg hx0.le]
    field_simp
  rw [← hbaseEq] at hq
  have hdiv : Real.log ((1 / 4 : ℝ) /
        routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T)) / Real.log 2 ≤
      Real.log ((1 / 4 : ℝ) / routeTPrimeGapPacketWidth lambda) / Real.log 2 := by
    exact div_le_div_of_nonneg_right hlog hlogTwo.le
  linarith

/-- The common central cutoff lies below the canonical natural order-50 cutoff at large height. -/
theorem eventually_routeTCommonModeCutoff_le_primeGapPacketCutoff :
    ∀ᶠ T : ℝ in Filter.atTop,
      routeTCommonModeCutoff (routeTPrimeGapPacketBase T) ≤
        (routeTPrimeGapPacketCutoff T : ℝ) := by
  have hdecay :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 5)).const_mul 2
  have hzero : (2 : ℝ) * 0 = 0 := by ring
  rw [hzero] at hdecay
  have hsmall := Filter.Tendsto.eventually_lt hdecay
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1))
      zero_lt_one
  filter_upwards [hsmall, Filter.eventually_ge_atTop (2 : ℝ)] with T hsmallT hT
  have hT0 : 0 < T := by linarith
  have hbaseLe : routeTPrimeGapPacketBase T ≤ T ^ (8 / 5 : ℝ) := by
    unfold routeTPrimeGapPacketBase
    have hp : 0 ≤ T ^ (8 / 5 : ℝ) := Real.rpow_nonneg hT0.le _
    linarith
  have hbase0 : 0 ≤ routeTPrimeGapPacketBase T := by
    unfold routeTPrimeGapPacketBase
    positivity
  have hcutLe : routeTCommonModeCutoff (routeTPrimeGapPacketBase T) ≤
      T ^ (1 / 5 : ℝ) := by
    unfold routeTCommonModeCutoff
    calc
      routeTPrimeGapPacketBase T ^ (1 / 8 : ℝ) ≤
          (T ^ (8 / 5 : ℝ)) ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow hbase0 hbaseLe (by norm_num)
      _ = T ^ (1 / 5 : ℝ) := by
        rw [← Real.rpow_mul hT0.le]
        congr 1
        norm_num
  have hcollapse : T ^ (1 / 5 : ℝ) = T * T ^ (-(4 / 5 : ℝ)) := by
    calc
      T ^ (1 / 5 : ℝ) = T ^ (1 + (-(4 / 5 : ℝ))) := by congr 1 <;> norm_num
      _ = T ^ (1 : ℝ) * T ^ (-(4 / 5 : ℝ)) := Real.rpow_add hT0 1 _
      _ = T * T ^ (-(4 / 5 : ℝ)) := by rw [Real.rpow_one]
  have hhalf : T ^ (1 / 5 : ℝ) ≤ T / 2 := by
    rw [hcollapse]
    have hnonneg : 0 ≤ T ^ (-(4 / 5 : ℝ)) := Real.rpow_nonneg hT0.le _
    nlinarith
  have hfloor : T / 2 ≤ (routeTPrimeGapPacketCutoff T : ℝ) := by
    dsimp only [routeTPrimeGapPacketCutoff]
    have hlt := Nat.lt_floor_add_one T
    linarith
  exact hcutLe.trans (hhalf.trans hfloor)

/-- The canonical order-50 cutoff discards the far tail of the *paired* common-mode kernel,
uniformly in the physical base and receiver-compatible Möbius cutoff. -/
theorem eventually_routeT_commonMode_pairedFarTail_le :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ L : ℕ, 1 ≤ L → L ≤ routeTPrimeGapPacketSupport T →
      ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T),
        (∫ y in {y : ℝ | (routeTPrimeGapPacketCutoff T : ℝ) ≤ |y|},
          ‖heathBrownWindowRelevantEligibleDyadicAggregate
                L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                  (routeTPrimeGapPacketBase T)
                ((1 : ℂ) + (y : ℝ) * Complex.I) *
            (routeTNormalizedSmoothWindowMellin lambda
                (lambda * routeTCommonModeReferenceRelativeWidth
                  (routeTPrimeGapPacketBase T))
                ((1 : ℂ) + (y : ℝ) * Complex.I) -
              routeTNormalizedSmoothWindowMellin lambda
                (lambda * routeTPrimeGapPacketWidth lambda)
                ((1 : ℂ) + (y : ℝ) * Complex.I))‖) ≤
          ((2 * Real.pi) *
            (routeTSmoothWindowCentralMargin *
              routeTCommonModeReferenceDensity / 2)) / 4 := by
  obtain ⟨C, hC, htail⟩ :=
    exists_integral_norm_fixedSource_mul_noncomparablePairedKernel_natOrder_tail_le
      50 (by norm_num)
  have hscalar :=
    eventually_routeTPrimeGapPacket_orderFifty_scalar_cutoff_leftCutoff
      (2 * C) (by positivity)
  have hlog := eventually_routeTCommonMode_tailLogRatio_ge_densityInverse
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hrefSmall := hbaseTop.eventually
    eventually_routeTCommonModeReferenceRelativeWidth_le_one_fourth
  filter_upwards [hscalar, hlog, hrefSmall, hbaseTop.eventually_ge_atTop 16,
      Filter.eventually_ge_atTop (2 : ℝ)] with
      T hscalarT hlogT hrefSmallT hx16 hT
  intro L hL hLX lambda hlambda
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let K : ℕ := routeTPrimeGapPacketCutoff T
  let H : ℝ := routeTPrimeGapPacketWidth lambda
  let R : ℝ := routeTCommonModeReferenceRelativeWidth x
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X 60 x 1
  let Q : ℝ := 1 + Real.log ((1 / 4) / H) / Real.log 2
  have hx0 : 0 < x := by dsimp only [x]; linarith
  have hx1 : 1 ≤ x := by dsimp only [x]; linarith
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hlambda1 : 1 ≤ lambda := hx1.trans hlambda.1
  have hH0 : 0 < H := by dsimp only [H, routeTPrimeGapPacketWidth]; positivity
  have hR0 : 0 < R := by
    dsimp only [R]
    exact routeTCommonModeReferenceRelativeWidth_pos hx0
  have hHR : H ≤ R := by
    dsimp only [H, R]
    exact routeTPrimeGapPacketWidth_le_commonModeReference hx1
      (by simpa only [x] using hlambda)
  have hRone : R ≤ 1 := by
    dsimp only [R, x]
    exact hrefSmallT.trans (by norm_num)
  have hphysicalOrder : lambda * H ≤ lambda * R :=
    mul_le_mul_of_nonneg_left hHR hlambda0.le
  have hphysicalR : lambda * R ≤ lambda := by
    calc
      lambda * R ≤ lambda * 1 := mul_le_mul_of_nonneg_left hRone hlambda0.le
      _ = lambda := by ring
  have hK : 0 < K := by
    dsimp only [K, routeTPrimeGapPacketCutoff]
    exact Nat.floor_pos.mpr (by linarith)
  have htailBound := htail L X 60 T (1 / 75 : ℝ)
    (M := x) (N := lambda) (H := lambda * H) (R := lambda * R) (U := K)
    hX hx0 hlambda1 (mul_pos hlambda0 hH0) (mul_pos hlambda0 hR0)
    hphysicalOrder hphysicalR (by exact_mod_cast hK)
  have htailShape :
      (∫ y in {y : ℝ | (K : ℝ) ≤ |y|},
        ‖heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (1 / 75) x
              ((1 : ℂ) + (y : ℝ) * Complex.I) *
          (routeTNormalizedSmoothWindowMellin lambda (lambda * R)
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin lambda (lambda * H)
              ((1 : ℂ) + (y : ℝ) * Complex.I))‖) ≤
        P * (2 * C * (1 / H) ^ (51 : ℕ) * (K : ℝ) ^ (-(50 : ℝ))) := by
    have hratioEq : lambda / (lambda * H) = 1 / H := by
      field_simp [hlambda0.ne']
    norm_num at htailBound ⊢
    simpa only [P, hratioEq, one_div, inv_pow] using htailBound
  have hscalarBound :
      P * (2 * C * (1 / H) ^ (51 : ℕ) * (K : ℝ) ^ (-(50 : ℝ))) ≤
        ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / (2 * Q) := by
    simpa only [P, X, x, H, K, Q] using
      hscalarT L hL (by simpa only [X] using hLX) lambda
        (by simpa only [x] using hlambda)
  have hrho : 0 < routeTCommonModeReferenceDensity :=
    routeTCommonModeReferenceDensity_pos
  have hQlower : 1 / routeTCommonModeReferenceDensity ≤ Q := by
    simpa only [H, Q, x] using hlogT lambda (by simpa only [x] using hlambda)
  have hQ0 : 0 < Q := (div_pos zero_lt_one hrho).trans_le hQlower
  have hrhoQ : 1 ≤ routeTCommonModeReferenceDensity * Q := by
    have hmul := mul_le_mul_of_nonneg_left hQlower hrho.le
    field_simp [hrho.ne'] at hmul
    exact hmul
  have hinvQ : 1 / Q ≤ routeTCommonModeReferenceDensity := by
    exact (div_le_iff₀ hQ0).2 (by simpa only [one_mul] using hrhoQ)
  have hmargin : 0 ≤ (2 * Real.pi) * routeTSmoothWindowCentralMargin / 8 := by
    positivity [routeTSmoothWindowCentralMargin_pos]
  have hfinal :
      ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / (2 * Q) ≤
        ((2 * Real.pi) *
          (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 4 := by
    calc
      ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / (2 * Q) =
          ((2 * Real.pi) * routeTSmoothWindowCentralMargin / 8) * (1 / Q) := by
            field_simp [hQ0.ne']
            ring
      _ ≤ ((2 * Real.pi) * routeTSmoothWindowCentralMargin / 8) *
          routeTCommonModeReferenceDensity :=
        mul_le_mul_of_nonneg_left hinvQ hmargin
      _ = ((2 * Real.pi) *
          (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 4 := by
        ring
  exact htailShape.trans (hscalarBound.trans hfinal)

/-- If a paired outer tail is large and its absolute far tail is small, the intervening annulus
retains their difference.  No endpoint pigeonhole is used. -/
theorem norm_setIntegral_annulus_ge_of_outerTail
    {f : ℝ → ℂ} (hf : Integrable f) {B U V E : ℝ}
    (hUV : U ≤ V)
    (houter : B ≤ ‖∫ y in {y : ℝ | U ≤ |y|}, f y‖)
    (htail : (∫ y in {y : ℝ | V ≤ |y|}, ‖f y‖) ≤ E) :
    B - E ≤ ‖∫ y in {y : ℝ | U ≤ |y| ∧ |y| < V}, f y‖ := by
  let TU : Set ℝ := {y : ℝ | U ≤ |y|}
  let TV : Set ℝ := {y : ℝ | V ≤ |y|}
  let M : Set ℝ := {y : ℝ | U ≤ |y| ∧ |y| < V}
  have hTVmeas : MeasurableSet TV :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hMunion : M ∪ TV = TU := by
    ext y
    simp only [M, TV, TU, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (hy | hy)
      · exact hy.1
      · exact hUV.trans hy
    · intro hy
      by_cases hyv : |y| < V
      · exact Or.inl ⟨hy, hyv⟩
      · exact Or.inr (not_lt.mp hyv)
  have hdisj : Disjoint M TV := by
    rw [Set.disjoint_left]
    intro y hyM hyTV
    exact (not_lt_of_ge hyTV) hyM.2
  have htailNorm : ‖∫ y in TV, f y‖ ≤ E := by
    calc
      ‖∫ y in TV, f y‖ ≤ ∫ y in TV, ‖f y‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ E := by simpa only [TV] using htail
  have hsplit : (∫ y in TU, f y) = (∫ y in M, f y) + ∫ y in TV, f y := by
    rw [← hMunion]
    exact MeasureTheory.setIntegral_union hdisj hTVmeas hf.integrableOn hf.integrableOn
  have hbound : B ≤ ‖∫ y in M, f y‖ + E := by
    calc
      B ≤ ‖∫ y in TU, f y‖ := by simpa only [TU] using houter
      _ = ‖(∫ y in M, f y) + ∫ y in TV, f y‖ := by rw [hsplit]
      _ ≤ ‖∫ y in M, f y‖ + ‖∫ y in TV, f y‖ := norm_add_le _ _
      _ ≤ ‖∫ y in M, f y‖ + E := add_le_add_right htailNorm _
  dsimp only [M] at hbound ⊢
  linarith

/-- A large paired common-mode high tail localizes to a finite two-sided annulus after only the
absolute far-tail error is paid. -/
theorem commonMode_pairedHighTailDifference_localizes_annulus
    (a : ℝ → ℂ) {N H R B U V E : ℝ}
    (hintR : Integrable (fun y : ℝ =>
      a y * routeTNormalizedSmoothWindowMellin N R
        ((1 : ℂ) + (y : ℝ) * Complex.I)))
    (hintH : Integrable (fun y : ℝ =>
      a y * routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + (y : ℝ) * Complex.I)))
    (hU : 0 ≤ U) (hUV : U ≤ V)
    (hlarge : B ≤ ‖maynardWidthHighTail a N R U -
      maynardWidthHighTail a N H U‖)
    (htail : (∫ y in {y : ℝ | V ≤ |y|},
      ‖a y *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * Complex.I))‖) ≤ E) :
    B - E ≤ ‖∫ y in {y : ℝ | U ≤ |y| ∧ |y| < V},
      a y *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * Complex.I))‖ := by
  let f : ℝ → ℂ := fun y =>
    a y *
      (routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * Complex.I))
  have hf : Integrable f := by
    have hsub := hintR.sub hintH
    refine hsub.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp only [f, Pi.sub_apply]
    ring
  have houter : B ≤ ‖∫ y in {y : ℝ | U ≤ |y|}, f y‖ := by
    rw [← maynardWidthHighTail_sub_eq_setIntegral a hintR hintH hU]
    exact hlarge
  exact norm_setIntegral_annulus_ge_of_outerTail hf hUV houter
    (by simpa only [f] using htail)

/-- Conjugate symmetry turns a nonzero two-sided annular defect into a positive-ordinate
interval defect. Taking the transition point at the outer endpoint keeps the paired kernel
intact and rules out the degenerate outer interval using positivity. -/
theorem norm_intervalIntegral_positiveWing_ge_quarter_of_annulus_of_conj
    {f : ℝ → ℂ} (hf : Integrable f)
    (hconj : ∀ y : ℝ, f (-y) = (starRingEnd ℂ) (f y))
    {B U V : ℝ} (hB0 : 0 < B) (hU : 0 ≤ U) (hUV : U ≤ V)
    (hB : B ≤ ‖∫ y in {y : ℝ | U ≤ |y| ∧ |y| < V}, f y‖) :
    B / 4 ≤ ‖∫ y in U..V, f y‖ := by
  rcases exists_positive_interval_norm_ge_quarter_of_annulus_of_conj
      hf hconj hU hUV le_rfl hB with h | h
  · exact h
  · have hz : B / 4 ≤ 0 := by simpa using h
    linarith

/-- A nonzero fixed-source paired annulus contains a height-matched positive dyadic shell.
The source base `M` remains frozen while the physical kernel base `N` varies independently;
reference-target cancellation is preserved until after shell selection. -/
theorem exists_fixedSource_reparametrized_pairedShell_of_annulus
    (L X k : ℕ) {T mu M N H R B U V : ℝ}
    (hT : 1 < T) (hX : 1 ≤ X) (hM : 0 < M)
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hB0 : 0 < B) (hU : 1 < U) (hUV : U ≤ V)
    (hB : B ≤ ‖∫ y in {y : ℝ | U ≤ |y| ∧ |y| < V},
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T (mu / 120) M
            ((1 : ℂ) + (y : ℝ) * Complex.I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * Complex.I))‖) :
    ∃ J : ℕ, 0 < J ∧
      (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ V / U ∧
      V / U < (((2 ^ J : ℕ) : ℝ)) ∧
      ∃ j ∈ Finset.range J,
        let T₁ := routeTComparableWidthLadder U V (j + 1)
        let mu₁ := routeTHeightMatchedExponent T mu T₁
        T₁ ∈ Set.Icc U V ∧
        routeTComparableWidthLadder U V j ≤ 2 * T₁ ∧
        T₁ ^ mu₁ = T ^ mu ∧
        (B / 4) / (J : ℝ) ≤ ‖routeTFixedSourceAdjacentIntervalPacket
          L X k T₁ (mu₁ / 120) M N R H 1 T₁
            (routeTComparableWidthLadder U V j)‖ := by
  let a : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T (mu / 120) M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let f : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T (mu / 120) M
      ((1 : ℂ) + (y : ℝ) * Complex.I) *
      (routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * Complex.I))
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k M 1
  have haBound : ∀ y : ℝ, ‖a y‖ ≤ P := by
    intro y
    dsimp only [a, P]
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T (mu / 120) M 1 y hM (by norm_num)
  have ha : Continuous a := by
    dsimp only [a]
    exact continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T (mu / 120) M 1
  have hkR := integrable_routeTNormalizedSmoothWindowMellin_one hN hR
  have hkH := integrable_routeTNormalizedSmoothWindowMellin_one hN hH
  have hintR : Integrable (fun y : ℝ =>
      a y * routeTNormalizedSmoothWindowMellin N R
        ((1 : ℂ) + (y : ℝ) * Complex.I)) := by
    exact hkR.bdd_mul ha.aestronglyMeasurable
      (Filter.Eventually.of_forall haBound)
  have hintH : Integrable (fun y : ℝ =>
      a y * routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + (y : ℝ) * Complex.I)) := by
    exact hkH.bdd_mul ha.aestronglyMeasurable
      (Filter.Eventually.of_forall haBound)
  have hf : Integrable f := by
    have hsub := hintR.sub hintH
    refine hsub.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp only [f, a, Pi.sub_apply]
    ring
  have hconj : ∀ y : ℝ, f (-y) = (starRingEnd ℂ) (f y) := by
    intro y
    dsimp only [f]
    exact (conj_fixedSource_mul_adjacentKernel
      L X k T (mu / 120) M N H R y).symm
  have hpositive : B / 4 ≤ ‖∫ y in U..V, f y‖ :=
    norm_intervalIntegral_positiveWing_ge_quarter_of_annulus_of_conj
      hf hconj hB0 (by linarith) hUV (by simpa only [f] using hB)
  exact exists_fixedSource_reparametrized_comparable_ordinate_shell_integral_norm_ge
    L X k hT hN hH hR (by norm_num) hU hUV (by
      convert hpositive using 1 <;>
        norm_num [f, routeTFixedSourceAdjacentIntervalPacket,
          routeTFixedSourceAdjacentIntegrand])

/-- Canonical-count form of paired annulus shell extraction.  The selected shell now belongs to
one finite ladder fixed solely by the two annulus endpoints, before any physical base is chosen. -/
theorem exists_fixedSource_reparametrized_pairedShell_of_annulus_canonicalCount
    (L X k : ℕ) {T mu M N H R B U V : ℝ}
    (hT : 1 < T) (hX : 1 ≤ X) (hM : 0 < M)
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hB0 : 0 < B) (hU : 1 < U) (hUV : U ≤ V)
    (hB : B ≤ ‖∫ y in {y : ℝ | U ≤ |y| ∧ |y| < V},
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T (mu / 120) M
            ((1 : ℂ) + (y : ℝ) * Complex.I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * Complex.I))‖) :
    ∃ j ∈ Finset.range (routeTOrdinateShellCount U V),
      let T₁ := routeTComparableWidthLadder U V (j + 1)
      let mu₁ := routeTHeightMatchedExponent T mu T₁
      T₁ ∈ Set.Icc U V ∧
      routeTComparableWidthLadder U V j ≤ 2 * T₁ ∧
      T₁ ^ mu₁ = T ^ mu ∧
      (B / 4) / (routeTOrdinateShellCount U V : ℝ) ≤
        ‖routeTFixedSourceAdjacentIntervalPacket
          L X k T₁ (mu₁ / 120) M N R H 1 T₁
            (routeTComparableWidthLadder U V j)‖ := by
  obtain ⟨J, hJ, hbelow, _habove, j, hj, hmem, hcomp, hmatch, hlarge⟩ :=
    exists_fixedSource_reparametrized_pairedShell_of_annulus
      L X k hT hX hM hN hH hR hB0 hU hUV hB
  have hJle : J ≤ routeTOrdinateShellCount U V :=
    routeTComparableWidthLadder_index_le_ordinateShellCount
      (by linarith) hUV hJ hbelow
  have hjCanonical : j ∈ Finset.range (routeTOrdinateShellCount U V) := by
    rw [Finset.mem_range] at hj ⊢
    exact hj.trans_le hJle
  have hdenom : (B / 4) / (routeTOrdinateShellCount U V : ℝ) ≤
      (B / 4) / (J : ℝ) := by
    apply div_le_div_of_nonneg_left
    · positivity
    · exact_mod_cast hJ
    · exact_mod_cast hJle
  refine ⟨j, hjCanonical, hmem, hcomp, hmatch, ?_⟩
  exact hdenom.trans hlarge

/-- **Canonical cancellation-preserving prime-free annulus.**  Eventually one frozen Heath--Brown
source works for every physical base in the block.  Prime-freeness forces a fixed positive paired
defect on the literal annulus between the common central cutoff and `floor T`; reference-target
cancellation is retained pointwise throughout. -/
theorem exists_eventually_routeT_primeFree_fixedSource_commonMode_pairedAnnulus :
    ∀ᶠ T : ℝ in atTop,
      ∃ L : ℕ, 1 ≤ L ∧
        L ≤ routeTPrimeGapPacketSupport T ∧
        routeTPrimeGapPacketSupport T < (L + 1) ^ (60 : ℕ) ∧
        (L : ℝ) ≤ T ^ (2 / 75 : ℝ) ∧
        ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
            (2 * routeTPrimeGapPacketBase T),
          Chebyshev.theta
                (lambda + 2 * (lambda * routeTPrimeGapPacketWidth lambda)) -
              Chebyshev.theta lambda = 0 →
          ((2 * Real.pi) *
              (routeTSmoothWindowCentralMargin *
                routeTCommonModeReferenceDensity / 2)) / 4 ≤
            ‖∫ y in {y : ℝ |
                routeTCommonModeCutoff (routeTPrimeGapPacketBase T) ≤ |y| ∧
                  |y| < (routeTPrimeGapPacketCutoff T : ℝ)},
              heathBrownWindowRelevantEligibleDyadicAggregate
                    L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                      (routeTPrimeGapPacketBase T)
                    ((1 : ℂ) + (y : ℝ) * Complex.I) *
                (routeTNormalizedSmoothWindowMellin lambda
                    (lambda * routeTCommonModeReferenceRelativeWidth
                      (routeTPrimeGapPacketBase T))
                    ((1 : ℂ) + (y : ℝ) * Complex.I) -
                  routeTNormalizedSmoothWindowMellin lambda
                    (lambda * routeTPrimeGapPacketWidth lambda)
                    ((1 : ℂ) + (y : ℝ) * Complex.I))‖ := by
  have hpaired := exists_eventually_routeT_primeFree_fixedSource_commonMode_pairedHighTail
  have hfar := eventually_routeT_commonMode_pairedFarTail_le
  have hcut := eventually_routeTCommonModeCutoff_le_primeGapPacketCutoff
  filter_upwards [hpaired, hfar, hcut, Filter.eventually_ge_atTop (2 : ℝ)] with
      T hpairedT hfarT hcutT hT
  obtain ⟨L, hL, hLX, hXL, hLscale, hlarge⟩ := hpairedT
  refine ⟨L, hL, hLX, hXL, hLscale, ?_⟩
  intro lambda hlambda hprimeFree
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let R : ℝ := routeTCommonModeReferenceRelativeWidth x
  let H : ℝ := routeTPrimeGapPacketWidth lambda
  let U : ℝ := routeTCommonModeCutoff x
  let V : ℝ := routeTPrimeGapPacketCutoff T
  let a : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (1 / 75) x
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X 60 x 1
  have hx0 : 0 < x := by
    dsimp only [x, routeTPrimeGapPacketBase]
    have hT0 : 0 < T := by linarith
    positivity
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hR0 : 0 < R := by
    dsimp only [R]
    exact routeTCommonModeReferenceRelativeWidth_pos hx0
  have hH0 : 0 < H := by dsimp only [H, routeTPrimeGapPacketWidth]; positivity
  have haBound : ∀ y : ℝ, ‖a y‖ ≤ P := by
    intro y
    dsimp only [a, P]
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X 60 hX T (1 / 75) x 1 y hx0 (by norm_num)
  have ha : Continuous a := by
    dsimp only [a]
    exact continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X 60 T (1 / 75) x 1
  have hkR := integrable_routeTNormalizedSmoothWindowMellin_one
    hlambda0 (mul_pos hlambda0 hR0)
  have hkH := integrable_routeTNormalizedSmoothWindowMellin_one
    hlambda0 (mul_pos hlambda0 hH0)
  have hintR : Integrable (fun y : ℝ =>
      a y * routeTNormalizedSmoothWindowMellin lambda (lambda * R)
        ((1 : ℂ) + (y : ℝ) * Complex.I)) := by
    exact hkR.bdd_mul ha.aestronglyMeasurable
      (Filter.Eventually.of_forall haBound)
  have hintH : Integrable (fun y : ℝ =>
      a y * routeTNormalizedSmoothWindowMellin lambda (lambda * H)
        ((1 : ℂ) + (y : ℝ) * Complex.I)) := by
    exact hkH.bdd_mul ha.aestronglyMeasurable
      (Filter.Eventually.of_forall haBound)
  have hlarge' :
      ((2 * Real.pi) *
          (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 2 ≤
        ‖maynardWidthHighTail a lambda (lambda * R) U -
          maynardWidthHighTail a lambda (lambda * H) U‖ := by
    simpa only [a, x, X, R, H, U] using hlarge lambda
      (by simpa only [x] using hlambda) hprimeFree
  have htail' :
      (∫ y in {y : ℝ | V ≤ |y|},
        ‖a y *
          (routeTNormalizedSmoothWindowMellin lambda (lambda * R)
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin lambda (lambda * H)
              ((1 : ℂ) + (y : ℝ) * Complex.I))‖) ≤
        ((2 * Real.pi) *
          (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 4 := by
    simpa only [a, x, X, R, H, V] using
      hfarT L hL (by simpa only [X] using hLX) lambda
        (by simpa only [x] using hlambda)
  have hU0 : 0 ≤ U := by dsimp only [U, routeTCommonModeCutoff]; positivity
  have hUV : U ≤ V := by simpa only [U, V, x] using hcutT
  have hannulus := commonMode_pairedHighTailDifference_localizes_annulus
    a hintR hintH hU0 hUV hlarge' htail'
  have hconst :
      ((2 * Real.pi) *
          (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 2 -
        ((2 * Real.pi) *
          (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 4 =
      ((2 * Real.pi) *
          (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 4 := by
    ring
  rw [hconst] at hannulus
  simpa only [a, x, X, R, H, U, V] using hannulus

/-- **Prime-free common mode reaches a height-matched positive shell.**  Eventually one frozen
Heath--Brown source works for the full dyadic physical block.  At every prime-free physical base,
the paired reference-target defect survives on one positive dyadic ordinate shell, and the shell
source is reparameterized without changing its support cutoff. -/
theorem exists_eventually_routeT_primeFree_fixedSource_commonMode_pairedShell :
    ∀ᶠ T : ℝ in atTop,
      ∃ L : ℕ, 1 ≤ L ∧
        L ≤ routeTPrimeGapPacketSupport T ∧
        routeTPrimeGapPacketSupport T < (L + 1) ^ (60 : ℕ) ∧
        (L : ℝ) ≤ T ^ (2 / 75 : ℝ) ∧
        ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
            (2 * routeTPrimeGapPacketBase T),
          Chebyshev.theta
                (lambda + 2 * (lambda * routeTPrimeGapPacketWidth lambda)) -
              Chebyshev.theta lambda = 0 →
          ∃ J : ℕ, 0 < J ∧
            (((2 ^ (J - 1) : ℕ) : ℝ)) ≤
              (routeTPrimeGapPacketCutoff T : ℝ) /
                routeTCommonModeCutoff (routeTPrimeGapPacketBase T) ∧
            (routeTPrimeGapPacketCutoff T : ℝ) /
                routeTCommonModeCutoff (routeTPrimeGapPacketBase T) <
              (((2 ^ J : ℕ) : ℝ)) ∧
            ∃ j ∈ Finset.range J,
              let T₁ := routeTComparableWidthLadder
                (routeTCommonModeCutoff (routeTPrimeGapPacketBase T))
                (routeTPrimeGapPacketCutoff T : ℝ) (j + 1)
              let mu₁ := routeTHeightMatchedExponent T (8 / 5 : ℝ) T₁
              T₁ ∈ Set.Icc
                  (routeTCommonModeCutoff (routeTPrimeGapPacketBase T))
                  (routeTPrimeGapPacketCutoff T : ℝ) ∧
                routeTComparableWidthLadder
                    (routeTCommonModeCutoff (routeTPrimeGapPacketBase T))
                    (routeTPrimeGapPacketCutoff T : ℝ) j ≤ 2 * T₁ ∧
                T₁ ^ mu₁ = T ^ (8 / 5 : ℝ) ∧
                ((((2 * Real.pi) *
                    (routeTSmoothWindowCentralMargin *
                      routeTCommonModeReferenceDensity / 2)) / 4) / 4) /
                    (J : ℝ) ≤
                  ‖routeTFixedSourceAdjacentIntervalPacket
                    L (routeTPrimeGapPacketSupport T) 60 T₁ (mu₁ / 120)
                    (routeTPrimeGapPacketBase T) lambda
                    (lambda * routeTCommonModeReferenceRelativeWidth
                      (routeTPrimeGapPacketBase T))
                    (lambda * routeTPrimeGapPacketWidth lambda) 1 T₁
                    (routeTComparableWidthLadder
                      (routeTCommonModeCutoff (routeTPrimeGapPacketBase T))
                      (routeTPrimeGapPacketCutoff T : ℝ) j)‖ := by
  have hannulus :=
    exists_eventually_routeT_primeFree_fixedSource_commonMode_pairedAnnulus
  have hcut := eventually_routeTCommonModeCutoff_le_primeGapPacketCutoff
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseOne := hbaseTop.eventually_gt_atTop 1
  filter_upwards [hannulus, hcut, hbaseOne,
      Filter.eventually_gt_atTop (1 : ℝ)] with T hannulusT hcutT hx hT
  obtain ⟨L, hL, hLX, hXL, hLscale, hlarge⟩ := hannulusT
  refine ⟨L, hL, hLX, hXL, hLscale, ?_⟩
  intro lambda hlambda hprimeFree
  have hx0 : 0 < routeTPrimeGapPacketBase T := zero_lt_one.trans hx
  have hX : 1 ≤ routeTPrimeGapPacketSupport T := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * routeTPrimeGapPacketBase T
    positivity
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hH : 0 < lambda * routeTPrimeGapPacketWidth lambda := by
    unfold routeTPrimeGapPacketWidth
    positivity
  have hR : 0 < lambda * routeTCommonModeReferenceRelativeWidth
      (routeTPrimeGapPacketBase T) :=
    mul_pos hlambda0 (routeTCommonModeReferenceRelativeWidth_pos hx0)
  have hU : 1 < routeTCommonModeCutoff (routeTPrimeGapPacketBase T) := by
    unfold routeTCommonModeCutoff
    exact Real.one_lt_rpow hx (by norm_num)
  have hB0 : 0 <
      ((2 * Real.pi) *
        (routeTSmoothWindowCentralMargin *
          routeTCommonModeReferenceDensity / 2)) / 4 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hmargin := routeTSmoothWindowCentralMargin_pos
    have hdensity := routeTCommonModeReferenceDensity_pos
    positivity
  have hshell := exists_fixedSource_reparametrized_pairedShell_of_annulus
    L (routeTPrimeGapPacketSupport T) 60
    (T := T) (mu := 8 / 5) (M := routeTPrimeGapPacketBase T)
    (N := lambda)
    (H := lambda * routeTPrimeGapPacketWidth lambda)
    (R := lambda * routeTCommonModeReferenceRelativeWidth
      (routeTPrimeGapPacketBase T))
    (B := ((2 * Real.pi) *
      (routeTSmoothWindowCentralMargin *
        routeTCommonModeReferenceDensity / 2)) / 4)
    (U := routeTCommonModeCutoff (routeTPrimeGapPacketBase T))
    (V := (routeTPrimeGapPacketCutoff T : ℝ))
    hT hX hx0 hlambda0 hH hR hB0 hU hcutT
    (by
      norm_num only [div_div]
      convert hlarge lambda hlambda hprimeFree using 1 <;> ring)
  simpa only using hshell

/-- Canonical shell family for the common-mode paired annulus. -/
def routeTCommonModeOrdinateShellCount (T : ℝ) : ℕ :=
  routeTOrdinateShellCount
    (routeTCommonModeCutoff (routeTPrimeGapPacketBase T))
    (routeTPrimeGapPacketCutoff T : ℝ)

/-- **Uniform finite-family form of the prime-free paired shell.**  Shell count and all shell
endpoints depend only on the ambient height `T`, not on the physical base `lambda`.  Thus every
prime-free base lands in one member of a single preselected finite family, with a common lower
threshold suitable for spatial `L²/L⁴` summation. -/
theorem exists_eventually_routeT_primeFree_fixedSource_commonMode_pairedShell_canonicalCount :
    ∀ᶠ T : ℝ in atTop,
      ∃ L : ℕ, 1 ≤ L ∧
        L ≤ routeTPrimeGapPacketSupport T ∧
        routeTPrimeGapPacketSupport T < (L + 1) ^ (60 : ℕ) ∧
        (L : ℝ) ≤ T ^ (2 / 75 : ℝ) ∧
        ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
            (2 * routeTPrimeGapPacketBase T),
          Chebyshev.theta
                (lambda + 2 * (lambda * routeTPrimeGapPacketWidth lambda)) -
              Chebyshev.theta lambda = 0 →
          ∃ j ∈ Finset.range (routeTCommonModeOrdinateShellCount T),
            let T₁ := routeTComparableWidthLadder
              (routeTCommonModeCutoff (routeTPrimeGapPacketBase T))
              (routeTPrimeGapPacketCutoff T : ℝ) (j + 1)
            let mu₁ := routeTHeightMatchedExponent T (8 / 5 : ℝ) T₁
            T₁ ∈ Set.Icc
                (routeTCommonModeCutoff (routeTPrimeGapPacketBase T))
                (routeTPrimeGapPacketCutoff T : ℝ) ∧
              routeTComparableWidthLadder
                  (routeTCommonModeCutoff (routeTPrimeGapPacketBase T))
                  (routeTPrimeGapPacketCutoff T : ℝ) j ≤ 2 * T₁ ∧
              T₁ ^ mu₁ = T ^ (8 / 5 : ℝ) ∧
              ((((2 * Real.pi) *
                  (routeTSmoothWindowCentralMargin *
                    routeTCommonModeReferenceDensity / 2)) / 4) / 4) /
                  (routeTCommonModeOrdinateShellCount T : ℝ) ≤
                ‖routeTFixedSourceAdjacentIntervalPacket
                  L (routeTPrimeGapPacketSupport T) 60 T₁ (mu₁ / 120)
                  (routeTPrimeGapPacketBase T) lambda
                  (lambda * routeTCommonModeReferenceRelativeWidth
                    (routeTPrimeGapPacketBase T))
                  (lambda * routeTPrimeGapPacketWidth lambda) 1 T₁
                  (routeTComparableWidthLadder
                    (routeTCommonModeCutoff (routeTPrimeGapPacketBase T))
                    (routeTPrimeGapPacketCutoff T : ℝ) j)‖ := by
  have hshell :=
    exists_eventually_routeT_primeFree_fixedSource_commonMode_pairedShell
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseOne := hbaseTop.eventually_gt_atTop 1
  filter_upwards [hshell, hbaseOne] with T hshellT hx
  obtain ⟨L, hL, hLX, hXL, hLscale, hselected⟩ := hshellT
  refine ⟨L, hL, hLX, hXL, hLscale, ?_⟩
  intro lambda hlambda hprimeFree
  obtain ⟨J, hJ, hbelow, _habove, j, hj, hmem, hcomp, hmatch, hlarge⟩ :=
    hselected lambda hlambda hprimeFree
  have hU0 : 0 < routeTCommonModeCutoff (routeTPrimeGapPacketBase T) := by
    unfold routeTCommonModeCutoff
    positivity
  have hJle : J ≤ routeTCommonModeOrdinateShellCount T := by
    exact routeTComparableWidthLadder_index_le_ordinateShellCount hU0
      (hmem.1.trans hmem.2) hJ hbelow
  have hjCanonical : j ∈ Finset.range (routeTCommonModeOrdinateShellCount T) := by
    rw [Finset.mem_range] at hj ⊢
    exact hj.trans_le hJle
  have hdenom :
      ((((2 * Real.pi) *
          (routeTSmoothWindowCentralMargin *
            routeTCommonModeReferenceDensity / 2)) / 4) / 4) /
          (routeTCommonModeOrdinateShellCount T : ℝ) ≤
        (((2 * Real.pi) *
          (routeTSmoothWindowCentralMargin *
            routeTCommonModeReferenceDensity / 2)) / 4) / 4 / (J : ℝ) := by
    apply div_le_div_of_nonneg_left
    · have hpi : 0 < Real.pi := Real.pi_pos
      have hmargin := routeTSmoothWindowCentralMargin_pos
      have hdensity := routeTCommonModeReferenceDensity_pos
      positivity
    · exact_mod_cast hJ
    · exact_mod_cast hJle
  refine ⟨j, hjCanonical, hmem, hcomp, hmatch, ?_⟩
  exact hdenom.trans hlarge

end

end RHTower.Sieve
