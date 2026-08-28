import GaloisForLFunctions.RHTower.Sieve.MaynardFixedWidthCanonicalPacket
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedWidthRungUniformization
import GaloisForLFunctions.RHTower.Sieve.MaynardOrdinateShellReparameterization
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedAmbientPacketInterval
import GaloisForLFunctions.RHTower.Sieve.MaynardElevenFifthsPhysicalCutoffCount
import GaloisForLFunctions.RHTower.Sieve.MaynardTrivialBoundaryGapSequence

/-!
# Fixed-width prime-gap shell cover by fixed-source Mellin packets

Pointwise prime-free localization chooses a stopped Mellin rung. Spatial estimates require the
packet family and its finite index set to be fixed before the physical base varies. This module
performs that quantifier-order conversion for the literal Route-T packet.
-/

noncomputable section
namespace RHTower.Sieve

open Filter Set MeasureTheory

/-- Prime-free bases in the canonical physical block at one fixed proportional width. -/
def routeTFixedWidthPrimeFreeBaseSet (T H0 : ℝ) : Set ℝ :=
  {lambda | lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
      (2 * routeTPrimeGapPacketBase T) ∧
    Chebyshev.theta (lambda + 2 * (lambda * H0)) - Chebyshev.theta lambda = 0}

/-- The fixed-source adjacent Mellin packet at one canonical stopped-width rung. -/
def routeTFixedWidthPhysicalDefectPacket
    (T : ℝ) (L : ℕ) (H0 : ℝ) (j : ℕ) (lambda : ℝ) : ℂ :=
  maynardFixedAmbientPhysicalDefectPacket
    (Finset.range (routeTPrimeGapPacketCutoff T))
    (fun y : ℝ ↦
      heathBrownWindowRelevantEligibleDyadicAggregate
        L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
        (routeTPrimeGapPacketBase T)
        ((1 : ℂ) + (y : ℝ) * Complex.I))
    lambda 1
    (routeTComparableWidthLadder H0 (1 / 4) j)
    (routeTComparableWidthLadder H0 (1 / 4) (j + 1)) 1

/-- Absolute physical defect produced before paying the canonical rung count. -/
def routeTFixedWidthPacketDefectFloor : ℝ :=
  ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / 8

theorem routeTFixedWidthPacketDefectFloor_pos :
    0 < routeTFixedWidthPacketDefectFloor := by
  unfold routeTFixedWidthPacketDefectFloor
  positivity [routeTSmoothWindowCentralMargin_pos]

/-- **Fixed-width shell cover.** One canonical cutoff and one finite rung family, both selected
before the physical base varies, cover every prime-free base by fixed-source packet superlevels. -/
theorem exists_eventually_routeT_fixedWidth_primeFree_subset_rung_union :
    ∃ C50 : ℝ, 1 ≤ C50 ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        ∃ L : ℕ, 1 ≤ L ∧
          routeTPrimeGapPacketSupport T < (L + 1) ^ (60 : ℕ) ∧
          (L : ℝ) ≤ T ^ (2 / 75 : ℝ) ∧
          ∀ H0 : ℝ, 0 < H0 → H0 ≤ 1 / 4 →
            routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) ≤ H0 →
            routeTFixedWidthPrimeFreeBaseSet T H0 ⊆
              ⋃ j ∈ Finset.range (routeTFixedWidthRungCount H0),
                {lambda |
                  routeTFixedWidthPacketDefectFloor /
                      (routeTFixedWidthRungCount H0 : ℝ) ≤
                    ‖routeTFixedWidthPhysicalDefectPacket T L H0 j lambda‖} := by
  obtain ⟨C50, hC50, hpacket⟩ :=
    exists_eventually_routeT_fixedWidth_primeFree_large_range_packet_canonicalCutoff
  refine ⟨C50, hC50, ?_⟩
  filter_upwards [hpacket] with T hpacketT
  obtain ⟨L, hL, hXL, hLscale, hproducer⟩ := hpacketT
  refine ⟨L, hL, hXL, hLscale, ?_⟩
  intro H0 hH0 hH0quarter hwidth
  apply fixedWidth_packet_bad_subset_rung_union
    hH0 hH0quarter routeTFixedWidthPacketDefectFloor_pos.le
  intro lambda hlambda
  obtain ⟨J, hJ, hbelow, j, hj, hlarge⟩ :=
    hproducer H0 hH0 hH0quarter hwidth lambda hlambda.1 hlambda.2
  refine ⟨J, hJ, hbelow, j, hj, ?_⟩
  change
    (((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / 8) / (J : ℝ) ≤
      ‖maynardFixedAmbientPhysicalDefectPacket
        (Finset.range (routeTPrimeGapPacketCutoff T))
        (fun y : ℝ ↦
          heathBrownWindowRelevantEligibleDyadicAggregate
            L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
            (routeTPrimeGapPacketBase T)
            ((1 : ℂ) + (y : ℝ) * Complex.I))
        lambda 1
        (routeTComparableWidthLadder H0 (1 / 4) j)
        (routeTComparableWidthLadder H0 (1 / 4) (j + 1)) 1‖
  calc
    (((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / 8) / (J : ℝ) =
        (((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / (J : ℝ)) / 8 := by
      ring
    _ ≤ _ := hlarge

/-- Measure form of the fixed-width cover. Spatial estimates may now be applied rungwise and
summed without a measurable choice depending on the physical base. -/
theorem volume_routeTFixedWidthPrimeFreeBaseSet_le_sum_rung_bad
    {T : ℝ} {L : ℕ} {H0 : ℝ}
    (hcover : routeTFixedWidthPrimeFreeBaseSet T H0 ⊆
      ⋃ j ∈ Finset.range (routeTFixedWidthRungCount H0),
        {lambda |
          routeTFixedWidthPacketDefectFloor /
              (routeTFixedWidthRungCount H0 : ℝ) ≤
            ‖routeTFixedWidthPhysicalDefectPacket T L H0 j lambda‖}) :
    (volume.restrict (Set.Icc (routeTPrimeGapPacketBase T)
        (2 * routeTPrimeGapPacketBase T))).real
        (routeTFixedWidthPrimeFreeBaseSet T H0) ≤
      ∑ j ∈ Finset.range (routeTFixedWidthRungCount H0),
        (volume.restrict (Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T))).real
          {lambda |
            routeTFixedWidthPacketDefectFloor /
                (routeTFixedWidthRungCount H0 : ℝ) ≤
              ‖routeTFixedWidthPhysicalDefectPacket T L H0 j lambda‖} := by
  let μ : Measure ℝ := volume.restrict
    (Set.Icc (routeTPrimeGapPacketBase T) (2 * routeTPrimeGapPacketBase T))
  let bad : ℕ → Set ℝ := fun j =>
    {lambda |
      routeTFixedWidthPacketDefectFloor /
          (routeTFixedWidthRungCount H0 : ℝ) ≤
        ‖routeTFixedWidthPhysicalDefectPacket T L H0 j lambda‖}
  have hmono : μ (routeTFixedWidthPrimeFreeBaseSet T H0) ≤
      μ (⋃ j ∈ Finset.range (routeTFixedWidthRungCount H0), bad j) :=
    measure_mono hcover
  have hmonoReal : μ.real (routeTFixedWidthPrimeFreeBaseSet T H0) ≤
      μ.real (⋃ j ∈ Finset.range (routeTFixedWidthRungCount H0), bad j) := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top μ _) hmono
  have hunion :
      μ.real (⋃ j ∈ Finset.range (routeTFixedWidthRungCount H0), bad j) ≤
        ∑ j ∈ Finset.range (routeTFixedWidthRungCount H0), μ.real (bad j) :=
    measureReal_biUnion_finset_le _ _
  simpa only [μ, bad] using hmonoReal.trans hunion

/-- Exact exponent at height `T` representing an arbitrary positive real cutoff scale. -/
def routeTExactRealCutoffExponent (T Y : ℝ) : ℝ :=
  Real.logb T Y

theorem rpow_routeTExactRealCutoffExponent
    {T Y : ℝ} (hT : 1 < T) (hY : 0 < Y) :
    T ^ routeTExactRealCutoffExponent T Y = Y := by
  exact Real.rpow_logb (by linarith) hT.ne' hY

/-- Re-expressing one real cutoff scale at two heights preserves the eligibility threshold. -/
theorem rpow_mu_div_oneTwenty_eq_of_rpow_mu_eq_realCutoff
    {Y T₀ mu₀ T₁ mu₁ : ℝ}
    (hT₀ : 1 < T₀) (hT₁ : 1 < T₁)
    (hY₀ : T₀ ^ mu₀ = Y) (hY₁ : T₁ ^ mu₁ = Y) :
    T₀ ^ (mu₀ / 120) = T₁ ^ (mu₁ / 120) := by
  have hT₀0 : 0 ≤ T₀ := by linarith
  have hT₁0 : 0 ≤ T₁ := by linarith
  calc
    T₀ ^ (mu₀ / 120) = (T₀ ^ mu₀) ^ (1 / 120 : ℝ) := by
      have he : mu₀ / 120 = mu₀ * (1 / 120 : ℝ) := by ring
      rw [he]
      exact Real.rpow_mul hT₀0 mu₀ (1 / 120 : ℝ)
    _ = Y ^ (1 / 120 : ℝ) := by rw [hY₀]
    _ = (T₁ ^ mu₁) ^ (1 / 120 : ℝ) := by rw [hY₁]
    _ = T₁ ^ (mu₁ / 120) := by
      have he : mu₁ / 120 = mu₁ * (1 / 120 : ℝ) := by ring
      rw [he]
      exact (Real.rpow_mul hT₁0 mu₁ (1 / 120 : ℝ)).symm

/-- Height-matched exponent preserving the original source eligibility threshold. -/
def routeTHeightMatchedExponent (T₀ mu₀ T₁ : ℝ) : ℝ :=
  routeTExactRealCutoffExponent T₁ (T₀ ^ mu₀)

theorem rpow_routeTHeightMatchedExponent
    {T₀ mu₀ T₁ : ℝ} (hT₀ : 1 < T₀) (hT₁ : 1 < T₁) :
    T₁ ^ routeTHeightMatchedExponent T₀ mu₀ T₁ = T₀ ^ mu₀ := by
  apply rpow_routeTExactRealCutoffExponent hT₁
  exact Real.rpow_pos_of_pos (by linarith) _

theorem heathBrownWindowRelevantEligibleDyadicAggregate_eq_heightMatched
    (L X k : ℕ) {T₀ mu₀ T₁ M : ℝ}
    (hT₀ : 1 < T₀) (hT₁ : 1 < T₁) (s : ℂ) :
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T₀ (mu₀ / 120) M s =
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T₁
        (routeTHeightMatchedExponent T₀ mu₀ T₁ / 120) M s := by
  apply heathBrownWindowRelevantEligibleDyadicAggregate_eq_of_rpow_threshold_eq
    L X k hT₀ hT₁
  exact rpow_mu_div_oneTwenty_eq_of_rpow_mu_eq_realCutoff
    hT₀ hT₁ rfl (rpow_routeTHeightMatchedExponent hT₀ hT₁)

/-- Frozen-source aggregate multiplied by an independently scaled adjacent Mellin kernel. -/
def routeTFixedSourceAdjacentIntegrand
    (L X k : ℕ) (T t M N R H sigma y : ℝ) : ℂ :=
  heathBrownWindowRelevantEligibleDyadicAggregate L X k T t M
      ((sigma : ℂ) + (y : ℝ) * Complex.I) *
    (routeTNormalizedSmoothWindowMellin N R
        ((sigma : ℂ) + (y : ℝ) * Complex.I) -
      routeTNormalizedSmoothWindowMellin N H
        ((sigma : ℂ) + (y : ℝ) * Complex.I))

/-- One fixed-source adjacent packet on an arbitrary ordinate interval. -/
def routeTFixedSourceAdjacentIntervalPacket
    (L X k : ℕ) (T t M N R H sigma a b : ℝ) : ℂ :=
  ∫ y in a..b, routeTFixedSourceAdjacentIntegrand
    L X k T t M N R H sigma y

theorem continuous_routeTFixedSourceAdjacentIntegrand
    (L X k : ℕ) (T t M : ℝ) {N R H sigma : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) (hsigma : 0 < sigma) :
    Continuous (routeTFixedSourceAdjacentIntegrand L X k T t M N R H sigma) := by
  apply Continuous.mul
  · exact continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T t M sigma
  · exact (continuous_routeTNormalizedSmoothWindowMellin_line hN hR hsigma).sub
      (continuous_routeTNormalizedSmoothWindowMellin_line hN hH hsigma)

theorem routeTFixedSourceAdjacentIntervalPacket_heightMatched
    (L X k : ℕ) {T₀ mu₀ T₁ M N R H sigma a b : ℝ}
    (hT₀ : 1 < T₀) (hT₁ : 1 < T₁) :
    routeTFixedSourceAdjacentIntervalPacket L X k T₀ (mu₀ / 120)
        M N R H sigma a b =
      routeTFixedSourceAdjacentIntervalPacket L X k T₁
        (routeTHeightMatchedExponent T₀ mu₀ T₁ / 120)
        M N R H sigma a b := by
  apply intervalIntegral.integral_congr
  intro y _hy
  unfold routeTFixedSourceAdjacentIntegrand
  rw [heathBrownWindowRelevantEligibleDyadicAggregate_eq_heightMatched
    L X k hT₀ hT₁]

/-- Shell-matched reparameterization with independent frozen source and physical Mellin bases. -/
theorem exists_fixedSource_reparametrized_comparable_ordinate_shell_integral_norm_ge
    (L X k : ℕ) {T₀ mu₀ M N H R sigma B U V : ℝ}
    (hT₀ : 1 < T₀) (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hsigma : 0 < sigma) (hU : 1 < U) (hUV : U ≤ V)
    (hB : B ≤ ‖routeTFixedSourceAdjacentIntervalPacket
      L X k T₀ (mu₀ / 120) M N R H sigma U V‖) :
    ∃ J : ℕ, 0 < J ∧
      (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ V / U ∧
      V / U < (((2 ^ J : ℕ) : ℝ)) ∧
      ∃ j ∈ Finset.range J,
        let T₁ := routeTComparableWidthLadder U V (j + 1)
        let mu₁ := routeTHeightMatchedExponent T₀ mu₀ T₁
        T₁ ∈ Set.Icc U V ∧
        routeTComparableWidthLadder U V j ≤ 2 * T₁ ∧
        T₁ ^ mu₁ = T₀ ^ mu₀ ∧
        B / (J : ℝ) ≤ ‖routeTFixedSourceAdjacentIntervalPacket
          L X k T₁ (mu₁ / 120) M N R H sigma T₁
            (routeTComparableWidthLadder U V j)‖ := by
  let f : ℝ → ℂ := routeTFixedSourceAdjacentIntegrand
    L X k T₀ (mu₀ / 120) M N R H sigma
  have hf : Continuous f := continuous_routeTFixedSourceAdjacentIntegrand
    L X k T₀ (mu₀ / 120) M hN hR hH hsigma
  obtain ⟨J, hJ, hbelow, habove, j, hj, _hdec, hcomp, hlarge⟩ :=
    exists_comparable_ordinate_shell_integral_norm_ge
      (f := f) (B := B) (U := U) (V := V) (by linarith) hUV
        (fun a b =>
          (show IntervalIntegrable f volume a b from hf.intervalIntegrable a b))
        (by simpa only [f, routeTFixedSourceAdjacentIntervalPacket] using hB)
  let T₁ : ℝ := routeTComparableWidthLadder U V (j + 1)
  let mu₁ : ℝ := routeTHeightMatchedExponent T₀ mu₀ T₁
  have hT₁mem : T₁ ∈ Set.Icc U V :=
    routeTComparableWidthLadder_mem (by linarith) hUV (j + 1)
  have hT₁ : 1 < T₁ := hU.trans_le hT₁mem.1
  have hcut : T₁ ^ mu₁ = T₀ ^ mu₀ :=
    rpow_routeTHeightMatchedExponent hT₀ hT₁
  have hinterval := routeTFixedSourceAdjacentIntervalPacket_heightMatched
    (L := L) (X := X) (k := k) (T₀ := T₀) (mu₀ := mu₀) (T₁ := T₁)
      (M := M) (N := N) (R := R) (H := H) (sigma := sigma)
      (a := T₁) (b := routeTComparableWidthLadder U V j) hT₀ hT₁
  refine ⟨J, hJ, hbelow, habove, j, hj, ?_⟩
  dsimp only
  refine ⟨hT₁mem, ?_, hcut, ?_⟩
  · simpa only [T₁] using hcomp
  · rw [← hinterval]
    simpa only [T₁, f, routeTFixedSourceAdjacentIntervalPacket] using hlarge

/-- Canonical finite count for the dyadic shells between two positive ordinates. -/
def routeTOrdinateShellCount (U V : ℝ) : ℕ :=
  ⌈1 + Real.log (V / U) / Real.log 2⌉₊

theorem routeTOrdinateShellCount_pos
    {U V : ℝ} (hU : 0 < U) (hUV : U ≤ V) :
    0 < routeTOrdinateShellCount U V := by
  apply Nat.ceil_pos.mpr
  have hratio : 1 ≤ V / U := (le_div_iff₀ hU).2 (by simpa using hUV)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogRatio : 0 ≤ Real.log (V / U) := Real.log_nonneg hratio
  positivity

theorem routeTComparableWidthLadder_index_le_ordinateShellCount
    {U V : ℝ} (hU : 0 < U) (hUV : U ≤ V)
    {J : ℕ} (hJ : 0 < J)
    (hbelow : (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ V / U) :
    J ≤ routeTOrdinateShellCount U V := by
  have hlog := routeTComparableWidthLadder_index_le_log hU hUV hJ hbelow
  have hceil :
      1 + Real.log (V / U) / Real.log 2 ≤
        (routeTOrdinateShellCount U V : ℝ) := Nat.le_ceil _
  exact_mod_cast hlog.trans hceil

/-- The `j`th ordinate shell, with its source reparameterized at the lower shell height. -/
def routeTFixedSourceReparametrizedOrdinateShellPacket
    (L X k : ℕ) (T₀ mu₀ M N R H sigma U V : ℝ) (j : ℕ) : ℂ :=
  let T₁ := routeTComparableWidthLadder U V (j + 1)
  let mu₁ := routeTHeightMatchedExponent T₀ mu₀ T₁
  routeTFixedSourceAdjacentIntervalPacket L X k T₁ (mu₁ / 120)
    M N R H sigma T₁ (routeTComparableWidthLadder U V j)

/-- **Fixed-source low/high shell cover.** A large packet on `[0,V]` is either already large on
the prescribed low interval, or is large on one member of a finite shell family fixed before the
spatial parameter varies.  Every high shell carries the exactly threshold-matched source. -/
theorem fixedSource_fullInterval_bad_subset_low_union_reparametrized_shells
    (L X k : ℕ) {T₀ mu₀ M sigma D U V : ℝ}
    (hT₀ : 1 < T₀) (hsigma : 0 < sigma) (hD : 0 ≤ D)
    (hU : 1 < U) (hUV : U ≤ V)
    {N R H : ℝ → ℝ} {P : Set ℝ}
    (hN : ∀ lambda ∈ P, 0 < N lambda)
    (hR : ∀ lambda ∈ P, 0 < R lambda)
    (hH : ∀ lambda ∈ P, 0 < H lambda)
    (hlarge : ∀ lambda ∈ P,
      D ≤ ‖routeTFixedSourceAdjacentIntervalPacket
        L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda)
          sigma 0 V‖) :
    P ⊆
      {lambda | D / 2 ≤ ‖routeTFixedSourceAdjacentIntervalPacket
        L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda)
          sigma 0 U‖} ∪
      ⋃ j ∈ Finset.range (routeTOrdinateShellCount U V),
        {lambda |
          (D / 2) / (routeTOrdinateShellCount U V : ℝ) ≤
            ‖routeTFixedSourceReparametrizedOrdinateShellPacket
              L X k T₀ mu₀ M (N lambda) (R lambda) (H lambda)
                sigma U V j‖} := by
  intro lambda hlambda
  let f : ℝ → ℂ := routeTFixedSourceAdjacentIntegrand
    L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda) sigma
  have hf : Continuous f := continuous_routeTFixedSourceAdjacentIntegrand
    L X k T₀ (mu₀ / 120) M (hN lambda hlambda) (hR lambda hlambda)
      (hH lambda hlambda) hsigma
  have hsplit :
      routeTFixedSourceAdjacentIntervalPacket
          L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda) sigma 0 V =
        routeTFixedSourceAdjacentIntervalPacket
            L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda) sigma 0 U +
          routeTFixedSourceAdjacentIntervalPacket
            L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda) sigma U V := by
    unfold routeTFixedSourceAdjacentIntervalPacket
    exact (intervalIntegral.integral_add_adjacent_intervals
      (show IntervalIntegrable f volume 0 U from hf.intervalIntegrable 0 U)
      (show IntervalIntegrable f volume U V from hf.intervalIntegrable U V)).symm
  by_cases hlow : D / 2 ≤ ‖routeTFixedSourceAdjacentIntervalPacket
      L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda) sigma 0 U‖
  · exact Set.mem_union_left _ hlow
  · apply Set.mem_union_right
    have htri := norm_add_le
      (routeTFixedSourceAdjacentIntervalPacket
        L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda) sigma 0 U)
      (routeTFixedSourceAdjacentIntervalPacket
        L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda) sigma U V)
    have hhigh : D / 2 ≤ ‖routeTFixedSourceAdjacentIntervalPacket
        L X k T₀ (mu₀ / 120) M (N lambda) (R lambda) (H lambda) sigma U V‖ := by
      rw [← hsplit] at htri
      have hfull := hlarge lambda hlambda
      exact le_of_not_gt (fun hlt => hlow (by linarith))
    obtain ⟨J, hJ, hbelow, _habove, j, hj, _hTmem, _hcomp, _hcut, hjlarge⟩ :=
      exists_fixedSource_reparametrized_comparable_ordinate_shell_integral_norm_ge
        L X k hT₀ (hN lambda hlambda) (hH lambda hlambda) (hR lambda hlambda)
          hsigma hU hUV hhigh
    have hJQ : J ≤ routeTOrdinateShellCount U V :=
      routeTComparableWidthLadder_index_le_ordinateShellCount
        (by linarith) hUV hJ hbelow
    have hJreal : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
    have hJQreal : (J : ℝ) ≤ (routeTOrdinateShellCount U V : ℝ) := by
      exact_mod_cast hJQ
    have hthreshold :
        (D / 2) / (routeTOrdinateShellCount U V : ℝ) ≤ (D / 2) / (J : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hJreal hJQreal
    apply Set.mem_iUnion_of_mem j
    apply Set.mem_iUnion_of_mem
      (Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hJQ))
    exact hthreshold.trans hjlarge

/-- Low-ordinate part of one fixed-width canonical packet. -/
def routeTFixedWidthLowOrdinatePacket
    (T : ℝ) (L : ℕ) (H0 : ℝ) (r : ℕ) (U lambda : ℝ) : ℂ :=
  routeTFixedSourceAdjacentIntervalPacket
    L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
    (routeTPrimeGapPacketBase T) lambda
    (lambda * routeTComparableWidthLadder H0 (1 / 4) r)
    (lambda * routeTComparableWidthLadder H0 (1 / 4) (r + 1))
    1 0 U

/-- High-ordinate shell of one fixed-width packet, with source height matched to that shell. -/
def routeTFixedWidthReparametrizedOrdinateShellPacket
    (T : ℝ) (L : ℕ) (H0 : ℝ) (r : ℕ) (U : ℝ) (j : ℕ)
    (lambda : ℝ) : ℂ :=
  routeTFixedSourceReparametrizedOrdinateShellPacket
    L (routeTPrimeGapPacketSupport T) 60 T (8 / 5)
    (routeTPrimeGapPacketBase T) lambda
    (lambda * routeTComparableWidthLadder H0 (1 / 4) r)
    (lambda * routeTComparableWidthLadder H0 (1 / 4) (r + 1))
    1 U (routeTPrimeGapPacketCutoff T : ℝ) j

theorem routeTFixedWidthPhysicalDefectPacket_eq_fixedSourceInterval
    {T : ℝ} {L : ℕ} {H0 : ℝ} {r : ℕ} {lambda : ℝ}
    (hH0 : 0 < H0) (hlambda : 0 < lambda) :
    routeTFixedWidthPhysicalDefectPacket T L H0 r lambda =
      routeTFixedSourceAdjacentIntervalPacket
        L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
        (routeTPrimeGapPacketBase T) lambda
        (lambda * routeTComparableWidthLadder H0 (1 / 4) r)
        (lambda * routeTComparableWidthLadder H0 (1 / 4) (r + 1))
        1 0 (routeTPrimeGapPacketCutoff T : ℝ) := by
  let a : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate
      L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
      (routeTPrimeGapPacketBase T) ((1 : ℂ) + (y : ℝ) * Complex.I)
  have ha : Continuous a :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
        (routeTPrimeGapPacketBase T) 1
  have hR : 0 < routeTComparableWidthLadder H0 (1 / 4) r :=
    routeTComparableWidthLadder_pos hH0 r
  have hH : 0 < routeTComparableWidthLadder H0 (1 / 4) (r + 1) :=
    routeTComparableWidthLadder_pos hH0 (r + 1)
  have heq := maynardFixedAmbientPhysicalDefectPacket_range_eq_intervalIntegral
    a ha lambda 1
      (routeTComparableWidthLadder H0 (1 / 4) r)
      (routeTComparableWidthLadder H0 (1 / 4) (r + 1)) 1
      (routeTPrimeGapPacketCutoff T)
      (by simpa using hlambda) (mul_pos hlambda hR) (mul_pos hlambda hH) (by norm_num)
  simpa [routeTFixedWidthPhysicalDefectPacket,
    routeTFixedSourceAdjacentIntervalPacket, routeTFixedSourceAdjacentIntegrand,
    a, one_div] using heq

/-- One fixed-width bad set splits into a low-ordinate bad set and finitely many fixed-source,
threshold-matched high-shell bad sets. -/
theorem routeTFixedWidth_rung_bad_subset_low_union_reparametrized_shells
    {T : ℝ} {L : ℕ} {H0 D U : ℝ} {r : ℕ}
    (hT : 1 < T) (hH0 : 0 < H0) (hD : 0 ≤ D)
    (hU : 1 < U) (hUK : U ≤ (routeTPrimeGapPacketCutoff T : ℝ)) :
    {lambda | lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T) ∧
        D ≤ ‖routeTFixedWidthPhysicalDefectPacket T L H0 r lambda‖} ⊆
      {lambda | D / 2 ≤ ‖routeTFixedWidthLowOrdinatePacket T L H0 r U lambda‖} ∪
        ⋃ j ∈ Finset.range
            (routeTOrdinateShellCount U (routeTPrimeGapPacketCutoff T : ℝ)),
          {lambda |
            (D / 2) /
                (routeTOrdinateShellCount U
                  (routeTPrimeGapPacketCutoff T : ℝ) : ℝ) ≤
              ‖routeTFixedWidthReparametrizedOrdinateShellPacket
                T L H0 r U j lambda‖} := by
  let P : Set ℝ := {lambda | lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
      (2 * routeTPrimeGapPacketBase T) ∧
    D ≤ ‖routeTFixedWidthPhysicalDefectPacket T L H0 r lambda‖}
  have hx : 0 < routeTPrimeGapPacketBase T := by
    unfold routeTPrimeGapPacketBase
    positivity
  have hN : ∀ lambda ∈ P, 0 < lambda := by
    intro lambda hlambda
    exact hx.trans_le hlambda.1.1
  have hR : ∀ lambda ∈ P,
      0 < lambda * routeTComparableWidthLadder H0 (1 / 4) r := by
    intro lambda hlambda
    exact mul_pos (hN lambda hlambda) (routeTComparableWidthLadder_pos hH0 r)
  have hH : ∀ lambda ∈ P,
      0 < lambda * routeTComparableWidthLadder H0 (1 / 4) (r + 1) := by
    intro lambda hlambda
    exact mul_pos (hN lambda hlambda)
      (routeTComparableWidthLadder_pos hH0 (r + 1))
  have hlarge : ∀ lambda ∈ P,
      D ≤ ‖routeTFixedSourceAdjacentIntervalPacket
        L (routeTPrimeGapPacketSupport T) 60 T ((8 / 5 : ℝ) / 120)
        (routeTPrimeGapPacketBase T) lambda
        (lambda * routeTComparableWidthLadder H0 (1 / 4) r)
        (lambda * routeTComparableWidthLadder H0 (1 / 4) (r + 1))
        1 0 (routeTPrimeGapPacketCutoff T : ℝ)‖ := by
    intro lambda hlambda
    rw [show (8 / 5 : ℝ) / 120 = 1 / 75 by norm_num]
    rw [← routeTFixedWidthPhysicalDefectPacket_eq_fixedSourceInterval
      hH0 (hN lambda hlambda)]
    exact hlambda.2
  have hcover := fixedSource_fullInterval_bad_subset_low_union_reparametrized_shells
    L (routeTPrimeGapPacketSupport T) 60 hT (by norm_num) hD hU hUK
      (N := fun lambda => lambda)
      (R := fun lambda => lambda * routeTComparableWidthLadder H0 (1 / 4) r)
      (H := fun lambda => lambda * routeTComparableWidthLadder H0 (1 / 4) (r + 1))
      (P := P) hN hR hH hlarge
  simpa only [P, routeTFixedWidthLowOrdinatePacket,
    routeTFixedWidthReparametrizedOrdinateShellPacket,
    show (8 / 5 : ℝ) / 120 = 1 / 75 by norm_num] using hcover

/-- Refinement law for any pre-existing finite fixed-width rung cover.  It commutes the width-rung
union with the ordinate low/high dichotomy without introducing any spatially dependent choice. -/
theorem routeTFixedWidth_rung_cover_refines_to_low_high_shell_cover
    {T : ℝ} {L Q : ℕ} {H0 D U : ℝ} {P : Set ℝ}
    (hT : 1 < T) (hH0 : 0 < H0) (hD : 0 ≤ D)
    (hU : 1 < U) (hUK : U ≤ (routeTPrimeGapPacketCutoff T : ℝ))
    (hPblock : P ⊆ Set.Icc (routeTPrimeGapPacketBase T)
      (2 * routeTPrimeGapPacketBase T))
    (hcover : P ⊆ ⋃ r ∈ Finset.range Q,
      {lambda | D ≤ ‖routeTFixedWidthPhysicalDefectPacket T L H0 r lambda‖}) :
    P ⊆ ⋃ r ∈ Finset.range Q,
      ({lambda | D / 2 ≤ ‖routeTFixedWidthLowOrdinatePacket T L H0 r U lambda‖} ∪
        ⋃ j ∈ Finset.range
            (routeTOrdinateShellCount U (routeTPrimeGapPacketCutoff T : ℝ)),
          {lambda |
            (D / 2) /
                (routeTOrdinateShellCount U
                  (routeTPrimeGapPacketCutoff T : ℝ) : ℝ) ≤
              ‖routeTFixedWidthReparametrizedOrdinateShellPacket
                T L H0 r U j lambda‖}) := by
  intro lambda hlambda
  obtain ⟨r, hrange⟩ := Set.mem_iUnion.mp (hcover hlambda)
  obtain ⟨hr, hbad⟩ := Set.mem_iUnion.mp hrange
  have hrefined := routeTFixedWidth_rung_bad_subset_low_union_reparametrized_shells
    hT hH0 hD hU hUK
      (show lambda ∈ {lambda | lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T) ∧
        D ≤ ‖routeTFixedWidthPhysicalDefectPacket T L H0 r lambda‖} from
        ⟨hPblock hlambda, hbad⟩)
  apply Set.mem_iUnion_of_mem r
  apply Set.mem_iUnion_of_mem hr
  exact hrefined

/-- Complete finite low/high ordinate-shell cover attached to one fixed physical width. -/
def routeTFixedWidthPrimeGapLowHighShellCover
    (T : ℝ) (L : ℕ) (H0 U : ℝ) : Set ℝ :=
  ⋃ r ∈ Finset.range (routeTFixedWidthRungCount H0),
    ({lambda |
      (routeTFixedWidthPacketDefectFloor /
          (routeTFixedWidthRungCount H0 : ℝ)) / 2 ≤
        ‖routeTFixedWidthLowOrdinatePacket T L H0 r U lambda‖} ∪
      ⋃ j ∈ Finset.range
          (routeTOrdinateShellCount U (routeTPrimeGapPacketCutoff T : ℝ)),
        {lambda |
          ((routeTFixedWidthPacketDefectFloor /
              (routeTFixedWidthRungCount H0 : ℝ)) / 2) /
                (routeTOrdinateShellCount U
                  (routeTPrimeGapPacketCutoff T : ℝ) : ℝ) ≤
            ‖routeTFixedWidthReparametrizedOrdinateShellPacket
              T L H0 r U j lambda‖})

/-- **Prime-free fixed-source low/high shell assembly.** Eventually, one Möbius cutoff selected
before both physical width and base works simultaneously for every admissible fixed width and every
admissible low/high ordinate split.  Prime-free bases are covered by a finite family consisting of
literal low packets and exactly height-matched high-shell packets; neither family contains a
base-dependent source choice. -/
theorem exists_eventually_routeT_fixedWidth_primeFree_subset_low_high_shell_cover :
    ∃ C50 : ℝ, 1 ≤ C50 ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        ∃ L : ℕ, 1 ≤ L ∧
          routeTPrimeGapPacketSupport T < (L + 1) ^ (60 : ℕ) ∧
          (L : ℝ) ≤ T ^ (2 / 75 : ℝ) ∧
          ∀ H0 : ℝ, 0 < H0 → H0 ≤ 1 / 4 →
            routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) ≤ H0 →
            ∀ U : ℝ, 1 < U →
              U ≤ (routeTPrimeGapPacketCutoff T : ℝ) →
              routeTFixedWidthPrimeFreeBaseSet T H0 ⊆
                routeTFixedWidthPrimeGapLowHighShellCover T L H0 U := by
  obtain ⟨C50, hC50, hcover⟩ :=
    exists_eventually_routeT_fixedWidth_primeFree_subset_rung_union
  refine ⟨C50, hC50, ?_⟩
  filter_upwards [hcover, Filter.eventually_gt_atTop (1 : ℝ)] with T hcoverT hT
  obtain ⟨L, hL, hXL, hLscale, hwidthCover⟩ := hcoverT
  refine ⟨L, hL, hXL, hLscale, ?_⟩
  intro H0 hH0 hH0quarter hwidth U hU hUK
  have hD : 0 ≤ routeTFixedWidthPacketDefectFloor /
      (routeTFixedWidthRungCount H0 : ℝ) :=
    div_nonneg routeTFixedWidthPacketDefectFloor_pos.le (Nat.cast_nonneg _)
  have hPblock : routeTFixedWidthPrimeFreeBaseSet T H0 ⊆
      Set.Icc (routeTPrimeGapPacketBase T) (2 * routeTPrimeGapPacketBase T) := by
    intro lambda hlambda
    exact hlambda.1
  have hrefined := routeTFixedWidth_rung_cover_refines_to_low_high_shell_cover
    hT hH0 hD hU hUK hPblock
      (hwidthCover H0 hH0 hH0quarter hwidth)
  simpa only [routeTFixedWidthPrimeGapLowHighShellCover] using hrefined

/-- Central-cell extraction with frozen source scale `M` independent of physical Mellin scale `N`.
Exact pole cancellation still costs only `4`; scale identification was never needed. -/
theorem exists_cell_max_norm_intervalIntegral_fixedSource_adjacent_defect_central_le
    (L X k : ℕ) (T0 t M : ℝ) {N H R a delta : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hdelta : 0 < delta) (m : ℕ)
    (hband : ∀ y ∈ Set.Icc a (a + (m : ℝ) * delta), |y| ≤ N / (2 * R)) :
    ∃ c : ℕ → ℝ,
      (∀ j, j < m → c j ∈
        Set.Icc (a + (j : ℝ) * delta) (a + ((j : ℝ) + 1) * delta)) ∧
      ‖routeTFixedSourceAdjacentIntervalPacket
          L X k T0 t M N R H 1 a (a + (m : ℝ) * delta)‖ ≤
        ∑ j ∈ Finset.range m, delta *
          (4 * ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
            ((1 : ℂ) + (c j : ℝ) * Complex.I)‖) := by
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let K : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R
        ((1 : ℂ) + (y : ℝ) * Complex.I) -
      routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + (y : ℝ) * Complex.I)
  have hA : Continuous A :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T0 t M 1
  have hK : Continuous K :=
    (continuous_routeTNormalizedSmoothWindowMellin_line hN hR (by norm_num)).sub
      (continuous_routeTNormalizedSmoothWindowMellin_line hN hH (by norm_num))
  have hKbound : ∀ y ∈ Set.Icc a (a + (m : ℝ) * delta), ‖K y‖ ≤ 4 := by
    intro y hy
    have hyabs := hband y hy
    let s : ℂ := (1 : ℂ) + (y : ℝ) * Complex.I
    have hsre : s.re = 1 := by simp [s]
    have hsnorm : ‖s - 1‖ = |y| := by simp [s, Real.norm_eq_abs]
    have hsmall : ‖s - 1‖ * (2 * R / N) ≤ 1 := by
      rw [hsnorm]
      calc
        |y| * (2 * R / N) ≤ (N / (2 * R)) * (2 * R / N) :=
          mul_le_mul_of_nonneg_right hyabs (by positivity)
        _ = 1 := by field_simp
    have hkernel := norm_routeTNormalizedSmoothWindowMellin_sub_le_reference
      hN hH hR hHR (by simp [hsre]) hsmall
    norm_num [hsre, hsnorm] at hkernel
    dsimp only [K, s] at hkernel ⊢
    calc
      ‖routeTNormalizedSmoothWindowMellin N R (1 + (y : ℂ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H (1 + (y : ℂ) * Complex.I)‖ ≤
          8 * |y| * (R / N) := hkernel
      _ ≤ 8 * (N / (2 * R)) * (R / N) := by gcongr
      _ = 4 := by field_simp; norm_num
  have hcell := exists_cell_max_norm_intervalIntegral_mul_le
    hA hK hdelta m hKbound
  simpa [A, K, routeTFixedSourceAdjacentIntervalPacket,
    routeTFixedSourceAdjacentIntegrand] using hcell

/-- Fixed-source central defect extraction.  A large shell for an independently scaled Mellin
kernel yields one globally spaced source-amplitude superlevel with exact retained signed mass. -/
theorem exists_gap_sequence_dyadic_superlevel_of_fixedSource_adjacent_defect_central
    (L X k : ℕ) (T0 t M : ℝ) {N H R a delta B v : ℝ} {Q n : ℕ}
    (hX : 1 ≤ X) (hM : 0 < M) (hN : 0 < N)
    (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hdelta : 0 < delta) (hB : 0 < B) (hv : 0 < v) (hQ : 0 < Q)
    (hband : ∀ y ∈ Set.Icc a (a + ((2 * n : ℕ) : ℝ) * delta),
      |y| ≤ N / (2 * R))
    (hdefect : B ≤ ‖routeTFixedSourceAdjacentIntervalPacket
      L X k T0 t M N R H 1 a (a + ((2 * n : ℕ) : ℝ) * delta)‖)
    (hP : heathBrownWindowRelevantFixedPolylogBound L X k M 1 ≤
      (((2 ^ Q : ℕ) : ℝ) * v))
    (hsmall : (n : ℝ) * v ≤ B / (16 * delta)) :
    ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
      (∀ i, lam i + delta ≤ lam (i + 1)) ∧
      S ⊆ Finset.range n ∧ q < Q ∧
      (∀ j < n,
        lam j ∈ Set.Icc (a + ((2 * j : ℕ) : ℝ) * delta)
            (a + (((2 * j : ℕ) : ℝ) + 1) * delta) ∨
        lam j ∈ Set.Icc (a + ((2 * j + 1 : ℕ) : ℝ) * delta)
            (a + (((2 * j + 1 : ℕ) : ℝ) + 1) * delta)) ∧
      (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * v) ≤
        ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
          ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) ∧
      B / (16 * delta * (Q : ℝ)) ≤
        (((2 ^ q : ℕ) : ℝ) * v) * (S.card : ℝ) := by
  obtain ⟨c, hc, hcellUpper⟩ :=
    exists_cell_max_norm_intervalIntegral_fixedSource_adjacent_defect_central_le
      L X k T0 t M hN hH hR hHR hdelta (2 * n) hband
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  have hcell : B ≤ ∑ j ∈ Finset.range (2 * n),
      delta * (4 * ‖A (c j)‖) := by
    exact hdefect.trans (by simpa only [A] using hcellUpper)
  have hA : ∀ y : ℝ, ‖A y‖ ≤
      heathBrownWindowRelevantFixedPolylogBound L X k M 1 := by
    intro y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t M 1 y hM (by norm_num)
  have hsmall' : (n : ℝ) * v ≤ B / (4 * delta * 4) := by
    convert hsmall using 1
    ring
  obtain ⟨lam, S, q, hgap, hS, hq, hmem, hlarge, hmass⟩ :=
    exists_gap_sequence_dyadic_superlevel_of_cell_sum
      hdelta (by norm_num : (0 : ℝ) < 4) hB hv hQ hc hcell hA hP hsmall'
  refine ⟨lam, S, q, hgap, hS, hq, hmem, ?_, ?_⟩
  · intro r hr
    simpa only [A] using hlarge r hr
  · convert hmass using 1
    ring


/-- Tail-cell extraction with frozen source scale independent of physical Mellin scale.
Quadratic kernel decay retains the exact comparable-width cost. -/
theorem exists_cell_max_norm_intervalIntegral_fixedSource_adjacent_defect_tail_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (L X k : ℕ) (T0 t M0 : ℝ) {N H R U a Δ : ℝ},
        0 < N → 0 < H → 0 < R → H ≤ R → R ≤ 2 * H → R ≤ N →
        0 < U → 0 < Δ → ∀ (m : ℕ),
        (∀ y ∈ Set.Icc a (a + (m : ℝ) * Δ), U ≤ |y|) →
        ∃ c : ℕ → ℝ,
          (∀ j, j < m → c j ∈
            Set.Icc (a + (j : ℝ) * Δ) (a + ((j : ℝ) + 1) * Δ)) ∧
          ‖∫ y in a..(a + (m : ℝ) * Δ),
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M0
                ((1 : ℂ) + (y : ℝ) * Complex.I) *
              (routeTNormalizedSmoothWindowMellin N R
                  ((1 : ℂ) + (y : ℝ) * Complex.I) -
                routeTNormalizedSmoothWindowMellin N H
                  ((1 : ℂ) + (y : ℝ) * Complex.I))‖ ≤
            ∑ j ∈ Finset.range m, Δ *
              ((65 * C * (N / R) ^ 2 / U ^ 2) *
                ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M0
                  ((1 : ℂ) + (c j : ℝ) * Complex.I)‖) := by
  obtain ⟨C, hC, hquad⟩ :=
    exists_routeTNormalizedSmoothWindowMellin_one_quadratic_bound
  refine ⟨C, hC, ?_⟩
  intro L X k T0 t M0 N H R U a Δ hN hH hR hHR hRH hRN hU hΔ m haway
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M0
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let K : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R ((1 : ℂ) + (y : ℝ) * Complex.I) -
      routeTNormalizedSmoothWindowMellin N H ((1 : ℂ) + (y : ℝ) * Complex.I)
  have hA : Continuous A :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line L X k T0 t M0 1
  have hK : Continuous K :=
    (continuous_routeTNormalizedSmoothWindowMellin_line hN hR (by norm_num)).sub
      (continuous_routeTNormalizedSmoothWindowMellin_line hN hH (by norm_num))
  have hHleN : H ≤ N := hHR.trans hRN
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hM : ∀ y ∈ Set.Icc a (a + (m : ℝ) * Δ),
      ‖K y‖ ≤ 65 * C * (N / R) ^ 2 / U ^ 2 := by
    intro y hy
    have hyU := haway y hy
    have hy2 : U ^ 2 ≤ |y| ^ 2 := by nlinarith [sq_nonneg (|y| - U)]
    have hqR := hquad N R y hN hR hRN
    have hqH := hquad N H y hN hH hHleN
    have hKR : ‖routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * Complex.I)‖ ≤
        13 * C * (N / R) ^ 2 / U ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hU)]
      calc
        ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * Complex.I)‖ * U ^ 2 =
            U ^ 2 * ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * Complex.I)‖ := by ring
        _ ≤ |y| ^ 2 * ‖routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * Complex.I)‖ :=
          mul_le_mul_of_nonneg_right hy2 (norm_nonneg _)
        _ ≤ 13 * C * (N / R) ^ 2 := hqR
    have hratio : R / H ≤ 2 := (div_le_iff₀ hH).2 hRH
    have hratio0 : 0 ≤ R / H := by positivity
    have hratioSq : (R / H) ^ 2 ≤ 4 := by nlinarith
    have hNH : (N / H) ^ 2 ≤ 4 * (N / R) ^ 2 := by
      have hre : N / H = (N / R) * (R / H) := by field_simp
      rw [hre, mul_pow]
      calc
        (N / R) ^ 2 * (R / H) ^ 2 ≤ (N / R) ^ 2 * 4 :=
          mul_le_mul_of_nonneg_left hratioSq (sq_nonneg (N / R))
        _ = 4 * (N / R) ^ 2 := by ring
    have hKH : ‖routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * Complex.I)‖ ≤
        52 * C * (N / R) ^ 2 / U ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hU)]
      calc
        ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * Complex.I)‖ * U ^ 2 =
            U ^ 2 * ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * Complex.I)‖ := by ring
        _ ≤ |y| ^ 2 * ‖routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * Complex.I)‖ :=
          mul_le_mul_of_nonneg_right hy2 (norm_nonneg _)
        _ ≤ 13 * C * (N / H) ^ 2 := hqH
        _ ≤ 13 * C * (4 * (N / R) ^ 2) :=
          mul_le_mul_of_nonneg_left hNH (mul_nonneg (by norm_num) hC0)
        _ = 52 * C * (N / R) ^ 2 := by ring
    dsimp only [K]
    calc
      ‖routeTNormalizedSmoothWindowMellin N R (1 + (y : ℂ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H (1 + (y : ℂ) * Complex.I)‖ ≤
          ‖routeTNormalizedSmoothWindowMellin N R (1 + (y : ℂ) * Complex.I)‖ +
            ‖routeTNormalizedSmoothWindowMellin N H (1 + (y : ℂ) * Complex.I)‖ :=
        norm_sub_le _ _
      _ ≤ 13 * C * (N / R) ^ 2 / U ^ 2 +
          52 * C * (N / R) ^ 2 / U ^ 2 := add_le_add hKR hKH
      _ = 65 * C * (N / R) ^ 2 / U ^ 2 := by ring
  exact exists_cell_max_norm_intervalIntegral_mul_le hA hK hΔ m hM

/-- Fixed-source outer-shell superlevel extraction. Source amplitudes remain attached to the
reparameterized Heath--Brown packet while the independent Mellin kernel pays its exact tail cost. -/
theorem exists_gap_sequence_dyadic_superlevel_of_fixedSource_adjacent_defect_tail :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (L X k : ℕ) (T0 t M0 : ℝ) {N H R U a Δ B v : ℝ} {Q n : ℕ},
        1 ≤ X → 0 < M0 → 0 < N → 0 < H → 0 < R → H ≤ R →
        R ≤ 2 * H → R ≤ N → 0 < U → 0 < Δ →
        0 < B → 0 < v → 0 < Q →
        (∀ y ∈ Set.Icc a (a + ((2 * n : ℕ) : ℝ) * Δ), U ≤ |y|) →
        B ≤ ‖∫ y in a..(a + ((2 * n : ℕ) : ℝ) * Δ),
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M0
              ((1 : ℂ) + (y : ℝ) * Complex.I) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * Complex.I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * Complex.I))‖ →
        heathBrownWindowRelevantFixedPolylogBound L X k M0 1 ≤
          (((2 ^ Q : ℕ) : ℝ) * v) →
        (n : ℝ) * v ≤
          B / (4 * Δ * (65 * C * (N / R) ^ 2 / U ^ 2)) →
        ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
          (∀ i, lam i + Δ ≤ lam (i + 1)) ∧
          S ⊆ Finset.range n ∧ q < Q ∧
          (∀ j < n,
            lam j ∈ Set.Icc (a + ((2 * j : ℕ) : ℝ) * Δ)
                (a + (((2 * j : ℕ) : ℝ) + 1) * Δ) ∨
            lam j ∈ Set.Icc (a + ((2 * j + 1 : ℕ) : ℝ) * Δ)
                (a + (((2 * j + 1 : ℕ) : ℝ) + 1) * Δ)) ∧
          (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * v) ≤
            ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M0
              ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) ∧
          B / (4 * Δ * (65 * C * (N / R) ^ 2 / U ^ 2) * (Q : ℝ)) ≤
            (((2 ^ q : ℕ) : ℝ) * v) * (S.card : ℝ) := by
  obtain ⟨C, hC, htailCell⟩ :=
    exists_cell_max_norm_intervalIntegral_fixedSource_adjacent_defect_tail_le
  refine ⟨C, hC, ?_⟩
  intro L X k T0 t M0 N H R U a Δ B v Q n hX hM0 hN hH hR hHR hRH hRN hU hΔ
    hB hv hQ hband hdefect hP hsmall
  obtain ⟨c, hc, hcellUpper⟩ :=
    htailCell L X k T0 t M0 hN hH hR hHR hRH hRN hU hΔ (2 * n) hband
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M0
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  let M : ℝ := 65 * C * (N / R) ^ 2 / U ^ 2
  have hM : 0 < M := by
    dsimp only [M]
    have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
    positivity
  have hcell : B ≤ ∑ j ∈ Finset.range (2 * n), Δ * (M * ‖A (c j)‖) := by
    exact hdefect.trans (by simpa only [A, M] using hcellUpper)
  have hA : ∀ y : ℝ, ‖A y‖ ≤
      heathBrownWindowRelevantFixedPolylogBound L X k M0 1 := by
    intro y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t M0 1 y hM0 (by norm_num)
  obtain ⟨lam, S, q, hgap, hS, hq, hmem, hlarge, hmass⟩ :=
    exists_gap_sequence_dyadic_superlevel_of_cell_sum
      hΔ hM hB hv hQ hc hcell hA hP (by simpa only [M] using hsmall)
  refine ⟨lam, S, q, hgap, hS, hq, hmem, ?_, ?_⟩
  · intro r hr
    simpa only [A] using hlarge r hr
  · simpa only [M] using hmass


/-- Receiver-normalized Maynard dichotomy for one arbitrary spaced source sequence through the
natural physical-cutoff ceiling `mu ≤ 11/5`. This is the gap-sequence form needed by exact
even-cell shell extraction; no unit-cell alignment or parity recoding remains. -/
theorem eventually_routeT_leftWindowRelevant_gapSequence_twoAlternative_elevenFifths
    (receiverQ : ℕ) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ {L X K : ℕ} {mu N0 V delta : ℝ},
      1 < X → 1 ≤ L → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      (X : ℝ) / (2 ^ 120 : ℝ) ≤ N0 →
      1 < N0 / (2 ^ 120 : ℝ) →
      0 < V →
      heathBrownEligibleBoxCost L X 60 *
          (N0 / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4) ≤ V →
      1 ≤ delta → delta ≤ 2 * T → (K : ℝ) ≤ T →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      (∀ r ∈ S,
        V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) N0
            ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      IsRouteTMaynardTwoAlternative receiverQ (S.card : ℝ) T (T ^ mu)
        (routeTAdaptiveCellAmplitude L X 60 N0 V) := by
  obtain ⟨A, hcount⟩ :=
    exists_eventually_routeT_selectedCell_physicalFixedCutoff_all_amplitude_elevenFifths
  filter_upwards [hcount,
    eventually_routeTSelectedCellAmplitudeReceiverCost_absorbed A receiverQ,
    eventually_routeTSelectedCellAmplitudeReceiverCost_absorbed A 0,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hcountT hcostQ hcost0 hT
  intro L X K mu N0 V delta hX hL hXL hXscale hLscale hmuLo hmuHi
    hlowCutoff hD hV hlow hdelta hdeltaHi hK S hS lam hband hgap hdiam
    haggregate
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 N0 V
  have halpha : 3 / 4 ≤ alpha := by
    dsimp only [alpha]
    exact routeTAdaptiveCellAmplitude_threeQuarter_le L X 60
      (by norm_num) hX hD hV hlow
  have hreserve : ∀ box : HeathBrownBoxChoice L X 60,
      IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
      IsHeathBrownBoxWindowRelevant N0 X 60 box →
      heathBrownEligibleBoxCost L X 60 *
        (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
            (alpha - 1) ≤ V := by
    intro box _helig hwin
    exact routeTAdaptiveCellAmplitude_windowRelevant_reserve
      L X 60 (by norm_num) hX hD hV box hwin
  have hraw := hcountT hX.le hL hXL hXscale hLscale hmuLo hmuHi
    hlowCutoff (by norm_num : (1 : ℝ) / 2 ≤ 1) halpha hV
      (by linarith) hdeltaHi S hS lam hband hgap hdiam haggregate hreserve
  have normalize :
      ((S.card : ℝ) ≤ maynardHarmonicFactor K delta *
            T ^ (mu * (1 - alpha) -
              routeTSelectedCellAmplitudeReserve A T alpha) ∨
        (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
            T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
              routeTSelectedCellAmplitudeReserve A T alpha)) →
      IsRouteTMaynardTwoAlternative receiverQ (S.card : ℝ) T (T ^ mu) alpha := by
    intro hcountRaw
    apply routeT_two_alternative_of_reserved_height_count
      hT rfl (routeTSelectedCellAmplitudeReserve_pos (A := A) hT)
    rcases hcountRaw with hfirst | hsecond
    · left
      exact maynard_count_receiver_margin_general hT.le hfirst
        (hcostQ alpha K delta hK hdelta)
    · right
      have hsecond' := maynard_count_receiver_margin_general
        (q := 0) hT.le hsecond (hcost0 alpha K delta hK hdelta)
      simpa using hsecond'
  simpa only [alpha] using normalize hraw

/-- Logarithmic selector base valid on every reparameterized Route-T shell through `mu ≤ 11/5`. -/
theorem routeTShellLogBase_le_one_add_log_elevenFifths
    {T : ℝ} {X : ℕ} (hT : 1 ≤ T) (hX : 1 ≤ X)
    (hXscale : (X : ℝ) ≤ T ^ (11 / 5 : ℝ)) :
    1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ)) ≤
      routeTTrivialBoundaryShellLogBaseConstant * (1 + Real.log T) := by
  let C : ℝ := (2 : ℝ) ^ 120
  let M : ℝ := (((2 ^ 120 * X : ℕ) : ℝ))
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hCpos : 0 < C := by dsimp only [C]; positivity
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hX)
  have hM : M = C * (X : ℝ) := by
    simp only [M, C, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hlogX : Real.log (X : ℝ) ≤ (11 / 5 : ℝ) * Real.log T := by
    have hlog := Real.log_le_log hXpos hXscale
    rwa [Real.log_rpow hTpos] at hlog
  have hlogC : Real.log C = 120 * Real.log 2 := by
    dsimp only [C]
    rw [Real.log_pow]
    norm_num
  have hlogM : Real.log M ≤
      120 * Real.log 2 + (11 / 5 : ℝ) * Real.log T := by
    rw [hM, Real.log_mul hCpos.ne' hXpos.ne', hlogC]
    linarith
  dsimp only [routeTTrivialBoundaryShellLogBaseConstant]
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

/-- One fixed logarithmic power absorbs variable-width shell depth and selector cost uniformly
through the full reparameterized exponent range `mu ≤ 11/5`. -/
theorem eventually_thirtytwo_shellBandCount_selectorCost_le_receiverLog_elevenFifths
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop,
      ∀ L X : ℕ, 1 ≤ X → L ≤ X → (X : ℝ) ≤ T ^ (11 / 5 : ℝ) →
        32 * (routeTTrivialBoundaryBandCount T : ℝ) *
            heathBrownEligibleBoxCost L X 60 *
              (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent ≤
          D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
  let CQ : ℝ := routeTTrivialBoundaryBandLogConstant
  let CB : ℝ := routeTTrivialBoundaryShellLogBaseConstant
  let CC : ℝ := (60 : ℝ) * (2 : ℝ) ^ 60
  let KD : ℝ := (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent
  let Cbase : ℝ := 32 * CQ * CC * CB ^ 120 * KD
  let C0 : ℝ := Cbase * 2 ^ 121
  let M : ℝ := max 1 (C0 / D)
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop M
  filter_upwards [hlog, Filter.eventually_ge_atTop (1 : ℝ)] with T hlogT hT
  intro L X hX hLX hXscale
  let ell : ℝ := Real.log T
  let B : ℝ := 1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))
  have hlogOne : 1 ≤ ell := by
    exact (le_max_left _ _).trans (by simpa only [ell, M] using hlogT)
  have hCQ : 0 ≤ CQ := by
    dsimp only [CQ, routeTTrivialBoundaryBandLogConstant]
    positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hCB : 0 ≤ CB := by
    dsimp only [CB, routeTTrivialBoundaryShellLogBaseConstant]
    positivity
  have hCC : 0 ≤ CC := by dsimp only [CC]; positivity
  have hKD : 0 ≤ KD := by dsimp only [KD]; positivity
  have hCbase : 0 ≤ Cbase := by
    dsimp only [Cbase]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) hCQ) hCC)
        (pow_nonneg hCB 120)) hKD
  have hB : 0 ≤ B := by
    have hMone : (1 : ℝ) ≤ (((2 ^ 120 * X : ℕ) : ℝ)) := by
      exact_mod_cast Nat.mul_le_mul (Nat.one_le_two_pow) hX
    dsimp only [B]
    linarith [Real.log_nonneg hMone]
  have hQ : (routeTTrivialBoundaryBandCount T : ℝ) ≤ CQ * (1 + ell) := by
    simpa only [CQ, ell] using routeTTrivialBoundaryBandCount_cast_le_log hT
  have hBupper : B ≤ CB * (1 + ell) := by
    simpa only [B, CB, ell] using routeTShellLogBase_le_one_add_log_elevenFifths hT hX hXscale
  have hcost0 : 0 ≤ heathBrownEligibleBoxCost L X 60 := by
    dsimp only [heathBrownEligibleBoxCost]
    positivity
  have hcostRaw := heathBrownEligibleBoxCost_sixty_le_routeTLogBase L X hX hLX
  have hBpow : B ^ 120 ≤ (CB * (1 + ell)) ^ 120 :=
    pow_le_pow_left₀ hB hBupper 120
  have hcost : heathBrownEligibleBoxCost L X 60 ≤
      CC * CB ^ 120 * (1 + ell) ^ 120 := by
    calc
      heathBrownEligibleBoxCost L X 60 ≤ CC * B ^ 120 := by
        simpa only [CC, B] using hcostRaw
      _ ≤ CC * (CB * (1 + ell)) ^ 120 :=
        mul_le_mul_of_nonneg_left hBpow hCC
      _ = CC * CB ^ 120 * (1 + ell) ^ 120 := by
        rw [mul_pow]
        ring
  have hOneLog : 0 ≤ 1 + ell := by linarith
  have hcore :
      32 * (routeTTrivialBoundaryBandCount T : ℝ) *
          heathBrownEligibleBoxCost L X 60 * KD ≤
        Cbase * (1 + ell) ^ 121 := by
    have hqUpper0 : 0 ≤ 32 * (CQ * (1 + ell)) :=
      mul_nonneg (by norm_num) (mul_nonneg hCQ hOneLog)
    have hqStep :
        32 * (routeTTrivialBoundaryBandCount T : ℝ) ≤
          32 * (CQ * (1 + ell)) :=
      mul_le_mul_of_nonneg_left hQ (by norm_num)
    have hfirst :
        32 * (routeTTrivialBoundaryBandCount T : ℝ) *
            heathBrownEligibleBoxCost L X 60 ≤
          32 * (CQ * (1 + ell)) *
            (CC * CB ^ 120 * (1 + ell) ^ 120) :=
      mul_le_mul hqStep hcost hcost0 hqUpper0
    calc
      32 * (routeTTrivialBoundaryBandCount T : ℝ) *
          heathBrownEligibleBoxCost L X 60 * KD ≤
        (32 * (CQ * (1 + ell)) *
          (CC * CB ^ 120 * (1 + ell) ^ 120)) * KD :=
            mul_le_mul_of_nonneg_right hfirst hKD
      _ = Cbase * (1 + ell) ^ 121 := by
        dsimp only [Cbase]
        rw [show (121 : ℕ) = 1 + 120 by norm_num, pow_add, pow_one]
        ring
  have hshapeBase : 1 + ell ≤ 2 * ell := by linarith
  have hshapePow : (1 + ell) ^ 121 ≤ (2 * ell) ^ 121 :=
    pow_le_pow_left₀ hOneLog hshapeBase 121
  have hshape : Cbase * (1 + ell) ^ 121 ≤ C0 * ell ^ 121 := by
    calc
      Cbase * (1 + ell) ^ 121 ≤ Cbase * (2 * ell) ^ 121 :=
        mul_le_mul_of_nonneg_left hshapePow hCbase
      _ = C0 * ell ^ 121 := by
        dsimp only [C0]
        rw [mul_pow]
        ring
  have hCD : C0 / D ≤ ell := by
    exact (le_max_right _ _).trans (by simpa only [ell, M] using hlogT)
  have hconst : C0 ≤ D * ell := by
    have hout : C0 ≤ ell * D := (div_le_iff₀ hD).mp hCD
    simpa only [mul_comm] using hout
  have hlast : C0 * ell ^ 121 ≤ D * ell ^ 122 := by
    have hp : 0 ≤ ell ^ 121 := pow_nonneg (zero_le_one.trans hlogOne) _
    calc
      C0 * ell ^ 121 ≤ (D * ell) * ell ^ 121 :=
        mul_le_mul_of_nonneg_right hconst hp
      _ = D * ell ^ 122 := by
        rw [show (122 : ℕ) = 1 + 121 by norm_num, pow_add, pow_one]
        ring
  simpa only [KD, ell, routeTTrivialBoundaryReceiverLogPower] using
    hcore.trans (hshape.trans hlast)

/-- First-exclusion threshold on a shell after exact height reparameterization.  Only the full
Route-T exponent bound and the physical-support comparison survive. -/
theorem eventually_routeT_amplitudeBand_reparameterizedShell_firstExclusionThreshold_elevenFifths
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X : ℕ} {N V : ℝ},
      1 < X → 1 ≤ L → L ≤ X → (X : ℝ) ≤ T ^ (11 / 5 : ℝ) →
      1 < N / (2 ^ 120 : ℝ) → 0 < V →
      (X : ℝ) ≤ (4 * (2 ^ 120 : ℝ)) * (N / (2 ^ 120 : ℝ)) →
      routeTTrivialBoundaryAmplitudeThreshold L X 60 N ≤ V →
      8 * V * (X : ℝ) ^
          (1 - routeTAdaptiveCellAmplitude L X 60 N V) ≤
        ((D / (2 * (routeTTrivialBoundaryBandCount T : ℝ))) / 2) *
          (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
  filter_upwards [
    eventually_thirtytwo_shellBandCount_selectorCost_le_receiverLog_elevenFifths hD,
    Filter.eventually_ge_atTop (1 : ℝ)] with T hcost hT
  intro L X N V hX hL hLX hXscale hN hV hcomparable hthreshold
  let kappa : ℝ := 4 * (2 ^ 120 : ℝ)
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 N V
  let Q : ℝ := routeTTrivialBoundaryBandCount T
  have hkappa : 1 ≤ kappa := by dsimp only [kappa]; norm_num
  have halpha : (1 + routeTGapMomentNu) / 2 ≤ alpha := by
    dsimp only [alpha]
    exact routeT_trivialCountBoundary_le_adaptive_of_threshold_le
      L X 60 (by norm_num) hX hN hthreshold
  have hA : V * (X : ℝ) ^ (1 - alpha) ≤
      heathBrownEligibleBoxCost L X 60 *
        kappa ^ routeTTrivialBoundaryDistortionExponent := by
    simpa only [alpha] using
      (routeTAdaptiveCellAmplitude_firstExclusionCost_trivialBoundary
        L X 60 (by norm_num) hX hN hV (by positivity : (0 : ℝ) < X)
          hkappa (le_refl _) (by simpa only [kappa] using hcomparable) halpha)
  have hcostFull :
      32 * Q * heathBrownEligibleBoxCost L X 60 *
          kappa ^ routeTTrivialBoundaryDistortionExponent ≤
        D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    simpa only [Q, kappa] using hcost L X hX.le hLX hXscale
  have hQnat : 0 < routeTTrivialBoundaryBandCount T :=
    routeTTrivialBoundaryBandCount_pos hT
  have hQ : 0 < Q := by dsimp only [Q]; exact_mod_cast hQnat
  have hfull : 32 * Q * (V * (X : ℝ) ^ (1 - alpha)) ≤
      D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    calc
      32 * Q * (V * (X : ℝ) ^ (1 - alpha)) ≤
          32 * Q * (heathBrownEligibleBoxCost L X 60 *
            kappa ^ routeTTrivialBoundaryDistortionExponent) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 32 * Q * heathBrownEligibleBoxCost L X 60 *
          kappa ^ routeTTrivialBoundaryDistortionExponent := by ring
      _ ≤ D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := hcostFull
  have hden : 0 < 4 * Q := by positivity
  have hdiv : 8 * (V * (X : ℝ) ^ (1 - alpha)) ≤
      (D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower) / (4 * Q) := by
    apply (le_div_iff₀ hden).2
    calc
      8 * (V * (X : ℝ) ^ (1 - alpha)) * (4 * Q) =
          32 * Q * (V * (X : ℝ) ^ (1 - alpha)) := by ring
      _ ≤ D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := hfull
  have htarget :
      (D * (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower) / (4 * Q) =
        ((D / (2 * Q)) / 2) *
          (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    field_simp
    ring
  rw [htarget] at hdiv
  simpa only [alpha, Q, mul_assoc] using hdiv

/-- The natural three-quarter receiver floor dominates the exact trivial-count boundary.
This comparison lets one use the stronger all-amplitude receiver without weakening the
first-alternative exclusion input. -/
theorem routeTTrivialBoundaryAmplitudeThreshold_le_threeQuarterThreshold
    (L X k : ℕ) {N : ℝ}
    (hk : 0 < k) (hN : 1 < N / (2 ^ (2 * k) : ℝ)) :
    routeTTrivialBoundaryAmplitudeThreshold L X k N ≤
      heathBrownEligibleBoxCost L X k *
        (N / (2 ^ (2 * k) : ℝ)) ^ (-(1 : ℝ) / 4) := by
  unfold routeTTrivialBoundaryAmplitudeThreshold
  have hbase : 1 ≤ N / (2 ^ (2 * k) : ℝ) := hN.le
  have hexp : (1 + routeTGapMomentNu) / 2 - 1 ≤ -(1 : ℝ) / 4 := by
    linarith [routeTGapMomentNu_lt_half]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hbase hexp)
    (heathBrownEligibleBoxCost_pos L X k hk).le

/-- A central shell with source cutoff independent of the physical Mellin cutoff forces the
second Maynard alternative through the natural `11/5` height ceiling.  This is the first receiver
theorem in the Route-T chain that preserves the fixed source scale introduced before the physical
base is varied. -/
theorem eventually_exists_routeT_fixedSource_adjacentDefect_central_gapSequence_forcedSecond_elevenFifths
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X n : ℕ} {mu M N H R delta : ℝ},
      1 < X → 1 ≤ L → L ≤ X → X < (L + 1) ^ 60 →
      T ^ mu = (X : ℝ) →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      (X : ℝ) / (2 ^ 120 : ℝ) ≤ M →
      1 < M / (2 ^ 120 : ℝ) →
      (X : ℝ) ≤ (4 * (2 ^ 120 : ℝ)) * (M / (2 ^ 120 : ℝ)) →
      0 < N → 0 < H → 0 < R → H ≤ R →
      1 ≤ delta → delta ≤ 2 →
      T + ((2 * n : ℕ) : ℝ) * delta ≤ 2 * T →
      (∀ y ∈ Set.Icc T (T + ((2 * n : ℕ) : ℝ) * delta),
        |y| ≤ N / (2 * R)) →
      D ≤ ‖routeTFixedSourceAdjacentIntervalPacket
        L X 60 T (mu / 120) M N R H 1 T
          (T + ((2 * n : ℕ) : ℝ) * delta)‖ →
      heathBrownWindowRelevantFixedPolylogBound L X 60 M 1 ≤
        (((2 ^ routeTTrivialBoundaryBandCount T : ℕ) : ℝ) *
          (heathBrownEligibleBoxCost L X 60 *
            (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4))) →
      (n : ℝ) * (heathBrownEligibleBoxCost L X 60 *
          (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4)) ≤ D / (16 * delta) →
      ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
        (∀ i, lam i + delta ≤ lam (i + 1)) ∧
        S ⊆ Finset.range n ∧ q < routeTTrivialBoundaryBandCount T ∧
        (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) ∧
        (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) *
          (heathBrownEligibleBoxCost L X 60 *
            (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4))) ≤
            ‖heathBrownWindowRelevantEligibleDyadicAggregate
              L X 60 T (mu / 120) M
                ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) ∧
        D / (16 * delta * (routeTTrivialBoundaryBandCount T : ℝ)) ≤
          (((2 ^ q : ℕ) : ℝ) *
            (heathBrownEligibleBoxCost L X 60 *
              (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4))) * (S.card : ℝ) ∧
        (S.card : ℝ) ≤ T * (T ^ mu) ^
          (1 + routeTGapMomentNu -
            2 * routeTAdaptiveCellAmplitude L X 60 M
              (((2 ^ q : ℕ) : ℝ) *
                (heathBrownEligibleBoxCost L X 60 *
                  (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4)))) := by
  filter_upwards [
    eventually_routeT_leftWindowRelevant_gapSequence_twoAlternative_elevenFifths
      routeTTrivialBoundaryReceiverLogPower,
    eventually_routeT_amplitudeBand_reparameterizedShell_firstExclusionThreshold_elevenFifths hD,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hreceiver hthresholdT hT
  intro L X n mu M N H R delta hX hL hLX hXL hXexact hLscale hmuLo hmuHi
    hlowCutoff hMbase hcomparable hN hH hR hHR hdelta hdeltaTwo hshellTop
    hcentral hdefect hcap hsmall
  let v : ℝ := heathBrownEligibleBoxCost L X 60 *
    (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4)
  have hM : 0 < M := by
    have hden : 0 < (2 ^ 120 : ℝ) := by positivity
    exact hden.trans ((one_lt_div hden).mp hMbase)
  have hv : 0 < v := by
    dsimp only [v]
    exact mul_pos (heathBrownEligibleBoxCost_pos L X 60 (by norm_num))
      (Real.rpow_pos_of_pos (by positivity) _)
  have hQ : 0 < routeTTrivialBoundaryBandCount T :=
    routeTTrivialBoundaryBandCount_pos hT.le
  obtain ⟨lam, S, q, hgap, hS, hq, hmem, hlarge, hmass⟩ :=
    exists_gap_sequence_dyadic_superlevel_of_fixedSource_adjacent_defect_central
      L X 60 T (mu / 120) M hX.le hM hN hH hR hHR
        (zero_lt_one.trans_le hdelta) hD hv hQ hcentral hdefect
        (by simpa only [v] using hcap) (by simpa only [v] using hsmall)
  have hdelta0 : 0 ≤ delta := zero_le_one.trans hdelta
  have hmemShell : ∀ j < n,
      lam j ∈ Set.Icc T (T + ((2 * n : ℕ) : ℝ) * delta) := by
    intro j hj
    rcases hmem j hj with heven | hodd
    · constructor
      · have hcoeff : (0 : ℝ) ≤ ((2 * j : ℕ) : ℝ) := Nat.cast_nonneg _
        exact (le_add_of_nonneg_right (mul_nonneg hcoeff hdelta0)).trans heven.1
      · have hcast : (((2 * j : ℕ) : ℝ) + 1) ≤ ((2 * n : ℕ) : ℝ) := by
          exact_mod_cast (show 2 * j + 1 ≤ 2 * n by omega)
        exact heven.2.trans (by
          simpa only [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_right hcast hdelta0) T)
    · constructor
      · have hcoeff : (0 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        exact (le_add_of_nonneg_right (mul_nonneg hcoeff hdelta0)).trans hodd.1
      · have hcast : (((2 * j + 1 : ℕ) : ℝ) + 1) ≤ ((2 * n : ℕ) : ℝ) := by
          exact_mod_cast (show (2 * j + 1) + 1 ≤ 2 * n by omega)
        exact hodd.2.trans (by
          simpa only [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_right hcast hdelta0) T)
  have hband : ∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T := by
    intro r hr
    have hrn := Finset.mem_range.mp (hS hr)
    have hm := hmemShell r hrn
    exact ⟨hm.1, hm.2.trans hshellTop⟩
  have hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T := by
    intro r hr s hs
    have hrb := hband r hr
    have hsb := hband s hs
    rw [abs_le]
    constructor <;> linarith
  have hnT : (n : ℝ) ≤ T := by
    have hnleTwoN : (n : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ 2 * n by omega)
    have htwoN0 : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hscale : ((2 * n : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) * delta := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdelta htwoN0
    have hmul : ((2 * n : ℕ) : ℝ) * delta ≤ T := by linarith
    exact hnleTwoN.trans (hscale.trans hmul)
  have hdeltaTop : delta ≤ 2 * T := by
    calc
      delta ≤ 2 := hdeltaTwo
      _ = 2 * 1 := by ring
      _ ≤ 2 * T := mul_le_mul_of_nonneg_left hT.le (by norm_num)
  let V : ℝ := (((2 ^ q : ℕ) : ℝ) * v)
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 M V
  let Q : ℝ := routeTTrivialBoundaryBandCount T
  have hV : 0 < V := by dsimp only [V]; positivity
  have hvV : v ≤ V := by
    have hp : (1 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_two_pow
    dsimp only [V]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hv.le
  have htrivialV : routeTTrivialBoundaryAmplitudeThreshold L X 60 M ≤ V :=
    (routeTTrivialBoundaryAmplitudeThreshold_le_threeQuarterThreshold
      L X 60 (by norm_num) hMbase).trans (by simpa only [v] using hvV)
  have halt : IsRouteTMaynardTwoAlternative routeTTrivialBoundaryReceiverLogPower
      (S.card : ℝ) T (T ^ mu) alpha := by
    dsimp only [alpha]
    apply hreceiver hX hL hXL (by rw [hXexact]) hLscale hmuLo hmuHi
      hlowCutoff hMbase hV
    · simpa only [V, v] using hvV
    · exact hdelta
    · exact hdeltaTop
    · exact hnT
    · exact hS
    · exact hband
    · exact hgap
    · exact hdiam
    · simpa only [V, v] using hlarge
  have hXscaleTop : (X : ℝ) ≤ T ^ (11 / 5 : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hmuHi
    simpa only [hXexact] using hpow
  have hthreshold := hthresholdT hX hL hLX hXscaleTop hMbase hV hcomparable
    htrivialV
  have hthreshold' : 8 * V * (T ^ mu) ^ (1 - alpha) ≤
      ((D / (2 * Q)) / 2) *
        (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    rw [hXexact]
    simpa only [V, alpha, Q] using hthreshold
  have hQreal : 0 < Q := by dsimp only [Q]; exact_mod_cast hQ
  have hsecond : (S.card : ℝ) ≤ T * (T ^ mu) ^
      (1 + routeTGapMomentNu - 2 * alpha) := by
    apply routeT_second_alternative_of_shell_mass hD hV hQreal hdelta hdeltaTwo
      (Real.log_nonneg hT.le) hthreshold'
    · simpa only [V, v, Q] using hmass
    · exact halt
  refine ⟨lam, S, q, hgap, hS, hq, hband, ?_, ?_, ?_⟩
  · simpa only [v] using hlarge
  · simpa only [v] using hmass
  · simpa only [V, v, alpha] using hsecond

/-- Arbitrary central-shell form of fixed-source forced second-alternative extraction.  Exact
adaptive even cells preserve the entire signed defect, so no endpoint loss or alignment premise
survives; source and physical Mellin cutoffs remain independent. -/
theorem eventually_exists_routeT_fixedSource_adjacentDefect_centralInterval_forcedSecond_elevenFifths
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X : ℕ} {mu M N H R b : ℝ},
      1 < X → 1 ≤ L → L ≤ X → X < (L + 1) ^ 60 →
      T ^ mu = (X : ℝ) →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      (X : ℝ) / (2 ^ 120 : ℝ) ≤ M →
      1 < M / (2 ^ 120 : ℝ) →
      (X : ℝ) ≤ (4 * (2 ^ 120 : ℝ)) * (M / (2 ^ 120 : ℝ)) →
      0 < N → 0 < H → 0 < R → H ≤ R →
      T + 2 ≤ b → b ≤ 2 * T →
      (∀ y ∈ Set.Icc T b, |y| ≤ N / (2 * R)) →
      D ≤ ‖routeTFixedSourceAdjacentIntervalPacket
        L X 60 T (mu / 120) M N R H 1 T b‖ →
      heathBrownWindowRelevantFixedPolylogBound L X 60 M 1 ≤
        (((2 ^ routeTTrivialBoundaryBandCount T : ℕ) : ℝ) *
          (heathBrownEligibleBoxCost L X 60 *
            (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4))) →
      (b - T) * (heathBrownEligibleBoxCost L X 60 *
          (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4)) ≤ D / 8 →
      ∃ n : ℕ, ∃ delta : ℝ, ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
        0 < n ∧ 1 ≤ delta ∧ delta ≤ 2 ∧
        b = T + ((2 * n : ℕ) : ℝ) * delta ∧
        (∀ i, lam i + delta ≤ lam (i + 1)) ∧
        S ⊆ Finset.range n ∧ q < routeTTrivialBoundaryBandCount T ∧
        (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) ∧
        (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) *
          (heathBrownEligibleBoxCost L X 60 *
            (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4))) ≤
            ‖heathBrownWindowRelevantEligibleDyadicAggregate
              L X 60 T (mu / 120) M
                ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) ∧
        D / (32 * (routeTTrivialBoundaryBandCount T : ℝ)) ≤
          (((2 ^ q : ℕ) : ℝ) *
            (heathBrownEligibleBoxCost L X 60 *
              (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4))) * (S.card : ℝ) ∧
        (S.card : ℝ) ≤ T * (T ^ mu) ^
          (1 + routeTGapMomentNu -
            2 * routeTAdaptiveCellAmplitude L X 60 M
              (((2 ^ q : ℕ) : ℝ) *
                (heathBrownEligibleBoxCost L X 60 *
                  (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4)))) := by
  filter_upwards [
    eventually_exists_routeT_fixedSource_adjacentDefect_central_gapSequence_forcedSecond_elevenFifths
      hD] with T hforced
  intro L X mu M N H R b hX hL hLX hXL hXexact hLscale hmuLo hmuHi
    hlowCutoff hMbase hcomparable hN hH hR hHR hlength htop hcentral hdefect
    hcap hbase
  obtain ⟨n, delta, hn, hdelta, hdeltaTwo, hb⟩ :=
    exists_even_cells_unit_two_of_two_le_length hlength
  have hshellTop : T + ((2 * n : ℕ) : ℝ) * delta ≤ 2 * T := by
    rw [← hb]
    exact htop
  have hcentral' : ∀ y ∈ Set.Icc T
      (T + ((2 * n : ℕ) : ℝ) * delta), |y| ≤ N / (2 * R) := by
    simpa only [← hb] using hcentral
  have hdefect' : D ≤ ‖routeTFixedSourceAdjacentIntervalPacket
      L X 60 T (mu / 120) M N R H 1 T
        (T + ((2 * n : ℕ) : ℝ) * delta)‖ := by
    simpa only [← hb] using hdefect
  let v : ℝ := heathBrownEligibleBoxCost L X 60 *
    (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4)
  have hbase' : 2 * (n : ℝ) * delta * v ≤ D / 8 := by
    rw [hb] at hbase
    push_cast at hbase
    convert hbase using 1
    ring
  have hsmall : (n : ℝ) * v ≤ D / (16 * delta) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * delta)).2
    calc
      (n : ℝ) * v * (16 * delta) =
          8 * (2 * (n : ℝ) * delta * v) := by ring
      _ ≤ 8 * (D / 8) := mul_le_mul_of_nonneg_left hbase' (by norm_num)
      _ = D := by ring
  obtain ⟨lam, S, q, hgap, hS, hq, hband, hlarge, hmass, hsecond⟩ :=
    hforced hX hL hLX hXL hXexact hLscale hmuLo hmuHi hlowCutoff hMbase
      hcomparable hN hH hR hHR hdelta hdeltaTwo hshellTop hcentral' hdefect'
      hcap (by simpa only [v] using hsmall)
  let Q : ℝ := routeTTrivialBoundaryBandCount T
  have hTone : (1 : ℝ) ≤ T := by linarith [hlength, htop]
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast routeTTrivialBoundaryBandCount_pos hTone
  have hdenSmall : 0 < 16 * delta * Q :=
    mul_pos (mul_pos (by norm_num) (zero_lt_one.trans_le hdelta)) hQ
  have hdeltaBound : 16 * delta ≤ (32 : ℝ) :=
    (mul_le_mul_of_nonneg_left hdeltaTwo (by norm_num)).trans_eq (by ring)
  have hdenLarge : 16 * delta * Q ≤ 32 * Q :=
    mul_le_mul_of_nonneg_right hdeltaBound hQ.le
  have hmassUniform : D / (32 * Q) ≤ D / (16 * delta * Q) :=
    div_le_div_of_nonneg_left hD.le hdenSmall hdenLarge
  refine ⟨n, delta, lam, S, q, hn, hdelta, hdeltaTwo, hb, hgap, hS, hq,
    hband, hlarge, ?_, hsecond⟩
  simpa only [Q] using hmassUniform.trans hmass

/-- Quadratic tail decay converts raw defect mass into receiver-normalized selected mass. -/
theorem routeT_tailKernelCost_normalizes_shellMass
    {D B delta K Q : ℝ}
    (hD : 0 < D) (hdelta : 0 < delta) (hK : 0 < K) (hQ : 0 < Q)
    (hcost : K ≤ 4 * B / D) :
    D / (16 * delta * Q) ≤ B / (4 * delta * K * Q) := by
  have hDK : D * K ≤ 4 * B := by
    have hout := (le_div_iff₀ hD).mp hcost
    simpa only [mul_comm] using hout
  have hscale : 0 ≤ 4 * delta * Q := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hDK hscale
  have hdenLeft : 0 < 16 * delta * Q := by positivity
  have hdenRight : 0 < 4 * delta * K * Q := by positivity
  apply (div_le_div_iff₀ hdenLeft hdenRight).2
  convert hscaled using 1 <;> ring

/-- Any three-quarter-normalized spaced source sequence with retained shell mass forces Maynard's
second alternative through `mu ≤ 11/5`.  Kernel localization is deliberately absent from this
statement, so central and quadratic-tail extraction share one receiver closure. -/
theorem eventually_routeT_threeQuarter_gapSequence_forcedSecond_elevenFifths
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu M V delta : ℝ},
      1 < X → 1 ≤ L → L ≤ X → X < (L + 1) ^ 60 →
      T ^ mu = (X : ℝ) →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      (X : ℝ) / (2 ^ 120 : ℝ) ≤ M →
      1 < M / (2 ^ 120 : ℝ) →
      (X : ℝ) ≤ (4 * (2 ^ 120 : ℝ)) * (M / (2 ^ 120 : ℝ)) →
      0 < V →
      heathBrownEligibleBoxCost L X 60 *
        (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4) ≤ V →
      1 ≤ delta → delta ≤ 2 → (K : ℝ) ≤ T →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      (∀ r ∈ S, V ≤
        ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) M
            ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      D / (16 * delta * (routeTTrivialBoundaryBandCount T : ℝ)) ≤
        V * (S.card : ℝ) →
      (S.card : ℝ) ≤ T * (T ^ mu) ^
        (1 + routeTGapMomentNu -
          2 * routeTAdaptiveCellAmplitude L X 60 M V) := by
  filter_upwards [
    eventually_routeT_leftWindowRelevant_gapSequence_twoAlternative_elevenFifths
      routeTTrivialBoundaryReceiverLogPower,
    eventually_routeT_amplitudeBand_reparameterizedShell_firstExclusionThreshold_elevenFifths hD,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hreceiver hthresholdT hT
  intro L X K mu M V delta hX hL hLX hXL hXexact hLscale hmuLo hmuHi
    hlowCutoff hMbase hcomparable hV hlow hdelta hdeltaTwo hK S hS lam hband
    hgap hdiam hlarge hmass
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 M V
  let Q : ℝ := routeTTrivialBoundaryBandCount T
  have hdeltaTop : delta ≤ 2 * T := by
    calc
      delta ≤ 2 := hdeltaTwo
      _ = 2 * 1 := by ring
      _ ≤ 2 * T := mul_le_mul_of_nonneg_left hT.le (by norm_num)
  have halt : IsRouteTMaynardTwoAlternative routeTTrivialBoundaryReceiverLogPower
      (S.card : ℝ) T (T ^ mu) alpha := by
    dsimp only [alpha]
    exact hreceiver hX hL hXL (by rw [hXexact]) hLscale hmuLo hmuHi
      hlowCutoff hMbase hV hlow hdelta hdeltaTop hK S hS lam hband hgap hdiam
        hlarge
  have htrivialV : routeTTrivialBoundaryAmplitudeThreshold L X 60 M ≤ V :=
    (routeTTrivialBoundaryAmplitudeThreshold_le_threeQuarterThreshold
      L X 60 (by norm_num) hMbase).trans hlow
  have hXscaleTop : (X : ℝ) ≤ T ^ (11 / 5 : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hmuHi
    simpa only [hXexact] using hpow
  have hthreshold := hthresholdT hX hL hLX hXscaleTop hMbase hV hcomparable
    htrivialV
  have hthreshold' : 8 * V * (T ^ mu) ^ (1 - alpha) ≤
      ((D / (2 * Q)) / 2) *
        (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    rw [hXexact]
    simpa only [alpha, Q] using hthreshold
  have hQnat : 0 < routeTTrivialBoundaryBandCount T :=
    routeTTrivialBoundaryBandCount_pos hT.le
  have hQ : 0 < Q := by dsimp only [Q]; exact_mod_cast hQnat
  apply routeT_second_alternative_of_shell_mass hD hV hQ hdelta hdeltaTwo
    (Real.log_nonneg hT.le) hthreshold'
  · simpa only [Q] using hmass
  · exact halt

/-- Quadratic-tail fixed-source forcing.  Whenever Mellin tail decay converts raw packet defect
`B` into fixed receiver mass `D`, exact cell extraction and the `11/5` receiver force Maynard's
second alternative.  The source cutoff and physical Mellin cutoff are independent. -/
theorem exists_eventually_routeT_fixedSource_adjacentDefect_tail_gapSequence_forcedSecond_elevenFifths
    {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ᶠ T : ℝ in atTop,
        ∀ {L X n : ℕ} {mu M N H R U delta B : ℝ},
        1 < X → 1 ≤ L → L ≤ X → X < (L + 1) ^ 60 →
        T ^ mu = (X : ℝ) →
        (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
        4 / 3 ≤ mu → mu ≤ 11 / 5 →
        (X : ℝ) / (2 ^ 120 : ℝ) ≤ M →
        1 < M / (2 ^ 120 : ℝ) →
        (X : ℝ) ≤ (4 * (2 ^ 120 : ℝ)) * (M / (2 ^ 120 : ℝ)) →
        0 < N → 0 < H → 0 < R → H ≤ R → R ≤ 2 * H → R ≤ N →
        0 < U → 1 ≤ delta → delta ≤ 2 → 0 < B →
        T + ((2 * n : ℕ) : ℝ) * delta ≤ 2 * T →
        (∀ y ∈ Set.Icc T (T + ((2 * n : ℕ) : ℝ) * delta), U ≤ |y|) →
        65 * C * (N / R) ^ 2 / U ^ 2 ≤ 4 * B / D →
        B ≤ ‖routeTFixedSourceAdjacentIntervalPacket
          L X 60 T (mu / 120) M N R H 1 T
            (T + ((2 * n : ℕ) : ℝ) * delta)‖ →
        heathBrownWindowRelevantFixedPolylogBound L X 60 M 1 ≤
          (((2 ^ routeTTrivialBoundaryBandCount T : ℕ) : ℝ) *
            (heathBrownEligibleBoxCost L X 60 *
              (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4))) →
        (n : ℝ) * (heathBrownEligibleBoxCost L X 60 *
            (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4)) ≤
          B / (4 * delta * (65 * C * (N / R) ^ 2 / U ^ 2)) →
        ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
          (∀ i, lam i + delta ≤ lam (i + 1)) ∧
          S ⊆ Finset.range n ∧ q < routeTTrivialBoundaryBandCount T ∧
          (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) ∧
          (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) *
            (heathBrownEligibleBoxCost L X 60 *
              (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4))) ≤
              ‖heathBrownWindowRelevantEligibleDyadicAggregate
                L X 60 T (mu / 120) M
                  ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) ∧
          D / (16 * delta * (routeTTrivialBoundaryBandCount T : ℝ)) ≤
            (((2 ^ q : ℕ) : ℝ) *
              (heathBrownEligibleBoxCost L X 60 *
                (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4))) * (S.card : ℝ) ∧
          (S.card : ℝ) ≤ T * (T ^ mu) ^
            (1 + routeTGapMomentNu -
              2 * routeTAdaptiveCellAmplitude L X 60 M
                (((2 ^ q : ℕ) : ℝ) *
                  (heathBrownEligibleBoxCost L X 60 *
                    (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4)))) := by
  obtain ⟨C, hC, hextract⟩ :=
    exists_gap_sequence_dyadic_superlevel_of_fixedSource_adjacent_defect_tail
  refine ⟨C, hC, ?_⟩
  filter_upwards [
    eventually_routeT_threeQuarter_gapSequence_forcedSecond_elevenFifths hD,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hforce hT
  intro L X n mu M N H R U delta B hX hL hLX hXL hXexact hLscale hmuLo
    hmuHi hlowCutoff hMbase hcomparable hN hH hR hHR hRH hRN hU hdelta
    hdeltaTwo hB hshellTop htail hcost hdefect hcap hsmall
  let v : ℝ := heathBrownEligibleBoxCost L X 60 *
    (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4)
  let Ktail : ℝ := 65 * C * (N / R) ^ 2 / U ^ 2
  have hM : 0 < M := by
    have hden : 0 < (2 ^ 120 : ℝ) := by positivity
    exact hden.trans ((one_lt_div hden).mp hMbase)
  have hv : 0 < v := by
    dsimp only [v]
    exact mul_pos (heathBrownEligibleBoxCost_pos L X 60 (by norm_num))
      (Real.rpow_pos_of_pos (by positivity) _)
  have hKtail : 0 < Ktail := by
    dsimp only [Ktail]
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    positivity
  have hQ : 0 < routeTTrivialBoundaryBandCount T :=
    routeTTrivialBoundaryBandCount_pos hT.le
  have hdefect' : B ≤ ‖∫ y in T..(T + ((2 * n : ℕ) : ℝ) * delta),
      heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (mu / 120) M
          ((1 : ℂ) + (y : ℝ) * Complex.I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * Complex.I))‖ := by
    simpa [routeTFixedSourceAdjacentIntervalPacket,
      routeTFixedSourceAdjacentIntegrand] using hdefect
  obtain ⟨lam, S, q, hgap, hS, hq, hmem, hlarge, hmassRaw⟩ :=
    hextract L X 60 T (mu / 120) M hX.le hM hN hH hR hHR hRH hRN hU
      (zero_lt_one.trans_le hdelta) hB hv hQ htail hdefect'
        (by simpa only [v] using hcap) (by simpa only [v] using hsmall)
  have hdelta0 : 0 ≤ delta := zero_le_one.trans hdelta
  have hmemShell : ∀ j < n,
      lam j ∈ Set.Icc T (T + ((2 * n : ℕ) : ℝ) * delta) := by
    intro j hj
    rcases hmem j hj with heven | hodd
    · constructor
      · have hcoeff : (0 : ℝ) ≤ ((2 * j : ℕ) : ℝ) := Nat.cast_nonneg _
        exact (le_add_of_nonneg_right (mul_nonneg hcoeff hdelta0)).trans heven.1
      · have hcast : (((2 * j : ℕ) : ℝ) + 1) ≤ ((2 * n : ℕ) : ℝ) := by
          exact_mod_cast (show 2 * j + 1 ≤ 2 * n by omega)
        exact heven.2.trans (by
          simpa only [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_right hcast hdelta0) T)
    · constructor
      · have hcoeff : (0 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        exact (le_add_of_nonneg_right (mul_nonneg hcoeff hdelta0)).trans hodd.1
      · have hcast : (((2 * j + 1 : ℕ) : ℝ) + 1) ≤ ((2 * n : ℕ) : ℝ) := by
          exact_mod_cast (show (2 * j + 1) + 1 ≤ 2 * n by omega)
        exact hodd.2.trans (by
          simpa only [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_right hcast hdelta0) T)
  have hband : ∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T := by
    intro r hr
    have hrn := Finset.mem_range.mp (hS hr)
    have hm := hmemShell r hrn
    exact ⟨hm.1, hm.2.trans hshellTop⟩
  have hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T := by
    intro r hr s hs
    have hrb := hband r hr
    have hsb := hband s hs
    rw [abs_le]
    constructor <;> linarith
  have hnT : (n : ℝ) ≤ T := by
    have hnleTwoN : (n : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ 2 * n by omega)
    have htwoN0 : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hscale : ((2 * n : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) * delta := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdelta htwoN0
    have hmul : ((2 * n : ℕ) : ℝ) * delta ≤ T := by linarith
    exact hnleTwoN.trans (hscale.trans hmul)
  let V : ℝ := (((2 ^ q : ℕ) : ℝ) * v)
  have hV : 0 < V := by dsimp only [V]; positivity
  have hvV : v ≤ V := by
    have hp : (1 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_two_pow
    dsimp only [V]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hv.le
  have hmassRaw' : B / (4 * delta * Ktail *
      (routeTTrivialBoundaryBandCount T : ℝ)) ≤ V * (S.card : ℝ) := by
    simpa only [Ktail, V, v] using hmassRaw
  have hmass : D / (16 * delta * (routeTTrivialBoundaryBandCount T : ℝ)) ≤
      V * (S.card : ℝ) := by
    apply (routeT_tailKernelCost_normalizes_shellMass hD
      (zero_lt_one.trans_le hdelta) hKtail (by exact_mod_cast hQ)
      (by simpa only [Ktail] using hcost)).trans
    exact hmassRaw'
  have hsecond := hforce hX hL hLX hXL hXexact hLscale hmuLo hmuHi
    hlowCutoff hMbase hcomparable hV (by simpa only [v] using hvV)
      hdelta hdeltaTwo hnT S hS lam hband hgap hdiam
        (by simpa only [V, v] using hlarge) hmass
  refine ⟨lam, S, q, hgap, hS, hq, hband, ?_, ?_, ?_⟩
  · simpa only [v] using hlarge
  · simpa only [V, v] using hmass
  · simpa only [V, v] using hsecond

/-- Arbitrary outer-shell fixed-source forcing.  Quadratic Mellin decay pays the tail localization
cost, exact adaptive even cells preserve the full signed interval defect, and the resulting source
sequence is forced into Maynard's second alternative through `mu ≤ 11/5`. -/
theorem exists_eventually_routeT_fixedSource_adjacentDefect_tailInterval_forcedSecond_elevenFifths
    {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ᶠ T : ℝ in atTop,
        ∀ {L X : ℕ} {mu M N H R U b B : ℝ},
        1 < X → 1 ≤ L → L ≤ X → X < (L + 1) ^ 60 →
        T ^ mu = (X : ℝ) →
        (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
        4 / 3 ≤ mu → mu ≤ 11 / 5 →
        (X : ℝ) / (2 ^ 120 : ℝ) ≤ M →
        1 < M / (2 ^ 120 : ℝ) →
        (X : ℝ) ≤ (4 * (2 ^ 120 : ℝ)) * (M / (2 ^ 120 : ℝ)) →
        0 < N → 0 < H → 0 < R → H ≤ R → R ≤ 2 * H → R ≤ N →
        0 < U → 0 < B → T + 2 ≤ b → b ≤ 2 * T →
        (∀ y ∈ Set.Icc T b, U ≤ |y|) →
        65 * C * (N / R) ^ 2 / U ^ 2 ≤ 4 * B / D →
        B ≤ ‖routeTFixedSourceAdjacentIntervalPacket
          L X 60 T (mu / 120) M N R H 1 T b‖ →
        heathBrownWindowRelevantFixedPolylogBound L X 60 M 1 ≤
          (((2 ^ routeTTrivialBoundaryBandCount T : ℕ) : ℝ) *
            (heathBrownEligibleBoxCost L X 60 *
              (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4))) →
        (b - T) * (heathBrownEligibleBoxCost L X 60 *
            (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4)) ≤
          B / (2 * (65 * C * (N / R) ^ 2 / U ^ 2)) →
        ∃ n : ℕ, ∃ delta : ℝ, ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
          0 < n ∧ 1 ≤ delta ∧ delta ≤ 2 ∧
          b = T + ((2 * n : ℕ) : ℝ) * delta ∧
          (∀ i, lam i + delta ≤ lam (i + 1)) ∧
          S ⊆ Finset.range n ∧ q < routeTTrivialBoundaryBandCount T ∧
          (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) ∧
          (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) *
            (heathBrownEligibleBoxCost L X 60 *
              (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4))) ≤
              ‖heathBrownWindowRelevantEligibleDyadicAggregate
                L X 60 T (mu / 120) M
                  ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) ∧
          D / (32 * (routeTTrivialBoundaryBandCount T : ℝ)) ≤
            (((2 ^ q : ℕ) : ℝ) *
              (heathBrownEligibleBoxCost L X 60 *
                (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4))) * (S.card : ℝ) ∧
          (S.card : ℝ) ≤ T * (T ^ mu) ^
            (1 + routeTGapMomentNu -
              2 * routeTAdaptiveCellAmplitude L X 60 M
                (((2 ^ q : ℕ) : ℝ) *
                  (heathBrownEligibleBoxCost L X 60 *
                    (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4)))) := by
  obtain ⟨C, hC, hgapForced⟩ :=
    exists_eventually_routeT_fixedSource_adjacentDefect_tail_gapSequence_forcedSecond_elevenFifths
      hD
  refine ⟨C, hC, ?_⟩
  filter_upwards [hgapForced] with T hforced
  intro L X mu M N H R U b B hX hL hLX hXL hXexact hLscale hmuLo hmuHi
    hlowCutoff hMbase hcomparable hN hH hR hHR hRH hRN hU hB hlength htop
    htail hcost hdefect hcap hbase
  obtain ⟨n, delta, hn, hdelta, hdeltaTwo, hb⟩ :=
    exists_even_cells_unit_two_of_two_le_length hlength
  have hshellTop : T + ((2 * n : ℕ) : ℝ) * delta ≤ 2 * T := by
    rw [← hb]
    exact htop
  have htail' : ∀ y ∈ Set.Icc T
      (T + ((2 * n : ℕ) : ℝ) * delta), U ≤ |y| := by
    simpa only [← hb] using htail
  have hdefect' : B ≤ ‖routeTFixedSourceAdjacentIntervalPacket
      L X 60 T (mu / 120) M N R H 1 T
        (T + ((2 * n : ℕ) : ℝ) * delta)‖ := by
    simpa only [← hb] using hdefect
  let v : ℝ := heathBrownEligibleBoxCost L X 60 *
    (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4)
  let Ktail : ℝ := 65 * C * (N / R) ^ 2 / U ^ 2
  have hKtail : 0 < Ktail := by
    dsimp only [Ktail]
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    positivity
  have hbase' : 2 * (n : ℝ) * delta * v ≤ B / (2 * Ktail) := by
    rw [hb] at hbase
    push_cast at hbase
    dsimp only [v, Ktail]
    convert hbase using 1
    ring
  have hsmall : (n : ℝ) * v ≤ B / (4 * delta * Ktail) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * delta * Ktail)).2
    have hscale : 0 ≤ 2 * Ktail := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hbase' hscale
    calc
      (n : ℝ) * v * (4 * delta * Ktail) =
          (2 * (n : ℝ) * delta * v) * (2 * Ktail) := by ring
      _ ≤ (B / (2 * Ktail)) * (2 * Ktail) := hscaled
      _ = B := by field_simp
  obtain ⟨lam, S, q, hgap, hS, hq, hband, hlarge, hmass, hsecond⟩ :=
    hforced hX hL hLX hXL hXexact hLscale hmuLo hmuHi hlowCutoff hMbase
      hcomparable hN hH hR hHR hRH hRN hU hdelta hdeltaTwo hB hshellTop
        htail' (by simpa only [Ktail] using hcost) hdefect' hcap
          (by simpa only [v, Ktail] using hsmall)
  let Q : ℝ := routeTTrivialBoundaryBandCount T
  have hTone : (1 : ℝ) ≤ T := by linarith [hlength, htop]
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast routeTTrivialBoundaryBandCount_pos hTone
  have hdenSmall : 0 < 16 * delta * Q :=
    mul_pos (mul_pos (by norm_num) (zero_lt_one.trans_le hdelta)) hQ
  have hdeltaBound : 16 * delta ≤ (32 : ℝ) :=
    (mul_le_mul_of_nonneg_left hdeltaTwo (by norm_num)).trans_eq (by ring)
  have hdenLarge : 16 * delta * Q ≤ 32 * Q :=
    mul_le_mul_of_nonneg_right hdeltaBound hQ.le
  have hmassUniform : D / (32 * Q) ≤ D / (16 * delta * Q) :=
    div_le_div_of_nonneg_left hD.le hdenSmall hdenLarge
  refine ⟨n, delta, lam, S, q, hn, hdelta, hdeltaTwo, hb, hgap, hS, hq,
    hband, hlarge, ?_, hsecond⟩
  simpa only [Q] using hmassUniform.trans hmass

/-- A bounded enlargement of support costs at most its distortion in the receiver's first
alternative, uniformly across both adaptive-amplitude branches.  For amplitudes above one the
power is antitone, so the distortion disappears rather than grows. -/
theorem rpow_receiverScale_le_distortion_mul_support_rpow
    {X Y kappa alpha : ℝ}
    (hX : 0 < X) (hXY : X ≤ Y) (hY : Y ≤ kappa * X)
    (hkappa : 1 ≤ kappa) (halpha : 3 / 4 ≤ alpha) :
    Y ^ (1 - alpha) ≤ kappa * X ^ (1 - alpha) := by
  by_cases ha : alpha ≤ 1
  · have he0 : 0 ≤ 1 - alpha := by linarith
    have he1 : 1 - alpha ≤ 1 := by linarith
    have hkappa0 : 0 ≤ kappa := zero_le_one.trans hkappa
    have hpow : Y ^ (1 - alpha) ≤ (kappa * X) ^ (1 - alpha) :=
      Real.rpow_le_rpow (hX.le.trans hXY) hY he0
    have hkpow : kappa ^ (1 - alpha) ≤ kappa := by
      calc
        kappa ^ (1 - alpha) ≤ kappa ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hkappa he1
        _ = kappa := Real.rpow_one _
    calc
      Y ^ (1 - alpha) ≤ (kappa * X) ^ (1 - alpha) := hpow
      _ = kappa ^ (1 - alpha) * X ^ (1 - alpha) :=
        Real.mul_rpow hkappa0 hX.le
      _ ≤ kappa * X ^ (1 - alpha) :=
        mul_le_mul_of_nonneg_right hkpow (Real.rpow_nonneg hX.le _)
  · have he : 1 - alpha ≤ 0 := by linarith
    have hanti : Y ^ (1 - alpha) ≤ X ^ (1 - alpha) :=
      Real.rpow_le_rpow_of_nonpos hX hXY he
    calc
      Y ^ (1 - alpha) ≤ X ^ (1 - alpha) := hanti
      _ = 1 * X ^ (1 - alpha) := by ring
      _ ≤ kappa * X ^ (1 - alpha) :=
        mul_le_mul_of_nonneg_right hkappa (Real.rpow_nonneg hX.le _)

/-- First-alternative exclusion survives a bounded mismatch between literal support `X` and
receiver scale `Y`.  This removes the false equality assumption exposed by canonical ceiling
support while retaining the full `11/5` receiver range. -/
theorem eventually_routeT_amplitudeBand_boundedReceiverScale_firstExclusionThreshold_elevenFifths
    {D kappa : ℝ} (hD : 0 < D) (hkappa : 1 ≤ kappa) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X : ℕ} {N V Y : ℝ},
      1 < X → 1 ≤ L → L ≤ X → (X : ℝ) ≤ T ^ (11 / 5 : ℝ) →
      1 < N / (2 ^ 120 : ℝ) → 0 < V →
      (X : ℝ) ≤ (4 * (2 ^ 120 : ℝ)) * (N / (2 ^ 120 : ℝ)) →
      heathBrownEligibleBoxCost L X 60 *
        (N / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4) ≤ V →
      (X : ℝ) ≤ Y → Y ≤ kappa * (X : ℝ) →
      8 * V * Y ^ (1 - routeTAdaptiveCellAmplitude L X 60 N V) ≤
        ((D / (2 * (routeTTrivialBoundaryBandCount T : ℝ))) / 2) *
          (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
  have hDscaled : 0 < D / kappa := div_pos hD (zero_lt_one.trans_le hkappa)
  filter_upwards [
    eventually_routeT_amplitudeBand_reparameterizedShell_firstExclusionThreshold_elevenFifths
      hDscaled,
    Filter.eventually_ge_atTop (1 : ℝ)] with T hthresholdT hT
  intro L X N V Y hX hL hLX hXscale hN hV hcomparable hlow hXY hY
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 N V
  let Q : ℝ := routeTTrivialBoundaryBandCount T
  have halpha : 3 / 4 ≤ alpha := by
    dsimp only [alpha]
    exact routeTAdaptiveCellAmplitude_threeQuarter_le L X 60
      (by norm_num) hX hN hV hlow
  have hsupportPos : 0 < (X : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hX)
  have hdistort : Y ^ (1 - alpha) ≤
      kappa * (X : ℝ) ^ (1 - alpha) :=
    rpow_receiverScale_le_distortion_mul_support_rpow
      hsupportPos hXY hY hkappa halpha
  have htrivial : routeTTrivialBoundaryAmplitudeThreshold L X 60 N ≤ V :=
    (routeTTrivialBoundaryAmplitudeThreshold_le_threeQuarterThreshold
      L X 60 (by norm_num) hN).trans hlow
  have hbase := hthresholdT hX hL hLX hXscale hN hV hcomparable htrivial
  have hleft : 8 * V * Y ^ (1 - alpha) ≤
      kappa * (8 * V * (X : ℝ) ^ (1 - alpha)) := by
    calc
      8 * V * Y ^ (1 - alpha) ≤ 8 * V *
          (kappa * (X : ℝ) ^ (1 - alpha)) :=
        mul_le_mul_of_nonneg_left hdistort (by positivity)
      _ = kappa * (8 * V * (X : ℝ) ^ (1 - alpha)) := by ring
  have hscaled := mul_le_mul_of_nonneg_left hbase (zero_le_one.trans hkappa)
  have hQnat : 0 < routeTTrivialBoundaryBandCount T :=
    routeTTrivialBoundaryBandCount_pos hT
  have hQ : 0 < Q := by dsimp only [Q]; exact_mod_cast hQnat
  calc
    8 * V * Y ^ (1 - alpha) ≤
        kappa * (8 * V * (X : ℝ) ^ (1 - alpha)) := hleft
    _ ≤ kappa * (((D / kappa) / (2 * Q) / 2) *
        (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower) := by
      simpa only [alpha, Q] using hscaled
    _ = ((D / (2 * Q)) / 2) *
        (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
      field_simp

/-- Receiver forcing with literal support only comparable to the eligibility scale.  This is the
quantifier-correct form needed by canonical Route-T packets, whose ceiling support is not an exact
real height power. -/
theorem eventually_routeT_threeQuarter_gapSequence_boundedSupport_forcedSecond_elevenFifths
    {D kappa : ℝ} (hD : 0 < D) (hkappa : 1 ≤ kappa) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu M V delta : ℝ},
      1 < X → 1 ≤ L → L ≤ X → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T ^ mu → T ^ mu ≤ kappa * (X : ℝ) →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      (X : ℝ) / (2 ^ 120 : ℝ) ≤ M →
      1 < M / (2 ^ 120 : ℝ) →
      (X : ℝ) ≤ (4 * (2 ^ 120 : ℝ)) * (M / (2 ^ 120 : ℝ)) →
      0 < V →
      heathBrownEligibleBoxCost L X 60 *
        (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4) ≤ V →
      1 ≤ delta → delta ≤ 2 → (K : ℝ) ≤ T →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      (∀ r ∈ S, V ≤
        ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) M
            ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      D / (16 * delta * (routeTTrivialBoundaryBandCount T : ℝ)) ≤
        V * (S.card : ℝ) →
      (S.card : ℝ) ≤ T * (T ^ mu) ^
        (1 + routeTGapMomentNu -
          2 * routeTAdaptiveCellAmplitude L X 60 M V) := by
  filter_upwards [
    eventually_routeT_leftWindowRelevant_gapSequence_twoAlternative_elevenFifths
      routeTTrivialBoundaryReceiverLogPower,
    eventually_routeT_amplitudeBand_boundedReceiverScale_firstExclusionThreshold_elevenFifths
      hD hkappa,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hreceiver hthresholdT hT
  intro L X K mu M V delta hX hL hLX hXL hXscale hscaleUpper hLscale hmuLo
    hmuHi hlowCutoff hMbase hcomparable hV hlow hdelta hdeltaTwo hK S hS lam
    hband hgap hdiam hlarge hmass
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 M V
  let Q : ℝ := routeTTrivialBoundaryBandCount T
  have hdeltaTop : delta ≤ 2 * T := by
    calc
      delta ≤ 2 := hdeltaTwo
      _ = 2 * 1 := by ring
      _ ≤ 2 * T := mul_le_mul_of_nonneg_left hT.le (by norm_num)
  have halt : IsRouteTMaynardTwoAlternative routeTTrivialBoundaryReceiverLogPower
      (S.card : ℝ) T (T ^ mu) alpha := by
    dsimp only [alpha]
    exact hreceiver hX hL hXL hXscale hLscale hmuLo hmuHi
      hlowCutoff hMbase hV hlow hdelta hdeltaTop hK S hS lam hband hgap hdiam
        hlarge
  have hXscaleTop : (X : ℝ) ≤ T ^ (11 / 5 : ℝ) :=
    hXscale.trans (Real.rpow_le_rpow_of_exponent_le hT.le hmuHi)
  have hthreshold := hthresholdT hX hL hLX hXscaleTop hMbase hV hcomparable
    hlow hXscale hscaleUpper
  have hthreshold' : 8 * V * (T ^ mu) ^ (1 - alpha) ≤
      ((D / (2 * Q)) / 2) *
        (Real.log T) ^ routeTTrivialBoundaryReceiverLogPower := by
    simpa only [alpha, Q] using hthreshold
  have hQnat : 0 < routeTTrivialBoundaryBandCount T :=
    routeTTrivialBoundaryBandCount_pos hT.le
  have hQ : 0 < Q := by dsimp only [Q]; exact_mod_cast hQnat
  apply routeT_second_alternative_of_shell_mass hD hV hQ hdelta hdeltaTwo
    (Real.log_nonneg hT.le) hthreshold'
  · simpa only [Q] using hmass
  · exact halt

/-- Canonical ceiling support and the real eligibility scale differ by at most `4/3`.  Both
directions are retained because the receiver and first-exclusion estimates use opposite sides. -/
theorem routeTPrimeGapPacketSupport_comparable_eligibilityScale
    {T : ℝ} (hT : 0 < T) (hbase : 1 ≤ routeTPrimeGapPacketBase T) :
    (routeTPrimeGapPacketSupport T : ℝ) ≤ T ^ (8 / 5 : ℝ) ∧
      T ^ (8 / 5 : ℝ) ≤
        (4 / 3 : ℝ) * (routeTPrimeGapPacketSupport T : ℝ) := by
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  have hx : 1 ≤ x := by simpa only [x] using hbase
  have hceilLower : 3 * x ≤ (X : ℝ) := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.le_ceil _
  have hceilUpper : (X : ℝ) < 3 * x + 1 := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.ceil_lt_add_one (by positivity)
  have hXx : (X : ℝ) ≤ 4 * x := by linarith
  have hxscale : 4 * x = T ^ (8 / 5 : ℝ) := by
    dsimp only [x, routeTPrimeGapPacketBase]
    field_simp
  constructor
  · rw [← hxscale]
    exact hXx
  · rw [← hxscale]
    have hscaled := mul_le_mul_of_nonneg_left hceilLower
      (by norm_num : (0 : ℝ) ≤ 4 / 3)
    calc
      4 * x = (4 / 3 : ℝ) * (3 * x) := by ring
      _ ≤ (4 / 3 : ℝ) * (X : ℝ) := hscaled

/-- Real-cutoff analogue of the exact exponent bracket. -/
theorem routeTExactRealCutoffExponent_mem_of_rpow_bracket
    {T Y a b : ℝ} (hT : 1 < T) (hY : 0 < Y)
    (hlo : T ^ a ≤ Y) (hhi : Y ≤ T ^ b) :
    routeTExactRealCutoffExponent T Y ∈ Set.Icc a b := by
  have hexact := rpow_routeTExactRealCutoffExponent hT hY
  constructor
  · apply (Real.strictMono_rpow_of_base_gt_one hT).le_iff_le.mp
    simpa only [hexact] using hlo
  · apply (Real.strictMono_rpow_of_base_gt_one hT).le_iff_le.mp
    simpa only [hexact] using hhi

/-- Every height matched to canonical eligibility scale `T₀^(8/5)` and lying between
`T₀^(8/11)` and `T₀` has receiver exponent in the full admissible band `[4/3,11/5]`. -/
theorem routeTHeightMatchedExponent_mem_fourThird_elevenFifths
    {T₀ T₁ : ℝ} (hT₀ : 1 < T₀)
    (hlower : T₀ ^ (8 / 11 : ℝ) ≤ T₁) (hupper : T₁ ≤ T₀) :
    routeTHeightMatchedExponent T₀ (8 / 5) T₁ ∈
      Set.Icc (4 / 3 : ℝ) (11 / 5 : ℝ) := by
  have hT₁ : 1 < T₁ := by
    have hpowOne : 1 < T₀ ^ (8 / 11 : ℝ) := by
      have hmono := (Real.strictMono_rpow_of_base_gt_one hT₀)
        (by norm_num : (0 : ℝ) < 8 / 11)
      simpa using hmono
    exact hpowOne.trans_le hlower
  have hT₀0 : 0 ≤ T₀ := zero_le_one.trans hT₀.le
  have hT₁0 : 0 ≤ T₁ := zero_le_one.trans hT₁.le
  have hlowPow : T₁ ^ (4 / 3 : ℝ) ≤ T₀ ^ (8 / 5 : ℝ) := by
    calc
      T₁ ^ (4 / 3 : ℝ) ≤ T₀ ^ (4 / 3 : ℝ) :=
        Real.rpow_le_rpow hT₁0 hupper (by norm_num)
      _ ≤ T₀ ^ (8 / 5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT₀.le (by norm_num)
  have hupperPow : T₀ ^ (8 / 5 : ℝ) ≤ T₁ ^ (11 / 5 : ℝ) := by
    have hbasePow : (T₀ ^ (8 / 11 : ℝ)) ^ (11 / 5 : ℝ) ≤
        T₁ ^ (11 / 5 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hT₀0 _) hlower (by norm_num)
    calc
      T₀ ^ (8 / 5 : ℝ) =
          (T₀ ^ (8 / 11 : ℝ)) ^ (11 / 5 : ℝ) := by
        rw [← Real.rpow_mul hT₀0]
        norm_num
      _ ≤ T₁ ^ (11 / 5 : ℝ) := hbasePow
  exact routeTExactRealCutoffExponent_mem_of_rpow_bracket hT₁
    (Real.rpow_pos_of_pos (by linarith) _) hlowPow hupperPow

/-- Canonical height-matched shell receiver.  Ceiling support, frozen source cutoff, shell
eligibility exponent, and Möbius cutoff are proved compatible internally; no exact-support-power
hypothesis remains. -/
theorem eventually_routeT_canonicalHeightMatched_threeQuarter_gapSequence_forcedSecond
    {D : ℝ} (hD : 0 < D) :
    ∀ᶠ T₀ : ℝ in atTop,
      ∀ {L K : ℕ} {T₁ V delta : ℝ},
      1 ≤ L → L ≤ routeTPrimeGapPacketSupport T₀ →
      routeTPrimeGapPacketSupport T₀ < (L + 1) ^ 60 →
      (L : ℝ) ≤ T₀ ^ (2 / 75 : ℝ) →
      T₀ ^ (8 / 11 : ℝ) ≤ T₁ → T₁ ≤ T₀ →
      0 < V →
      heathBrownEligibleBoxCost L (routeTPrimeGapPacketSupport T₀) 60 *
        (routeTPrimeGapPacketBase T₀ / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4) ≤ V →
      1 ≤ delta → delta ≤ 2 → (K : ℝ) ≤ T₁ →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T₁ ≤ lam r ∧ lam r ≤ 2 * T₁) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T₁) →
      (∀ r ∈ S, V ≤
        ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L (routeTPrimeGapPacketSupport T₀) 60 T₁
            (routeTHeightMatchedExponent T₀ (8 / 5) T₁ / 120)
            (routeTPrimeGapPacketBase T₀)
              ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      D / (16 * delta * (routeTTrivialBoundaryBandCount T₁ : ℝ)) ≤
        V * (S.card : ℝ) →
      (S.card : ℝ) ≤ T₁ *
        (T₁ ^ routeTHeightMatchedExponent T₀ (8 / 5) T₁) ^
          (1 + routeTGapMomentNu -
            2 * routeTAdaptiveCellAmplitude L
              (routeTPrimeGapPacketSupport T₀) 60
                (routeTPrimeGapPacketBase T₀) V) := by
  obtain ⟨A, hforceA⟩ := Filter.eventually_atTop.1
    (eventually_routeT_threeQuarter_gapSequence_boundedSupport_forcedSecond_elevenFifths
      hD (by norm_num : (1 : ℝ) ≤ 4 / 3))
  have hheight : ∀ᶠ T₀ : ℝ in atTop, A ≤ T₀ ^ (8 / 11 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 11)).eventually_ge_atTop A
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T₀ : ℝ in atTop,
      (2 ^ 120 : ℝ) + 1 ≤ routeTPrimeGapPacketBase T₀ :=
    hbaseTop.eventually_ge_atTop ((2 ^ 120 : ℝ) + 1)
  filter_upwards [hheight, hbaseLarge, Filter.eventually_gt_atTop (1 : ℝ)] with
    T₀ hheightT hbase hT₀
  intro L K T₁ V delta hL hLX hXL hLscale hlower hupper hV hlow hdelta
    hdeltaTwo hK S hS lam hband hgap hdiam hlarge hmass
  let X : ℕ := routeTPrimeGapPacketSupport T₀
  let M : ℝ := routeTPrimeGapPacketBase T₀
  let mu : ℝ := routeTHeightMatchedExponent T₀ (8 / 5) T₁
  have hT₁ : 1 < T₁ := by
    have hpowOne : 1 < T₀ ^ (8 / 11 : ℝ) := by
      have hmono := (Real.strictMono_rpow_of_base_gt_one hT₀)
        (by norm_num : (0 : ℝ) < 8 / 11)
      simpa using hmono
    exact hpowOne.trans_le hlower
  have hforce := hforceA T₁ (hheightT.trans hlower)
    (L := L) (X := X) (K := K) (mu := mu) (M := M) (V := V) (delta := delta)
  have hM : 1 ≤ M := by dsimp only [M]; linarith
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hX : 1 < X := by
    have hceil : 3 * M ≤ (X : ℝ) := by
      dsimp only [X, M, routeTPrimeGapPacketSupport]
      exact Nat.le_ceil _
    have hXreal : (1 : ℝ) < X := by linarith
    exact_mod_cast hXreal
  have hsupport := routeTPrimeGapPacketSupport_comparable_eligibilityScale
    (by linarith : 0 < T₀) (by simpa only [M] using hM)
  have hexact : T₁ ^ mu = T₀ ^ (8 / 5 : ℝ) := by
    dsimp only [mu]
    exact rpow_routeTHeightMatchedExponent hT₀ hT₁
  have hXscale : (X : ℝ) ≤ T₁ ^ mu := by
    rw [hexact]
    simpa only [X] using hsupport.1
  have hscaleUpper : T₁ ^ mu ≤ (4 / 3 : ℝ) * (X : ℝ) := by
    rw [hexact]
    simpa only [X] using hsupport.2
  have hmu : mu ∈ Set.Icc (4 / 3 : ℝ) (11 / 5 : ℝ) := by
    dsimp only [mu]
    exact routeTHeightMatchedExponent_mem_fourThird_elevenFifths hT₀ hlower hupper
  have hLscaleShell : (L : ℝ) ≤ T₁ ^ (2 * (mu / 120)) := by
    have hscaleEq : T₁ ^ (2 * (mu / 120)) = T₀ ^ (2 / 75 : ℝ) := by
      calc
        T₁ ^ (2 * (mu / 120)) = T₁ ^ (mu * (1 / 60 : ℝ)) := by
          congr 1
          ring
        _ = (T₁ ^ mu) ^ (1 / 60 : ℝ) :=
          Real.rpow_mul (zero_le_one.trans hT₁.le) mu (1 / 60 : ℝ)
        _ = (T₀ ^ (8 / 5 : ℝ)) ^ (1 / 60 : ℝ) := by rw [hexact]
        _ = T₀ ^ (2 / 75 : ℝ) := by
          rw [← Real.rpow_mul (zero_le_one.trans hT₀.le)]
          norm_num
    rw [hscaleEq]
    exact hLscale
  have hMbase : 1 < M / (2 ^ 120 : ℝ) := by
    apply (one_lt_div (by positivity : (0 : ℝ) < 2 ^ 120)).2
    dsimp only [M]
    linarith
  have hlowCutoff : (X : ℝ) / (2 ^ 120 : ℝ) ≤ M := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 120)).2
    have hXM : (X : ℝ) ≤ 4 * M := by
      calc
        (X : ℝ) ≤ T₀ ^ (8 / 5 : ℝ) := by simpa only [X] using hsupport.1
        _ = 4 * M := by
          dsimp only [M, routeTPrimeGapPacketBase]
          field_simp
    calc
      (X : ℝ) ≤ 4 * M := hXM
      _ ≤ M * (2 ^ 120 : ℝ) := by
        have hfour : (4 : ℝ) ≤ 2 ^ 120 := by norm_num
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hfour hM0
  have hcomparable : (X : ℝ) ≤
      (4 * (2 ^ 120 : ℝ)) * (M / (2 ^ 120 : ℝ)) := by
    have hXM : (X : ℝ) ≤ 4 * M := by
      calc
        (X : ℝ) ≤ T₀ ^ (8 / 5 : ℝ) := by simpa only [X] using hsupport.1
        _ = 4 * M := by
          dsimp only [M, routeTPrimeGapPacketBase]
          field_simp
    convert hXM using 1
    field_simp
  have hsecond := hforce hX hL (by simpa only [X] using hLX)
    (by simpa only [X] using hXL) hXscale hscaleUpper hLscaleShell hmu.1 hmu.2
      hlowCutoff hMbase hcomparable hV (by simpa only [X, M] using hlow)
        hdelta hdeltaTwo hK S hS lam hband hgap hdiam
          (by simpa only [X, M, mu] using hlarge)
            (by simpa only [X, M] using hmass)
  simpa only [X, M, mu] using hsecond

/-- Deterministic first-exclusion law for a receiver scale only comparable with literal support.
All asymptotic and height-dependent bookkeeping is isolated in the single selector-budget premise,
so defect thresholds may vary with rung and shell counts. -/
theorem routeT_amplitudeBand_boundedReceiverScale_firstExclusion_of_selectorCost
    {q L X : ℕ} {N V Y T D Q kappa : ℝ}
    (hX : 1 < X) (hN : 1 < N / (2 ^ 120 : ℝ)) (hV : 0 < V)
    (hQ : 0 < Q) (hkappa : 1 ≤ kappa)
    (hcomparable : (X : ℝ) ≤
      (4 * (2 ^ 120 : ℝ)) * (N / (2 ^ 120 : ℝ)))
    (hlow : heathBrownEligibleBoxCost L X 60 *
      (N / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4) ≤ V)
    (hXY : (X : ℝ) ≤ Y) (hY : Y ≤ kappa * (X : ℝ))
    (hselector : 32 * Q * kappa * heathBrownEligibleBoxCost L X 60 *
        (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent ≤
      D * (Real.log T) ^ q) :
    8 * V * Y ^ (1 - routeTAdaptiveCellAmplitude L X 60 N V) ≤
      ((D / (2 * Q)) / 2) * (Real.log T) ^ q := by
  let kappa0 : ℝ := 4 * (2 ^ 120 : ℝ)
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 N V
  have halphaThree : 3 / 4 ≤ alpha := by
    dsimp only [alpha]
    exact routeTAdaptiveCellAmplitude_threeQuarter_le L X 60
      (by norm_num) hX hN hV hlow
  have htrivial : routeTTrivialBoundaryAmplitudeThreshold L X 60 N ≤ V :=
    (routeTTrivialBoundaryAmplitudeThreshold_le_threeQuarterThreshold
      L X 60 (by norm_num) hN).trans hlow
  have halpha : (1 + routeTGapMomentNu) / 2 ≤ alpha := by
    dsimp only [alpha]
    exact routeT_trivialCountBoundary_le_adaptive_of_threshold_le
      L X 60 (by norm_num) hX hN htrivial
  have hkappa0 : 1 ≤ kappa0 := by dsimp only [kappa0]; norm_num
  have hsupportPos : 0 < (X : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hX)
  have hA : V * (X : ℝ) ^ (1 - alpha) ≤
      heathBrownEligibleBoxCost L X 60 *
        kappa0 ^ routeTTrivialBoundaryDistortionExponent := by
    simpa only [alpha] using
      (routeTAdaptiveCellAmplitude_firstExclusionCost_trivialBoundary
        L X 60 (by norm_num) hX hN hV hsupportPos hkappa0 (le_refl _)
          (by simpa only [kappa0] using hcomparable) halpha)
  have hdistort : Y ^ (1 - alpha) ≤
      kappa * (X : ℝ) ^ (1 - alpha) :=
    rpow_receiverScale_le_distortion_mul_support_rpow
      hsupportPos hXY hY hkappa halphaThree
  have hVA : V * Y ^ (1 - alpha) ≤
      kappa * (heathBrownEligibleBoxCost L X 60 *
        kappa0 ^ routeTTrivialBoundaryDistortionExponent) := by
    calc
      V * Y ^ (1 - alpha) ≤
          V * (kappa * (X : ℝ) ^ (1 - alpha)) :=
        mul_le_mul_of_nonneg_left hdistort hV.le
      _ = kappa * (V * (X : ℝ) ^ (1 - alpha)) := by ring
      _ ≤ kappa * (heathBrownEligibleBoxCost L X 60 *
          kappa0 ^ routeTTrivialBoundaryDistortionExponent) :=
        mul_le_mul_of_nonneg_left hA (zero_le_one.trans hkappa)
  have hfull : 32 * Q * (V * Y ^ (1 - alpha)) ≤
      D * (Real.log T) ^ q := by
    calc
      32 * Q * (V * Y ^ (1 - alpha)) ≤
          32 * Q * (kappa * (heathBrownEligibleBoxCost L X 60 *
            kappa0 ^ routeTTrivialBoundaryDistortionExponent)) :=
        mul_le_mul_of_nonneg_left hVA (by positivity)
      _ = 32 * Q * kappa * heathBrownEligibleBoxCost L X 60 *
          kappa0 ^ routeTTrivialBoundaryDistortionExponent := by ring
      _ ≤ D * (Real.log T) ^ q := by
        simpa only [kappa0] using hselector
  have hden : 0 < 4 * Q := by positivity
  have hdiv : 8 * (V * Y ^ (1 - alpha)) ≤
      (D * (Real.log T) ^ q) / (4 * Q) := by
    apply (le_div_iff₀ hden).2
    calc
      8 * (V * Y ^ (1 - alpha)) * (4 * Q) =
          32 * Q * (V * Y ^ (1 - alpha)) := by ring
      _ ≤ D * (Real.log T) ^ q := hfull
  have htarget : (D * (Real.log T) ^ q) / (4 * Q) =
      ((D / (2 * Q)) / 2) * (Real.log T) ^ q := by
    field_simp
    norm_num
  rw [htarget] at hdiv
  simpa only [alpha, mul_assoc] using hdiv

/-- Variable-threshold forced-second receiver.  Defect mass `D` and selector budget `Q` may depend
on height; the only required payment is the explicit deterministic selector-cost inequality. -/
theorem eventually_routeT_threeQuarter_gapSequence_boundedSupport_forcedSecond_of_selectorCost
    (q : ℕ) {kappa : ℝ} (hkappa : 1 ≤ kappa) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu M V delta D Q : ℝ},
      1 < X → 1 ≤ L → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T ^ mu → T ^ mu ≤ kappa * (X : ℝ) →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      (X : ℝ) / (2 ^ 120 : ℝ) ≤ M →
      1 < M / (2 ^ 120 : ℝ) →
      (X : ℝ) ≤ (4 * (2 ^ 120 : ℝ)) * (M / (2 ^ 120 : ℝ)) →
      0 < V →
      heathBrownEligibleBoxCost L X 60 *
        (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4) ≤ V →
      1 ≤ delta → delta ≤ 2 → (K : ℝ) ≤ T →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      (∀ r ∈ S, V ≤
        ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) M
            ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      0 < D → 0 < Q →
      32 * Q * kappa * heathBrownEligibleBoxCost L X 60 *
          (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent ≤
        D * (Real.log T) ^ q →
      D / (16 * delta * Q) ≤ V * (S.card : ℝ) →
      (S.card : ℝ) ≤ T * (T ^ mu) ^
        (1 + routeTGapMomentNu -
          2 * routeTAdaptiveCellAmplitude L X 60 M V) := by
  filter_upwards [
    eventually_routeT_leftWindowRelevant_gapSequence_twoAlternative_elevenFifths q,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hreceiver hT
  intro L X K mu M V delta D Q hX hL hXL hXscale hscaleUpper hLscale hmuLo
    hmuHi hlowCutoff hMbase hcomparable hV hlow hdelta hdeltaTwo hK S hS lam
    hband hgap hdiam hlarge hD hQ hselector hmass
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 M V
  have hdeltaTop : delta ≤ 2 * T := by
    calc
      delta ≤ 2 := hdeltaTwo
      _ = 2 * 1 := by ring
      _ ≤ 2 * T := mul_le_mul_of_nonneg_left hT.le (by norm_num)
  have halt : IsRouteTMaynardTwoAlternative q (S.card : ℝ) T (T ^ mu) alpha := by
    dsimp only [alpha]
    exact hreceiver hX hL hXL hXscale hLscale hmuLo hmuHi hlowCutoff hMbase
      hV hlow hdelta hdeltaTop hK S hS lam hband hgap hdiam hlarge
  have hthreshold :=
    routeT_amplitudeBand_boundedReceiverScale_firstExclusion_of_selectorCost
      hX hMbase hV hQ hkappa hcomparable hlow hXscale hscaleUpper hselector
  apply routeT_second_alternative_of_shell_mass hD hV hQ hdelta hdeltaTwo
    (Real.log_nonneg hT.le) (by simpa only [alpha] using hthreshold) hmass halt

/-! ## Literal finite-selector budget -/

/-- Universal linear-log constant for a selector count obtained by rounding
`1 + log(ratio) / log 2`. -/
def routeTFiniteSelectorLogConstant : ℝ := 2 + 1 / Real.log 2

/-- Any canonical dyadic selector whose ratio lies in `[1,T]` has only linear-log depth. -/
theorem routeT_ceilLogSelectorCount_cast_le_log
    {Q T : ℝ} (hQ : 1 ≤ Q) (hQT : Q ≤ T) :
    (⌈1 + Real.log Q / Real.log 2⌉₊ : ℝ) ≤
      routeTFiniteSelectorLogConstant * (1 + Real.log T) := by
  have hT : 1 ≤ T := hQ.trans hQT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : 0 < 1 + Real.log Q / Real.log 2 := by
    have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
    positivity
  have hceil : (⌈1 + Real.log Q / Real.log 2⌉₊ : ℝ) <
      2 + Real.log Q / Real.log 2 := by
    calc
      (⌈1 + Real.log Q / Real.log 2⌉₊ : ℝ) <
          1 + Real.log Q / Real.log 2 + 1 := Nat.ceil_lt_add_one harg.le
      _ = 2 + Real.log Q / Real.log 2 := by ring
  have hlogQ : Real.log Q ≤ Real.log T :=
    Real.log_le_log (zero_lt_one.trans_le hQ) hQT
  have hdiv : Real.log Q / Real.log 2 ≤ Real.log T / Real.log 2 :=
    div_le_div_of_nonneg_right hlogQ hlogTwo.le
  have hinv : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr hlogTwo.le
  calc
    (⌈1 + Real.log Q / Real.log 2⌉₊ : ℝ) ≤
        2 + Real.log Q / Real.log 2 := hceil.le
    _ ≤ 2 + Real.log T / Real.log 2 := by linarith
    _ ≤ routeTFiniteSelectorLogConstant * (1 + Real.log T) := by
      dsimp only [routeTFiniteSelectorLogConstant]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      nlinarith [mul_nonneg hinv hlogT]

/-- The literal fixed-width ladder count is linear-log once its endpoint ratio is at most the
ambient height. -/
theorem routeTFixedWidthRungCount_cast_le_log
    {T H0 : ℝ} (hH0 : 0 < H0) (hH0quarter : H0 ≤ 1 / 4)
    (hratio : (1 / 4) / H0 ≤ T) :
    (routeTFixedWidthRungCount H0 : ℝ) ≤
      routeTFiniteSelectorLogConstant * (1 + Real.log T) := by
  apply routeT_ceilLogSelectorCount_cast_le_log
  · exact (le_div_iff₀ hH0).2 (by simpa using hH0quarter)
  · exact hratio

/-- The literal ordinate-shell count is linear-log relative to any containing ambient height. -/
theorem routeTOrdinateShellCount_cast_le_log
    {T U V : ℝ} (hU : 1 ≤ U) (hUV : U ≤ V) (hVT : V ≤ T) :
    (routeTOrdinateShellCount U V : ℝ) ≤
      routeTFiniteSelectorLogConstant * (1 + Real.log T) := by
  apply routeT_ceilLogSelectorCount_cast_le_log
  · exact (le_div_iff₀ (zero_lt_one.trans_le hU)).2 (by simpa using hUV)
  · apply (div_le_iff₀ (zero_lt_one.trans_le hU)).2
    calc
      V ≤ T := hVT
      _ = T * 1 := by ring
      _ ≤ T * U := mul_le_mul_of_nonneg_left hU
        (zero_le_one.trans (hU.trans (hUV.trans hVT)))

/-- Canonical packet-width admissibility already forces the entire stopped-width ladder ratio
below ambient height.  No independent rung-growth hypothesis is required. -/
theorem routeT_canonical_fixedWidth_rung_ratio_le_height
    {T H0 : ℝ} (hT : 1 ≤ T) (hH0 : 0 < H0)
    (hwidth : routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) ≤ H0) :
    (1 / 4) / H0 ≤ T := by
  let x : ℝ := routeTPrimeGapPacketBase T
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hxpos : 0 < x := by
    dsimp only [x, routeTPrimeGapPacketBase]
    positivity
  have hinv : 1 / H0 ≤ 1 / routeTPrimeGapPacketWidth x :=
    one_div_le_one_div_of_le
      (by dsimp only [routeTPrimeGapPacketWidth]; positivity) hwidth
  have hinv' : 1 / H0 ≤ x ^ (49 / 80 : ℝ) := by
    simpa only [routeTPrimeGapPacketWidth, Real.rpow_neg hxpos.le,
      one_div, inv_inv] using hinv
  have hxTop : x ≤ T ^ (8 / 5 : ℝ) := by
    dsimp only [x, routeTPrimeGapPacketBase]
    have hp : 0 ≤ T ^ (8 / 5 : ℝ) := Real.rpow_nonneg hTpos.le _
    nlinarith
  have hpow : x ^ (49 / 80 : ℝ) ≤ (T ^ (8 / 5 : ℝ)) ^ (49 / 80 : ℝ) :=
    Real.rpow_le_rpow hxpos.le hxTop (by norm_num)
  have hpowTop : (T ^ (8 / 5 : ℝ)) ^ (49 / 80 : ℝ) ≤ T := by
    calc
      (T ^ (8 / 5 : ℝ)) ^ (49 / 80 : ℝ) = T ^ (49 / 50 : ℝ) := by
        rw [← Real.rpow_mul hTpos.le]
        norm_num
      _ ≤ T := by
        simpa using Real.rpow_le_rpow_of_exponent_le hT
          (by norm_num : (49 / 50 : ℝ) ≤ 1)
  calc
    (1 / 4) / H0 ≤ 1 / H0 :=
      div_le_div_of_nonneg_right (by norm_num) hH0.le
    _ ≤ x ^ (49 / 80 : ℝ) := hinv'
    _ ≤ (T ^ (8 / 5 : ℝ)) ^ (49 / 80 : ℝ) := hpow
    _ ≤ T := hpowTop

/-- Receiver logarithmic power after paying width-rung, ordinate-shell, and amplitude-band
selectors in addition to the degree-60 Heath--Brown box cost. -/
def routeTFixedWidthShellReceiverLogPower : ℕ := 124

/-- Linear-log selector constant transported from ambient packet height to every admissible
height-matched shell. -/
def routeTFixedWidthSelectorShellLogConstant : ℝ :=
  routeTFiniteSelectorLogConstant * (19 / 8 : ℝ)

/-- **Complete literal selector budget.**  On every admissible height-matched shell, the actual
fixed-width rung count, ordinate-shell count, amplitude-band count, and degree-60 box selector are
simultaneously absorbed.  The right side is exactly the defect threshold left by the finite cover;
no fixed-defect or bounded-selector surrogate remains. -/
theorem eventually_routeT_fixedWidth_rung_shell_band_selectorCost_le_receiverLog :
    ∀ᶠ T₀ : ℝ in atTop,
      ∀ {T₁ H0 U V : ℝ} {L X : ℕ},
      T₀ ^ (8 / 11 : ℝ) ≤ T₁ →
      0 < H0 → H0 ≤ 1 / 4 →
      routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T₀) ≤ H0 →
      1 ≤ U → U ≤ V → V ≤ T₀ →
      1 ≤ X → L ≤ X → (X : ℝ) ≤ T₁ ^ (11 / 5 : ℝ) →
      32 * (routeTTrivialBoundaryBandCount T₁ : ℝ) * (4 / 3 : ℝ) *
          heathBrownEligibleBoxCost L X 60 *
            (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent ≤
        (((routeTFixedWidthPacketDefectFloor /
              (routeTFixedWidthRungCount H0 : ℝ)) / 2) /
            (routeTOrdinateShellCount U V : ℝ)) *
          (Real.log T₁) ^ routeTFixedWidthShellReceiverLogPower := by
  let C0 : ℝ := routeTFiniteSelectorLogConstant
  let C : ℝ := routeTFixedWidthSelectorShellLogConstant
  let kappa : ℝ := 4 / 3
  let D0 : ℝ := routeTFixedWidthPacketDefectFloor / (2 * kappa * C ^ 2)
  have hC0 : 0 < C0 := by
    dsimp only [C0, routeTFiniteSelectorLogConstant]
    positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hC : 0 < C := by
    dsimp only [C, routeTFixedWidthSelectorShellLogConstant]
    positivity
  have hkappa : 0 < kappa := by dsimp only [kappa]; norm_num
  have hD0 : 0 < D0 := by
    dsimp only [D0]
    positivity [routeTFixedWidthPacketDefectFloor_pos]
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1
    (eventually_thirtytwo_shellBandCount_selectorCost_le_receiverLog_elevenFifths hD0)
  let B : ℝ := max A (Real.exp 1)
  have hheight : ∀ᶠ T₀ : ℝ in atTop, B ≤ T₀ ^ (8 / 11 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 11)).eventually_ge_atTop B
  filter_upwards [hheight, Filter.eventually_ge_atTop (1 : ℝ)] with T₀ hheightT hT₀
  intro T₁ H0 U V L X hT₁lower hH0 hH0quarter hwidth hU hUV hVT₀ hX hLX
    hXscale
  let ell : ℝ := Real.log T₁
  let Rcount : ℝ := routeTFixedWidthRungCount H0
  let Scount : ℝ := routeTOrdinateShellCount U V
  let Acost : ℝ := 32 * (routeTTrivialBoundaryBandCount T₁ : ℝ) *
    heathBrownEligibleBoxCost L X 60 *
      (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent
  have hT₀pos : 0 < T₀ := zero_lt_one.trans_le hT₀
  have hT₁A : A ≤ T₁ :=
    (le_max_left A (Real.exp 1)).trans (hheightT.trans hT₁lower)
  have hexpT₁ : Real.exp 1 ≤ T₁ :=
    (le_max_right A (Real.exp 1)).trans (hheightT.trans hT₁lower)
  have hT₁one : 1 ≤ T₁ := by
    have honeExp : (1 : ℝ) ≤ Real.exp 1 := by
      have h := Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 from zero_le_one)
      rwa [Real.exp_zero] at h
    exact honeExp.trans hexpT₁
  have hellOne : 1 ≤ ell := by
    have hlog := Real.log_le_log (Real.exp_pos 1) hexpT₁
    simpa only [Real.log_exp, ell] using hlog
  have hell0 : 0 ≤ ell := zero_le_one.trans hellOne
  have hlogRelation : (8 / 11 : ℝ) * Real.log T₀ ≤ ell := by
    have hlog := Real.log_le_log
      (Real.rpow_pos_of_pos hT₀pos (8 / 11 : ℝ)) hT₁lower
    rw [Real.log_rpow hT₀pos] at hlog
    simpa only [ell] using hlog
  have hlogT₀ : 0 ≤ Real.log T₀ := Real.log_nonneg hT₀
  have hshape : 1 + Real.log T₀ ≤ (19 / 8 : ℝ) * ell := by
    nlinarith
  have hratio := routeT_canonical_fixedWidth_rung_ratio_le_height
    hT₀ hH0 hwidth
  have hRraw := routeTFixedWidthRungCount_cast_le_log hH0 hH0quarter hratio
  have hR : Rcount ≤ C * ell := by
    calc
      Rcount ≤ C0 * (1 + Real.log T₀) := by
        simpa only [Rcount, C0] using hRraw
      _ ≤ C0 * ((19 / 8 : ℝ) * ell) :=
        mul_le_mul_of_nonneg_left hshape hC0.le
      _ = C * ell := by
        dsimp only [C, C0, routeTFixedWidthSelectorShellLogConstant]
        ring
  have hSraw := routeTOrdinateShellCount_cast_le_log hU hUV hVT₀
  have hS : Scount ≤ C * ell := by
    calc
      Scount ≤ C0 * (1 + Real.log T₀) := by
        simpa only [Scount, C0] using hSraw
      _ ≤ C0 * ((19 / 8 : ℝ) * ell) :=
        mul_le_mul_of_nonneg_left hshape hC0.le
      _ = C * ell := by
        dsimp only [C, C0, routeTFixedWidthSelectorShellLogConstant]
        ring
  have hRpos : 0 < Rcount := by
    dsimp only [Rcount]
    exact_mod_cast routeTFixedWidthRungCount_pos hH0 hH0quarter
  have hSpos : 0 < Scount := by
    dsimp only [Scount]
    exact_mod_cast routeTOrdinateShellCount_pos (zero_lt_one.trans_le hU) hUV
  have hcost : Acost ≤ D0 * ell ^ routeTTrivialBoundaryReceiverLogPower := by
    simpa only [Acost, ell] using hA T₁ hT₁A L X hX hLX hXscale
  have hcostKappa : kappa * Acost ≤
      (routeTFixedWidthPacketDefectFloor / (2 * C ^ 2)) *
        ell ^ routeTTrivialBoundaryReceiverLogPower := by
    calc
      kappa * Acost ≤ kappa *
          (D0 * ell ^ routeTTrivialBoundaryReceiverLogPower) :=
        mul_le_mul_of_nonneg_left hcost hkappa.le
      _ = (routeTFixedWidthPacketDefectFloor / (2 * C ^ 2)) *
          ell ^ routeTTrivialBoundaryReceiverLogPower := by
        dsimp only [D0]
        field_simp [hkappa.ne', hC.ne']
  have hRS : Rcount * Scount ≤ C ^ 2 * ell ^ 2 := by
    calc
      Rcount * Scount ≤ (C * ell) * Scount :=
        mul_le_mul_of_nonneg_right hR hSpos.le
      _ ≤ (C * ell) * (C * ell) :=
        mul_le_mul_of_nonneg_left hS (mul_nonneg hC.le hell0)
      _ = C ^ 2 * ell ^ 2 := by ring
  have hcoefficient : 0 ≤
      (routeTFixedWidthPacketDefectFloor / (C ^ 2)) *
        ell ^ routeTTrivialBoundaryReceiverLogPower :=
    mul_nonneg
      (div_nonneg routeTFixedWidthPacketDefectFloor_pos.le (sq_nonneg C))
      (pow_nonneg hell0 _)
  have hscaled : (kappa * Acost) * (2 * Rcount * Scount) ≤
      routeTFixedWidthPacketDefectFloor *
        ell ^ routeTFixedWidthShellReceiverLogPower := by
    calc
      (kappa * Acost) * (2 * Rcount * Scount) ≤
          ((routeTFixedWidthPacketDefectFloor / (2 * C ^ 2)) *
            ell ^ routeTTrivialBoundaryReceiverLogPower) *
              (2 * Rcount * Scount) :=
        mul_le_mul_of_nonneg_right hcostKappa (by positivity)
      _ = ((routeTFixedWidthPacketDefectFloor / (C ^ 2)) *
            ell ^ routeTTrivialBoundaryReceiverLogPower) *
              (Rcount * Scount) := by ring
      _ ≤ ((routeTFixedWidthPacketDefectFloor / (C ^ 2)) *
            ell ^ routeTTrivialBoundaryReceiverLogPower) *
              (C ^ 2 * ell ^ 2) :=
        mul_le_mul_of_nonneg_left hRS hcoefficient
      _ = routeTFixedWidthPacketDefectFloor *
          ell ^ routeTFixedWidthShellReceiverLogPower := by
        dsimp only [routeTFixedWidthShellReceiverLogPower,
          routeTTrivialBoundaryReceiverLogPower]
        rw [show (124 : ℕ) = 122 + 2 by norm_num, pow_add]
        field_simp [hC.ne']
  have hden : 0 < 2 * Rcount * Scount := by positivity
  have hmain : kappa * Acost ≤
      (routeTFixedWidthPacketDefectFloor *
          ell ^ routeTFixedWidthShellReceiverLogPower) /
        (2 * Rcount * Scount) := (le_div_iff₀ hden).2 hscaled
  calc
    32 * (routeTTrivialBoundaryBandCount T₁ : ℝ) * (4 / 3 : ℝ) *
          heathBrownEligibleBoxCost L X 60 *
            (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent =
        kappa * Acost := by dsimp only [kappa, Acost]; ring
    _ ≤ (routeTFixedWidthPacketDefectFloor *
          ell ^ routeTFixedWidthShellReceiverLogPower) /
        (2 * Rcount * Scount) := hmain
    _ = (((routeTFixedWidthPacketDefectFloor /
              (routeTFixedWidthRungCount H0 : ℝ)) / 2) /
            (routeTOrdinateShellCount U V : ℝ)) *
          (Real.log T₁) ^ routeTFixedWidthShellReceiverLogPower := by
      dsimp only [Rcount, Scount, ell]
      field_simp [hRpos.ne', hSpos.ne']

/-- **Literal fixed-width high-shell receiver.**  The exact defect remaining after width-rung and
ordinate-shell pigeonholing forces the second Maynard alternative.  The amplitude-band selector
and degree-60 box cost are discharged internally, so no selector-cost premise survives. -/
theorem eventually_routeT_fixedWidth_literalShell_gapSequence_forcedSecond :
    ∀ᶠ T₀ : ℝ in atTop,
      ∀ {T₁ H0 U W : ℝ} {L X K : ℕ} {mu M Aamp delta : ℝ},
      T₀ ^ (8 / 11 : ℝ) ≤ T₁ →
      0 < H0 → H0 ≤ 1 / 4 →
      routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T₀) ≤ H0 →
      1 ≤ U → U ≤ W → W ≤ T₀ →
      1 < X → 1 ≤ L → L ≤ X → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T₁ ^ mu → T₁ ^ mu ≤ (4 / 3 : ℝ) * (X : ℝ) →
      (L : ℝ) ≤ T₁ ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      (X : ℝ) / (2 ^ 120 : ℝ) ≤ M →
      1 < M / (2 ^ 120 : ℝ) →
      (X : ℝ) ≤ (4 * (2 ^ 120 : ℝ)) * (M / (2 ^ 120 : ℝ)) →
      0 < Aamp →
      heathBrownEligibleBoxCost L X 60 *
        (M / (2 ^ 120 : ℝ)) ^ (-(1 : ℝ) / 4) ≤ Aamp →
      1 ≤ delta → delta ≤ 2 → (K : ℝ) ≤ T₁ →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T₁ ≤ lam r ∧ lam r ≤ 2 * T₁) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T₁) →
      (∀ r ∈ S, Aamp ≤
        ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T₁ (mu / 120) M
            ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      (((routeTFixedWidthPacketDefectFloor /
              (routeTFixedWidthRungCount H0 : ℝ)) / 2) /
            (routeTOrdinateShellCount U W : ℝ)) /
          (16 * delta * (routeTTrivialBoundaryBandCount T₁ : ℝ)) ≤
        Aamp * (S.card : ℝ) →
      (S.card : ℝ) ≤ T₁ * (T₁ ^ mu) ^
        (1 + routeTGapMomentNu -
          2 * routeTAdaptiveCellAmplitude L X 60 M Aamp) := by
  obtain ⟨A, hforceA⟩ := Filter.eventually_atTop.1
    (eventually_routeT_threeQuarter_gapSequence_boundedSupport_forcedSecond_of_selectorCost
      routeTFixedWidthShellReceiverLogPower (by norm_num : (1 : ℝ) ≤ 4 / 3))
  have hheight : ∀ᶠ T₀ : ℝ in atTop, A ≤ T₀ ^ (8 / 11 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 11)).eventually_ge_atTop A
  filter_upwards [
    hheight,
    eventually_routeT_fixedWidth_rung_shell_band_selectorCost_le_receiverLog,
    Filter.eventually_gt_atTop (1 : ℝ)] with T₀ hheightT hselectorT hT₀
  intro T₁ H0 U W L X K mu M Aamp delta hT₁lower hH0 hH0quarter hwidth hU hUW
    hWT₀ hX hL hLX hXL hXscale hscaleUpper hLscale hmuLo hmuHi hlowCutoff
    hMbase hcomparable hAamp hlow hdelta hdeltaTwo hK S hS lam hband hgap hdiam
    hlarge hmass
  have hT₁ : 1 < T₁ := by
    have hpowOne : 1 < T₀ ^ (8 / 11 : ℝ) := by
      have hmono := (Real.strictMono_rpow_of_base_gt_one hT₀)
        (by norm_num : (0 : ℝ) < 8 / 11)
      simpa using hmono
    exact hpowOne.trans_le hT₁lower
  have hXscaleTop : (X : ℝ) ≤ T₁ ^ (11 / 5 : ℝ) :=
    hXscale.trans (Real.rpow_le_rpow_of_exponent_le hT₁.le hmuHi)
  have hselector := hselectorT hT₁lower hH0 hH0quarter hwidth hU hUW hWT₀
    hX.le hLX hXscaleTop
  let Dcover : ℝ := ((routeTFixedWidthPacketDefectFloor /
      (routeTFixedWidthRungCount H0 : ℝ)) / 2) /
        (routeTOrdinateShellCount U W : ℝ)
  let Qband : ℝ := routeTTrivialBoundaryBandCount T₁
  have hRpos : 0 < (routeTFixedWidthRungCount H0 : ℝ) := by
    exact_mod_cast routeTFixedWidthRungCount_pos hH0 hH0quarter
  have hSpos : 0 < (routeTOrdinateShellCount U W : ℝ) := by
    exact_mod_cast routeTOrdinateShellCount_pos (zero_lt_one.trans_le hU) hUW
  have hD : 0 < Dcover := by
    dsimp only [Dcover]
    exact div_pos
      (div_pos (div_pos routeTFixedWidthPacketDefectFloor_pos hRpos) (by norm_num))
      hSpos
  have hQ : 0 < Qband := by
    dsimp only [Qband]
    exact_mod_cast routeTTrivialBoundaryBandCount_pos hT₁.le
  have hselector' : 32 * Qband * (4 / 3 : ℝ) *
        heathBrownEligibleBoxCost L X 60 *
          (4 * (2 ^ 120 : ℝ)) ^ routeTTrivialBoundaryDistortionExponent ≤
      Dcover * (Real.log T₁) ^ routeTFixedWidthShellReceiverLogPower := by
    simpa only [Dcover, Qband] using hselector
  have hmass' : Dcover / (16 * delta * Qband) ≤ Aamp * (S.card : ℝ) := by
    simpa only [Dcover, Qband] using hmass
  exact hforceA T₁ (hheightT.trans hT₁lower)
    (L := L) (X := X) (K := K) (mu := mu) (M := M) (V := Aamp)
    (delta := delta) (D := Dcover) (Q := Qband)
    hX hL hXL hXscale hscaleUpper hLscale hmuLo hmuHi hlowCutoff
      hMbase hcomparable hAamp hlow hdelta hdeltaTwo hK S hS lam hband hgap
        hdiam hlarge hD hQ hselector' hmass'


end RHTower.Sieve
