import GaloisForLFunctions.RHTower.Sieve.MaynardCommonModePairedAnnulus
import GaloisForLFunctions.RHTower.Sieve.MaynardNaturalOrdinateShellSpatialBridge

open Complex MeasureTheory Set
open Filter ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

/-!
# Natural-cell landing for a cancellation-preserving paired shell

A paired Route-T interval can be spatially summed only after its ordinate cells are fixed before
the physical base varies.  When the interval endpoints are natural numbers, the stopped dyadic
ladder admits an exact terminal rung, and every nonzero selected piece is a literal `Finset.Ico`
packet.  This keeps the reference-target kernel difference intact while landing directly in the
existing spatial `L²/L⁴` interface.
-/

/-- A paired interval with natural endpoints lands in one canonical natural-cell shell.  The
temporary stopping index is absorbed by `routeTOrdinateShellCount`; positivity rules out a
degenerate selected interval. -/
theorem exists_fixedSource_naturalized_pairedShell_of_naturalInterval_canonicalCount
    (L X k U V : ℕ) {T mu M N H R B : ℝ}
    (hT : 1 < T) (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hU : 2 ≤ U) (hUV : 2 * U ≤ V) (hB0 : 0 < B)
    (hB : B ≤ ‖routeTFixedSourceAdjacentIntervalPacket
      L X k T (mu / 120) M N R H 1 U V‖) :
    ∃ j ∈ Finset.range (routeTOrdinateShellCount U V),
      let A := routeTNaturalizedOrdinateLadder U V (j + 1)
      let C := routeTNaturalizedOrdinateLadder U V j
      let T₁ : ℝ := A
      let mu₁ := routeTHeightMatchedExponent T mu T₁
      1 < T₁ ∧ A < C ∧ C ≤ 2 * A ∧ T₁ ^ mu₁ = T ^ mu ∧
        B / (routeTOrdinateShellCount U V : ℝ) ≤
          ‖routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket
            L X k T mu M N R H U V j 1‖ := by
  have hU0 : 0 < (U : ℝ) := by exact_mod_cast (by omega : 0 < U)
  have hUVreal : (U : ℝ) ≤ (V : ℝ) := by exact_mod_cast (by omega : U ≤ V)
  have hV0 : 0 < (V : ℝ) := hU0.trans_le hUVreal
  obtain ⟨J, hJ, hbelow, _habove, _hinitialReal, hterminalReal⟩ :=
    exists_routeTComparableWidthLadder_endpoint hU0 hUVreal
  have hterminalNatural : routeTNaturalizedOrdinateLadder U V J = U := by
    rw [routeTNaturalizedOrdinateLadder, hterminalReal, Nat.ceil_natCast]
  have hinitialNatural : routeTNaturalizedOrdinateLadder U V 0 = V := by
    exact routeTNaturalizedOrdinateLadder_initial hUVreal
  have hUone : (1 : ℝ) < U := by exact_mod_cast (by omega : 1 < U)
  have hlargeNatural : B ≤ ‖routeTFixedSourceAdjacentIntervalPacket
      L X k T (mu / 120) M N R H 1
        (routeTNaturalizedOrdinateLadder U V J)
        (routeTNaturalizedOrdinateLadder U V 0)‖ := by
    simpa only [hterminalNatural, hinitialNatural] using hB
  obtain ⟨j, hj, hT₁, hlarge⟩ :=
    exists_fixedSource_naturalized_ordinate_shell_norm_ge
      L X k hT hN hR hH (by norm_num) hUone hUVreal hJ hlargeNatural
  have hJle : J ≤ routeTOrdinateShellCount U V :=
    routeTComparableWidthLadder_index_le_ordinateShellCount
      hU0 hUVreal hJ hbelow
  have hjCanonical : j ∈ Finset.range (routeTOrdinateShellCount U V) := by
    rw [Finset.mem_range] at hj ⊢
    exact hj.trans_le hJle
  let A := routeTNaturalizedOrdinateLadder U V (j + 1)
  let C := routeTNaturalizedOrdinateLadder U V j
  let T₁ : ℝ := A
  let mu₁ := routeTHeightMatchedExponent T mu T₁
  have hcountPos : 0 < (routeTOrdinateShellCount U V : ℝ) := by
    exact_mod_cast routeTOrdinateShellCount_pos hU0 hUVreal
  have hdenom : B / (routeTOrdinateShellCount U V : ℝ) ≤ B / (J : ℝ) := by
    apply div_le_div_of_nonneg_left hB0.le
    · exact_mod_cast hJ
    · exact_mod_cast hJle
  have hlargeCanonical : B / (routeTOrdinateShellCount U V : ℝ) ≤
      ‖routeTFixedSourceAdjacentIntervalPacket
        L X k T₁ (mu₁ / 120) M N R H 1 A C‖ := by
    exact hdenom.trans (by simpa only [A, C, T₁, mu₁] using hlarge)
  have hAmem := routeTComparableWidthLadder_mem hU0 hUVreal (j + 1)
  have hAceil : routeTComparableWidthLadder U V (j + 1) ≤ (A : ℝ) := by
    dsimp only [A, routeTNaturalizedOrdinateLadder]
    exact Nat.le_ceil _
  have hA_U : U ≤ A := by
    exact_mod_cast hAmem.1.trans hAceil
  have hAleC : A ≤ C :=
    Nat.ceil_mono (routeTComparableWidthLadder_adjacent hU0 hV0 j).1
  have hAC : A < C := by
    by_contra hnot
    have hEq : A = C := Nat.le_antisymm hAleC (Nat.le_of_not_gt hnot)
    rw [hEq, routeTFixedSourceAdjacentIntervalPacket,
      intervalIntegral.integral_same, norm_zero] at hlargeCanonical
    have hquotPos : 0 < B / (routeTOrdinateShellCount U V : ℝ) :=
      div_pos hB0 hcountPos
    linarith
  have hCtwo : C ≤ 2 * A := by
    apply Nat.ceil_le.mpr
    have hcomp : routeTComparableWidthLadder U V j ≤
        2 * routeTComparableWidthLadder U V (j + 1) :=
      (routeTComparableWidthLadder_adjacent hU0 hV0 j).2
    calc
      routeTComparableWidthLadder U V j ≤
          2 * routeTComparableWidthLadder U V (j + 1) := hcomp
      _ ≤ 2 * (A : ℝ) := mul_le_mul_of_nonneg_left hAceil (by norm_num)
      _ = ((2 * A : ℕ) : ℝ) := by norm_num
  have hmatch : T₁ ^ mu₁ = T ^ mu :=
    rpow_routeTHeightMatchedExponent hT hT₁
  refine ⟨j, hjCanonical, hT₁, hAC, hCtwo, hmatch, ?_⟩
  have heq := routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket_eq_interval
    L X k (T₀ := T) (mu₀ := mu) (M := M) (N := N) (R := R) (H := H)
      (U := U) (V := V) (lambda := 1) (j := j)
      hAleC (by norm_num) hN hR hH
  rw [heq]
  simpa only [A, C, T₁, mu₁, one_mul] using hlargeCanonical

/-- Buffered paired-kernel `L²` on the exact natural-cell shell selected above.  The shell's
natural geometry discharges the ordinate-band premise for every unit cell, so the negative power
survives without a partial-cell or endpoint loss. -/
theorem integral_norm_sq_routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket_le_bufferedPower
    (L X k : ℕ) {T₀ mu₀ M H U V x W : ℝ} {j cellCount : ℕ}
    (hx : 1 ≤ x)
    (hT₁ : 1 < (routeTNaturalizedOrdinateLadder U V (j + 1) : ℝ))
    (hmu₁ : routeTPairedKernelBufferedMu ≤
      routeTHeightMatchedExponent T₀ mu₀
        (routeTNaturalizedOrdinateLadder U V (j + 1)))
    (hH : 0 < H)
    (hHR : H ≤ routeTPairedKernelReferenceRelativeWidth
      ((routeTNaturalizedOrdinateLadder U V (j + 1) : ℝ) ^
        routeTHeightMatchedExponent T₀ mu₀
          (routeTNaturalizedOrdinateLadder U V (j + 1)) / 4))
    (hW : 0 ≤ W)
    (hcells : Finset.Ico (routeTNaturalizedOrdinateLadder U V (j + 1))
        (routeTNaturalizedOrdinateLadder U V j) ⊆ Finset.range cellCount)
    (hCtwo : routeTNaturalizedOrdinateLadder U V j ≤
      2 * routeTNaturalizedOrdinateLadder U V (j + 1))
    (hsource : ∀ m ∈ Finset.Ico
        (routeTNaturalizedOrdinateLadder U V (j + 1))
        (routeTNaturalizedOrdinateLadder U V j),
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k
          (routeTNaturalizedOrdinateLadder U V (j + 1))
          (routeTHeightMatchedExponent T₀ mu₀
              (routeTNaturalizedOrdinateLadder U V (j + 1)) / 120) M
          ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * Complex.I)‖ ≤ W)
    (hready : 4 * routeTPairedKernelCommonReferenceCoefficient *
      (routeTNaturalizedOrdinateLadder U V (j + 1) : ℝ) ^
        (-routeTPairedKernelDecayReserve) ≤ 1) :
    let T₁ : ℝ := routeTNaturalizedOrdinateLadder U V (j + 1)
    let mu₁ := routeTHeightMatchedExponent T₀ mu₀ T₁
    let R := routeTPairedKernelReferenceRelativeWidth (T₁ ^ mu₁ / 4)
    (∫ lambda : ℝ in x..(2 * x),
        ‖routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket
          L X k T₀ mu₀ M 1 R H U V j lambda‖ ^ 2) ≤
      4 * (2 * x) *
        (W * (16 * routeTPairedKernelCommonReferenceCoefficient *
          T₁ ^ (-routeTPairedKernelDecayReserve))) ^ 2 *
        ((Finset.Ico (routeTNaturalizedOrdinateLadder U V (j + 1))
          (routeTNaturalizedOrdinateLadder U V j)).card : ℝ) *
        (1 + 2 * (1 + Real.log cellCount)) := by
  let A := routeTNaturalizedOrdinateLadder U V (j + 1)
  let C := routeTNaturalizedOrdinateLadder U V j
  let T₁ : ℝ := A
  let mu₁ := routeTHeightMatchedExponent T₀ mu₀ T₁
  let R := routeTPairedKernelReferenceRelativeWidth (T₁ ^ mu₁ / 4)
  let source : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T₁ (mu₁ / 120) M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  have hsourceContinuous : Continuous source := by
    dsimp only [source]
    exact continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T₁ (mu₁ / 120) M 1
  have hy : ∀ m ∈ Finset.Ico A C, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      T₁ ≤ (m : ℝ) + u ∧ (m : ℝ) + u ≤ 2 * T₁ := by
    intro m hm u hu
    have hmIco := Finset.mem_Ico.mp hm
    rcases hu with ⟨hu0, hu1⟩
    have hmLower : (A : ℝ) ≤ m := by exact_mod_cast hmIco.1
    have hmUpper : ((m : ℝ) + 1) ≤ C := by exact_mod_cast (by omega : m + 1 ≤ C)
    have hCtwoReal : (C : ℝ) ≤ 2 * A := by exact_mod_cast hCtwo
    dsimp only [T₁]
    constructor <;> linarith
  have hbound := integral_norm_sq_maynardFixedAmbientPhysicalDefectPacket_le_bufferedPower
    (x := x) (T := T₁) (mu := mu₁) (H := H) (V := W)
      (cellCount := cellCount) hx (by simpa only [T₁, A] using hT₁)
      (by simpa only [mu₁, T₁, A] using hmu₁) hH
      (by simpa only [R, mu₁, T₁, A] using hHR) hW
      (Finset.Ico A C) (by simpa only [A, C] using hcells)
      source hsourceContinuous (by simpa only [source, T₁, mu₁, A, C] using hsource)
      hy (by simpa only [T₁, A] using hready)
  simpa only [routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket,
    source, R, T₁, mu₁, A, C] using hbound

/-- Natural lower endpoint for the common-mode paired tail. -/
def routeTCommonModeNaturalCutoff (x : ℝ) : ℕ :=
  ⌊routeTCommonModeCutoff x⌋₊

private theorem tendsto_routeTCommonModeCutoff_mul_reference_zero_naturalCell :
    Tendsto (fun x : ℝ => routeTCommonModeCutoff x *
      (2 * routeTCommonModeReferenceRelativeWidth x)) atTop (nhds 0) := by
  let delta : ℝ := 7 / 8 - routeTPhysicalSliceHandoffTheta
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
  have hdecay := (tendsto_rpow_neg_atTop hdelta).const_mul
    (8 * 2 ^ routeTPhysicalSliceHandoffTheta)
  have heq : ∀ᶠ x : ℝ in atTop,
      routeTCommonModeCutoff x *
          (2 * routeTCommonModeReferenceRelativeWidth x) =
        (8 * 2 ^ routeTPhysicalSliceHandoffTheta) * x ^ (-delta) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    unfold routeTCommonModeCutoff routeTCommonModeReferenceRelativeWidth
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le]
    have hpows : x ^ (1 / 8 : ℝ) * x ^ routeTPhysicalSliceHandoffTheta / x =
        x ^ (-delta) := by
      rw [← Real.rpow_add hx]
      have hexp : (1 / 8 : ℝ) + routeTPhysicalSliceHandoffTheta =
          1 + (-delta) := by dsimp only [delta]; ring
      rw [hexp, Real.rpow_add hx, Real.rpow_one]
      field_simp
    calc
      x ^ (1 / 8 : ℝ) *
          (2 * (4 * (2 ^ routeTPhysicalSliceHandoffTheta *
            x ^ routeTPhysicalSliceHandoffTheta) / x)) =
        (8 * 2 ^ routeTPhysicalSliceHandoffTheta) *
          (x ^ (1 / 8 : ℝ) * x ^ routeTPhysicalSliceHandoffTheta / x) := by ring
      _ = _ := by rw [hpows]
  have ht : Tendsto (fun x : ℝ => routeTCommonModeCutoff x *
      (2 * routeTCommonModeReferenceRelativeWidth x)) atTop
      (nhds ((8 * 2 ^ routeTPhysicalSliceHandoffTheta) * 0)) := by
    apply hdecay.congr'
    filter_upwards [heq] with x hx
    exact hx.symm
  simpa only [mul_zero] using ht

/-- Rounding the common central cutoff downward to a natural endpoint preserves the complete
two-width error budget. -/
theorem eventually_routeT_commonMode_naturalCentralErrors_le_of_target :
    ∀ᶠ T : ℝ in atTop, ∀ L : ℕ,
      1 ≤ L → L ≤ routeTPrimeGapPacketSupport T →
      ∀ H0 : ℝ, 0 < H0 →
        H0 ≤ routeTCommonModeReferenceRelativeWidth (routeTPrimeGapPacketBase T) →
      ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T),
        ‖maynardCentralWidthError
          (fun y : ℝ =>
            heathBrownWindowRelevantEligibleDyadicAggregate
              L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                (routeTPrimeGapPacketBase T)
              ((1 : ℂ) + (y : ℝ) * Complex.I))
          lambda
          (lambda * routeTCommonModeReferenceRelativeWidth
            (routeTPrimeGapPacketBase T))
          (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) : ℝ)‖ +
        ‖maynardCentralWidthError
          (fun y : ℝ =>
            heathBrownWindowRelevantEligibleDyadicAggregate
              L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                (routeTPrimeGapPacketBase T)
              ((1 : ℂ) + (y : ℝ) * Complex.I))
          lambda (lambda * H0)
          (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) : ℝ)‖ ≤
        ((2 * Real.pi) *
          (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 2 := by
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hsmall := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    (tendsto_routeTCommonModeCutoff_mul_reference_zero_naturalCell.comp hbaseTop)
  have hcost := eventually_routeT_commonMode_centralCost_le
  have hbaseLarge : ∀ᶠ T : ℝ in atTop, 1 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop 1
  filter_upwards [hsmall, hcost, hbaseLarge,
      eventually_gt_atTop (0 : ℝ)] with T hsmallT hcostT hx1 hT
  intro L hL hLX H0 hH0Input hHReference lambda hlambda
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X 60 x 1
  let U : ℝ := routeTCommonModeCutoff x
  let Uₙ : ℝ := routeTCommonModeNaturalCutoff x
  let R : ℝ := routeTCommonModeReferenceRelativeWidth x
  let H : ℝ := H0
  have hx1' : 1 ≤ x := by simpa only [x] using hx1
  have hx0 : 0 < x := zero_lt_one.trans_le hx1'
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    exact (norm_nonneg
      (heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (1 / 75) x
        ((1 : ℂ) + (0 : ℝ) * Complex.I))).trans
      (norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
        L X 60 hX T (1 / 75) x 1 0 hx0 (by norm_num))
  have hU0 : 0 ≤ U := by dsimp only [U, routeTCommonModeCutoff]; positivity
  have hUₙ0 : 0 ≤ Uₙ := by dsimp only [Uₙ]; positivity
  have hUₙU : Uₙ ≤ U := by
    dsimp only [Uₙ, routeTCommonModeNaturalCutoff, U]
    exact Nat.floor_le hU0
  have hR0 : 0 < R := by
    dsimp only [R]
    exact routeTCommonModeReferenceRelativeWidth_pos hx0
  have hH0 : 0 < H := by simpa only [H] using hH0Input
  have hHR : H ≤ R := by
    simpa only [H, R, x] using hHReference
  have hsmallR : Uₙ * (2 * (lambda * R) / lambda) ≤ 1 := by
    have hUR : Uₙ * (2 * R) ≤ U * (2 * R) := by gcongr
    have hcanonical : U * (2 * R) ≤ 1 := by
      simpa only [Function.comp_apply, U, R, x] using hsmallT
    have hphysical : Uₙ * (2 * (lambda * R) / lambda) = Uₙ * (2 * R) := by
      field_simp [hlambda0.ne']
    rw [hphysical]
    exact hUR.trans hcanonical
  have hsmallH : Uₙ * (2 * (lambda * H) / lambda) ≤ 1 := by
    have hs : Uₙ * (2 * H) ≤ Uₙ * (2 * R) := by gcongr
    have hsR : Uₙ * (2 * R) ≤ 1 := by
      have hUR : Uₙ * (2 * R) ≤ U * (2 * R) := by gcongr
      exact hUR.trans (by simpa only [Function.comp_apply, U, R, x] using hsmallT)
    have hphysical : Uₙ * (2 * (lambda * H) / lambda) = Uₙ * (2 * H) := by
      field_simp [hlambda0.ne']
    rw [hphysical]
    exact hs.trans hsR
  let a : ℝ → ℂ := fun y : ℝ =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (1 / 75) x
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  have haBound : ∀ y, ‖a y‖ ≤ P := by
    intro y
    dsimp only [a, P]
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X 60 hX T (1 / 75) x 1 y hx0 (by norm_num)
  have herrorR := norm_maynardCentralWidthError_le
    a hP0 haBound hlambda0 (mul_pos hlambda0 hR0) hUₙ0 hsmallR
  have herrorH := norm_maynardCentralWidthError_le
    a hP0 haBound hlambda0 (mul_pos hlambda0 hH0) hUₙ0 hsmallH
  have herrorR' : ‖maynardCentralWidthError a lambda (lambda * R) Uₙ‖ ≤
      8 * P * Uₙ ^ 2 * R := by
    convert herrorR using 1
    field_simp [hlambda0.ne']
  have herrorH' : ‖maynardCentralWidthError a lambda (lambda * H) Uₙ‖ ≤
      8 * P * Uₙ ^ 2 * H := by
    convert herrorH using 1
    field_simp [hlambda0.ne']
  have hfactor0 : 0 ≤ 8 * P * Uₙ ^ 2 := by positivity
  have hsum : ‖maynardCentralWidthError a lambda (lambda * R) Uₙ‖ +
      ‖maynardCentralWidthError a lambda (lambda * H) Uₙ‖ ≤
      16 * P * Uₙ ^ 2 * R := by
    calc
      _ ≤ 8 * P * Uₙ ^ 2 * R + 8 * P * Uₙ ^ 2 * H :=
        add_le_add herrorR' herrorH'
      _ ≤ 8 * P * Uₙ ^ 2 * R + 8 * P * Uₙ ^ 2 * R := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hHR hfactor0)
      _ = 16 * P * Uₙ ^ 2 * R := by ring
  have hUscale : Uₙ ^ 2 ≤ U ^ 2 := by gcongr
  have hcostNatural : 16 * P * Uₙ ^ 2 * R ≤ 16 * P * U ^ 2 * R := by
    gcongr
  exact hsum.trans (hcostNatural.trans
    (by simpa only [P, U, R, x, X] using hcostT L hL hLX))

private theorem tendsto_routeTCommonModeReferenceQuarterRatio_atTop :
    Tendsto (fun x : ℝ => (1 / 4 : ℝ) /
      routeTCommonModeReferenceRelativeWidth x) atTop atTop := by
  let theta : ℝ := routeTPhysicalSliceHandoffTheta
  let g : ℝ := 1 - theta
  have hg : 0 < g := by
    dsimp only [g, theta]
    linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
  have hcoeff : 0 < (1 / (16 * 2 ^ theta) : ℝ) := by positivity
  have htop := (tendsto_rpow_atTop hg).const_mul_atTop hcoeff
  have heq : ∀ᶠ x : ℝ in atTop,
      (1 / 4 : ℝ) / routeTCommonModeReferenceRelativeWidth x =
        (1 / (16 * 2 ^ theta) : ℝ) * x ^ g := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    unfold routeTCommonModeReferenceRelativeWidth
    dsimp only [theta, g]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le,
      Real.rpow_sub hx, Real.rpow_one]
    field_simp
    norm_num
  apply htop.congr'
  filter_upwards [heq] with x hx
  exact hx.symm

/-- The common reference itself leaves an arbitrarily large order-50 logarithmic denominator;
therefore every narrower fixed target width shares the same density absorption. -/
theorem eventually_routeTCommonMode_fixedTarget_tailLogRatio_ge_densityInverse :
    ∀ᶠ T : ℝ in atTop,
      ∀ H0 : ℝ, 0 < H0 →
        H0 ≤ routeTCommonModeReferenceRelativeWidth (routeTPrimeGapPacketBase T) →
        1 / routeTCommonModeReferenceDensity ≤
          1 + Real.log ((1 / 4) / H0) / Real.log 2 := by
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hratioTop := tendsto_routeTCommonModeReferenceQuarterRatio_atTop.comp hbaseTop
  have hlogTop := Real.tendsto_log_atTop.comp hratioTop
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdivTop := hlogTop.atTop_div_const hlogTwo
  have hthreshold := hdivTop.eventually_ge_atTop
    (1 / routeTCommonModeReferenceDensity - 1)
  filter_upwards [hthreshold, hbaseTop.eventually_ge_atTop 1] with T hq hx
  simp only [Function.comp_apply] at hq
  intro H0 hH0 hHR
  have hR0 : 0 < routeTCommonModeReferenceRelativeWidth
      (routeTPrimeGapPacketBase T) :=
    routeTCommonModeReferenceRelativeWidth_pos (zero_lt_one.trans_le hx)
  have hratio : (1 / 4 : ℝ) /
        routeTCommonModeReferenceRelativeWidth (routeTPrimeGapPacketBase T) ≤
      (1 / 4 : ℝ) / H0 := by gcongr
  have hlog : Real.log ((1 / 4 : ℝ) /
        routeTCommonModeReferenceRelativeWidth (routeTPrimeGapPacketBase T)) ≤
      Real.log ((1 / 4 : ℝ) / H0) := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (div_pos (by norm_num) hR0))
      (Set.mem_Ioi.mpr (div_pos (by norm_num) hH0)) hratio
  have hdiv : Real.log ((1 / 4 : ℝ) /
        routeTCommonModeReferenceRelativeWidth (routeTPrimeGapPacketBase T)) /
        Real.log 2 ≤ Real.log ((1 / 4 : ℝ) / H0) / Real.log 2 :=
    div_le_div_of_nonneg_right hlog hlogTwo.le
  linarith

theorem eventually_routeT_commonMode_fixedTarget_pairedFarTail_le :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ L : ℕ, 1 ≤ L → L ≤ routeTPrimeGapPacketSupport T →
      ∀ H0 : ℝ, 0 < H0 →
        routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) ≤ H0 →
        H0 ≤ routeTCommonModeReferenceRelativeWidth (routeTPrimeGapPacketBase T) →
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
                (lambda * H0)
                ((1 : ℂ) + (y : ℝ) * Complex.I))‖) ≤
          ((2 * Real.pi) *
            (routeTSmoothWindowCentralMargin *
              routeTCommonModeReferenceDensity / 2)) / 4 := by
  obtain ⟨C, hC, htail⟩ :=
    exists_integral_norm_fixedSource_mul_noncomparablePairedKernel_natOrder_tail_le
      50 (by norm_num)
  have hscalar :=
    eventually_routeTPrimeGapPacket_orderFifty_scalar_cutoff_fixedWidth
      (2 * C) (by positivity)
  have hlog := eventually_routeTCommonMode_fixedTarget_tailLogRatio_ge_densityInverse
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hrefSmall := hbaseTop.eventually
    eventually_routeTCommonModeReferenceRelativeWidth_le_one_fourth
  filter_upwards [hscalar, hlog, hrefSmall, hbaseTop.eventually_ge_atTop 16,
      Filter.eventually_ge_atTop (2 : ℝ)] with
      T hscalarT hlogT hrefSmallT hx16 hT
  intro L hL hLX H0 hH0Input hwidth hHReference lambda hlambda
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let K : ℕ := routeTPrimeGapPacketCutoff T
  let H : ℝ := H0
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
  have hH0 : 0 < H := by simpa only [H] using hH0Input
  have hR0 : 0 < R := by
    dsimp only [R]
    exact routeTCommonModeReferenceRelativeWidth_pos hx0
  have hHR : H ≤ R := by
    simpa only [H, R, x] using hHReference
  have hHquarter : H ≤ 1 / 4 := by
    exact hHR.trans (by simpa only [R, x] using hrefSmallT)
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
      hscalarT L hL (by simpa only [X] using hLX) H hH0 hHquarter
        (by simpa only [H, x] using hwidth)
  have hrho : 0 < routeTCommonModeReferenceDensity :=
    routeTCommonModeReferenceDensity_pos
  have hQlower : 1 / routeTCommonModeReferenceDensity ≤ Q := by
    simpa only [H, Q, x] using hlogT H hH0
      (by simpa only [H, x] using hHReference)
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

theorem eventually_routeT_commonMode_naturalCentralErrors_le :
    ∀ᶠ T : ℝ in atTop, ∀ L : ℕ,
      1 ≤ L → L ≤ routeTPrimeGapPacketSupport T →
      ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T),
        ‖maynardCentralWidthError
          (fun y : ℝ =>
            heathBrownWindowRelevantEligibleDyadicAggregate
              L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                (routeTPrimeGapPacketBase T)
              ((1 : ℂ) + (y : ℝ) * Complex.I))
          lambda
          (lambda * routeTCommonModeReferenceRelativeWidth
            (routeTPrimeGapPacketBase T))
          (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) : ℝ)‖ +
        ‖maynardCentralWidthError
          (fun y : ℝ =>
            heathBrownWindowRelevantEligibleDyadicAggregate
              L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                (routeTPrimeGapPacketBase T)
              ((1 : ℂ) + (y : ℝ) * Complex.I))
          lambda (lambda * routeTPrimeGapPacketWidth lambda)
          (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) : ℝ)‖ ≤
        ((2 * Real.pi) *
          (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 2 := by
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hsmall := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    (tendsto_routeTCommonModeCutoff_mul_reference_zero_naturalCell.comp hbaseTop)
  have hcost := eventually_routeT_commonMode_centralCost_le
  have hbaseLarge : ∀ᶠ T : ℝ in atTop, 1 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop 1
  filter_upwards [hsmall, hcost, hbaseLarge,
      eventually_gt_atTop (0 : ℝ)] with T hsmallT hcostT hx1 hT
  intro L hL hLX lambda hlambda
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X 60 x 1
  let U : ℝ := routeTCommonModeCutoff x
  let Uₙ : ℝ := routeTCommonModeNaturalCutoff x
  let R : ℝ := routeTCommonModeReferenceRelativeWidth x
  let H : ℝ := routeTPrimeGapPacketWidth lambda
  have hx1' : 1 ≤ x := by simpa only [x] using hx1
  have hx0 : 0 < x := zero_lt_one.trans_le hx1'
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    exact (norm_nonneg
      (heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (1 / 75) x
        ((1 : ℂ) + (0 : ℝ) * Complex.I))).trans
      (norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
        L X 60 hX T (1 / 75) x 1 0 hx0 (by norm_num))
  have hU0 : 0 ≤ U := by dsimp only [U, routeTCommonModeCutoff]; positivity
  have hUₙ0 : 0 ≤ Uₙ := by dsimp only [Uₙ]; positivity
  have hUₙU : Uₙ ≤ U := by
    dsimp only [Uₙ, routeTCommonModeNaturalCutoff, U]
    exact Nat.floor_le hU0
  have hR0 : 0 < R := by
    dsimp only [R]
    exact routeTCommonModeReferenceRelativeWidth_pos hx0
  have hH0 : 0 < H := by dsimp only [H, routeTPrimeGapPacketWidth]; positivity
  have hHR : H ≤ R := by
    dsimp only [H, R]
    exact routeTPrimeGapPacketWidth_le_commonModeReference hx1'
      (by simpa only [x] using hlambda)
  have hsmallR : Uₙ * (2 * (lambda * R) / lambda) ≤ 1 := by
    have hUR : Uₙ * (2 * R) ≤ U * (2 * R) := by gcongr
    have hcanonical : U * (2 * R) ≤ 1 := by
      simpa only [Function.comp_apply, U, R, x] using hsmallT
    have hphysical : Uₙ * (2 * (lambda * R) / lambda) = Uₙ * (2 * R) := by
      field_simp [hlambda0.ne']
    rw [hphysical]
    exact hUR.trans hcanonical
  have hsmallH : Uₙ * (2 * (lambda * H) / lambda) ≤ 1 := by
    have hs : Uₙ * (2 * H) ≤ Uₙ * (2 * R) := by gcongr
    have hsR : Uₙ * (2 * R) ≤ 1 := by
      have hUR : Uₙ * (2 * R) ≤ U * (2 * R) := by gcongr
      exact hUR.trans (by simpa only [Function.comp_apply, U, R, x] using hsmallT)
    have hphysical : Uₙ * (2 * (lambda * H) / lambda) = Uₙ * (2 * H) := by
      field_simp [hlambda0.ne']
    rw [hphysical]
    exact hs.trans hsR
  let a : ℝ → ℂ := fun y : ℝ =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (1 / 75) x
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  have haBound : ∀ y, ‖a y‖ ≤ P := by
    intro y
    dsimp only [a, P]
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X 60 hX T (1 / 75) x 1 y hx0 (by norm_num)
  have herrorR := norm_maynardCentralWidthError_le
    a hP0 haBound hlambda0 (mul_pos hlambda0 hR0) hUₙ0 hsmallR
  have herrorH := norm_maynardCentralWidthError_le
    a hP0 haBound hlambda0 (mul_pos hlambda0 hH0) hUₙ0 hsmallH
  have herrorR' : ‖maynardCentralWidthError a lambda (lambda * R) Uₙ‖ ≤
      8 * P * Uₙ ^ 2 * R := by
    convert herrorR using 1
    field_simp [hlambda0.ne']
  have herrorH' : ‖maynardCentralWidthError a lambda (lambda * H) Uₙ‖ ≤
      8 * P * Uₙ ^ 2 * H := by
    convert herrorH using 1
    field_simp [hlambda0.ne']
  have hfactor0 : 0 ≤ 8 * P * Uₙ ^ 2 := by positivity
  have hsum : ‖maynardCentralWidthError a lambda (lambda * R) Uₙ‖ +
      ‖maynardCentralWidthError a lambda (lambda * H) Uₙ‖ ≤
      16 * P * Uₙ ^ 2 * R := by
    calc
      _ ≤ 8 * P * Uₙ ^ 2 * R + 8 * P * Uₙ ^ 2 * H :=
        add_le_add herrorR' herrorH'
      _ ≤ 8 * P * Uₙ ^ 2 * R + 8 * P * Uₙ ^ 2 * R := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hHR hfactor0)
      _ = 16 * P * Uₙ ^ 2 * R := by ring
  have hUscale : Uₙ ^ 2 ≤ U ^ 2 := by gcongr
  have hcostNatural : 16 * P * Uₙ ^ 2 * R ≤ 16 * P * U ^ 2 * R := by
    gcongr
  exact hsum.trans (hcostNatural.trans
    (by simpa only [P, U, R, x, X] using hcostT L hL hLX))

/-- The natural common-mode cutoff eventually contains at least two unit cells. -/
theorem eventually_two_le_routeTCommonModeNaturalCutoff :
    ∀ᶠ T : ℝ in atTop,
      2 ≤ routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) := by
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hcutTop : Tendsto
      (fun T : ℝ => routeTCommonModeCutoff (routeTPrimeGapPacketBase T))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp hbaseTop
  filter_upwards [hcutTop.eventually_ge_atTop 2] with T hT
  exact Nat.le_floor hT

/-- The natural common-mode cutoff and the canonical far cutoff leave a nondegenerate
factor-two annulus, as required by literal natural-cell shell extraction. -/
theorem eventually_two_mul_routeTCommonModeNaturalCutoff_le_primeGapPacketCutoff :
    ∀ᶠ T : ℝ in atTop,
      2 * routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) ≤
        routeTPrimeGapPacketCutoff T := by
  have hdecay :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 5)).const_mul 4
  have hzero : (4 : ℝ) * 0 = 0 := by ring
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
  have hcut0 : 0 ≤ routeTCommonModeCutoff (routeTPrimeGapPacketBase T) := by
    unfold routeTCommonModeCutoff
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
      T ^ (1 / 5 : ℝ) = T ^ (1 + (-(4 / 5 : ℝ))) := by
        norm_num
      _ = T ^ (1 : ℝ) * T ^ (-(4 / 5 : ℝ)) := Real.rpow_add hT0 1 _
      _ = T * T ^ (-(4 / 5 : ℝ)) := by rw [Real.rpow_one]
  have hquarter : T ^ (1 / 5 : ℝ) ≤ T / 4 := by
    rw [hcollapse]
    have hnonneg : 0 ≤ T ^ (-(4 / 5 : ℝ)) := Real.rpow_nonneg hT0.le _
    nlinarith
  have hfloor : T / 2 ≤ (routeTPrimeGapPacketCutoff T : ℝ) := by
    dsimp only [routeTPrimeGapPacketCutoff]
    have hlt := Nat.lt_floor_add_one T
    linarith
  have hnaturalLe :
      (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) : ℝ) ≤
        routeTCommonModeCutoff (routeTPrimeGapPacketBase T) := by
    exact Nat.floor_le hcut0
  have hreal :
      (2 * routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) : ℕ) ≤
        routeTPrimeGapPacketCutoff T := by
    exact_mod_cast (calc
      2 * (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) : ℝ) ≤
          2 * routeTCommonModeCutoff (routeTPrimeGapPacketBase T) := by gcongr
      _ ≤ 2 * T ^ (1 / 5 : ℝ) := by gcongr
      _ ≤ T / 2 := by linarith
      _ ≤ (routeTPrimeGapPacketCutoff T : ℝ) := hfloor)
  exact hreal

/-- Canonical prime-free paired-tail producer whose common cutoff is a natural cell boundary. -/
theorem exists_eventually_routeT_primeFree_fixedSource_commonMode_naturalPairedHighTail :
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
                routeTCommonModeReferenceDensity / 2)) / 2 ≤
            ‖maynardWidthHighTail
                (fun y : ℝ =>
                  heathBrownWindowRelevantEligibleDyadicAggregate
                    L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                      (routeTPrimeGapPacketBase T)
                    ((1 : ℂ) + (y : ℝ) * Complex.I))
                lambda
                (lambda * routeTCommonModeReferenceRelativeWidth
                  (routeTPrimeGapPacketBase T))
                (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) : ℝ) -
              maynardWidthHighTail
                (fun y : ℝ =>
                  heathBrownWindowRelevantEligibleDyadicAggregate
                    L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                      (routeTPrimeGapPacketBase T)
                    ((1 : ℂ) + (y : ℝ) * Complex.I))
                lambda (lambda * routeTPrimeGapPacketWidth lambda)
                (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) : ℝ)‖ := by
  have hproducer :=
    exists_eventually_routeT_primeFree_fixedSource_commonMode_pairedHighTail
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hmass := hbaseTop.eventually
    eventually_routeT_commonMode_fixedReference_smooth_vonMangoldt_mass_lower
  have hcentral := eventually_routeT_commonMode_naturalCentralErrors_le
  have hrefSmall := hbaseTop.eventually
    eventually_routeTCommonModeReferenceRelativeWidth_le_one_fourth
  have hbaseLarge : ∀ᶠ T : ℝ in atTop, 16 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop 16
  have htargetSmall : ∀ᶠ T : ℝ in atTop,
      routeTPrimeGapPacketBase T ^ (-(49 / 80 : ℝ)) ≤ 1 / 4 := by
    have hlim := (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 49 / 80)).comp hbaseTop
    exact Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4) hlim
  have hscale : ∀ᶠ T : ℝ in atTop,
      4 * (((2 ^ 120 : ℕ) : ℝ)) ≤ T ^ (119 / 75 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 119 / 75)).eventually_ge_atTop
      (4 * (((2 ^ 120 : ℕ) : ℝ)))
  have hleakAll := eventually_routeT_primePowerLeakage_le_of_power_width_const
    (theta := (31 / 80 : ℝ)) (epsilon :=
      routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)
      (by norm_num) (by positivity [routeTSmoothWindowCentralMargin_pos,
        routeTCommonModeReferenceDensity_pos])
  rcases eventually_atTop.1 hleakAll with ⟨Q, hQ⟩
  have hleakThreshold : ∀ᶠ T : ℝ in atTop,
      Q ≤ routeTPrimeGapPacketBase T := hbaseTop.eventually_ge_atTop Q
  filter_upwards [hproducer, hmass, hcentral, hrefSmall, hbaseLarge,
      htargetSmall, hscale, hleakThreshold,
      eventually_ge_atTop (2 : ℝ)] with T hproducerT hmassT hcentralT
        hrefSmallT hbase16 htargetBase hscaleT hthreshold hT
  rcases hproducerT with ⟨L, hL, hLX, hXL, hLscale, _hold⟩
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  have hT0 : 0 < T := by linarith
  have hTone : 1 < T := by linarith
  have hx0 : 0 < x := by
    dsimp only [x, routeTPrimeGapPacketBase]
    positivity
  have hx1 : 1 ≤ x := by
    dsimp only [x] at hbase16 ⊢
    linarith
  have hceilLower : 3 * x ≤ (X : ℝ) := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.le_ceil _
  refine ⟨L, hL, hLX, hXL, hLscale, ?_⟩
  intro lambda hlambda hprimeFree
  let H : ℝ := routeTPrimeGapPacketWidth lambda
  let R : ℝ := routeTCommonModeReferenceRelativeWidth x
  let U : ℝ := routeTCommonModeNaturalCutoff x
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hlambda2 : 2 ≤ lambda := by linarith [hlambda.1, hbase16]
  have hH0 : 0 < H := by
    dsimp only [H, routeTPrimeGapPacketWidth]
    positivity
  have hR0 : 0 < R := by
    dsimp only [R]
    exact routeTCommonModeReferenceRelativeWidth_pos hx0
  have hHquarter : H ≤ 1 / 4 := by
    have hanti := Real.rpow_le_rpow_of_nonpos hx0 hlambda.1
      (by norm_num : (-(49 / 80 : ℝ)) ≤ 0)
    dsimp only [H, routeTPrimeGapPacketWidth]
    exact hanti.trans (by simpa only [x] using htargetBase)
  have hRquarter : R ≤ 1 / 4 := by simpa only [R, x] using hrefSmallT
  have hscaleLambda :
      (((2 ^ (2 * 60) : ℕ) : ℝ)) * T ^ (1 / 75 : ℝ) ≤ lambda := by
    have hmul :
        (4 * (((2 ^ 120 : ℕ) : ℝ))) * (T ^ (1 / 75 : ℝ) / 4) ≤
          T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hscaleT
        (div_nonneg (Real.rpow_nonneg hT0.le (1 / 75 : ℝ)) (by norm_num))
    calc
      (((2 ^ (2 * 60) : ℕ) : ℝ)) * T ^ (1 / 75 : ℝ) =
          (4 * (((2 ^ 120 : ℕ) : ℝ))) * (T ^ (1 / 75 : ℝ) / 4) := by
            norm_num; ring
      _ ≤ T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) := hmul
      _ = T ^ (8 / 5 : ℝ) / 4 := by
        rw [show T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) =
          (T ^ (119 / 75 : ℝ) * T ^ (1 / 75 : ℝ)) / 4 by ring,
          ← Real.rpow_add hT0]
        congr 2
        norm_num
      _ = x := by rfl
      _ ≤ lambda := hlambda.1
  have hpowerEq : lambda ^ (31 / 80 : ℝ) = lambda * H := by
    dsimp only [H, routeTPrimeGapPacketWidth]
    calc
      lambda ^ (31 / 80 : ℝ) = lambda ^ (1 + (-(49 / 80 : ℝ))) := by
        congr 1
        norm_num
      _ = lambda ^ (1 : ℝ) * lambda ^ (-(49 / 80 : ℝ)) :=
        Real.rpow_add hlambda0 1 (-(49 / 80 : ℝ))
      _ = lambda * lambda ^ (-(49 / 80 : ℝ)) := by rw [Real.rpow_one]
  have hphysicalH1 : 1 ≤ lambda * H := by
    rw [← hpowerEq]
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hphysicalHle : lambda * H ≤ lambda := by
    calc
      lambda * H ≤ lambda * 1 :=
        mul_le_mul_of_nonneg_left (hHquarter.trans (by norm_num)) hlambda0.le
      _ = lambda := by ring
  have hwidthH : 1 ≤ 2 * (lambda * H) := by linarith
  have hsupportQuarter : lambda + 2 * (lambda / 4) ≤ (X : ℝ) := by
    calc
      lambda + 2 * (lambda / 4) = (3 / 2 : ℝ) * lambda := by ring
      _ ≤ (3 / 2 : ℝ) * (2 * x) :=
        mul_le_mul_of_nonneg_left hlambda.2 (by norm_num)
      _ = 3 * x := by ring
      _ ≤ (X : ℝ) := hceilLower
  have hHmul : lambda * H ≤ lambda / 4 := by
    calc
      lambda * H ≤ lambda * (1 / 4) :=
        mul_le_mul_of_nonneg_left hHquarter hlambda0.le
      _ = lambda / 4 := by ring
  have hRmul : lambda * R ≤ lambda / 4 := by
    calc
      lambda * R ≤ lambda * (1 / 4) :=
        mul_le_mul_of_nonneg_left hRquarter hlambda0.le
      _ = lambda / 4 := by ring
  have hsupportH : lambda + 2 * (lambda * H) ≤ (X : ℝ) := by
    calc
      lambda + 2 * (lambda * H) ≤ lambda + 2 * (lambda / 4) :=
        add_le_add_right
          (mul_le_mul_of_nonneg_left hHmul (by norm_num : (0 : ℝ) ≤ 2)) lambda
      _ ≤ (X : ℝ) := hsupportQuarter
  have hsupportR : lambda + 2 * (lambda * R) ≤ (X : ℝ) := by
    calc
      lambda + 2 * (lambda * R) ≤ lambda + 2 * (lambda / 4) :=
        add_le_add_right
          (mul_le_mul_of_nonneg_left hRmul (by norm_num : (0 : ℝ) ≤ 2)) lambda
      _ ≤ (X : ℝ) := hsupportQuarter
  have hleakage := hQ lambda (hthreshold.trans hlambda.1) (lambda * H)
    (by rw [← hpowerEq]) hphysicalHle
  have href := hmassT lambda (by simpa only [x] using hlambda)
  have hlow := hcentralT L hL (by simpa only [X] using hLX) lambda
    (by simpa only [x] using hlambda)
  have hresult := primeFree_forces_fixedSource_commonMode_highTailDifference
    L X 60 hXL (T0 := T) (t := (1 / 75 : ℝ)) (x := x) (lambda := lambda)
      (H := H) (R := R) (U := U) (rho := routeTCommonModeReferenceDensity)
      hx0 hlambda hTone hscaleLambda hlambda2 hH0 hR0
      routeTCommonModeReferenceDensity_pos hwidthH hsupportH hsupportR
      hprimeFree href.le hleakage (by simpa only [x, X, H, R, U] using hlow)
  simpa only [x, X, H, R, U] using hresult

theorem exists_eventually_routeT_primeFree_fixedSource_commonMode_fixedTarget_naturalPairedHighTail :
    ∀ᶠ T : ℝ in atTop,
      ∃ L : ℕ, 1 ≤ L ∧
        L ≤ routeTPrimeGapPacketSupport T ∧
        routeTPrimeGapPacketSupport T < (L + 1) ^ (60 : ℕ) ∧
        (L : ℝ) ≤ T ^ (2 / 75 : ℝ) ∧
        ∀ H0 : ℝ, 0 < H0 →
          routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) ≤ H0 →
          H0 ≤ routeTCommonModeReferenceRelativeWidth (routeTPrimeGapPacketBase T) →
          ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
              (2 * routeTPrimeGapPacketBase T),
            Chebyshev.theta (lambda + 2 * (lambda * H0)) -
                Chebyshev.theta lambda = 0 →
            ((2 * Real.pi) *
                (routeTSmoothWindowCentralMargin *
                  routeTCommonModeReferenceDensity / 2)) / 2 ≤
              ‖maynardWidthHighTail
                  (fun y : ℝ =>
                    heathBrownWindowRelevantEligibleDyadicAggregate
                      L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                        (routeTPrimeGapPacketBase T)
                      ((1 : ℂ) + (y : ℝ) * Complex.I))
                  lambda
                  (lambda * routeTCommonModeReferenceRelativeWidth
                    (routeTPrimeGapPacketBase T))
                  (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) : ℝ) -
                maynardWidthHighTail
                  (fun y : ℝ =>
                    heathBrownWindowRelevantEligibleDyadicAggregate
                      L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                        (routeTPrimeGapPacketBase T)
                      ((1 : ℂ) + (y : ℝ) * Complex.I))
                  lambda (lambda * H0)
                  (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) : ℝ)‖ := by
  have hproducer :=
    exists_eventually_routeT_primeFree_fixedSource_commonMode_naturalPairedHighTail
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hmass := hbaseTop.eventually
    eventually_routeT_commonMode_fixedReference_smooth_vonMangoldt_mass_lower
  have hcentral := eventually_routeT_commonMode_naturalCentralErrors_le_of_target
  have hrefSmall := hbaseTop.eventually
    eventually_routeTCommonModeReferenceRelativeWidth_le_one_fourth
  have hbaseLarge : ∀ᶠ T : ℝ in atTop, 16 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop 16
  have hscale : ∀ᶠ T : ℝ in atTop,
      4 * (((2 ^ 120 : ℕ) : ℝ)) ≤ T ^ (119 / 75 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 119 / 75)).eventually_ge_atTop
      (4 * (((2 ^ 120 : ℕ) : ℝ)))
  have hleakAll := eventually_routeT_primePowerLeakage_le_of_power_width_const
    (theta := (31 / 80 : ℝ)) (epsilon :=
      routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)
      (by norm_num) (by positivity [routeTSmoothWindowCentralMargin_pos,
        routeTCommonModeReferenceDensity_pos])
  rcases eventually_atTop.1 hleakAll with ⟨Q, hQ⟩
  have hleakThreshold : ∀ᶠ T : ℝ in atTop,
      Q ≤ routeTPrimeGapPacketBase T := hbaseTop.eventually_ge_atTop Q
  filter_upwards [hproducer, hmass, hcentral, hrefSmall, hbaseLarge,
      hscale, hleakThreshold, eventually_ge_atTop (2 : ℝ)] with
      T hproducerT hmassT hcentralT hrefSmallT hbase16 hscaleT hthreshold hT
  rcases hproducerT with ⟨L, hL, hLX, hXL, hLscale, _hold⟩
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  have hT0 : 0 < T := by linarith
  have hTone : 1 < T := by linarith
  have hx0 : 0 < x := by
    dsimp only [x, routeTPrimeGapPacketBase]
    positivity
  have hceilLower : 3 * x ≤ (X : ℝ) := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.le_ceil _
  refine ⟨L, hL, hLX, hXL, hLscale, ?_⟩
  intro H0 hH0Input hwidthBase hHReference lambda hlambda hprimeFree
  let H : ℝ := H0
  let R : ℝ := routeTCommonModeReferenceRelativeWidth x
  let U : ℝ := routeTCommonModeNaturalCutoff x
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hlambda2 : 2 ≤ lambda := by linarith [hlambda.1, hbase16]
  have hH0 : 0 < H := by simpa only [H] using hH0Input
  have hR0 : 0 < R := by
    dsimp only [R]
    exact routeTCommonModeReferenceRelativeWidth_pos hx0
  have hHR : H ≤ R := by simpa only [H, R, x] using hHReference
  have hHquarter : H ≤ 1 / 4 :=
    hHR.trans (by simpa only [R, x] using hrefSmallT)
  have hRquarter : R ≤ 1 / 4 := by simpa only [R, x] using hrefSmallT
  have hscaleLambda :
      (((2 ^ (2 * 60) : ℕ) : ℝ)) * T ^ (1 / 75 : ℝ) ≤ lambda := by
    have hmul :
        (4 * (((2 ^ 120 : ℕ) : ℝ))) * (T ^ (1 / 75 : ℝ) / 4) ≤
          T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hscaleT
        (div_nonneg (Real.rpow_nonneg hT0.le (1 / 75 : ℝ)) (by norm_num))
    calc
      (((2 ^ (2 * 60) : ℕ) : ℝ)) * T ^ (1 / 75 : ℝ) =
          (4 * (((2 ^ 120 : ℕ) : ℝ))) * (T ^ (1 / 75 : ℝ) / 4) := by
            norm_num; ring
      _ ≤ T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) := hmul
      _ = T ^ (8 / 5 : ℝ) / 4 := by
        rw [show T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) =
          (T ^ (119 / 75 : ℝ) * T ^ (1 / 75 : ℝ)) / 4 by ring,
          ← Real.rpow_add hT0]
        congr 2
        norm_num
      _ = x := by rfl
      _ ≤ lambda := hlambda.1
  have hwidthLambda : routeTPrimeGapPacketWidth lambda ≤ H := by
    have hanti := Real.rpow_le_rpow_of_nonpos hx0 hlambda.1
      (by norm_num : (-(49 / 80 : ℝ)) ≤ 0)
    have hwidthx : routeTPrimeGapPacketWidth lambda ≤
        routeTPrimeGapPacketWidth x := by
      simpa only [routeTPrimeGapPacketWidth] using hanti
    exact hwidthx.trans (by simpa only [H, x] using hwidthBase)
  have hpowerEq : lambda ^ (31 / 80 : ℝ) =
      lambda * routeTPrimeGapPacketWidth lambda := by
    dsimp only [routeTPrimeGapPacketWidth]
    calc
      lambda ^ (31 / 80 : ℝ) = lambda ^ (1 + (-(49 / 80 : ℝ))) := by
        congr 1
        norm_num
      _ = lambda ^ (1 : ℝ) * lambda ^ (-(49 / 80 : ℝ)) :=
        Real.rpow_add hlambda0 1 (-(49 / 80 : ℝ))
      _ = lambda * lambda ^ (-(49 / 80 : ℝ)) := by rw [Real.rpow_one]
  have hphysicalLower : lambda ^ (31 / 80 : ℝ) ≤ lambda * H := by
    rw [hpowerEq]
    exact mul_le_mul_of_nonneg_left hwidthLambda hlambda0.le
  have hphysicalH1 : 1 ≤ lambda * H :=
    (Real.one_le_rpow (by linarith) (by norm_num)).trans hphysicalLower
  have hphysicalHle : lambda * H ≤ lambda := by
    calc
      lambda * H ≤ lambda * 1 :=
        mul_le_mul_of_nonneg_left (hHquarter.trans (by norm_num)) hlambda0.le
      _ = lambda := by ring
  have hwidthH : 1 ≤ 2 * (lambda * H) := by linarith
  have hsupportQuarter : lambda + 2 * (lambda / 4) ≤ (X : ℝ) := by
    calc
      lambda + 2 * (lambda / 4) = (3 / 2 : ℝ) * lambda := by ring
      _ ≤ (3 / 2 : ℝ) * (2 * x) :=
        mul_le_mul_of_nonneg_left hlambda.2 (by norm_num)
      _ = 3 * x := by ring
      _ ≤ (X : ℝ) := hceilLower
  have hHmul : lambda * H ≤ lambda / 4 := by
    calc
      lambda * H ≤ lambda * (1 / 4) :=
        mul_le_mul_of_nonneg_left hHquarter hlambda0.le
      _ = lambda / 4 := by ring
  have hRmul : lambda * R ≤ lambda / 4 := by
    calc
      lambda * R ≤ lambda * (1 / 4) :=
        mul_le_mul_of_nonneg_left hRquarter hlambda0.le
      _ = lambda / 4 := by ring
  have hsupportH : lambda + 2 * (lambda * H) ≤ (X : ℝ) := by
    calc
      lambda + 2 * (lambda * H) ≤ lambda + 2 * (lambda / 4) :=
        add_le_add_right
          (mul_le_mul_of_nonneg_left hHmul (by norm_num : (0 : ℝ) ≤ 2)) lambda
      _ ≤ (X : ℝ) := hsupportQuarter
  have hsupportR : lambda + 2 * (lambda * R) ≤ (X : ℝ) := by
    calc
      lambda + 2 * (lambda * R) ≤ lambda + 2 * (lambda / 4) :=
        add_le_add_right
          (mul_le_mul_of_nonneg_left hRmul (by norm_num : (0 : ℝ) ≤ 2)) lambda
      _ ≤ (X : ℝ) := hsupportQuarter
  have hleakage := hQ lambda (hthreshold.trans hlambda.1) (lambda * H)
    hphysicalLower hphysicalHle
  have href := hmassT lambda (by simpa only [x] using hlambda)
  have hlow := hcentralT L hL (by simpa only [X] using hLX) H hH0
    (by simpa only [H, x] using hHReference) lambda
    (by simpa only [x] using hlambda)
  have hresult := primeFree_forces_fixedSource_commonMode_highTailDifference
    L X 60 hXL (T0 := T) (t := (1 / 75 : ℝ)) (x := x) (lambda := lambda)
      (H := H) (R := R) (U := U) (rho := routeTCommonModeReferenceDensity)
      hx0 hlambda hTone hscaleLambda hlambda2 hH0 hR0
      routeTCommonModeReferenceDensity_pos hwidthH hsupportH hsupportR
      (by simpa only [H] using hprimeFree) href.le hleakage
      (by simpa only [x, X, H, R, U] using hlow)
  simpa only [x, X, H, R, U] using hresult

/-- A fixed target width satisfying the Route-T leakage floor reaches a literal natural-endpoint
paired annulus, with target coefficients independent of the physical base. -/
theorem exists_eventually_routeT_primeFree_fixedSource_commonMode_fixedTarget_naturalPairedAnnulus :
    ∀ᶠ T : ℝ in atTop,
      ∃ L : ℕ, 1 ≤ L ∧
        L ≤ routeTPrimeGapPacketSupport T ∧
        routeTPrimeGapPacketSupport T < (L + 1) ^ (60 : ℕ) ∧
        (L : ℝ) ≤ T ^ (2 / 75 : ℝ) ∧
        ∀ H0 : ℝ, 0 < H0 →
          routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) ≤ H0 →
          H0 ≤ routeTCommonModeReferenceRelativeWidth (routeTPrimeGapPacketBase T) →
          ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
              (2 * routeTPrimeGapPacketBase T),
            Chebyshev.theta (lambda + 2 * (lambda * H0)) -
                Chebyshev.theta lambda = 0 →
            ((2 * Real.pi) *
                (routeTSmoothWindowCentralMargin *
                  routeTCommonModeReferenceDensity / 2)) / 4 ≤
              ‖∫ y in {y : ℝ |
                  (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) : ℝ) ≤ |y| ∧
                    |y| < (routeTPrimeGapPacketCutoff T : ℝ)},
                heathBrownWindowRelevantEligibleDyadicAggregate
                      L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                        (routeTPrimeGapPacketBase T)
                      ((1 : ℂ) + (y : ℝ) * Complex.I) *
                  (routeTNormalizedSmoothWindowMellin lambda
                      (lambda * routeTCommonModeReferenceRelativeWidth
                        (routeTPrimeGapPacketBase T))
                      ((1 : ℂ) + (y : ℝ) * Complex.I) -
                    routeTNormalizedSmoothWindowMellin lambda (lambda * H0)
                      ((1 : ℂ) + (y : ℝ) * Complex.I))‖ := by
  have hpaired :=
    exists_eventually_routeT_primeFree_fixedSource_commonMode_fixedTarget_naturalPairedHighTail
  have hfar := eventually_routeT_commonMode_fixedTarget_pairedFarTail_le
  have hcut := eventually_routeTCommonModeCutoff_le_primeGapPacketCutoff
  filter_upwards [hpaired, hfar, hcut, Filter.eventually_ge_atTop (2 : ℝ)] with
      T hpairedT hfarT hcutT hT
  obtain ⟨L, hL, hLX, hXL, hLscale, hlarge⟩ := hpairedT
  refine ⟨L, hL, hLX, hXL, hLscale, ?_⟩
  intro H0 hH0Input hwidth hHReference lambda hlambda hprimeFree
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let R : ℝ := routeTCommonModeReferenceRelativeWidth x
  let H : ℝ := H0
  let U : ℝ := routeTCommonModeNaturalCutoff x
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
  have hH0 : 0 < H := by simpa only [H] using hH0Input
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
    simpa only [a, x, X, R, H, U] using hlarge H0 hH0Input hwidth hHReference
      lambda (by simpa only [x] using hlambda) hprimeFree
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
      hfarT L hL (by simpa only [X] using hLX) H0 hH0Input hwidth hHReference
        lambda (by simpa only [x] using hlambda)
  have hU0 : 0 ≤ U := by
    dsimp only [U]
    exact_mod_cast Nat.zero_le (routeTCommonModeNaturalCutoff x)
  have hnaturalLe : U ≤ routeTCommonModeCutoff x := by
    dsimp only [U, routeTCommonModeNaturalCutoff]
    exact Nat.floor_le (Real.rpow_nonneg hx0.le _)
  have hUV : U ≤ V := hnaturalLe.trans
    (by simpa only [V, x] using hcutT)
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


/-- A nonzero paired annulus with natural endpoints lands directly in a literal natural-cell
shell, retaining the reference-target difference through positive-wing and shell selection. -/
theorem exists_fixedSource_naturalized_pairedShell_of_annulus_canonicalCount
    (L X k U V : ℕ) {T mu M N H R B : ℝ}
    (hT : 1 < T) (hX : 1 ≤ X) (hM : 0 < M)
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hB0 : 0 < B) (hU : 2 ≤ U) (hUV : 2 * U ≤ V)
    (hB : B ≤ ‖∫ y in {y : ℝ | (U : ℝ) ≤ |y| ∧ |y| < (V : ℝ)},
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T (mu / 120) M
            ((1 : ℂ) + (y : ℝ) * Complex.I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * Complex.I))‖) :
    ∃ j ∈ Finset.range (routeTOrdinateShellCount U V),
      let A := routeTNaturalizedOrdinateLadder U V (j + 1)
      let C := routeTNaturalizedOrdinateLadder U V j
      let T₁ : ℝ := A
      let mu₁ := routeTHeightMatchedExponent T mu T₁
      1 < T₁ ∧ A < C ∧ C ≤ 2 * A ∧ T₁ ^ mu₁ = T ^ mu ∧
        (B / 4) / (routeTOrdinateShellCount U V : ℝ) ≤
          ‖routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket
            L X k T mu M N R H U V j 1‖ := by
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
  have hU0 : (0 : ℝ) ≤ U := by positivity
  have hUVreal : (U : ℝ) ≤ V := by exact_mod_cast (by omega : U ≤ V)
  have hpositive : B / 4 ≤ ‖∫ y in (U : ℝ)..(V : ℝ), f y‖ :=
    norm_intervalIntegral_positiveWing_ge_quarter_of_annulus_of_conj
      hf hconj hB0 hU0 hUVreal (by simpa only [f] using hB)
  have hpacket : B / 4 ≤ ‖routeTFixedSourceAdjacentIntervalPacket
      L X k T (mu / 120) M N R H 1 U V‖ := by
    convert hpositive using 1
    all_goals
      norm_num [f, routeTFixedSourceAdjacentIntervalPacket,
        routeTFixedSourceAdjacentIntegrand]
  exact exists_fixedSource_naturalized_pairedShell_of_naturalInterval_canonicalCount
    L X k U V hT hN hH hR hU hUV (by positivity) hpacket

/-- **Canonical natural-cell cancellation-preserving prime-free annulus.**  Eventually one frozen Heath--Brown
source works for every physical base in the block.  Prime-freeness forces a fixed positive paired
defect on the literal annulus between the common central cutoff and `floor T`; reference-target
cancellation is retained pointwise throughout. -/
theorem exists_eventually_routeT_primeFree_fixedSource_commonMode_naturalPairedAnnulus :
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
                (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T) : ℝ) ≤ |y| ∧
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
  have hpaired := exists_eventually_routeT_primeFree_fixedSource_commonMode_naturalPairedHighTail
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
  let U : ℝ := routeTCommonModeNaturalCutoff x
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
  have hU0 : 0 ≤ U := by
    dsimp only [U]
    exact_mod_cast Nat.zero_le (routeTCommonModeNaturalCutoff x)
  have hnaturalLe : U ≤ routeTCommonModeCutoff x := by
    dsimp only [U, routeTCommonModeNaturalCutoff]
    exact Nat.floor_le (Real.rpow_nonneg hx0.le _)
  have hUV : U ≤ V := hnaturalLe.trans
    (by simpa only [V, x] using hcutT)
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

/-- **Unconditional natural-cell source insertion for Route T.**  One frozen source and one
finite natural shell family are selected before the physical base varies.  Every prime-free base
forces a nonzero member of that exact `Finset.Ico` family, with the paired kernel intact. -/
theorem exists_eventually_routeT_primeFree_fixedSource_commonMode_naturalCellShell :
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
          ∃ j ∈ Finset.range (routeTOrdinateShellCount
              (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
              (routeTPrimeGapPacketCutoff T)),
            let A := routeTNaturalizedOrdinateLadder
              (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
              (routeTPrimeGapPacketCutoff T) (j + 1)
            let C := routeTNaturalizedOrdinateLadder
              (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
              (routeTPrimeGapPacketCutoff T) j
            let T₁ : ℝ := A
            let mu₁ := routeTHeightMatchedExponent T (8 / 5 : ℝ) T₁
            1 < T₁ ∧ A < C ∧ C ≤ 2 * A ∧
              T₁ ^ mu₁ = T ^ (8 / 5 : ℝ) ∧
              (((((2 * Real.pi) *
                    (routeTSmoothWindowCentralMargin *
                      routeTCommonModeReferenceDensity / 2)) / 4) / 4) /
                  (routeTOrdinateShellCount
                    (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
                    (routeTPrimeGapPacketCutoff T) : ℝ)) ≤
                ‖routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket
                  L (routeTPrimeGapPacketSupport T) 60 T (8 / 5 : ℝ)
                  (routeTPrimeGapPacketBase T) lambda
                  (lambda * routeTCommonModeReferenceRelativeWidth
                    (routeTPrimeGapPacketBase T))
                  (lambda * routeTPrimeGapPacketWidth lambda)
                  (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
                  (routeTPrimeGapPacketCutoff T) j 1‖ := by
  have hannulus :=
    exists_eventually_routeT_primeFree_fixedSource_commonMode_naturalPairedAnnulus
  have hU := eventually_two_le_routeTCommonModeNaturalCutoff
  have hUV :=
    eventually_two_mul_routeTCommonModeNaturalCutoff_le_primeGapPacketCutoff
  filter_upwards [hannulus, hU, hUV,
      Filter.eventually_gt_atTop (1 : ℝ)] with T hannulusT hUT hUVT hT
  obtain ⟨L, hL, hLX, hXL, hLscale, hlarge⟩ := hannulusT
  refine ⟨L, hL, hLX, hXL, hLscale, ?_⟩
  intro lambda hlambda hprimeFree
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let U : ℕ := routeTCommonModeNaturalCutoff x
  let V : ℕ := routeTPrimeGapPacketCutoff T
  let R : ℝ := routeTCommonModeReferenceRelativeWidth x
  let H : ℝ := routeTPrimeGapPacketWidth lambda
  let B : ℝ := ((2 * Real.pi) *
    (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 4
  have hx0 : 0 < x := by
    dsimp only [x, routeTPrimeGapPacketBase]
    positivity
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hR0 : 0 < R := by
    dsimp only [R]
    exact routeTCommonModeReferenceRelativeWidth_pos hx0
  have hH0 : 0 < H := by
    dsimp only [H, routeTPrimeGapPacketWidth]
    positivity
  have hU' : 2 ≤ U := by simpa only [U, x] using hUT
  have hUV' : 2 * U ≤ V := by simpa only [U, V, x] using hUVT
  have hB0 : 0 < B := by
    dsimp only [B]
    positivity [routeTSmoothWindowCentralMargin_pos,
      routeTCommonModeReferenceDensity_pos]
  have hlarge' : B ≤ ‖∫ y in {y : ℝ | (U : ℝ) ≤ |y| ∧ |y| < (V : ℝ)},
      heathBrownWindowRelevantEligibleDyadicAggregate
            L X 60 T ((8 / 5 : ℝ) / 120) x
            ((1 : ℂ) + (y : ℝ) * Complex.I) *
        (routeTNormalizedSmoothWindowMellin lambda (lambda * R)
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin lambda (lambda * H)
            ((1 : ℂ) + (y : ℝ) * Complex.I))‖ := by
    rw [show (8 / 5 : ℝ) / 120 = 1 / 75 by norm_num]
    simpa only [B, U, V, X, x, R, H] using hlarge lambda
      (by simpa only [x] using hlambda) hprimeFree
  have hshell :=
    exists_fixedSource_naturalized_pairedShell_of_annulus_canonicalCount
      L X 60 U V (T := T) (mu := (8 / 5 : ℝ)) (M := x) (N := lambda)
        (H := lambda * H) (R := lambda * R) (B := B)
        hT hX hx0 hlambda0 (mul_pos hlambda0 hH0) (mul_pos hlambda0 hR0)
        hB0 hU' hUV' hlarge'
  simpa only [x, X, U, V, R, H, B] using hshell

/-- Physical-base insertion and proportional dilation are exactly the same natural-cell packet. -/
theorem routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket_physicalScale
    (L X k : ℕ) (T₀ mu₀ M lambda R H U V : ℝ) (j : ℕ) :
    routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket
        L X k T₀ mu₀ M lambda (lambda * R) (lambda * H) U V j 1 =
      routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket
        L X k T₀ mu₀ M 1 R H U V j lambda := by
  simp only [routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket,
    maynardFixedAmbientPhysicalDefectPacket, one_mul, mul_one]

/-- Unconditional fixed-target source insertion in the exact spatial-dilation coordinates needed
by the natural-cell `L²/L⁴` estimates. -/
theorem exists_eventually_routeT_primeFree_fixedSource_commonMode_fixedTarget_naturalCellShell :
    ∀ᶠ T : ℝ in atTop,
      ∃ L : ℕ, 1 ≤ L ∧
        L ≤ routeTPrimeGapPacketSupport T ∧
        routeTPrimeGapPacketSupport T < (L + 1) ^ (60 : ℕ) ∧
        (L : ℝ) ≤ T ^ (2 / 75 : ℝ) ∧
        ∀ H0 : ℝ, 0 < H0 →
          routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) ≤ H0 →
          H0 ≤ routeTCommonModeReferenceRelativeWidth (routeTPrimeGapPacketBase T) →
          ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
              (2 * routeTPrimeGapPacketBase T),
            Chebyshev.theta (lambda + 2 * (lambda * H0)) -
                Chebyshev.theta lambda = 0 →
            ∃ j ∈ Finset.range (routeTOrdinateShellCount
                (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
                (routeTPrimeGapPacketCutoff T)),
              let A := routeTNaturalizedOrdinateLadder
                (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
                (routeTPrimeGapPacketCutoff T) (j + 1)
              let C := routeTNaturalizedOrdinateLadder
                (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
                (routeTPrimeGapPacketCutoff T) j
              let T₁ : ℝ := A
              let mu₁ := routeTHeightMatchedExponent T (8 / 5 : ℝ) T₁
              1 < T₁ ∧ A < C ∧ C ≤ 2 * A ∧
                T₁ ^ mu₁ = T ^ (8 / 5 : ℝ) ∧
                (((((2 * Real.pi) *
                      (routeTSmoothWindowCentralMargin *
                        routeTCommonModeReferenceDensity / 2)) / 4) / 4) /
                    (routeTOrdinateShellCount
                      (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
                      (routeTPrimeGapPacketCutoff T) : ℝ)) ≤
                  ‖routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket
                    L (routeTPrimeGapPacketSupport T) 60 T (8 / 5 : ℝ)
                    (routeTPrimeGapPacketBase T) 1
                    (routeTCommonModeReferenceRelativeWidth
                      (routeTPrimeGapPacketBase T)) H0
                    (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
                    (routeTPrimeGapPacketCutoff T) j lambda‖ := by
  have hannulus :=
    exists_eventually_routeT_primeFree_fixedSource_commonMode_fixedTarget_naturalPairedAnnulus
  have hU := eventually_two_le_routeTCommonModeNaturalCutoff
  have hUV :=
    eventually_two_mul_routeTCommonModeNaturalCutoff_le_primeGapPacketCutoff
  filter_upwards [hannulus, hU, hUV,
      Filter.eventually_gt_atTop (1 : ℝ)] with T hannulusT hUT hUVT hT
  obtain ⟨L, hL, hLX, hXL, hLscale, hlarge⟩ := hannulusT
  refine ⟨L, hL, hLX, hXL, hLscale, ?_⟩
  intro H0 hH0Input hwidth hHReference lambda hlambda hprimeFree
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let U : ℕ := routeTCommonModeNaturalCutoff x
  let V : ℕ := routeTPrimeGapPacketCutoff T
  let R : ℝ := routeTCommonModeReferenceRelativeWidth x
  let H : ℝ := H0
  let B : ℝ := ((2 * Real.pi) *
    (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 4
  have hx0 : 0 < x := by
    dsimp only [x, routeTPrimeGapPacketBase]
    positivity
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hR0 : 0 < R := by
    dsimp only [R]
    exact routeTCommonModeReferenceRelativeWidth_pos hx0
  have hH0 : 0 < H := by simpa only [H] using hH0Input
  have hU' : 2 ≤ U := by simpa only [U, x] using hUT
  have hUV' : 2 * U ≤ V := by simpa only [U, V, x] using hUVT
  have hB0 : 0 < B := by
    dsimp only [B]
    positivity [routeTSmoothWindowCentralMargin_pos,
      routeTCommonModeReferenceDensity_pos]
  have hlarge' : B ≤ ‖∫ y in {y : ℝ | (U : ℝ) ≤ |y| ∧ |y| < (V : ℝ)},
      heathBrownWindowRelevantEligibleDyadicAggregate
            L X 60 T ((8 / 5 : ℝ) / 120) x
            ((1 : ℂ) + (y : ℝ) * Complex.I) *
        (routeTNormalizedSmoothWindowMellin lambda (lambda * R)
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin lambda (lambda * H)
            ((1 : ℂ) + (y : ℝ) * Complex.I))‖ := by
    rw [show (8 / 5 : ℝ) / 120 = 1 / 75 by norm_num]
    simpa only [B, U, V, X, x, R, H] using
      hlarge H0 hH0Input hwidth hHReference lambda
        (by simpa only [x] using hlambda) hprimeFree
  have hshell :=
    exists_fixedSource_naturalized_pairedShell_of_annulus_canonicalCount
      L X 60 U V (T := T) (mu := (8 / 5 : ℝ)) (M := x) (N := lambda)
        (H := lambda * H) (R := lambda * R) (B := B)
        hT hX hx0 hlambda0 (mul_pos hlambda0 hH0) (mul_pos hlambda0 hR0)
        hB0 hU' hUV' hlarge'
  simpa only [x, X, U, V, R, H, B,
    routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket_physicalScale] using hshell


/-- Common-mode defect threshold after paying only the canonical ordinate-shell selector. -/
def routeTCommonModeNaturalCellDefectThreshold (T : ℝ) : ℝ :=
  (((((2 * Real.pi) *
      (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 4) / 4) /
    (routeTOrdinateShellCount
      (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
      (routeTPrimeGapPacketCutoff T) : ℝ))

/-- One fixed-target common-mode natural-shell superlevel set. -/
def routeTCommonModeFixedTargetNaturalShellBadSet
    (T : ℝ) (L : ℕ) (H0 : ℝ) (j : ℕ) : Set ℝ :=
  {lambda |
    routeTCommonModeNaturalCellDefectThreshold T ≤
      ‖routeTFixedSourceNaturalizedOrdinateShellPhysicalPacket
        L (routeTPrimeGapPacketSupport T) 60 T (8 / 5 : ℝ)
        (routeTPrimeGapPacketBase T) 1
        (routeTCommonModeReferenceRelativeWidth (routeTPrimeGapPacketBase T)) H0
        (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
        (routeTPrimeGapPacketCutoff T) j lambda‖}

/-- Finite natural-shell family selected before the physical base varies. -/
def routeTCommonModeFixedTargetNaturalShellCover
    (T : ℝ) (L : ℕ) (H0 : ℝ) : Set ℝ :=
  ⋃ j ∈ Finset.range (routeTOrdinateShellCount
      (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
      (routeTPrimeGapPacketCutoff T)),
    routeTCommonModeFixedTargetNaturalShellBadSet T L H0 j

/-- Every admissible fixed-target prime-free base belongs to one member of a single finite
natural-shell family fixed before the base varies. -/
theorem exists_eventually_routeT_fixedTarget_primeFree_subset_commonModeNaturalShellCover :
    ∀ᶠ T : ℝ in atTop,
      ∃ L : ℕ, 1 ≤ L ∧
        L ≤ routeTPrimeGapPacketSupport T ∧
        routeTPrimeGapPacketSupport T < (L + 1) ^ (60 : ℕ) ∧
        (L : ℝ) ≤ T ^ (2 / 75 : ℝ) ∧
        ∀ H0 : ℝ, 0 < H0 →
          routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) ≤ H0 →
          H0 ≤ routeTCommonModeReferenceRelativeWidth (routeTPrimeGapPacketBase T) →
          routeTFixedWidthPrimeFreeBaseSet T H0 ⊆
            routeTCommonModeFixedTargetNaturalShellCover T L H0 := by
  filter_upwards [
      exists_eventually_routeT_primeFree_fixedSource_commonMode_fixedTarget_naturalCellShell]
      with T hsource
  obtain ⟨L, hL, hLX, hXL, hLscale, hlarge⟩ := hsource
  refine ⟨L, hL, hLX, hXL, hLscale, ?_⟩
  intro H0 hH0 hwidth hHReference lambda hlambda
  obtain ⟨j, hj, _hT₁, _hAC, _hCtwo, _hmatch, hlargej⟩ :=
    hlarge H0 hH0 hwidth hHReference lambda hlambda.1 hlambda.2
  unfold routeTCommonModeFixedTargetNaturalShellCover
  apply Set.mem_iUnion_of_mem j
  apply Set.mem_iUnion_of_mem hj
  simpa only [routeTCommonModeFixedTargetNaturalShellBadSet,
    routeTCommonModeNaturalCellDefectThreshold, Set.mem_setOf_eq] using hlargej

/-- The fixed-target prime-free measure pays exactly one finite sum over the canonical natural
shell family; no union over physical bases or target widths is introduced. -/
theorem exists_eventually_volume_routeT_fixedTarget_primeFree_le_sum_commonModeNaturalShell :
    ∀ᶠ T : ℝ in atTop,
      ∃ L : ℕ, 1 ≤ L ∧
        L ≤ routeTPrimeGapPacketSupport T ∧
        routeTPrimeGapPacketSupport T < (L + 1) ^ (60 : ℕ) ∧
        (L : ℝ) ≤ T ^ (2 / 75 : ℝ) ∧
        ∀ H0 : ℝ, 0 < H0 →
          routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) ≤ H0 →
          H0 ≤ routeTCommonModeReferenceRelativeWidth (routeTPrimeGapPacketBase T) →
          (volume.restrict (Set.Icc (routeTPrimeGapPacketBase T)
              (2 * routeTPrimeGapPacketBase T))).real
              (routeTFixedWidthPrimeFreeBaseSet T H0) ≤
            ∑ j ∈ Finset.range (routeTOrdinateShellCount
                (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
                (routeTPrimeGapPacketCutoff T)),
              (volume.restrict (Set.Icc (routeTPrimeGapPacketBase T)
                (2 * routeTPrimeGapPacketBase T))).real
                (routeTCommonModeFixedTargetNaturalShellBadSet T L H0 j) := by
  filter_upwards [
      exists_eventually_routeT_fixedTarget_primeFree_subset_commonModeNaturalShellCover]
      with T hcover
  obtain ⟨L, hL, hLX, hXL, hLscale, hsub⟩ := hcover
  refine ⟨L, hL, hLX, hXL, hLscale, ?_⟩
  intro H0 hH0 hwidth hHReference
  let μ := volume.restrict (Set.Icc (routeTPrimeGapPacketBase T)
    (2 * routeTPrimeGapPacketBase T))
  calc
    μ.real (routeTFixedWidthPrimeFreeBaseSet T H0) ≤
        μ.real (routeTCommonModeFixedTargetNaturalShellCover T L H0) :=
      measureReal_mono (hsub H0 hH0 hwidth hHReference)
    _ ≤ ∑ j ∈ Finset.range (routeTOrdinateShellCount
          (routeTCommonModeNaturalCutoff (routeTPrimeGapPacketBase T))
          (routeTPrimeGapPacketCutoff T)),
        μ.real (routeTCommonModeFixedTargetNaturalShellBadSet T L H0 j) := by
      unfold routeTCommonModeFixedTargetNaturalShellCover
      exact measureReal_biUnion_finset_le _ _


end

end RHTower.Sieve
