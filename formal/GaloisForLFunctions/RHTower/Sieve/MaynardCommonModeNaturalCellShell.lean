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

end

end RHTower.Sieve
