import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorCommonZeroPacket
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorExponentialLayerCake
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorRouteTEdgeSuperpolylog

/-!
# Route T density-to-physical weighted zero packet

This module closes the layer-cake handoff from the uniform `16/5` zero-density exponent to the
zero weights appearing in a short-interval explicit formula.  A small physical slack is essential:
choose interval exponent `701/1000`, hence height-scale exponent `1000/299`.  Then

`1000/299 - 16/5 = 216/1495 > 0`.

The exact exponential layer cake, common zero packet, uniform Route-T zero-free edge, and its
superpolylogarithmic absorption combine to prove that the full multiplicity-weighted high-zero
packet tends to zero.  No discretization, asymptotic premise, or RH assumption is introduced.
-/

open Complex Filter Metric Set ArithmeticFunction Finset Topology MeasureTheory intervalIntegral

namespace RHTower.Sieve

noncomputable section

/-- Physical exponent corresponding to the interval length `N^(701/1000)` and height
`N/H = X`. -/
def inghamRouteTPhysicalScaleExponent : ℝ := 1000 / 299

/-- Positive exponent left after combining physical zero weight with density exponent `16/5`. -/
def inghamRouteTDensitySlack : ℝ := 216 / 1495

theorem inghamRouteTPhysicalScaleExponent_pos :
    0 < inghamRouteTPhysicalScaleExponent := by
  unfold inghamRouteTPhysicalScaleExponent
  norm_num

theorem inghamRouteTDensitySlack_pos : 0 < inghamRouteTDensitySlack := by
  unfold inghamRouteTDensitySlack
  norm_num

theorem inghamRouteTPhysicalScaleExponent_sub_density :
    inghamRouteTPhysicalScaleExponent - 16 / 5 = inghamRouteTDensitySlack := by
  unfold inghamRouteTPhysicalScaleExponent inghamRouteTDensitySlack
  norm_num

theorem inghamRouteTPhysicalScaleExponent_low_strip_margin :
    1 + inghamRouteTPhysicalScaleExponent * (7 / 10 - 1) = -(1 / 299 : ℝ) := by
  unfold inghamRouteTPhysicalScaleExponent
  norm_num

/-- Multiplicity weight of one residue-unit zero. -/
def inghamRouteTZeroMultiplicity (w : ℂ) : ℝ :=
  ((analyticOrderAt zetaResidueUnit w).toNat : ℝ)

theorem inghamRouteTZeroMultiplicity_nonneg (w : ℂ) :
    0 ≤ inghamRouteTZeroMultiplicity w := by
  unfold inghamRouteTZeroMultiplicity
  positivity

/-- Common packet restricted to the density range. -/
def inghamRouteTHighZeroPacket (X : ℕ) : Finset ℂ :=
  (inghamRouteTCommonZeroPacket X).filter (fun w => 7 / 10 ≤ w.re)

/-- Every common-packet member is a genuine Xi zero in the open critical strip. -/
theorem mem_inghamRouteTCommonZeroPacket_strip
    {X : ℕ} {w : ℂ} (hw : w ∈ inghamRouteTCommonZeroPacket X) :
    0 < w.re ∧ w.re < 1 ∧ RHTower.xi w = 0 := by
  have hwdata := mem_zetaResidueUnitClosedRectangleZeros.mp hw
  have hwK := Complex.mem_reProdIm.mp hwdata.1
  have hcenterFour : inghamUniformGabrielCenter (7 / 10 : ℝ) ≤ 4 := by
    unfold inghamUniformGabrielCenter
    norm_num
  have hwre : w.re ∈ Set.Icc (inghamUniformGabrielCenter (7 / 10 : ℝ)) 4 := by
    simpa [inghamRouteTCommonZeroPacket, uIcc_of_le hcenterFour] using hwK.1
  have hwre0 : 0 < w.re := by
    have hc : 0 < inghamUniformGabrielCenter (7 / 10 : ℝ) := by
      unfold inghamUniformGabrielCenter
      norm_num
    exact hc.trans_le hwre.1
  have hw1 : w ≠ 1 := by
    intro heq
    rw [heq, zetaResidueUnit_one] at hwdata
    norm_num at hwdata
  have hzeta : riemannZeta w = 0 := by
    by_contra hne
    exact ((zetaResidueUnit_ne_zero_iff hw1).2 hne) hwdata.2
  have hwre1 : w.re < 1 := by
    by_contra hcon
    exact (riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcon)) hzeta
  exact ⟨hwre0, hwre1,
    (RHTower.xi_zero_iff_zeta_zero_of_mem_strip hwre0 hwre1).2 hzeta⟩

theorem inghamRouteTZeroMultiplicity_pos_of_mem_common
    {X : ℕ} {w : ℂ} (hw : w ∈ inghamRouteTCommonZeroPacket X) :
    0 < inghamRouteTZeroMultiplicity w := by
  have hstrip := mem_inghamRouteTCommonZeroPacket_strip hw
  have horder : analyticOrderAt zetaResidueUnit w =
      analyticOrderAt RHTower.xi w :=
    analyticOrderAt_zetaResidueUnit_eq_xi_of_mem_strip ⟨hstrip.1, hstrip.2.1⟩
  have hne : (analyticOrderAt zetaResidueUnit w).toNat ≠ 0 := by
    rw [horder]
    exact RHTower.xi_order_toNat_ne_zero hstrip.2.2
  unfold inghamRouteTZeroMultiplicity
  exact_mod_cast Nat.pos_of_ne_zero hne

theorem mem_inghamRouteTHighZeroPacket_bounds
    {X : ℕ} {w : ℂ} (hw : w ∈ inghamRouteTHighZeroPacket X) :
    7 / 10 ≤ w.re ∧ w.re < 1 := by
  rw [inghamRouteTHighZeroPacket, Finset.mem_filter] at hw
  exact ⟨hw.2, (mem_inghamRouteTCommonZeroPacket_strip hw.1).2.1⟩

/-- The zero-free envelope is an actual upper edge for every member of the high packet. -/
theorem exists_eventually_inghamRouteTHighZeroPacket_re_le_edge :
    ∃ A : ℝ,
      ∀ᶠ X : ℕ in atTop,
        ∀ w ∈ inghamRouteTHighZeroPacket X,
          w.re ≤ 1 - routeTContourShiftEnvelope A ((X : ℝ) - 1) := by
  obtain ⟨A, hzero⟩ :=
    exists_eventually_zetaLittlewoodZeroCountAbove_eq_zero_routeT_envelope
  have hshiftZero : Tendsto
      (fun X : ℕ => routeTContourShiftEnvelope A ((X : ℝ) - 1))
      atTop (𝓝 0) := by
    have htend : Tendsto (fun X : ℕ => (X : ℝ) - 1) atTop atTop := by
      simpa only [sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
    exact (tendsto_routeTContourShiftEnvelope_zero A).comp htend
  have hsmall : ∀ᶠ X : ℕ in atTop,
      routeTContourShiftEnvelope A ((X : ℝ) - 1) < 3 / 10 :=
    hshiftZero.eventually (eventually_lt_nhds (by norm_num))
  refine ⟨A, ?_⟩
  filter_upwards [hzero, hsmall, eventually_ge_atTop (1 : ℕ)] with X hzeroX hsmallX hX
  intro w hw
  let edge : ℝ := 1 - routeTContourShiftEnvelope A ((X : ℝ) - 1)
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hT0 : 0 ≤ (X : ℝ) - 1 := by linarith
  have hshiftPos : 0 < routeTContourShiftEnvelope A ((X : ℝ) - 1) :=
    routeTContourShiftEnvelope_pos A hT0
  have hedge0 : 7 / 10 ≤ edge := by dsimp only [edge]; linarith
  have hedge1 : edge < 1 := by dsimp only [edge]; linarith
  have hcount : zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter edge) 4
      ((X : ℝ) - 2) edge = 0 := hzeroX (by rfl)
  have hsum : ∑ z ∈ (inghamRouteTCommonZeroPacket X).filter (fun z => edge ≤ z.re),
      inghamRouteTZeroMultiplicity z = 0 := by
    rw [zetaLittlewoodZeroCountAbove_eq_commonZeroPacket hedge0 hedge1] at hcount
    simpa only [inghamRouteTZeroMultiplicity] using hcount
  by_contra hnot
  have hwCommon : w ∈ inghamRouteTCommonZeroPacket X :=
    (Finset.mem_filter.mp hw).1
  have hwEdge : edge ≤ w.re := le_of_not_ge hnot
  have hwFilter : w ∈
      (inghamRouteTCommonZeroPacket X).filter (fun z => edge ≤ z.re) :=
    Finset.mem_filter.mpr ⟨hwCommon, hwEdge⟩
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun z _ => inghamRouteTZeroMultiplicity_nonneg z)).mp hsum w hwFilter
  exact (ne_of_gt (inghamRouteTZeroMultiplicity_pos_of_mem_common hwCommon)) hterm

/-- Physical explicit-formula weight of the high zero packet. -/
def inghamRouteTHighZeroWeightedMass (X : ℕ) : ℝ :=
  ∑ w ∈ inghamRouteTHighZeroPacket X,
    (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (w.re - 1)) *
      inghamRouteTZeroMultiplicity w

/-- Exact exponential layer-cake decomposition of the physical high-zero weight. -/
theorem inghamRouteTHighZeroWeightedMass_eq_layerCake
    {X : ℕ} (hX : 1 ≤ X) :
    inghamRouteTHighZeroWeightedMass X =
      (∫ sigma in (7 / 10 : ℝ)..1,
        Real.log ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) *
          ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) ^ (sigma - 1) *
          ∑ w ∈ (inghamRouteTHighZeroPacket X).filter (fun w => sigma < w.re),
            inghamRouteTZeroMultiplicity w) +
      ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) ^ ((7 / 10 : ℝ) - 1) *
        ∑ w ∈ inghamRouteTHighZeroPacket X, inghamRouteTZeroMultiplicity w := by
  let B : ℝ := (X : ℝ) ^ inghamRouteTPhysicalScaleExponent
  have hXR : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hB : 0 < B := Real.rpow_pos_of_pos hXR _
  have hbounds : ∀ w ∈ inghamRouteTHighZeroPacket X,
      (7 / 10 : ℝ) ≤ w.re ∧ w.re ≤ 1 := by
    intro w hw
    have h := mem_inghamRouteTHighZeroPacket_bounds hw
    exact ⟨h.1, h.2.le⟩
  have hlayer := RHTower.sum_rpow_sub_eq_integral_weighted_count
    (B := B) (σ₀ := (7 / 10 : ℝ)) (σ₁ := 1)
    (inghamRouteTHighZeroPacket X) (fun w : ℂ => w.re)
    inghamRouteTZeroMultiplicity hB hbounds
  have hweight : ∀ w : ℂ,
      (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (w.re - 1)) =
        B ^ (w.re - 1) := by
    intro w
    dsimp only [B]
    exact Real.rpow_mul hXR.le _ _
  unfold inghamRouteTHighZeroWeightedMass
  calc
    (∑ w ∈ inghamRouteTHighZeroPacket X,
        (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (w.re - 1)) *
          inghamRouteTZeroMultiplicity w) =
      ∑ w ∈ inghamRouteTHighZeroPacket X,
        ((B ^ (w.re - 1) - B ^ ((7 / 10 : ℝ) - 1)) *
            inghamRouteTZeroMultiplicity w +
          B ^ ((7 / 10 : ℝ) - 1) * inghamRouteTZeroMultiplicity w) := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [hweight]
        ring
    _ = (∑ w ∈ inghamRouteTHighZeroPacket X,
          (B ^ (w.re - 1) - B ^ ((7 / 10 : ℝ) - 1)) *
            inghamRouteTZeroMultiplicity w) +
        B ^ ((7 / 10 : ℝ) - 1) *
          ∑ w ∈ inghamRouteTHighZeroPacket X,
            inghamRouteTZeroMultiplicity w := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
    _ = _ := by
      rw [hlayer]

/-- Strict high-packet counts are bounded by the detector's non-strict moving count. -/
theorem inghamRouteTHighZeroPacket_strictCount_le_detector
    {X : ℕ} {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma < 1) :
    (∑ w ∈ (inghamRouteTHighZeroPacket X).filter (fun w => sigma < w.re),
        inghamRouteTZeroMultiplicity w) ≤
      zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
        ((X : ℝ) - 2) sigma := by
  let S := (inghamRouteTHighZeroPacket X).filter (fun w => sigma < w.re)
  let T := (inghamRouteTCommonZeroPacket X).filter (fun w => sigma ≤ w.re)
  have hsub : S ⊆ T := by
    intro w hw
    simp only [S, Finset.mem_filter] at hw
    simp only [T, Finset.mem_filter]
    have hwHigh := Finset.mem_filter.mp hw.1
    exact ⟨hwHigh.1, hw.2.le⟩
  have hsum : (∑ w ∈ S, inghamRouteTZeroMultiplicity w) ≤
      ∑ w ∈ T, inghamRouteTZeroMultiplicity w :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun w _ _ => inghamRouteTZeroMultiplicity_nonneg w)
  rw [zetaLittlewoodZeroCountAbove_eq_commonZeroPacket hsigma0 hsigma1]
  simpa only [S, T, inghamRouteTZeroMultiplicity] using hsum

/-- The physical exponent and density exponent combine to exactly the positive Route-T slack. -/
theorem inghamRouteT_density_weight_rpow_identity
    {X sigma : ℝ} (hX : 0 < X) :
    X ^ (inghamRouteTPhysicalScaleExponent * (sigma - 1)) *
        X ^ ((16 / 5 : ℝ) * (1 - sigma)) =
      X ^ (-inghamRouteTDensitySlack * (1 - sigma)) := by
  rw [← Real.rpow_add hX]
  congr 1
  rw [← inghamRouteTPhysicalScaleExponent_sub_density]
  ring

/-- Density bound simplified to one physical exponential and one fixed polylogarithm. -/
theorem inghamRouteTHighZeroPacket_strictCount_le_simplified
    {K sigma : ℝ} {X : ℕ} (hK : 0 ≤ K) (hX : 1 ≤ X)
    (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma < 1)
    (hdensity :
      zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
          ((X : ℝ) - 2) sigma ≤
        K * (1 + Real.log (X : ℝ)) ^ (14 : ℕ) *
          (1 +
            (X : ℝ) ^ ((16 / 5 : ℝ) * (1 - sigma)) *
              (1 + Real.log (X : ℝ)) ^ (2 : ℕ) +
            (1 + Real.log (X : ℝ)) ^ (2 : ℕ))) :
    (∑ w ∈ (inghamRouteTHighZeroPacket X).filter (fun w => sigma < w.re),
        inghamRouteTZeroMultiplicity w) ≤
      3 * K * (1 + Real.log (X : ℝ)) ^ (16 : ℕ) *
        (X : ℝ) ^ ((16 / 5 : ℝ) * (1 - sigma)) := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hLog : 1 ≤ 1 + Real.log (X : ℝ) := by
    linarith [Real.log_nonneg hXR]
  have hu : 0 ≤ 1 - sigma := by linarith
  have hP : 1 ≤ (X : ℝ) ^ ((16 / 5 : ℝ) * (1 - sigma)) :=
    Real.one_le_rpow hXR (by positivity)
  let L : ℝ := 1 + Real.log (X : ℝ)
  let P : ℝ := (X : ℝ) ^ ((16 / 5 : ℝ) * (1 - sigma))
  have hL : 1 ≤ L := by simpa only [L] using hLog
  have hL2 : 1 ≤ L ^ (2 : ℕ) := one_le_pow₀ (by simpa only [L] using hLog)
  have htail : 1 + P * L ^ (2 : ℕ) + L ^ (2 : ℕ) ≤
      3 * P * L ^ (2 : ℕ) := by
    have hP0 : 0 ≤ P := le_trans zero_le_one (by simpa only [P] using hP)
    have hL0 : 0 ≤ L ^ (2 : ℕ) := pow_nonneg (by linarith) _
    have h1 : 1 ≤ P * L ^ (2 : ℕ) :=
      one_le_mul_of_one_le_of_one_le (by simpa only [P] using hP) hL2
    have h2 : L ^ (2 : ℕ) ≤ P * L ^ (2 : ℕ) :=
      by simpa only [P, one_mul] using
        (mul_le_mul_of_nonneg_right hP hL0)
    linarith
  have hcount := (inghamRouteTHighZeroPacket_strictCount_le_detector
    hsigma0 hsigma1).trans hdensity
  have hcoeff : 0 ≤ K * L ^ (14 : ℕ) :=
    mul_nonneg hK (pow_nonneg (by linarith) _)
  have hmul := mul_le_mul_of_nonneg_left htail hcoeff
  calc
    (∑ w ∈ (inghamRouteTHighZeroPacket X).filter (fun w => sigma < w.re),
        inghamRouteTZeroMultiplicity w) ≤
      K * L ^ (14 : ℕ) * (1 + P * L ^ (2 : ℕ) + L ^ (2 : ℕ)) := by
        simpa only [L, P] using hcount
    _ ≤ K * L ^ (14 : ℕ) * (3 * P * L ^ (2 : ℕ)) := hmul
    _ = 3 * K * L ^ (16 : ℕ) * P := by ring
    _ = _ := by simp only [L, P]

/-- Pointwise exponential layer-cake kernel bound on the whole density interval. -/
theorem norm_inghamRouteTHighZero_layerCake_integrand_le
    {K shift sigma : ℝ} {X : ℕ}
    (hK : 0 ≤ K) (hX : 1 ≤ X)
    (hupper : ∀ w ∈ inghamRouteTHighZeroPacket X, w.re ≤ 1 - shift)
    (hdensity : ∀ {tau : ℝ}, 7 / 10 ≤ tau → tau < 1 →
      zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter tau) 4
          ((X : ℝ) - 2) tau ≤
        K * (1 + Real.log (X : ℝ)) ^ (14 : ℕ) *
          (1 +
            (X : ℝ) ^ ((16 / 5 : ℝ) * (1 - tau)) *
              (1 + Real.log (X : ℝ)) ^ (2 : ℕ) +
            (1 + Real.log (X : ℝ)) ^ (2 : ℕ)))
    (hsigma : sigma ∈ Set.Icc (7 / 10 : ℝ) 1) :
    ‖Real.log ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) *
        ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) ^ (sigma - 1) *
        (∑ w ∈ (inghamRouteTHighZeroPacket X).filter (fun w => sigma < w.re),
          inghamRouteTZeroMultiplicity w)‖ ≤
      3 * inghamRouteTPhysicalScaleExponent * K *
        (1 + Real.log (X : ℝ)) ^ (17 : ℕ) *
        (X : ℝ) ^ (-inghamRouteTDensitySlack * shift) := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXRpos : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hXR
  have hlog0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hXR
  have hL : 1 ≤ 1 + Real.log (X : ℝ) := by linarith
  have hq : 0 < inghamRouteTPhysicalScaleExponent :=
    inghamRouteTPhysicalScaleExponent_pos
  have hlogB : Real.log ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) =
      inghamRouteTPhysicalScaleExponent * Real.log (X : ℝ) :=
    Real.log_rpow hXRpos _
  have hBpow :
      ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) ^ (sigma - 1) =
        (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (sigma - 1)) := by
    rw [← Real.rpow_mul (zero_le_one.trans hXR)]
  by_cases hsigma1 : sigma < 1
  · by_cases hedge : 1 - shift ≤ sigma
    · have hempty :
          (inghamRouteTHighZeroPacket X).filter (fun w => sigma < w.re) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro w hw hpred
        have := hupper w hw
        linarith
      simp [hempty]
      positivity
    · have hsigmaEdge : sigma < 1 - shift := lt_of_not_ge hedge
      have hcount := inghamRouteTHighZeroPacket_strictCount_le_simplified
        hK hX hsigma.1 hsigma1 (hdensity hsigma.1 hsigma1)
      let L : ℝ := 1 + Real.log (X : ℝ)
      let P : ℝ := (X : ℝ) ^ ((16 / 5 : ℝ) * (1 - sigma))
      let Q : ℝ := (X : ℝ) ^
        (inghamRouteTPhysicalScaleExponent * (sigma - 1))
      let E : ℝ := (X : ℝ) ^ (-inghamRouteTDensitySlack * (1 - sigma))
      let Eedge : ℝ := (X : ℝ) ^ (-inghamRouteTDensitySlack * shift)
      have hcount' :
          (∑ w ∈ (inghamRouteTHighZeroPacket X).filter (fun w => sigma < w.re),
              inghamRouteTZeroMultiplicity w) ≤ 3 * K * L ^ (16 : ℕ) * P := by
        simpa only [L, P] using hcount
      have hcount0 : 0 ≤
          ∑ w ∈ (inghamRouteTHighZeroPacket X).filter (fun w => sigma < w.re),
            inghamRouteTZeroMultiplicity w := by
        apply Finset.sum_nonneg
        intro w hw
        exact inghamRouteTZeroMultiplicity_nonneg w
      have hQ0 : 0 ≤ Q := Real.rpow_nonneg (zero_le_one.trans hXR) _
      have hkernel0 : 0 ≤
          Real.log ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) *
            ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) ^ (sigma - 1) *
            (∑ w ∈ (inghamRouteTHighZeroPacket X).filter (fun w => sigma < w.re),
              inghamRouteTZeroMultiplicity w) := by
        rw [hlogB, hBpow]
        exact mul_nonneg (mul_nonneg (mul_nonneg hq.le hlog0) hQ0) hcount0
      have hQP : Q * P = E := by
        dsimp only [Q, P, E]
        exact inghamRouteT_density_weight_rpow_identity hXRpos
      have hEedge : E ≤ Eedge := by
        dsimp only [E, Eedge]
        apply Real.rpow_le_rpow_of_exponent_le hXR
        have hd := inghamRouteTDensitySlack_pos
        have hu : shift ≤ 1 - sigma := by linarith
        have hm := mul_le_mul_of_nonneg_left hu hd.le
        linarith
      have hlogL : Real.log (X : ℝ) * L ^ (16 : ℕ) ≤ L ^ (17 : ℕ) := by
        calc
          Real.log (X : ℝ) * L ^ (16 : ℕ) ≤
              L * L ^ (16 : ℕ) :=
            mul_le_mul_of_nonneg_right (by dsimp only [L]; linarith) (pow_nonneg (by
              dsimp only [L]; linarith) _)
          _ = L ^ (17 : ℕ) := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg hkernel0, hlogB, hBpow]
      calc
        inghamRouteTPhysicalScaleExponent * Real.log (X : ℝ) * Q *
            (∑ w ∈ (inghamRouteTHighZeroPacket X).filter (fun w => sigma < w.re),
              inghamRouteTZeroMultiplicity w) ≤
          inghamRouteTPhysicalScaleExponent * Real.log (X : ℝ) * Q *
            (3 * K * L ^ (16 : ℕ) * P) :=
          mul_le_mul_of_nonneg_left hcount'
            (mul_nonneg (mul_nonneg hq.le hlog0) hQ0)
        _ = 3 * inghamRouteTPhysicalScaleExponent * K *
            (Real.log (X : ℝ) * L ^ (16 : ℕ)) * E := by
          rw [← hQP]
          ring
        _ ≤ 3 * inghamRouteTPhysicalScaleExponent * K * L ^ (17 : ℕ) * E := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogL (by positivity)) (by positivity)
        _ ≤ 3 * inghamRouteTPhysicalScaleExponent * K * L ^ (17 : ℕ) * Eedge :=
          mul_le_mul_of_nonneg_left hEedge (by positivity)
        _ = _ := by simp only [L, Eedge]
  · have hsigmaEq : sigma = 1 := le_antisymm hsigma.2 (not_lt.mp hsigma1)
    subst sigma
    have hempty :
        (inghamRouteTHighZeroPacket X).filter (fun w => (1 : ℝ) < w.re) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw hpred
      exact (not_lt_of_ge (mem_inghamRouteTHighZeroPacket_bounds hw).2.le) hpred
    simp [hempty]
    positivity

/-- Density estimate at `7/10`, simplified for the baseline term in exponential layer cake. -/
theorem inghamRouteTHighZeroPacket_total_le_simplified
    {K : ℝ} {X : ℕ} (hK : 0 ≤ K) (hX : 1 ≤ X)
    (hdensity :
      zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter (7 / 10 : ℝ)) 4
          ((X : ℝ) - 2) (7 / 10 : ℝ) ≤
        K * (1 + Real.log (X : ℝ)) ^ (14 : ℕ) *
          (1 +
            (X : ℝ) ^ ((16 / 5 : ℝ) * (1 - (7 / 10 : ℝ))) *
              (1 + Real.log (X : ℝ)) ^ (2 : ℕ) +
            (1 + Real.log (X : ℝ)) ^ (2 : ℕ))) :
    (∑ w ∈ inghamRouteTHighZeroPacket X, inghamRouteTZeroMultiplicity w) ≤
      3 * K * (1 + Real.log (X : ℝ)) ^ (16 : ℕ) *
        (X : ℝ) ^ ((16 / 5 : ℝ) * (1 - (7 / 10 : ℝ))) := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hLog : 1 ≤ 1 + Real.log (X : ℝ) := by
    linarith [Real.log_nonneg hXR]
  have hP : 1 ≤ (X : ℝ) ^ ((16 / 5 : ℝ) * (1 - (7 / 10 : ℝ))) :=
    Real.one_le_rpow hXR (by norm_num)
  let L : ℝ := 1 + Real.log (X : ℝ)
  let P : ℝ := (X : ℝ) ^ ((16 / 5 : ℝ) * (1 - (7 / 10 : ℝ)))
  have hL : 1 ≤ L := by simpa only [L] using hLog
  have hL2 : 1 ≤ L ^ (2 : ℕ) := one_le_pow₀ hL
  have htail : 1 + P * L ^ (2 : ℕ) + L ^ (2 : ℕ) ≤
      3 * P * L ^ (2 : ℕ) := by
    have hP' : 1 ≤ P := by simpa only [P] using hP
    have hL0 : 0 ≤ L ^ (2 : ℕ) := pow_nonneg (by linarith) _
    have h1 : 1 ≤ P * L ^ (2 : ℕ) :=
      one_le_mul_of_one_le_of_one_le hP' hL2
    have h2 : L ^ (2 : ℕ) ≤ P * L ^ (2 : ℕ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hP' hL0
    linarith
  have htotalEq :
      (∑ w ∈ inghamRouteTHighZeroPacket X, inghamRouteTZeroMultiplicity w) =
        zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter (7 / 10 : ℝ)) 4
          ((X : ℝ) - 2) (7 / 10 : ℝ) := by
    rw [zetaLittlewoodZeroCountAbove_eq_commonZeroPacket (le_refl _) (by norm_num)]
    simp only [inghamRouteTHighZeroPacket, inghamRouteTZeroMultiplicity]
  have hraw := htotalEq.le.trans hdensity
  have hcoeff : 0 ≤ K * L ^ (14 : ℕ) :=
    mul_nonneg hK (pow_nonneg (by linarith) _)
  have hmul := mul_le_mul_of_nonneg_left htail hcoeff
  calc
    (∑ w ∈ inghamRouteTHighZeroPacket X, inghamRouteTZeroMultiplicity w) ≤
        K * L ^ (14 : ℕ) * (1 + P * L ^ (2 : ℕ) + L ^ (2 : ℕ)) := by
      simpa only [L, P] using hraw
    _ ≤ K * L ^ (14 : ℕ) * (3 * P * L ^ (2 : ℕ)) := hmul
    _ = 3 * K * L ^ (16 : ℕ) * P := by ring
    _ = _ := by simp only [L, P]

/-- Complete finite high-zero packet bound: detector density and a common zero-free edge imply one
edge-damped polylogarithmic majorant for the physical weight. -/
theorem inghamRouteTHighZeroWeightedMass_le_edgePower
    {K shift : ℝ} {X : ℕ}
    (hK : 0 ≤ K) (hX : 1 ≤ X)
    (hshift1 : shift ≤ 3 / 10)
    (hupper : ∀ w ∈ inghamRouteTHighZeroPacket X, w.re ≤ 1 - shift)
    (hdensity : ∀ {sigma : ℝ}, 7 / 10 ≤ sigma → sigma < 1 →
      zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
          ((X : ℝ) - 2) sigma ≤
        K * (1 + Real.log (X : ℝ)) ^ (14 : ℕ) *
          (1 +
            (X : ℝ) ^ ((16 / 5 : ℝ) * (1 - sigma)) *
              (1 + Real.log (X : ℝ)) ^ (2 : ℕ) +
            (1 + Real.log (X : ℝ)) ^ (2 : ℕ))) :
    inghamRouteTHighZeroWeightedMass X ≤
      6 * inghamRouteTPhysicalScaleExponent * K *
        (1 + Real.log (X : ℝ)) ^ (17 : ℕ) *
        (X : ℝ) ^ (-inghamRouteTDensitySlack * shift) := by
  let f : ℝ → ℝ := fun sigma =>
    Real.log ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) *
      ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) ^ (sigma - 1) *
      ∑ w ∈ (inghamRouteTHighZeroPacket X).filter (fun w => sigma < w.re),
        inghamRouteTZeroMultiplicity w
  let C : ℝ := 3 * inghamRouteTPhysicalScaleExponent * K *
    (1 + Real.log (X : ℝ)) ^ (17 : ℕ) *
    (X : ℝ) ^ (-inghamRouteTDensitySlack * shift)
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hL : 1 ≤ 1 + Real.log (X : ℝ) := by
    linarith [Real.log_nonneg hXR]
  have hq : 0 < inghamRouteTPhysicalScaleExponent :=
    inghamRouteTPhysicalScaleExponent_pos
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hintegralNorm : ‖∫ sigma in (7 / 10 : ℝ)..1, f sigma‖ ≤ C := by
    have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (7 / 10 : ℝ)) (b := 1) (C := C) (f := f) (by
        intro sigma hsigma
        apply norm_inghamRouteTHighZero_layerCake_integrand_le hK hX hupper hdensity
        have hmem := Set.uIoc_subset_uIcc hsigma
        simpa [Set.uIcc_of_le (by norm_num : (7 / 10 : ℝ) ≤ 1)] using hmem)
    have habs : |(1 : ℝ) - 7 / 10| = 3 / 10 := by norm_num
    rw [habs] at hraw
    exact hraw.trans (by nlinarith)
  have htotal := inghamRouteTHighZeroPacket_total_le_simplified
    hK hX (hdensity (le_refl _) (by norm_num))
  let L : ℝ := 1 + Real.log (X : ℝ)
  let Q : ℝ := (X : ℝ) ^
    (inghamRouteTPhysicalScaleExponent * ((7 / 10 : ℝ) - 1))
  let P : ℝ := (X : ℝ) ^
    ((16 / 5 : ℝ) * (1 - (7 / 10 : ℝ)))
  let E : ℝ := (X : ℝ) ^
    (-inghamRouteTDensitySlack * (1 - (7 / 10 : ℝ)))
  let Eedge : ℝ := (X : ℝ) ^ (-inghamRouteTDensitySlack * shift)
  have hXRpos : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hXR
  have hbase :
      ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) ^ ((7 / 10 : ℝ) - 1) = Q := by
    dsimp only [Q]
    rw [← Real.rpow_mul (zero_le_one.trans hXR)]
  have htotal' :
      (∑ w ∈ inghamRouteTHighZeroPacket X, inghamRouteTZeroMultiplicity w) ≤
        3 * K * L ^ (16 : ℕ) * P := by
    simpa only [L, P] using htotal
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg (zero_le_one.trans hXR) _
  have hQP : Q * P = E := by
    dsimp only [Q, P, E]
    exact inghamRouteT_density_weight_rpow_identity hXRpos
  have hEedge : E ≤ Eedge := by
    dsimp only [E, Eedge]
    apply Real.rpow_le_rpow_of_exponent_le hXR
    have hd := inghamRouteTDensitySlack_pos
    have hu : shift ≤ 1 - (7 / 10 : ℝ) := by linarith
    have hm := mul_le_mul_of_nonneg_left hu hd.le
    linarith
  have hLpoly : L ^ (16 : ℕ) ≤
      inghamRouteTPhysicalScaleExponent * L ^ (17 : ℕ) := by
    have hq1 : 1 ≤ inghamRouteTPhysicalScaleExponent := by
      unfold inghamRouteTPhysicalScaleExponent
      norm_num
    calc
      L ^ (16 : ℕ) = 1 * L ^ (16 : ℕ) := by ring
      _ ≤ L * L ^ (16 : ℕ) :=
        mul_le_mul_of_nonneg_right (by simpa only [L] using hL) (pow_nonneg (by
          simpa only [L] using (zero_le_one.trans hL)) _)
      _ = L ^ (17 : ℕ) := by ring
      _ = 1 * L ^ (17 : ℕ) := by ring
      _ ≤ inghamRouteTPhysicalScaleExponent * L ^ (17 : ℕ) :=
        mul_le_mul_of_nonneg_right hq1 (pow_nonneg (by
          simpa only [L] using (zero_le_one.trans hL)) _)
  have hbaseline :
      ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) ^ ((7 / 10 : ℝ) - 1) *
          (∑ w ∈ inghamRouteTHighZeroPacket X, inghamRouteTZeroMultiplicity w) ≤ C := by
    rw [hbase]
    calc
      Q * (∑ w ∈ inghamRouteTHighZeroPacket X, inghamRouteTZeroMultiplicity w) ≤
          Q * (3 * K * L ^ (16 : ℕ) * P) :=
        mul_le_mul_of_nonneg_left htotal' hQ0
      _ = 3 * K * L ^ (16 : ℕ) * E := by rw [← hQP]; ring
      _ ≤ 3 * K * L ^ (16 : ℕ) * Eedge :=
        mul_le_mul_of_nonneg_left hEedge (by positivity)
      _ ≤ 3 * K * (inghamRouteTPhysicalScaleExponent * L ^ (17 : ℕ)) *
          Eedge :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLpoly (by positivity)) (by positivity)
      _ = C := by dsimp only [C, L, Eedge]; ring
  rw [inghamRouteTHighZeroWeightedMass_eq_layerCake hX]
  change (∫ sigma in (7 / 10 : ℝ)..1, f sigma) + _ ≤ _
  calc
    (∫ sigma in (7 / 10 : ℝ)..1, f sigma) +
        ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) ^ ((7 / 10 : ℝ) - 1) *
          ∑ w ∈ inghamRouteTHighZeroPacket X, inghamRouteTZeroMultiplicity w ≤
      ‖∫ sigma in (7 / 10 : ℝ)..1, f sigma‖ +
        ((X : ℝ) ^ inghamRouteTPhysicalScaleExponent) ^ ((7 / 10 : ℝ) - 1) *
          ∑ w ∈ inghamRouteTHighZeroPacket X, inghamRouteTZeroMultiplicity w :=
      add_le_add (Real.le_norm_self _) (le_refl _)
    _ ≤ C + C := add_le_add hintegralNorm hbaseline
    _ = 6 * inghamRouteTPhysicalScaleExponent * K *
        (1 + Real.log (X : ℝ)) ^ (17 : ℕ) *
        (X : ℝ) ^ (-inghamRouteTDensitySlack * shift) := by
      dsimp only [C]
      ring

/-- Integer-height version of Route T superpolylogarithmic edge absorption, with the natural
`X - 1` contour parameter used by the common zero packet. -/
theorem tendsto_nat_one_add_log_pow_mul_routeTShiftedPower_zero
    (A : ℝ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Tendsto (fun X : ℕ =>
      (1 + Real.log (X : ℝ)) ^ n *
        (X : ℝ) ^ (-c * routeTContourShiftEnvelope A ((X : ℝ) - 1)))
      atTop (𝓝 0) := by
  let S : ℕ → ℝ := fun X => (X : ℝ) - 1
  have hS : Tendsto S atTop atTop := by
    simpa only [S, sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
  have hcore : Tendsto (fun X : ℕ =>
      (1 + Real.log (S X)) ^ n *
        S X ^ (-c * routeTContourShiftEnvelope A (S X))) atTop (𝓝 0) :=
    (tendsto_one_add_log_pow_mul_routeTShiftPower_zero A hc n).comp hS
  have hupper : Tendsto (fun X : ℕ =>
      (2 : ℝ) ^ n * ((1 + Real.log (S X)) ^ n *
        S X ^ (-c * routeTContourShiftEnvelope A (S X)))) atTop (𝓝 0) := by
    simpa using hcore.const_mul ((2 : ℝ) ^ n)
  have hcompare : ∀ᶠ X : ℕ in atTop,
      (1 + Real.log (X : ℝ)) ^ n *
          (X : ℝ) ^ (-c * routeTContourShiftEnvelope A (S X)) ≤
        (2 : ℝ) ^ n * ((1 + Real.log (S X)) ^ n *
          S X ^ (-c * routeTContourShiftEnvelope A (S X))) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with X hX
    have hXR : (3 : ℝ) ≤ X := by exact_mod_cast hX
    have hS1 : 1 ≤ S X := by dsimp only [S]; linarith
    have hSpos : 0 < S X := lt_of_lt_of_le zero_lt_one hS1
    have hXpos : (0 : ℝ) < X := by linarith
    have hSX : S X ≤ (X : ℝ) := by dsimp only [S]; linarith
    have hquad : (X : ℝ) ≤ (S X) ^ (2 : ℕ) := by
      dsimp only [S]
      nlinarith
    have hlogquad := Real.log_le_log hXpos hquad
    have hlogpow : Real.log ((S X) ^ (2 : ℕ)) = 2 * Real.log (S X) := by
      rw [Real.log_pow]
      norm_num
    rw [hlogpow] at hlogquad
    have hlogS0 : 0 ≤ Real.log (S X) := Real.log_nonneg hS1
    have hL : 1 + Real.log (X : ℝ) ≤ 2 * (1 + Real.log (S X)) := by
      linarith
    have hL0 : 0 ≤ 1 + Real.log (X : ℝ) := by
      linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ X)]
    have hpow := pow_le_pow_left₀ hL0 hL n
    have hedge0 : 0 < routeTContourShiftEnvelope A (S X) :=
      routeTContourShiftEnvelope_pos A (by linarith)
    have hexp : -c * routeTContourShiftEnvelope A (S X) ≤ 0 := by
      nlinarith [mul_pos hc hedge0]
    have hlogbase : Real.log (S X) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hSpos hSX
    have hrpow :
        (X : ℝ) ^ (-c * routeTContourShiftEnvelope A (S X)) ≤
          S X ^ (-c * routeTContourShiftEnvelope A (S X)) := by
      rw [Real.rpow_def_of_pos hXpos, Real.rpow_def_of_pos hSpos]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_right hlogbase hexp
    have hright0 : 0 ≤ S X ^ (-c * routeTContourShiftEnvelope A (S X)) :=
      Real.rpow_nonneg hSpos.le _
    have hLright0 : 0 ≤ 2 * (1 + Real.log (S X)) := by linarith
    calc
      (1 + Real.log (X : ℝ)) ^ n *
          (X : ℝ) ^ (-c * routeTContourShiftEnvelope A (S X)) ≤
        (2 * (1 + Real.log (S X))) ^ n *
          S X ^ (-c * routeTContourShiftEnvelope A (S X)) :=
        mul_le_mul hpow hrpow (Real.rpow_nonneg hXpos.le _) (pow_nonneg hLright0 _)
      _ = (2 : ℝ) ^ n * ((1 + Real.log (S X)) ^ n *
          S X ^ (-c * routeTContourShiftEnvelope A (S X))) := by
        rw [mul_pow]
        ring
  refine squeeze_zero' ?_ hcompare hupper
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  exact mul_nonneg (pow_nonneg (by linarith [Real.log_nonneg hXR]) _)
    (Real.rpow_nonneg (zero_le_one.trans hXR) _)

/-- Uniform detector density and the Route-T zero-free edge yield the physical high-packet
majorant with no remaining hypotheses. -/
theorem exists_eventually_inghamRouteTHighZeroWeightedMass_le_edgePower :
    ∃ A K : ℝ, 0 ≤ K ∧
      ∀ᶠ X : ℕ in atTop,
        inghamRouteTHighZeroWeightedMass X ≤
          6 * inghamRouteTPhysicalScaleExponent * K *
            (1 + Real.log (X : ℝ)) ^ (17 : ℕ) *
            (X : ℝ) ^ (-inghamRouteTDensitySlack *
              routeTContourShiftEnvelope A ((X : ℝ) - 1)) := by
  obtain ⟨K, hK, hdensity⟩ :=
    exists_eventually_zetaLittlewoodZeroCountAbove_le_linearExponent
  obtain ⟨A, hupper⟩ := exists_eventually_inghamRouteTHighZeroPacket_re_le_edge
  have hshiftZero : Tendsto
      (fun X : ℕ => routeTContourShiftEnvelope A ((X : ℝ) - 1))
      atTop (𝓝 0) := by
    have htend : Tendsto (fun X : ℕ => (X : ℝ) - 1) atTop atTop := by
      simpa only [sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
    exact (tendsto_routeTContourShiftEnvelope_zero A).comp htend
  have hshiftSmall : ∀ᶠ X : ℕ in atTop,
      routeTContourShiftEnvelope A ((X : ℝ) - 1) ≤ 3 / 10 := by
    have hlt := hshiftZero.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 3 / 10))
    filter_upwards [hlt] with X hX
    exact hX.le
  refine ⟨A, K, hK, ?_⟩
  filter_upwards [hdensity, hupper, hshiftSmall,
    eventually_ge_atTop (1 : ℕ)] with X hdensityX hupperX hshiftX hX
  exact inghamRouteTHighZeroWeightedMass_le_edgePower
    hK hX hshiftX hupperX hdensityX

/-- **Route-T physical high-zero packet vanishes.**  At interval exponent `701/1000`, the complete
multiplicity-weighted packet in the density range contributes `o(1)` after normalization by the
interval length. -/
theorem tendsto_inghamRouteTHighZeroWeightedMass_zero :
    Tendsto inghamRouteTHighZeroWeightedMass atTop (𝓝 0) := by
  obtain ⟨A, K, hK, hbound⟩ :=
    exists_eventually_inghamRouteTHighZeroWeightedMass_le_edgePower
  have hcore := tendsto_nat_one_add_log_pow_mul_routeTShiftedPower_zero
    A inghamRouteTDensitySlack_pos 17
  have hupper : Tendsto (fun X : ℕ =>
      (6 * inghamRouteTPhysicalScaleExponent * K) *
        ((1 + Real.log (X : ℝ)) ^ (17 : ℕ) *
          (X : ℝ) ^ (-inghamRouteTDensitySlack *
            routeTContourShiftEnvelope A ((X : ℝ) - 1)))) atTop (𝓝 0) := by
    simpa using hcore.const_mul (6 * inghamRouteTPhysicalScaleExponent * K)
  have hbound' : ∀ᶠ X : ℕ in atTop,
      inghamRouteTHighZeroWeightedMass X ≤
        (6 * inghamRouteTPhysicalScaleExponent * K) *
          ((1 + Real.log (X : ℝ)) ^ (17 : ℕ) *
            (X : ℝ) ^ (-inghamRouteTDensitySlack *
              routeTContourShiftEnvelope A ((X : ℝ) - 1))) := by
    filter_upwards [hbound] with X hX
    calc
      inghamRouteTHighZeroWeightedMass X ≤
          6 * inghamRouteTPhysicalScaleExponent * K *
            (1 + Real.log (X : ℝ)) ^ (17 : ℕ) *
            (X : ℝ) ^ (-inghamRouteTDensitySlack *
              routeTContourShiftEnvelope A ((X : ℝ) - 1)) := hX
      _ = _ := by ring
  refine squeeze_zero' ?_ hbound' hupper
  filter_upwards with X
  unfold inghamRouteTHighZeroWeightedMass
  apply Finset.sum_nonneg
  intro w hw
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (inghamRouteTZeroMultiplicity_nonneg w)

end

end RHTower.Sieve
