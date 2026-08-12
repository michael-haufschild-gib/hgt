import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusSharp

/-!
# Explicit asymptotic envelopes for Route-T contour parameters

These estimates expose the analytic scale hidden behind Route T's discrete binary shell.  They are
proved from the exact `clog`/`nthRoot` definitions, so later endpoint absorption uses no informal
replacement of integer parameters by logarithms.
-/

namespace RHTower.Sieve

open Complex Filter Topology

noncomputable section

/-- Continuous logarithmic envelope for the discrete binary height. -/
def routeTLogHeightEnvelope (t : ℝ) : ℝ :=
  2 * Real.log (t + 2) + 1

/-- Above height two, the binary height is nonzero. -/
theorem routeTBinaryHeight_pos {t : ℝ} (ht : 2 ≤ t) :
    1 ≤ routeTBinaryHeight t := by
  unfold routeTBinaryHeight
  apply Nat.clog_pos (by norm_num)
  have hceil : 2 ≤ ⌈t⌉₊ := by
    have : (2 : ℝ) ≤ (⌈t⌉₊ : ℝ) := ht.trans (Nat.le_ceil t)
    exact_mod_cast this
  omega

/-- The logarithmic envelope is at least one on the positive-height range. -/
theorem routeTLogHeightEnvelope_one_le {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ routeTLogHeightEnvelope t := by
  have harg : (1 : ℝ) ≤ t + 2 := by linarith
  have hlog : 0 ≤ Real.log (t + 2) := Real.log_nonneg harg
  unfold routeTLogHeightEnvelope
  linarith

/-- Binary height is at most twice the natural logarithmic height, up to one unit. -/
theorem routeTBinaryHeight_cast_lt_two_log_add_one
    {t : ℝ} (ht : 2 ≤ t) :
    (routeTBinaryHeight t : ℝ) < routeTLogHeightEnvelope t := by
  let n : ℕ := ⌈t⌉₊
  let L : ℕ := Nat.clog 2 n
  have hn2 : 2 ≤ n := by
    dsimp only [n]
    have hreal : (2 : ℝ) ≤ (⌈t⌉₊ : ℝ) := ht.trans (Nat.le_ceil t)
    exact_mod_cast hreal
  have hL0 : 0 < L := Nat.clog_pos (by norm_num) (by omega)
  have hpowNat : 2 ^ L.pred < n := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hpow0 : (0 : ℝ) < ((2 ^ L.pred : ℕ) : ℝ) := by positivity
  have hnreal : (n : ℝ) < t + 1 := by
    dsimp only [n]
    exact Nat.ceil_lt_add_one (by linarith)
  have ht2pos : 0 < t + 2 := by linarith
  have hpowReal : ((2 ^ L.pred : ℕ) : ℝ) < t + 2 := by
    have : ((2 ^ L.pred : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hpowNat
    linarith
  have hlog := Real.log_lt_log hpow0 hpowReal
  have hlogPow : Real.log (((2 ^ L.pred : ℕ) : ℝ)) =
      (L.pred : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hpred : (L.pred : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.pred_eq_sub_one, Nat.cast_sub (by omega : 1 ≤ L)]
    norm_num
  rw [hlogPow, hpred] at hlog
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hLcast : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL0
  have hmul : ((L : ℝ) - 1) / 2 ≤ ((L : ℝ) - 1) * Real.log 2 := by
    have hnonneg : 0 ≤ (L : ℝ) - 1 := by linarith
    have := mul_le_mul_of_nonneg_left hlog2.le hnonneg
    nlinarith
  have hmain : (L : ℝ) < 2 * Real.log (t + 2) + 1 := by
    nlinarith
  simpa only [routeTBinaryHeight, routeTLogHeightEnvelope, n, L] using hmain

private theorem routeT_nthRoot_nine_le_rpow
    {L : ℕ} (hL : 1 ≤ L) :
    ((Nat.nthRoot 10 L : ℕ) : ℝ) ^ (9 : ℕ) ≤
      (L : ℝ) ^ ((9 : ℝ) / 10) := by
  let r : ℕ := Nat.nthRoot 10 L
  have hr1 : 1 ≤ r := by
    apply (Nat.le_nthRoot_iff (by norm_num)).2
    simpa using hL
  have hrpowNat : r ^ 10 ≤ L := by
    dsimp only [r]
    exact Nat.pow_nthRoot_le (Or.inl (by norm_num))
  have hrpow : ((r : ℝ) ^ (10 : ℕ)) ≤ (L : ℝ) := by exact_mod_cast hrpowNat
  have hr0 : 0 ≤ (r : ℝ) ^ (10 : ℕ) := by positivity
  have hmono := Real.rpow_le_rpow hr0 hrpow (by norm_num : (0 : ℝ) ≤ 9 / 10)
  have hcollapse : (((r : ℝ) ^ (10 : ℕ)) : ℝ) ^ ((9 : ℝ) / 10) =
      (r : ℝ) ^ (9 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ r)]
    norm_num
  rw [hcollapse] at hmono
  simpa only [r] using hmono

/-- The ninth power entering every Route-T strip parameter preserves the exact `9/10` exponent. -/
theorem routeTBandShell_add_one_pow_nine_le
    {t : ℝ} (hL : 1 ≤ routeTBinaryHeight t) :
    ((routeTBandShell t + 1 : ℕ) : ℝ) ^ (9 : ℕ) ≤
      (4 : ℝ) ^ (9 : ℕ) *
        (routeTBinaryHeight t : ℝ) ^ ((9 : ℝ) / 10) := by
  let L : ℕ := routeTBinaryHeight t
  let r : ℕ := Nat.nthRoot 10 L
  have hr1 : 1 ≤ r := by
    apply (Nat.le_nthRoot_iff (by norm_num)).2
    simpa only [one_pow, L] using hL
  have hadd : r + 3 ≤ 4 * r := by omega
  have hpowNat : (r + 3) ^ 9 ≤ (4 * r) ^ 9 := Nat.pow_le_pow_left hadd 9
  have hpowReal : ((r + 3 : ℕ) : ℝ) ^ (9 : ℕ) ≤
      ((4 * r : ℕ) : ℝ) ^ (9 : ℕ) := by exact_mod_cast hpowNat
  have hroot := routeT_nthRoot_nine_le_rpow (L := L) hL
  calc
    ((routeTBandShell t + 1 : ℕ) : ℝ) ^ (9 : ℕ) =
        ((r + 3 : ℕ) : ℝ) ^ (9 : ℕ) := by rfl
    _ ≤ ((4 * r : ℕ) : ℝ) ^ (9 : ℕ) := hpowReal
    _ = (4 : ℝ) ^ (9 : ℕ) * (r : ℝ) ^ (9 : ℕ) := by
      push_cast
      rw [mul_pow]
    _ ≤ (4 : ℝ) ^ (9 : ℕ) * (L : ℝ) ^ ((9 : ℝ) / 10) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = (4 : ℝ) ^ (9 : ℕ) *
        (routeTBinaryHeight t : ℝ) ^ ((9 : ℝ) / 10) := by rfl

/-- The exact shell denominator is controlled by the continuous logarithmic envelope. -/
theorem routeTBandShell_add_one_pow_nine_le_logHeight
    {t : ℝ} (ht : 2 ≤ t) :
    ((routeTBandShell t + 1 : ℕ) : ℝ) ^ (9 : ℕ) ≤
      (4 : ℝ) ^ (9 : ℕ) *
        (routeTLogHeightEnvelope t) ^ ((9 : ℝ) / 10) := by
  have hL1 := routeTBinaryHeight_pos ht
  have hshell := routeTBandShell_add_one_pow_nine_le hL1
  have hL0 : (0 : ℝ) ≤ routeTBinaryHeight t := by positivity
  have hLenvelope := (routeTBinaryHeight_cast_lt_two_log_add_one ht).le
  have hrpow := Real.rpow_le_rpow hL0 hLenvelope (by norm_num : (0 : ℝ) ≤ 9 / 10)
  exact hshell.trans (mul_le_mul_of_nonneg_left hrpow (by positivity))

/-- Route T's strip width retains a quantitative `log(t)^(-9/10)` lower envelope. -/
theorem routeTStripWidth_logHeight_lower
    {t : ℝ} (ht : 2 ≤ t) :
    1 / ((routeTStripDenominator : ℝ) * (4 : ℝ) ^ (9 : ℕ) *
        (routeTLogHeightEnvelope t) ^ ((9 : ℝ) / 10)) ≤
      routeTStripWidth (routeTBandShell t) := by
  have hshell := routeTBandShell_add_one_pow_nine_le_logHeight ht
  have hshell' : ((routeTBandShell t : ℝ) + 1) ^ (9 : ℕ) ≤
      (4 : ℝ) ^ (9 : ℕ) *
        (routeTLogHeightEnvelope t) ^ ((9 : ℝ) / 10) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hshell
  have hden :
      ((routeTStripDenominator * (routeTBandShell t + 1) ^ 9 : ℕ) : ℝ) ≤
        (routeTStripDenominator : ℝ) * (4 : ℝ) ^ (9 : ℕ) *
          (routeTLogHeightEnvelope t) ^ ((9 : ℝ) / 10) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    calc
      (routeTStripDenominator : ℝ) *
          ((routeTBandShell t : ℝ) + 1) ^ (9 : ℕ) ≤
          (routeTStripDenominator : ℝ) *
            ((4 : ℝ) ^ (9 : ℕ) *
              (routeTLogHeightEnvelope t) ^ ((9 : ℝ) / 10)) :=
        mul_le_mul_of_nonneg_left hshell' (by positivity)
      _ = (routeTStripDenominator : ℝ) * (4 : ℝ) ^ (9 : ℕ) *
          (routeTLogHeightEnvelope t) ^ ((9 : ℝ) / 10) := by ring
  have hactual :
      (0 : ℝ) < ((routeTStripDenominator * (routeTBandShell t + 1) ^ 9 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos routeTStripDenominator_pos
      (pow_pos (by omega : 0 < routeTBandShell t + 1) 9)
  unfold routeTStripWidth
  exact one_div_le_one_div_of_le hactual hden

/-- Fixed coefficient in the logarithmic lower envelope for the Landau radius. -/
def routeTLandauRadiusEnvelopeConstant : ℝ :=
  2 * (routeTStripDenominator : ℝ) * (4 : ℝ) ^ (9 : ℕ)

theorem routeTLandauRadiusEnvelopeConstant_pos :
    0 < routeTLandauRadiusEnvelopeConstant := by
  have hD : (0 : ℝ) < routeTStripDenominator := by
    exact_mod_cast routeTStripDenominator_pos
  unfold routeTLandauRadiusEnvelopeConstant
  positivity

/-- Landau's disc radius loses no more than the same `9/10` logarithmic power. -/
theorem routeTLandauRadius_logHeight_lower
    {γ : ℝ} (hγ : 1 ≤ γ) :
    1 / (routeTLandauRadiusEnvelopeConstant *
        (routeTLogHeightEnvelope (4 * γ)) ^ ((9 : ℝ) / 10)) ≤
      routeTLandauRadius γ := by
  have hwidth := routeTStripWidth_logHeight_lower
    (t := 4 * γ) (by linarith)
  unfold routeTLandauRadius routeTLandauRadiusEnvelopeConstant
  calc
    1 / ((2 * (routeTStripDenominator : ℝ) * (4 : ℝ) ^ (9 : ℕ)) *
        (routeTLogHeightEnvelope (4 * γ)) ^ ((9 : ℝ) / 10)) =
        (1 / ((routeTStripDenominator : ℝ) * (4 : ℝ) ^ (9 : ℕ) *
          (routeTLogHeightEnvelope (4 * γ)) ^ ((9 : ℝ) / 10))) / 2 := by ring
    _ ≤ routeTStripWidth (routeTBandShell (4 * γ)) / 2 :=
      div_le_div_of_nonneg_right hwidth (by norm_num)

/-- Fixed coefficient which absorbs all three sources in the Route-T rectangle bound. -/
def routeTBandGrowthEnvelopeConstant : ℝ :=
  20 + 2 * (routeTLogCentreExponent : ℝ) *
      ((routeTLogReceiverDegreeNineConstant : ℝ) * (4 : ℝ) ^ (9 : ℕ) + 1) +
    20736

theorem routeTBandGrowthEnvelopeConstant_pos :
    0 < routeTBandGrowthEnvelopeConstant := by
  unfold routeTBandGrowthEnvelopeConstant
  positivity

/-- Exact powers-of-two identity for the global receiver start. -/
theorem log_routeTGlobalStart (V : ℕ) :
    Real.log (routeTGlobalStart V : ℝ) =
      (routeTGlobalExponent V : ℝ) * Real.log 2 := by
  unfold routeTGlobalStart
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

/-- The receiver exponent is linear in the continuous log-height envelope after shell selection. -/
theorem routeTGlobalExponent_bandShell_cast_le
    {t : ℝ} (ht : 2 ≤ t) :
    (routeTGlobalExponent (routeTBandShell t) : ℝ) ≤
      (routeTLogCentreExponent : ℝ) *
        ((routeTLogReceiverDegreeNineConstant : ℝ) * (4 : ℝ) ^ (9 : ℕ) + 1) *
          routeTLogHeightEnvelope t := by
  have hshell := routeTBandShell_add_one_pow_nine_le_logHeight ht
  have hZ1 := routeTLogHeightEnvelope_one_le (by linarith : 0 ≤ t)
  have hZpow : routeTLogHeightEnvelope t ^ ((9 : ℝ) / 10) ≤
      routeTLogHeightEnvelope t :=
    Real.rpow_le_self_of_one_le hZ1 (by norm_num)
  have hshellLinear :
      ((routeTBandShell t + 1 : ℕ) : ℝ) ^ (9 : ℕ) ≤
        (4 : ℝ) ^ (9 : ℕ) * routeTLogHeightEnvelope t :=
    hshell.trans (mul_le_mul_of_nonneg_left hZpow (by positivity))
  have hshellLinear' :
      ((routeTBandShell t : ℝ) + 1) ^ (9 : ℕ) ≤
        (4 : ℝ) ^ (9 : ℕ) * routeTLogHeightEnvelope t := by
    simpa only [Nat.cast_add, Nat.cast_one] using hshellLinear
  rw [routeTGlobalExponent_eq]
  push_cast
  have hinner :
      (routeTLogReceiverDegreeNineConstant : ℝ) *
          ((routeTBandShell t : ℝ) + 1) ^ (9 : ℕ) + 1 ≤
        ((routeTLogReceiverDegreeNineConstant : ℝ) * (4 : ℝ) ^ (9 : ℕ) + 1) *
          routeTLogHeightEnvelope t := by
    have hmul := mul_le_mul_of_nonneg_left hshellLinear'
      (by positivity : (0 : ℝ) ≤ routeTLogReceiverDegreeNineConstant)
    nlinarith
  have hc0 : (0 : ℝ) ≤ (routeTLogCentreExponent : ℝ) := by positivity
  calc
    (routeTLogCentreExponent : ℝ) *
        ((routeTLogReceiverDegreeNineConstant : ℝ) *
          ((routeTBandShell t : ℝ) + 1) ^ (9 : ℕ) + 1) ≤
      (routeTLogCentreExponent : ℝ) *
        (((routeTLogReceiverDegreeNineConstant : ℝ) * (4 : ℝ) ^ (9 : ℕ) + 1) *
          routeTLogHeightEnvelope t) := mul_le_mul_of_nonneg_left hinner hc0
    _ = _ := by ring

/-- The chosen cubic truncation exponent contributes only linearly in `log(t)`. -/
theorem topExponent_prev_cast_le_six_log
    {t : ℝ} (ht : 8 * Real.pi + 1 ≤ t) :
    (topExponent (t - 1) : ℝ) ≤ 6 * Real.log (t + 2) := by
  have hpi0 : 0 < 8 * Real.pi := by positivity
  have hpi1 : (1 : ℝ) ≤ 8 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have htprev : 8 * Real.pi ≤ t - 1 := by linarith
  have harg0 : 0 < (t - 1) / (8 * Real.pi) :=
    div_pos (by linarith) hpi0
  have hargle : (t - 1) / (8 * Real.pi) ≤ t + 2 := by
    calc
      (t - 1) / (8 * Real.pi) ≤ t - 1 := div_le_self (by linarith) hpi1
      _ ≤ t + 2 := by linarith
  have hlogle : Real.log ((t - 1) / (8 * Real.pi)) ≤ Real.log (t + 2) :=
    Real.log_le_log harg0 hargle
  have hlogarg0 : 0 ≤ Real.log ((t - 1) / (8 * Real.pi)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hpi0]
    simpa only [one_mul] using htprev
  have htop := topExponent_le htprev
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have htop0 : (0 : ℝ) ≤ topExponent (t - 1) := by positivity
  have hmul : (topExponent (t - 1) : ℝ) * Real.log 2 ≤
      3 * Real.log ((t - 1) / (8 * Real.pi)) := by
    rwa [le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))] at htop
  have hhalf : (topExponent (t - 1) : ℝ) / 2 ≤
      (topExponent (t - 1) : ℝ) * Real.log 2 := by
    nlinarith [mul_nonneg htop0 (sub_nonneg.mpr hlog2.le)]
  nlinarith

/-- Route T's full rectangle majorant grows at most linearly in the log-height envelope. -/
theorem routeTBandGrowthBound_logHeight_upper
    {t : ℝ} (ht : 8 * Real.pi + 1 ≤ t) :
    routeTBandGrowthBound t ≤
      routeTBandGrowthEnvelopeConstant * routeTLogHeightEnvelope t := by
  have ht2 : 2 ≤ t := by nlinarith [Real.pi_gt_three]
  have hZ1 := routeTLogHeightEnvelope_one_le (by linarith : 0 ≤ t)
  have hE := routeTGlobalExponent_bandShell_cast_le ht2
  have hlogStart : Real.log (routeTGlobalStart (routeTBandShell t) : ℝ) ≤
      (routeTLogCentreExponent : ℝ) *
        ((routeTLogReceiverDegreeNineConstant : ℝ) * (4 : ℝ) ^ (9 : ℕ) + 1) *
          routeTLogHeightEnvelope t := by
    rw [log_routeTGlobalStart]
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    calc
      (routeTGlobalExponent (routeTBandShell t) : ℝ) * Real.log 2 ≤
          (routeTGlobalExponent (routeTBandShell t) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ ≤ _ := by simpa only [mul_one] using hE
  have htop := topExponent_prev_cast_le_six_log ht
  have hlognonneg : 0 ≤ Real.log (t + 2) :=
    Real.log_nonneg (by linarith : (1 : ℝ) ≤ t + 2)
  let C : ℝ := (routeTLogCentreExponent : ℝ) *
    ((routeTLogReceiverDegreeNineConstant : ℝ) * (4 : ℝ) ^ (9 : ℕ) + 1)
  let Z : ℝ := routeTLogHeightEnvelope t
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have htopTerm : (topExponent (t - 1) : ℝ) * 6912 ≤
      41472 * Real.log (t + 2) := by nlinarith
  calc
    routeTBandGrowthBound t ≤ 20 + 2 * C * Z +
        41472 * Real.log (t + 2) := by
      unfold routeTBandGrowthBound
      dsimp only [C, Z]
      linarith
    _ ≤ (20 + 2 * C + 20736) * Z := by
      dsimp only [Z, routeTLogHeightEnvelope]
      nlinarith
    _ = routeTBandGrowthEnvelopeConstant * routeTLogHeightEnvelope t := by
      unfold routeTBandGrowthEnvelopeConstant
      dsimp only [C, Z]
      ring

theorem routeTLogHeightEnvelope_mono {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    routeTLogHeightEnvelope s ≤ routeTLogHeightEnvelope t := by
  have hsarg : 0 < s + 2 := by linarith
  have harg : s + 2 ≤ t + 2 := by linarith
  have hlog := Real.log_le_log hsarg harg
  unfold routeTLogHeightEnvelope
  linarith

/-- Fixed coefficient for the three-centre Landau majorant. -/
def routeTLandauPhiEnvelopeConstant : ℝ :=
  3 * routeTBandGrowthEnvelopeConstant + 1

theorem routeTLandauPhiEnvelopeConstant_one_le :
    1 ≤ routeTLandauPhiEnvelopeConstant := by
  unfold routeTLandauPhiEnvelopeConstant
  nlinarith [routeTBandGrowthEnvelopeConstant_pos]

/-- The complete Landau majorant is `O(log γ)` with an explicit coefficient. -/
theorem routeTLandauPhi_logHeight_upper
    {γ : ℝ} (hγ : 8 * Real.pi + 1 ≤ γ) :
    routeTLandauPhi γ ≤
      routeTLandauPhiEnvelopeConstant * routeTLogHeightEnvelope (4 * γ) := by
  have hγ0 : 0 ≤ γ := by nlinarith [Real.pi_pos]
  have h2γ : 8 * Real.pi + 1 ≤ 2 * γ := by nlinarith [Real.pi_pos]
  have h4γ : 8 * Real.pi + 1 ≤ 4 * γ := by nlinarith [Real.pi_pos]
  have h1 := routeTBandGrowthBound_logHeight_upper hγ
  have h2 := routeTBandGrowthBound_logHeight_upper h2γ
  have h4 := routeTBandGrowthBound_logHeight_upper h4γ
  have hZ1 := routeTLogHeightEnvelope_one_le (by positivity : 0 ≤ 4 * γ)
  have hm1 := routeTLogHeightEnvelope_mono hγ0 (by linarith : γ ≤ 4 * γ)
  have hm2 := routeTLogHeightEnvelope_mono (by positivity : 0 ≤ 2 * γ)
    (by linarith : 2 * γ ≤ 4 * γ)
  have hK := routeTBandGrowthEnvelopeConstant_pos
  unfold routeTLandauPhi routeTLandauPhiEnvelopeConstant
  nlinarith

/-- The reciprocal Landau radius has the matching explicit `log(γ)^(9/10)` upper envelope. -/
theorem one_add_inv_routeTLandauRadius_logHeight_upper
    {γ : ℝ} (hγ : 1 ≤ γ) :
    1 + 1 / routeTLandauRadius γ ≤
      (1 + routeTLandauRadiusEnvelopeConstant) *
        routeTLogHeightEnvelope (4 * γ) := by
  let Z := routeTLogHeightEnvelope (4 * γ)
  let K := routeTLandauRadiusEnvelopeConstant
  have hZ1 : 1 ≤ Z := by
    dsimp only [Z]
    exact routeTLogHeightEnvelope_one_le (by positivity)
  have hZpow : Z ^ ((9 : ℝ) / 10) ≤ Z :=
    Real.rpow_le_self_of_one_le hZ1 (by norm_num)
  have hK0 : 0 < K := by
    simpa only [K] using routeTLandauRadiusEnvelopeConstant_pos
  have hKZ0 : 0 < K * Z ^ ((9 : ℝ) / 10) := by positivity
  have hR := routeTLandauRadius_logHeight_lower hγ
  have hinv : 1 / routeTLandauRadius γ ≤ K * Z ^ ((9 : ℝ) / 10) := by
    have hlower0 : 0 < 1 / (K * Z ^ ((9 : ℝ) / 10)) := by positivity
    have hh := one_div_le_one_div_of_le hlower0 (by simpa only [Z, K] using hR)
    simpa only [one_div_div, one_mul, div_one, Z, K] using hh
  have hpow : K * Z ^ ((9 : ℝ) / 10) ≤ K * Z :=
    mul_le_mul_of_nonneg_left hZpow hK0.le
  dsimp only [Z, K] at *
  nlinarith

/-- Fixed additive coefficient in the Route-T zero-free budget envelope. -/
def routeTZeroFreeBudgetEnvelopeConstant (A : ℝ) : ℝ :=
  10001 + |A| + Real.log routeTLandauPhiEnvelopeConstant +
    Real.log (1 + routeTLandauRadiusEnvelopeConstant)

theorem routeTZeroFreeBudgetEnvelopeConstant_pos (A : ℝ) :
    0 < routeTZeroFreeBudgetEnvelopeConstant A := by
  have hPhiLog : 0 ≤ Real.log routeTLandauPhiEnvelopeConstant :=
    Real.log_nonneg routeTLandauPhiEnvelopeConstant_one_le
  have hRadiusLog : 0 ≤ Real.log (1 + routeTLandauRadiusEnvelopeConstant) :=
    Real.log_nonneg (by nlinarith [routeTLandauRadiusEnvelopeConstant_pos])
  unfold routeTZeroFreeBudgetEnvelopeConstant
  nlinarith [abs_nonneg A]

/-- The full zero-free budget is at most affine in `log log γ`. -/
theorem routeTZeroFreeBudget_logHeight_upper
    {A γ : ℝ} (hγ : 8 * Real.pi + 1 ≤ γ) :
    routeTZeroFreeBudget A γ ≤
      routeTZeroFreeBudgetEnvelopeConstant A +
        2 * Real.log (routeTLogHeightEnvelope (4 * γ)) := by
  have hγ1 : 1 ≤ γ := by nlinarith [Real.pi_pos]
  have hZ1 := routeTLogHeightEnvelope_one_le (by positivity : 0 ≤ 4 * γ)
  have hPhi := routeTLandauPhi_logHeight_upper hγ
  have hPhi0 : 0 < routeTLandauPhi γ :=
    lt_of_lt_of_le (by norm_num) (routeTLandauPhi_one_le γ)
  have hPhiK0 : 0 < routeTLandauPhiEnvelopeConstant *
      routeTLogHeightEnvelope (4 * γ) := by
    have hK := routeTLandauPhiEnvelopeConstant_one_le
    positivity
  have hlogPhi := Real.log_le_log hPhi0 hPhi
  have hlogPhiSplit :
      Real.log (routeTLandauPhiEnvelopeConstant * routeTLogHeightEnvelope (4 * γ)) =
        Real.log routeTLandauPhiEnvelopeConstant +
          Real.log (routeTLogHeightEnvelope (4 * γ)) := by
    rw [Real.log_mul (ne_of_gt (lt_of_lt_of_le zero_lt_one
      routeTLandauPhiEnvelopeConstant_one_le))
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hZ1))]
  rw [hlogPhiSplit] at hlogPhi
  have hRadius := one_add_inv_routeTLandauRadius_logHeight_upper hγ1
  have hRadius0 : 0 < 1 + 1 / routeTLandauRadius γ := by
    have hinv : 0 < 1 / routeTLandauRadius γ :=
      one_div_pos.mpr (routeTLandauRadius_pos γ)
    linarith
  have hlogRadius := Real.log_le_log hRadius0 hRadius
  have hlogRadiusSplit :
      Real.log ((1 + routeTLandauRadiusEnvelopeConstant) *
          routeTLogHeightEnvelope (4 * γ)) =
        Real.log (1 + routeTLandauRadiusEnvelopeConstant) +
          Real.log (routeTLogHeightEnvelope (4 * γ)) := by
    rw [Real.log_mul
      (ne_of_gt (by nlinarith [routeTLandauRadiusEnvelopeConstant_pos] :
        (0 : ℝ) < 1 + routeTLandauRadiusEnvelopeConstant))
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hZ1))]
  rw [hlogRadiusSplit] at hlogRadius
  unfold routeTZeroFreeBudget routeTZeroFreeBudgetEnvelopeConstant
  linarith

/-- Multiplicative polylogarithmic form of the budget envelope. -/
theorem routeTZeroFreeBudget_polylog_upper
    {A γ : ℝ} (hγ : 8 * Real.pi + 1 ≤ γ) :
    routeTZeroFreeBudget A γ ≤
      (routeTZeroFreeBudgetEnvelopeConstant A + 2) *
        (1 + Real.log (routeTLogHeightEnvelope (4 * γ))) := by
  have hmain := routeTZeroFreeBudget_logHeight_upper (A := A) hγ
  have hC0 := routeTZeroFreeBudgetEnvelopeConstant_pos A
  have hlog0 : 0 ≤ Real.log (routeTLogHeightEnvelope (4 * γ)) :=
    Real.log_nonneg (routeTLogHeightEnvelope_one_le (by
      nlinarith [Real.pi_pos] : 0 ≤ 4 * γ))
  nlinarith

/-- Fixed coefficient in the explicit lower envelope for the Route-T zero-free displacement. -/
def routeTZeroFreeDeltaEnvelopeConstant (A : ℝ) : ℝ :=
  10000 * routeTLandauRadiusEnvelopeConstant *
    (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ 2

theorem routeTZeroFreeDeltaEnvelopeConstant_pos (A : ℝ) :
    0 < routeTZeroFreeDeltaEnvelopeConstant A := by
  have hC := routeTZeroFreeBudgetEnvelopeConstant_pos A
  have hR := routeTLandauRadiusEnvelopeConstant_pos
  unfold routeTZeroFreeDeltaEnvelopeConstant
  exact mul_pos (mul_pos (by norm_num) hR) (sq_pos_of_pos (by linarith))

/-- Explicit lower envelope for the displacement in the Route-T zero-free region. -/
theorem routeTZeroFreeDelta_polylog_lower
    {A γ : ℝ} (hγ : 8 * Real.pi + 1 ≤ γ) :
    1 / (routeTZeroFreeDeltaEnvelopeConstant A *
        (routeTLogHeightEnvelope (4 * γ)) ^ ((9 : ℝ) / 10) *
        (1 + Real.log (routeTLogHeightEnvelope (4 * γ))) ^ 2) ≤
      routeTZeroFreeDelta A γ := by
  let Z := routeTLogHeightEnvelope (4 * γ)
  let KR := routeTLandauRadiusEnvelopeConstant
  let B := (routeTZeroFreeBudgetEnvelopeConstant A + 2) * (1 + Real.log Z)
  have hγ1 : 1 ≤ γ := by nlinarith [Real.pi_pos]
  have hZ1 : 1 ≤ Z := by
    dsimp only [Z]
    exact routeTLogHeightEnvelope_one_le (by positivity)
  have hlogZ0 : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  have hKR0 : 0 < KR := by
    simpa only [KR] using routeTLandauRadiusEnvelopeConstant_pos
  have hC0 := routeTZeroFreeBudgetEnvelopeConstant_pos A
  have hB0 : 0 < B := by
    dsimp only [B]
    positivity
  have hR := routeTLandauRadius_logHeight_lower hγ1
  have hQ := routeTZeroFreeBudget_polylog_upper (A := A) hγ
  have hQ0 := routeTZeroFreeBudget_pos A γ
  have hQsq : routeTZeroFreeBudget A γ ^ 2 ≤ B ^ 2 := by
    apply pow_le_pow_left₀ hQ0.le
    simpa only [B, Z] using hQ
  have hden : 10000 * routeTZeroFreeBudget A γ ^ 2 ≤ 10000 * B ^ 2 :=
    mul_le_mul_of_nonneg_left hQsq (by norm_num)
  have hdenQ0 : 0 < 10000 * routeTZeroFreeBudget A γ ^ 2 := by positivity
  have hdenB0 : 0 < 10000 * B ^ 2 := by positivity
  have hstep :
      (1 / (KR * Z ^ ((9 : ℝ) / 10))) / (10000 * B ^ 2) ≤
        routeTLandauRadius γ / (10000 * routeTZeroFreeBudget A γ ^ 2) := by
    calc
      (1 / (KR * Z ^ ((9 : ℝ) / 10))) / (10000 * B ^ 2) ≤
          routeTLandauRadius γ / (10000 * B ^ 2) :=
        div_le_div_of_nonneg_right (by simpa only [KR, Z] using hR) hdenB0.le
      _ ≤ routeTLandauRadius γ / (10000 * routeTZeroFreeBudget A γ ^ 2) :=
        div_le_div_of_nonneg_left (routeTLandauRadius_pos γ).le hdenQ0 hden
  unfold routeTZeroFreeDelta
  calc
    1 / (routeTZeroFreeDeltaEnvelopeConstant A * Z ^ ((9 : ℝ) / 10) *
        (1 + Real.log Z) ^ 2) =
        (1 / (KR * Z ^ ((9 : ℝ) / 10))) / (10000 * B ^ 2) := by
      unfold routeTZeroFreeDeltaEnvelopeConstant
      dsimp only [B, KR]
      field_simp [ne_of_gt hKR0, ne_of_gt hB0]
    _ ≤ routeTLandauRadius γ / (10000 * routeTZeroFreeBudget A γ ^ 2) := hstep

/-- Exponential cost envelope for every high edge of the shifted Möbius contour. -/
def routeTContourEdgeLogEnvelope (A γ : ℝ) : ℝ :=
  400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ 2 *
    (1 + Real.log (routeTLogHeightEnvelope (4 * (γ + 1)))) ^ 2

theorem routeTContourEdgeBound_logHeight_upper
    {A γ : ℝ} (hγ : 8 * Real.pi ≤ γ) :
    routeTContourEdgeBound A γ ≤ Real.exp (routeTContourEdgeLogEnvelope A γ) := by
  have hQ := routeTZeroFreeBudget_polylog_upper
    (A := A) (γ := γ + 1) (by linarith)
  have hQ0 := routeTZeroFreeBudget_pos A (γ + 1)
  have hB0 : 0 < (routeTZeroFreeBudgetEnvelopeConstant A + 2) *
      (1 + Real.log (routeTLogHeightEnvelope (4 * (γ + 1)))) := by
    have hC := routeTZeroFreeBudgetEnvelopeConstant_pos A
    have hZ := routeTLogHeightEnvelope_one_le (by
      nlinarith [Real.pi_pos] : 0 ≤ 4 * (γ + 1))
    have hlog := Real.log_nonneg hZ
    positivity
  have hsq := pow_le_pow_left₀ hQ0.le hQ 2
  unfold routeTContourEdgeBound routeTContourEdgeLogEnvelope routeTInverseHeight
  apply Real.exp_le_exp.mpr
  calc
    400 * routeTZeroFreeBudget A (γ + 1) ^ 2 ≤
        400 * ((routeTZeroFreeBudgetEnvelopeConstant A + 2) *
          (1 + Real.log (routeTLogHeightEnvelope (4 * (γ + 1))))) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ 2 *
        (1 + Real.log (routeTLogHeightEnvelope (4 * (γ + 1)))) ^ 2 := by ring

/-- The right edge is always cheaper than the high-edge reciprocal majorant. -/
theorem routeTContourRightBound_le_edgeBound (A T : ℝ) :
    routeTContourRightBound A T ≤ routeTContourEdgeBound A T := by
  let Q := routeTZeroFreeBudget A (routeTInverseHeight T)
  let d := routeTInverseDelta A T
  have hQ := routeTZeroFreeBudget_ge A (routeTInverseHeight T)
  have hQ0 : 0 < Q := by
    simpa only [Q] using routeTZeroFreeBudget_pos A (routeTInverseHeight T)
  have hd0 : 0 < d := by simpa only [d] using routeTInverseDelta_pos A T
  have harg0 : 0 < 1 + 1 / d := by positivity
  have hlog := routeT_log_delta_le_budget_sq A (routeTInverseHeight T)
  have hlogShape : Real.log (1 + 1 / d) ≤ Q ^ 2 := by
    simpa only [d, routeTInverseDelta, Q] using hlog
  have hbudget : 22 / 4 + Real.log (1 + 1 / d) ≤ 400 * Q ^ 2 := by
    nlinarith
  have hexp := Real.exp_le_exp.mpr hbudget
  have hrewrite : Real.exp (22 / 4) * (1 + 1 / d) =
      Real.exp (22 / 4 + Real.log (1 + 1 / d)) := by
    rw [Real.exp_add, Real.exp_log harg0]
  unfold routeTContourRightBound routeTContourEdgeBound
  simpa only [d, Q, hrewrite] using hexp

/-- Explicit vanishing lower envelope for the actual contour shift. -/
def routeTContourShiftEnvelope (A T : ℝ) : ℝ :=
  1 / (20 * routeTZeroFreeDeltaEnvelopeConstant A *
    (routeTLogHeightEnvelope (4 * (T + 1))) ^ ((9 : ℝ) / 10) *
    (1 + Real.log (routeTLogHeightEnvelope (4 * (T + 1)))) ^ 2)

theorem routeTContourShiftEnvelope_pos (A : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    0 < routeTContourShiftEnvelope A T := by
  have hK := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hZ := routeTLogHeightEnvelope_one_le (by positivity : 0 ≤ 4 * (T + 1))
  have hlog := Real.log_nonneg hZ
  unfold routeTContourShiftEnvelope
  positivity

/-- The explicit envelope lies below one twentieth of the inverse-zeta displacement. -/
theorem routeTContourShiftEnvelope_le_inverseDelta
    {A T : ℝ} (hT : 8 * Real.pi ≤ T) :
    routeTContourShiftEnvelope A T ≤ routeTInverseDelta A T / 20 := by
  have hdelta := routeTZeroFreeDelta_polylog_lower
    (A := A) (γ := T + 1) (by linarith)
  have hD : 0 < routeTZeroFreeDeltaEnvelopeConstant A :=
    routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hZ : 1 ≤ routeTLogHeightEnvelope (4 * (T + 1)) :=
    routeTLogHeightEnvelope_one_le (by nlinarith [Real.pi_pos])
  have hfac : 0 < 1 + Real.log (routeTLogHeightEnvelope (4 * (T + 1))) := by
    have := Real.log_nonneg hZ
    linarith
  unfold routeTInverseDelta routeTInverseHeight
  unfold routeTContourShiftEnvelope
  calc
    1 / (20 * routeTZeroFreeDeltaEnvelopeConstant A *
        routeTLogHeightEnvelope (4 * (T + 1)) ^ ((9 : ℝ) / 10) *
        (1 + Real.log (routeTLogHeightEnvelope (4 * (T + 1)))) ^ 2) =
      (1 / (routeTZeroFreeDeltaEnvelopeConstant A *
        routeTLogHeightEnvelope (4 * (T + 1)) ^ ((9 : ℝ) / 10) *
        (1 + Real.log (routeTLogHeightEnvelope (4 * (T + 1)))) ^ 2)) / 20 := by
      field_simp [ne_of_gt hD, ne_of_gt hfac]
    _ ≤ routeTZeroFreeDelta A (T + 1) / 20 :=
      div_le_div_of_nonneg_right hdelta (by norm_num)

theorem tendsto_routeTLogHeightEnvelope_four_add_atTop :
    Tendsto (fun T : ℝ => routeTLogHeightEnvelope (4 * (T + 1))) atTop atTop := by
  have hlinear : Tendsto (fun T : ℝ => 4 * (T + 1) + 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop ((b - 6) / 4)] with T hT
    linarith
  have hlog := Real.tendsto_log_atTop.comp hlinear
  have hmul := hlog.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  simpa only [routeTLogHeightEnvelope, Function.comp_apply] using
    (tendsto_atTop_add_const_right atTop 1 hmul)

/-- The contour-shift lower envelope vanishes; hence it eventually fits every fixed compact box. -/
theorem tendsto_routeTContourShiftEnvelope_zero (A : ℝ) :
    Tendsto (routeTContourShiftEnvelope A) atTop (𝓝 0) := by
  let Z : ℝ → ℝ := fun T => routeTLogHeightEnvelope (4 * (T + 1))
  let K : ℝ := 20 * routeTZeroFreeDeltaEnvelopeConstant A
  have hK0 : 0 < K := by
    dsimp only [K]
    positivity [routeTZeroFreeDeltaEnvelopeConstant_pos A]
  have hZ : Tendsto Z atTop atTop := by
    simpa only [Z] using tendsto_routeTLogHeightEnvelope_four_add_atTop
  have hpow : Tendsto (fun T => Z T ^ ((9 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hZ
  have hden : Tendsto (fun T => K * Z T ^ ((9 : ℝ) / 10)) atTop atTop :=
    hpow.const_mul_atTop hK0
  have hupper : Tendsto (fun T => 1 / (K * Z T ^ ((9 : ℝ) / 10))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hden
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact (routeTContourShiftEnvelope_pos A hT).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have hZ1 : 1 ≤ Z T := by
      dsimp only [Z]
      exact routeTLogHeightEnvelope_one_le (by positivity)
    have hlog : 0 ≤ Real.log (Z T) := Real.log_nonneg hZ1
    have hlogfac : 1 ≤ (1 + Real.log (Z T)) ^ 2 := by nlinarith
    have hbase : 0 < K * Z T ^ ((9 : ℝ) / 10) := by positivity
    have hdenle : K * Z T ^ ((9 : ℝ) / 10) ≤
        K * Z T ^ ((9 : ℝ) / 10) * (1 + Real.log (Z T)) ^ 2 := by
      nlinarith
    have hinv := one_div_le_one_div_of_le hbase hdenle
    simpa only [routeTContourShiftEnvelope, Z, K, mul_assoc] using hinv

/-- Once the compact reciprocal box is fixed, the actual contour shift dominates the explicit
polylogarithmic envelope. -/
theorem eventually_routeTContourShiftEnvelope_le
    {A δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop,
      routeTContourShiftEnvelope A T ≤ routeTContourShift A δ T := by
  have hbox : ∀ᶠ T : ℝ in atTop, routeTContourShiftEnvelope A T < δ / 2 :=
    (tendsto_routeTContourShiftEnvelope_zero A).eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hbox, eventually_ge_atTop (8 * Real.pi)] with T hsmall hT
  unfold routeTContourShift
  exact le_min (routeTContourShiftEnvelope_le_inverseDelta hT) hsmall.le

end

end RHTower.Sieve
