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
  rw [routeTGlobalExponent_eq]
  push_cast
  have hinner :
      (routeTLogReceiverDegreeNineConstant : ℝ) *
          ((routeTBandShell t : ℝ) + 1) ^ (9 : ℕ) + 1 ≤
        ((routeTLogReceiverDegreeNineConstant : ℝ) * (4 : ℝ) ^ (9 : ℕ) + 1) *
          routeTLogHeightEnvelope t := by
    have hmul := mul_le_mul_of_nonneg_left hshellLinear
      (by positivity : (0 : ℝ) ≤ routeTLogReceiverDegreeNineConstant)
    nlinarith
  exact mul_le_mul_of_nonneg_left hinner (by positivity)

/-- The chosen cubic truncation exponent contributes only linearly in `log(t)`. -/
theorem topExponent_prev_cast_le_six_log
    {t : ℝ} (ht : 8 * Real.pi + 1 ≤ t) :
    (topExponent (t - 1) : ℝ) ≤ 6 * Real.log (t + 2) := by
  have hpi0 : 0 < 8 * Real.pi := by positivity
  have hpi1 : (1 : ℝ) ≤ 8 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have htprev : 8 * Real.pi ≤ t - 1 := by linarith
  have harg0 : 0 < (t - 1) / (8 * Real.pi) := by positivity
  have hargle : (t - 1) / (8 * Real.pi) ≤ t + 2 := by
    calc
      (t - 1) / (8 * Real.pi) ≤ t - 1 := div_le_self (by linarith) hpi1
      _ ≤ t + 2 := by linarith
  have hlogle : Real.log ((t - 1) / (8 * Real.pi)) ≤ Real.log (t + 2) :=
    Real.log_le_log harg0 hargle
  have hlogarg0 : 0 ≤ Real.log ((t - 1) / (8 * Real.pi)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hpi0]
    exact htprev
  have htop := topExponent_le htprev
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have htop0 : (0 : ℝ) ≤ topExponent (t - 1) := by positivity
  have hmul : (topExponent (t - 1) : ℝ) * Real.log 2 ≤
      3 * Real.log ((t - 1) / (8 * Real.pi)) := by
    rwa [le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))] at htop
  have hhalf : (topExponent (t - 1) : ℝ) / 2 ≤
      (topExponent (t - 1) : ℝ) * Real.log 2 := by
    exact mul_le_mul_of_nonneg_left hlog2.le htop0
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
  unfold routeTBandGrowthBound routeTBandGrowthEnvelopeConstant routeTLogHeightEnvelope
  nlinarith

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
    have hh := one_div_le_one_div_of_le (routeTLandauRadius_pos γ) hR
    simpa only [one_div_div, one_mul, Z, K] using hh
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
    rw [Real.log_mul (by positivity) (by positivity)]
  rw [hlogPhiSplit] at hlogPhi
  have hRadius := one_add_inv_routeTLandauRadius_logHeight_upper hγ1
  have hRadius0 : 0 < 1 + 1 / routeTLandauRadius γ := by positivity
  have hlogRadius := Real.log_le_log hRadius0 hRadius
  have hlogRadiusSplit :
      Real.log ((1 + routeTLandauRadiusEnvelopeConstant) *
          routeTLogHeightEnvelope (4 * γ)) =
        Real.log (1 + routeTLandauRadiusEnvelopeConstant) +
          Real.log (routeTLogHeightEnvelope (4 * γ)) := by
    rw [Real.log_mul (by positivity) (by positivity)]
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
    Real.log_nonneg (routeTLogHeightEnvelope_one_le (by positivity : 0 ≤ 4 * γ))
  nlinarith

/-- Fixed coefficient in the explicit lower envelope for the Route-T zero-free displacement. -/
def routeTZeroFreeDeltaEnvelopeConstant (A : ℝ) : ℝ :=
  10000 * routeTLandauRadiusEnvelopeConstant *
    (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ 2

theorem routeTZeroFreeDeltaEnvelopeConstant_pos (A : ℝ) :
    0 < routeTZeroFreeDeltaEnvelopeConstant A := by
  have hC := routeTZeroFreeBudgetEnvelopeConstant_pos A
  unfold routeTZeroFreeDeltaEnvelopeConstant
  positivity

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
  unfold routeTZeroFreeDeltaEnvelopeConstant
  dsimp only [B, KR, Z] at hstep ⊢
  convert hstep using 1 <;> ring

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
    have hZ := routeTLogHeightEnvelope_one_le (by positivity : 0 ≤ 4 * (γ + 1))
    have hlog := Real.log_nonneg hZ
    positivity
  have hsq := pow_le_pow_left₀ hQ0.le hQ 2
  unfold routeTContourEdgeBound routeTContourEdgeLogEnvelope
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsq (by norm_num))

end

end RHTower.Sieve
