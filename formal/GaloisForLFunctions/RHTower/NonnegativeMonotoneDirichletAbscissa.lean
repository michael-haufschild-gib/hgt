import GaloisForLFunctions.RHTower.CCM.CCMCumulativeNegativeMassSpectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.LiminfLimsup

/-!
# Monotone nonnegative Dirichlet coefficients and logarithmic power order

For a nonnegative nondecreasing sequence which is not eventually zero, the absolute-convergence
abscissa of its Dirichlet series is exactly one plus the extended logarithmic limsup exponent.
The proof retains the endpoint and the infinite-exponent case.  Its lower half is the dyadic
blocking argument: a summatory bound of order `X ^ q` forces the coefficient itself to have
order `X ^ (q - 1)`.
-/

open Complex Filter Function Set LSeries Finset Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

/-- Extended logarithmic power exponent of a nonnegative coefficient sequence. -/
noncomputable def NonnegativeCoefficientLogPowerExponent (b : ℕ → ℝ) : EReal :=
  limsup (fun n : ℕ =>
    ((Real.log (1 + b n) / Real.log n : ℝ) : EReal)) atTop

theorem coefficientLogPowerExponent_nonneg
    {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n) :
    (0 : EReal) ≤ NonnegativeCoefficientLogPowerExponent b := by
  apply le_limsup_of_frequently_le'
  apply (eventually_ge_atTop (2 : ℕ)).frequently.mono
  intro n hn
  exact_mod_cast div_nonneg
    (Real.log_nonneg (by linarith [hb0 n]))
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n))

/-- The logarithmic limsup exponent gives the coefficientwise upper half of the abscissa law. -/
theorem abscissa_le_one_add_coefficientLogPowerExponent
    {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n) :
    LSeries.abscissaOfAbsConv (fun n => ((b n : ℝ) : ℂ)) ≤
      1 + NonnegativeCoefficientLogPowerExponent b := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'
  intro sigma hsigma
  let beta : EReal := NonnegativeCoefficientLogPowerExponent b
  change 1 + beta < (sigma : EReal) at hsigma
  have hbeta0 : (0 : EReal) ≤ beta :=
    coefficientLogPowerExponent_nonneg hb0
  have hbetatop : beta ≠ ⊤ := by
    intro htop
    rw [htop] at hsigma
    exact (not_lt_of_ge le_top) (hsigma.trans (EReal.coe_lt_top sigma))
  have hbetabot : beta ≠ ⊥ := by
    intro hbot
    rw [hbot] at hbeta0
    exact (not_le_of_gt (by simp : (⊥ : EReal) < 0)) hbeta0
  have hbetaCoe : ((beta.toReal : ℝ) : EReal) = beta :=
    EReal.coe_toReal hbetatop hbetabot
  have hsigmaReal : 1 + beta.toReal < sigma := by
    rw [← hbetaCoe] at hsigma
    exact_mod_cast hsigma
  let gamma : ℝ := (beta.toReal + sigma - 1) / 2
  have hbetaGamma : beta.toReal < gamma := by
    dsimp only [gamma]
    linarith
  have hgammaSigma : 1 + gamma < sigma := by
    dsimp only [gamma]
    linarith
  have hlimsup :
      limsup (fun n : ℕ =>
        ((Real.log (1 + b n) / Real.log n : ℝ) : EReal)) atTop ≤ beta := by
    exact le_rfl
  have heventRatio : ∀ᶠ n : ℕ in atTop,
      ((Real.log (1 + b n) / Real.log n : ℝ) : EReal) ≤ (gamma : EReal) := by
    apply (Filter.limsup_le_iff').mp hlimsup
    rw [← hbetaCoe]
    exact_mod_cast hbetaGamma
  apply LSeriesSummable_of_isBigO_rpow (x := 1 + gamma)
  · simpa only [ofReal_add, ofReal_one, add_re, one_re, ofReal_re] using hgammaSigma
  · apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [heventRatio, eventually_ge_atTop (2 : ℕ)] with n hratio hn
    have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have hratioReal : Real.log (1 + b n) / Real.log n ≤ gamma := by
      exact_mod_cast hratio
    have hlogbound : Real.log (1 + b n) ≤ gamma * Real.log n :=
      (div_le_iff₀ hlogn).mp hratioReal
    have hnpos : (0 : ℝ) < n := by positivity
    have honebpos : 0 < 1 + b n := add_pos_of_pos_of_nonneg zero_lt_one (hb0 n)
    have hexpbound := Real.exp_le_exp.mpr hlogbound
    rw [Real.exp_log honebpos] at hexpbound
    have hrpow : Real.exp (gamma * Real.log n) = (n : ℝ) ^ gamma := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring
    rw [hrpow] at hexpbound
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb0 n), one_mul,
      add_sub_cancel_left, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) gamma)]
    linarith

/-- Dyadic blocking: a summatory power bound saves one full power for a nondecreasing
nonnegative coefficient. -/
theorem monotone_coefficient_isBigO_rpow_sub_one_of_summatory_isBigO
    {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n) (hbmono : Monotone b) {q : ℝ}
    (hO : (fun X : ℕ => ∑ n ∈ Finset.Icc 1 X, b n) =O[atTop]
      (fun X : ℕ => (X : ℝ) ^ q)) :
    b =O[atTop] (fun X : ℕ => (X : ℝ) ^ (q - 1)) := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hO
  rw [eventually_atTop] at hC
  obtain ⟨M, hM⟩ := hC
  apply Asymptotics.IsBigO.of_bound (max C 0 * (2 : ℝ) ^ q)
  filter_upwards [eventually_ge_atTop (max M 1)] with X hX
  have hXM : M ≤ X := (le_max_left M 1).trans hX
  have hX1 : 1 ≤ X := (le_max_right M 1).trans hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (Nat.zero_lt_of_lt hX1)
  have h2XM : M ≤ 2 * X := hXM.trans (by omega)
  have hsumNonneg : 0 ≤ ∑ n ∈ Finset.Icc 1 (2 * X), b n :=
    Finset.sum_nonneg fun n _ => hb0 n
  have hraw := hM (2 * X) h2XM
  rw [Real.norm_eq_abs, abs_of_nonneg hsumNonneg,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) q)] at hraw
  have hCmax : C * ((2 * X : ℕ) : ℝ) ^ q ≤
      max C 0 * ((2 * X : ℕ) : ℝ) ^ q := by
    gcongr
    exact le_max_left C 0
  have hsumUpper : ∑ n ∈ Finset.Icc 1 (2 * X), b n ≤
      max C 0 * ((2 * X : ℕ) : ℝ) ^ q := hraw.trans hCmax
  have hblock : ((X + 1 : ℕ) : ℝ) * b X ≤
      ∑ n ∈ Finset.Icc X (2 * X), b n := by
    have hcard : (Finset.Icc X (2 * X)).card = X + 1 := by
      rw [Nat.card_Icc]
      omega
    calc
      ((X + 1 : ℕ) : ℝ) * b X = ∑ _n ∈ Finset.Icc X (2 * X), b X := by
        rw [Finset.sum_const, hcard]
        simp only [nsmul_eq_mul]
      _ ≤ ∑ n ∈ Finset.Icc X (2 * X), b n := by
        apply Finset.sum_le_sum
        intro n hn
        exact hbmono (Finset.mem_Icc.mp hn).1
  have hsubset : Finset.Icc X (2 * X) ⊆ Finset.Icc 1 (2 * X) := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hX1.trans hn.1, hn.2⟩
  have hblockFull : ∑ n ∈ Finset.Icc X (2 * X), b n ≤
      ∑ n ∈ Finset.Icc 1 (2 * X), b n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _ => hb0 n)
  have hXb : (X : ℝ) * b X ≤
      max C 0 * ((2 * X : ℕ) : ℝ) ^ q := by
    calc
      (X : ℝ) * b X ≤ ((X + 1 : ℕ) : ℝ) * b X := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.le_succ X) (hb0 X)
      _ ≤ ∑ n ∈ Finset.Icc X (2 * X), b n := hblock
      _ ≤ ∑ n ∈ Finset.Icc 1 (2 * X), b n := hblockFull
      _ ≤ max C 0 * ((2 * X : ℕ) : ℝ) ^ q := hsumUpper
  have hbX : b X ≤ max C 0 * ((2 * X : ℕ) : ℝ) ^ q / X :=
    (le_div_iff₀ hXpos).mpr (by simpa [mul_comm] using hXb)
  rw [show (((2 * X : ℕ) : ℝ)) = 2 * (X : ℝ) by norm_num,
    Real.mul_rpow (by norm_num) (Nat.cast_nonneg X)] at hbX
  have hbX' : b X ≤ max C 0 * (2 : ℝ) ^ q * (X : ℝ) ^ (q - 1) := by
    calc
      b X ≤ max C 0 * ((2 : ℝ) ^ q * (X : ℝ) ^ q) / X := hbX
      _ = max C 0 * (2 : ℝ) ^ q * (X : ℝ) ^ (q - 1) := by
        rw [Real.rpow_sub hXpos, Real.rpow_one]
        field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg (hb0 X),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) (q - 1)),
    mul_assoc]
  simpa [mul_assoc] using hbX'

/-- A nonnegative coefficient with a nonnegative power bound has logarithmic limsup exponent at
most that power. -/
theorem coefficientLogPowerExponent_le_of_isBigO_rpow
    {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n) {p : ℝ} (hp0 : 0 ≤ p)
    (hO : b =O[atTop] (fun n : ℕ => (n : ℝ) ^ p)) :
    NonnegativeCoefficientLogPowerExponent b ≤ (p : EReal) := by
  rw [NonnegativeCoefficientLogPowerExponent, Filter.limsup_le_iff']
  intro y hpy
  by_cases hytop : y = ⊤
  · rw [hytop]
    exact Eventually.of_forall fun _ => le_top
  have hybot : y ≠ ⊥ := by
    exact ne_of_gt ((EReal.bot_lt_coe p).trans hpy)
  have hyCoe : ((y.toReal : ℝ) : EReal) = y := EReal.coe_toReal hytop hybot
  have hpyReal : p < y.toReal := by
    rw [← hyCoe] at hpy
    exact_mod_cast hpy
  let delta : ℝ := y.toReal - p
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hO
  have hpowTop : Tendsto (fun n : ℕ => (n : ℝ) ^ delta) atTop atTop :=
    (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop, 1 + max C 0 ≤ (n : ℝ) ^ delta :=
    hpowTop.eventually_ge_atTop (1 + max C 0)
  filter_upwards [hC, hlarge, eventually_ge_atTop (2 : ℕ)] with n hbn hlargeN hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hnpow1 : 1 ≤ (n : ℝ) ^ p := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hn1 hp0
  have hbn' : b n ≤ max C 0 * (n : ℝ) ^ p := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb0 n),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) p)] at hbn
    exact hbn.trans (mul_le_mul_of_nonneg_right (le_max_left C 0)
      (Real.rpow_nonneg (Nat.cast_nonneg n) p))
  have honeb : 1 + b n ≤ (1 + max C 0) * (n : ℝ) ^ p := by
    calc
      1 + b n ≤ 1 + max C 0 * (n : ℝ) ^ p := add_le_add le_rfl hbn'
      _ ≤ (1 + max C 0) * (n : ℝ) ^ p := by
        nlinarith [le_max_right C 0]
  have honebPower : 1 + b n ≤ (n : ℝ) ^ y.toReal := by
    calc
      1 + b n ≤ (1 + max C 0) * (n : ℝ) ^ p := honeb
      _ ≤ (n : ℝ) ^ delta * (n : ℝ) ^ p :=
        mul_le_mul_of_nonneg_right hlargeN (Real.rpow_nonneg (Nat.cast_nonneg n) p)
      _ = (n : ℝ) ^ y.toReal := by
        rw [← Real.rpow_add hnpos]
        congr 1
        dsimp only [delta]
        ring
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hlogbound : Real.log (1 + b n) ≤ Real.log ((n : ℝ) ^ y.toReal) := by
    exact Real.strictMonoOn_log.monotoneOn
      (add_pos_of_pos_of_nonneg zero_lt_one (hb0 n))
      (Real.rpow_pos_of_pos hnpos y.toReal) honebPower
  rw [Real.log_rpow hnpos] at hlogbound
  rw [← hyCoe]
  exact_mod_cast (show Real.log (1 + b n) / Real.log n ≤ y.toReal by
    exact (div_le_iff₀ hlogn).mpr (by simpa [mul_comm] using hlogbound))

/-- A nonnegative nondecreasing sequence with a negative power bound is identically zero. -/
theorem eq_zero_of_monotone_nonnegative_isBigO_negative_rpow
    {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n) (hbmono : Monotone b)
    {p : ℝ} (hp : p < 0)
    (hO : b =O[atTop] (fun n : ℕ => (n : ℝ) ^ p)) :
    b = 0 := by
  have hpTendsto : Tendsto (fun n : ℕ => (n : ℝ) ^ p) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (neg_pos.mpr hp)).comp
      tendsto_natCast_atTop_atTop
    simpa only [neg_neg] using! h
  have hbTendsto : Tendsto b atTop (𝓝 0) := hO.trans_tendsto hpTendsto
  funext n
  simp only [Pi.zero_apply]
  apply le_antisymm
  · have hshift : Tendsto (fun m : ℕ => b (m + n)) atTop (𝓝 0) :=
      hbTendsto.comp (tendsto_add_atTop_nat n)
    apply ge_of_tendsto' hshift
    intro m
    exact hbmono (by omega)
  · exact hb0 n

/-- The dyadic block lower bound gives the reverse inequality in the abscissa law. -/
theorem one_add_coefficientLogPowerExponent_le_abscissa
    {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n) (hbmono : Monotone b)
    (hnotzero : ¬ ∀ᶠ n : ℕ in atTop, b n = 0) :
    1 + NonnegativeCoefficientLogPowerExponent b ≤
      LSeries.abscissaOfAbsConv (fun n => ((b n : ℝ) : ℂ)) := by
  let beta : EReal := NonnegativeCoefficientLogPowerExponent b
  let abs : EReal := LSeries.abscissaOfAbsConv (fun n => ((b n : ℝ) : ℂ))
  change 1 + beta ≤ abs
  by_contra hnotle
  have habsLt : abs < 1 + beta := lt_of_not_ge hnotle
  have hbeta0 : (0 : EReal) ≤ beta :=
    coefficientLogPowerExponent_nonneg hb0
  by_cases hbetaZero : beta = 0
  · have habsOne : abs < (1 : EReal) := by
      simpa [hbetaZero] using habsLt
    have hmax : max abs (0 : EReal) < (1 : EReal) :=
      max_lt habsOne (by norm_num)
    obtain ⟨sigma, hmaxSigma, hsigmaOne⟩ := EReal.exists_between_coe_real hmax
    have habsSigma : abs ≤ (sigma : EReal) :=
      (le_max_left _ _).trans hmaxSigma.le
    have hsigma0 : 0 ≤ sigma := by
      have : (0 : EReal) < (sigma : EReal) :=
        (le_max_right abs 0).trans_lt hmaxSigma
      exact_mod_cast this.le
    have hsigmaLtOne : sigma < 1 := by exact_mod_cast hsigmaOne
    let epsilon : ℝ := (1 - sigma) / 2
    have hepsilon : 0 < epsilon := by
      dsimp only [epsilon]
      linarith
    let p : ℝ := sigma + epsilon - 1
    have hp : p < 0 := by
      dsimp only [p, epsilon]
      linarith
    have hgrowth : NonnegativeDirichletSummatoryGrowthAt b sigma :=
      (abscissaOfAbsConv_le_iff_nonnegativeDirichletSummatoryGrowthAt
        hb0 hsigma0).mp habsSigma
    have hcoeffO : b =O[atTop] (fun n : ℕ => (n : ℝ) ^ p) := by
      have hO := hgrowth epsilon hepsilon
      have h := monotone_coefficient_isBigO_rpow_sub_one_of_summatory_isBigO
        hb0 hbmono hO
      simpa only [p] using h
    have hbzero := eq_zero_of_monotone_nonnegative_isBigO_negative_rpow
      hb0 hbmono hp hcoeffO
    apply hnotzero
    filter_upwards with n
    simp [hbzero]
  · have hbetaPos : (0 : EReal) < beta := lt_of_le_of_ne hbeta0 (Ne.symm hbetaZero)
    have honeTarget : (1 : EReal) < 1 + beta := by
      by_cases htop : beta = ⊤
      · rw [htop]
        exact EReal.coe_lt_top 1
      · have hbot : beta ≠ ⊥ := ne_of_gt ((by norm_num : (⊥ : EReal) < 0).trans hbetaPos)
        have hcoe : ((beta.toReal : ℝ) : EReal) = beta := EReal.coe_toReal htop hbot
        rw [← hcoe]
        exact_mod_cast (show (1 : ℝ) < 1 + beta.toReal by
          have : 0 < beta.toReal := by
            rw [← EReal.coe_pos, hcoe]
            exact hbetaPos
          linarith)
    have hmax : max abs (1 : EReal) < 1 + beta :=
      max_lt habsLt honeTarget
    obtain ⟨sigma, hmaxSigma, hsigmaTarget⟩ := EReal.exists_between_coe_real hmax
    have habsSigma : abs ≤ (sigma : EReal) :=
      (le_max_left _ _).trans hmaxSigma.le
    have hsigmaOne : 1 < sigma := by
      have : (1 : EReal) < (sigma : EReal) :=
        (le_max_right abs 1).trans_lt hmaxSigma
      exact_mod_cast this
    have hsigma0 : 0 ≤ sigma := hsigmaOne.le.trans' zero_le_one
    by_cases hbetatop : beta = ⊤
    · let epsilon : ℝ := 1
      let p : ℝ := sigma + epsilon - 1
      have hp0 : 0 ≤ p := by
        dsimp only [p, epsilon]
        linarith
      have hgrowth : NonnegativeDirichletSummatoryGrowthAt b sigma :=
        (abscissaOfAbsConv_le_iff_nonnegativeDirichletSummatoryGrowthAt
          hb0 hsigma0).mp habsSigma
      have hcoeffO : b =O[atTop] (fun n : ℕ => (n : ℝ) ^ p) := by
        have hO := hgrowth epsilon (by norm_num)
        have h := monotone_coefficient_isBigO_rpow_sub_one_of_summatory_isBigO
          hb0 hbmono hO
        simpa only [p] using h
      have hbetaBound := coefficientLogPowerExponent_le_of_isBigO_rpow
        hb0 hp0 hcoeffO
      change beta ≤ (p : EReal) at hbetaBound
      rw [hbetatop] at hbetaBound
      exact (not_le_of_gt (EReal.coe_lt_top p)) hbetaBound
    · have hbetabot : beta ≠ ⊥ := ne_of_gt ((by norm_num : (⊥ : EReal) < 0).trans_le hbeta0)
      have hbetaCoe : ((beta.toReal : ℝ) : EReal) = beta :=
        EReal.coe_toReal hbetatop hbetabot
      have hsigmaTargetReal : sigma < 1 + beta.toReal := by
        rw [← hbetaCoe] at hsigmaTarget
        exact_mod_cast hsigmaTarget
      let epsilon : ℝ := (1 + beta.toReal - sigma) / 2
      have hepsilon : 0 < epsilon := by
        dsimp only [epsilon]
        linarith
      let p : ℝ := sigma + epsilon - 1
      have hp0 : 0 ≤ p := by
        dsimp only [p]
        linarith
      have hpBeta : p < beta.toReal := by
        dsimp only [p, epsilon]
        linarith
      have hgrowth : NonnegativeDirichletSummatoryGrowthAt b sigma :=
        (abscissaOfAbsConv_le_iff_nonnegativeDirichletSummatoryGrowthAt
          hb0 hsigma0).mp habsSigma
      have hcoeffO : b =O[atTop] (fun n : ℕ => (n : ℝ) ^ p) := by
        have hO := hgrowth epsilon hepsilon
        have h := monotone_coefficient_isBigO_rpow_sub_one_of_summatory_isBigO
          hb0 hbmono hO
        simpa only [p] using h
      have hbetaBound := coefficientLogPowerExponent_le_of_isBigO_rpow
        hb0 hp0 hcoeffO
      change beta ≤ (p : EReal) at hbetaBound
      have hpBetaE : (p : EReal) < beta := by
        rw [← hbetaCoe]
        exact_mod_cast hpBeta
      exact (not_lt_of_ge hbetaBound) hpBetaE

/-- Equation (22): the absolute-convergence abscissa is one plus the logarithmic limsup power
exponent for every nonnegative nondecreasing coefficient which is not eventually zero. -/
theorem monotone_nonnegative_abscissa_eq_one_add_logPowerExponent
    {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n) (hbmono : Monotone b)
    (hnotzero : ¬ ∀ᶠ n : ℕ in atTop, b n = 0) :
    LSeries.abscissaOfAbsConv (fun n => ((b n : ℝ) : ℂ)) =
      1 + NonnegativeCoefficientLogPowerExponent b :=
  le_antisymm
    (abscissa_le_one_add_coefficientLogPowerExponent hb0)
    (one_add_coefficientLogPowerExponent_le_abscissa hb0 hbmono hnotzero)

end

end RHTower
