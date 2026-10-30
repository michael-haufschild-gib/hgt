import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.GrowingShellSourcesHaveLogarithmicRates
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CountingActiveShellsMakesTheAffineSourceLinear
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AffineShellErrorsHaveAUniformHarmonicBudget

/-!
# Total variation controls the actual reciprocal shell source

The reciprocal change of variables preserves a uniform variation bound.
Abel summation therefore charges each active shell a constant weight cost.
The resulting harmonic square budget is quadratic in overlap, up to a logarithm.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  BezoutValuationIncidence SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

private theorem deriv_zero_of_flat {W : ℝ → ℝ} {a : ℝ}
    (hflat : ∀ u, |u| < a → W u = 0) {u : ℝ} (hu : |u| < a) : deriv W u = 0 := by
  have hlocal : W =ᶠ[𝓝 u] fun _ => 0 := by
    filter_upwards [continuous_abs.continuousAt.eventually (gt_mem_nhds hu)] with v hv
    exact hflat v hv
  exact ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hlocal).deriv

/-- Abel transfer pays the integral of the derivative rather than its supremum. -/
theorem eventually_weightedResiduePrimeReading_variation_log_bound {q : ℕ} [NeZero q] (k : ℕ) :
    ∀ᶠ Y : ℝ in atTop, 1 < Real.log Y ∧
      ∀ a B D : ℝ, 0 < a → 0 ≤ B → 0 ≤ D → ∀ W : ℝ → ℝ, ContDiff ℝ 1 W →
      (∀ u, |u| < a → W u = 0) → |W 1| ≤ B →
      (∫ u in (0 : ℝ)..1, |deriv W u|) ≤ D →
      ∀ X : ℝ, Y ≤ X → Y ≤ X * a → ∀ F : ZMod q → ℝ,
      |weightedResiduePrimeReading q F W X -
          primeClassKappa q F * ∫ u in (0 : ℝ)..1, W u / u| ≤
        (2 * (B + D) / Real.log Y ^ k) * ∑ r : ZMod q, |F r| := by
  filter_upwards [eventually_residuePrimeRealError_log_bound (q := q) k,
    eventually_ge_atTop (1 : ℝ)] with Y hY hY1
  refine ⟨hY.1, ?_⟩
  intro a B D ha hB _ W hW hflat hW1 hWD X hYX hYXa F
  have hX0 : 0 < X := zero_lt_one.trans_le (hY1.trans hYX)
  let E : ℝ := (2 / Real.log Y ^ k) * ∑ r : ZMod q, |F r|
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (div_nonneg zero_le_two (pow_nonneg (zero_lt_one.trans hY.1).le _))
      (sum_nonneg fun r _ => abs_nonneg _)
  have hEX : |residuePrimeRealError q F X| ≤ E := hY.2 X hYX F
  have hpoint : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      ‖deriv W u * residuePrimeRealError q F (X * u)‖ ≤ |deriv W u| * E := by
    intro u hu
    by_cases hua : u < a
    · rw [deriv_zero_of_flat hflat (by rw [abs_of_pos hu.1]; exact hua),
        zero_mul, norm_zero, abs_zero, zero_mul]
    · have hXu : Y ≤ X * u := hYXa.trans
        (mul_le_mul_of_nonneg_left (le_of_not_gt hua) hX0.le)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hY.2 (X * u) hXu F) (abs_nonneg _)
  have hcont : Continuous (fun u => |deriv W u| * E) :=
    (hW.continuous_deriv (by norm_num)).abs.mul continuous_const
  have hI := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall hpoint) (hcont.intervalIntegrable 0 1)
  rw [Real.norm_eq_abs, intervalIntegral.integral_mul_const] at hI
  have hID := hI.trans (mul_le_mul_of_nonneg_right hWD hE)
  rw [weightedResiduePrimeReading_sub_mean_eq F hW ha hflat hX0]
  calc
    _ ≤ |W 1| * |residuePrimeRealError q F X| +
        |∫ u in (0 : ℝ)..1, deriv W u * residuePrimeRealError q F (X * u)| := by
      simpa only [abs_mul] using abs_sub (W 1 * residuePrimeRealError q F X)
        (∫ u in (0 : ℝ)..1, deriv W u * residuePrimeRealError q F (X * u))
    _ ≤ B * E + D * E := add_le_add (mul_le_mul hW1 hEX (abs_nonneg _) hB) hID
    _ = _ := by dsimp only [E]; ring

/-- Reciprocal autocorrelation weights have uniformly bounded total variation. -/
theorem exists_reciprocalShellWeight_variation_bounds {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
      |reciprocalShellWeight φ a 1| ≤ ∫ u, φ u ^ 2 ∧
      (∫ u in (0 : ℝ)..1, |deriv (reciprocalShellWeight φ a) u|) ≤ 2 * L := by
  obtain ⟨L, hLip⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  refine ⟨L, L.coe_nonneg, fun a ha ha1 => ?_⟩
  constructor
  · rw [reciprocalShellWeight, if_neg one_ne_zero, div_one]
    exact abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) a
  · let δ : ℝ := a / 2
    have hδ : 0 < δ := half_pos ha
    have hδ1 : δ ≤ 1 := by dsimp only [δ]; linarith only [ha1]
    have hδa : δ < a := half_lt_self ha
    have hcont : Continuous (fun u => |deriv (reciprocalShellWeight φ a) u|) :=
      ((contDiff_reciprocalShellWeight hφ hsupp ha).continuous_deriv (by norm_num)).abs
    have hzero : (∫ u in (0 : ℝ)..δ, |deriv (reciprocalShellWeight φ a) u|) = 0 := by
      calc
        _ = ∫ _u in (0 : ℝ)..δ, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [Set.uIcc_of_le hδ.le] at hu
          rw [deriv_zero_of_flat (fun v hv => reciprocalShellWeight_zero_near hφ hsupp ha hv)
            (by rw [abs_of_nonneg hu.1]; exact hu.2.trans_lt hδa), abs_zero]
        _ = 0 := intervalIntegral.integral_zero
    have hmajor : ContinuousOn (fun u : ℝ => (L : ℝ) * a / u ^ 2) (Set.Icc δ 1) :=
      continuousOn_const.div (continuousOn_id.pow 2) fun u hu =>
        pow_ne_zero _ (hδ.trans_le hu.1).ne'
    have hint : IntervalIntegrable (fun u : ℝ => (L : ℝ) * a / u ^ 2) volume δ 1 :=
      ContinuousOn.intervalIntegrable_of_Icc hδ1 hmajor
    have hpoint : ∀ u ∈ Set.Icc δ 1,
        |deriv (reciprocalShellWeight φ a) u| ≤ (L : ℝ) * a / u ^ 2 := by
      intro u hu
      have hu0 : 0 < u := hδ.trans_le hu.1
      have hderiv : |deriv (shellAutocorr φ) (a / u)| ≤ L := by
        simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := a / u) hLip
      rw [deriv_reciprocalShellWeight_of_ne_zero hφ hsupp a hu0.ne', abs_mul, abs_div,
        abs_neg, abs_of_pos ha, abs_of_nonneg (sq_nonneg u)]
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_right hderiv (div_nonneg ha.le (sq_nonneg u))
    have hanti : ∀ u ∈ Set.uIcc δ 1,
        HasDerivAt (fun t : ℝ => -((L : ℝ) * a) / t) ((L : ℝ) * a / u ^ 2) u := by
      intro u hu
      rw [Set.uIcc_of_le hδ1] at hu
      have hd := (hasDerivAt_const u (-((L : ℝ) * a))).div (hasDerivAt_id u)
        (hδ.trans_le hu.1).ne'
      convert hd using 1 <;> ring
    have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt hanti hint
    have hend : -((L : ℝ) * a) / 1 - -((L : ℝ) * a) / δ = (L : ℝ) * (2 - a) := by
      dsimp only [δ]
      field_simp [ha.ne'] <;> ring
    rw [hend] at hcalc
    have hbound := intervalIntegral.integral_mono_on hδ1
      (hcont.intervalIntegrable δ 1) hint hpoint
    rw [hcalc] at hbound
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 δ) (hcont.intervalIntegrable δ 1)
    rw [hzero, zero_add] at hsplit
    rw [← hsplit]
    exact hbound.trans (by nlinarith only [mul_nonneg L.coe_nonneg ha.le])

/-- Every inverse-logarithmic source rate has only a linear overlap cost, uniformly in shifts. -/
theorem exists_affineShellCorrection_linear_log_rate {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ᶠ Y : ℝ in atTop,
      1 < Real.log Y ∧ ∀ c X : ℝ, 1 ≤ c → 2 * c * Y ≤ X →
      ∀ shift : ℕ → ℕ, ∀ n : ℕ,
      |affinePrimeShellCorrectionOfShift q n shift φ c X -
        ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| ≤
        C * c / Real.log Y ^ k := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htot : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  obtain ⟨L, hL, hweights⟩ := exists_reciprocalShellWeight_variation_bounds hφ hsupp
  let M := ∫ u, φ u ^ 2
  let C := 8 * q * q.totient * (M + 2 * L) / M
  have hC : 0 < C := by dsimp only [C, M]; positivity
  refine ⟨C, hC, ?_⟩
  intro k
  filter_upwards [eventually_weightedResiduePrimeReading_variation_log_bound (q := q) k,
    eventually_ge_atTop (1 : ℝ)] with Y hY hY1
  refine ⟨hY.1, ?_⟩
  intro c X hc hX shift n
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hYX : Y ≤ X := by nlinarith only [hX, hc, hY0]
  have hX0 : 0 < X := hY0.trans_le hYX
  have hlog : 0 < Real.log Y := zero_lt_one.trans hY.1
  have hXa : Y ≤ X * (1 / (2 * c)) := by
    rw [mul_one_div, le_div_iff₀ (mul_pos zero_lt_two hc0)]
    nlinarith only [hX]
  have hcard : ((Ico 1 ⌈c⌉₊).card : ℝ) ≤ 2 * c := by
    have hn : (Ico 1 ⌈c⌉₊).card ≤ ⌈c⌉₊ := by rw [Nat.card_Ico]; omega
    have hceil : (⌈c⌉₊ : ℝ) < c + 1 := Nat.ceil_lt_add_one hc0.le
    have hnr : ((Ico 1 ⌈c⌉₊).card : ℝ) ≤ ⌈c⌉₊ := by exact_mod_cast hn
    linarith only [hnr, hceil, hc]
  let B := (2 * (M + 2 * L) / Real.log Y ^ k) * ((q : ℝ) * q.totient)
  have hB : 0 ≤ B := by dsimp only [B, M]; positivity
  have hsingle (h : ℕ) (hh : h ∈ Ico 1 ⌈c⌉₊) :
      |affineRamanujanPrimeShell q n (shift h) φ c h X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q (shift h) / (q.totient : ℝ)) *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| ≤ B := by
    have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (mem_Ico.mp hh).1
    have hhc : (h : ℝ) < c := by
      have hhceil : (h : ℝ) + 1 ≤ ⌈c⌉₊ := by exact_mod_cast Nat.succ_le_iff.mpr (mem_Ico.mp hh).2
      have hceil := Nat.ceil_lt_add_one hc0.le
      linarith only [hhceil, hceil]
    have ha : 0 < (h : ℝ) / c := div_pos (zero_lt_one.trans_le hh1) hc0
    have hlow : 1 / c ≤ (h : ℝ) / c := div_le_div_of_nonneg_right hh1 hc0.le
    have hhigh : (h : ℝ) / c ≤ 1 := (div_le_one hc0).mpr hhc.le
    have hw := (contDiff_reciprocalShellWeight hφ hsupp ha).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hflat : ∀ u, |u| < 1 / (2 * c) → reciprocalShellWeight φ (h / c) u = 0 := by
      intro u hu
      exact reciprocalShellWeight_zero_near hφ hsupp ha
        (hu.trans_le ((one_div_le_one_div_of_le hc0 (by linarith only [hc0])).trans hlow))
    have hs := hY.2 (1 / (2 * c)) M (2 * L) (by positivity) hM.le (by positivity)
      (reciprocalShellWeight φ (h / c)) hw hflat
      (hweights (h / c) ha hhigh).1 (hweights (h / c) ha hhigh).2 X hYX hXa
      (affineRamanujanResidue q n (shift h))
    rw [← weightedAffineRamanujanPrimeReading_eq_residue, primeClassKappa_affineRamanujanResidue,
      integral_reciprocalShellWeight hφ hsupp ha] at hs
    rw [affineRamanujanPrimeShell_eq_weighted q n (shift h) φ hc0 h hX0]
    have hresidue : (∑ r : ZMod q, |affineRamanujanResidue q n (shift h) r|) ≤
        (q : ℝ) * q.totient := by
      have hsum := sum_le_sum (s := (univ : Finset (ZMod q))) fun r _ =>
        BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient q (r.val * n + shift h)
      simpa only [affineRamanujanResidue, sum_const, card_univ, ZMod.card, nsmul_eq_mul] using hsum
    exact hs.trans (mul_le_mul_of_nonneg_left hresidue
      (show 0 ≤ 2 * (M + 2 * L) / Real.log Y ^ k by positivity))
  have heq : affinePrimeShellCorrectionOfShift q n shift φ c X -
      ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift =
      (2 / M) * ∑ h ∈ Ico 1 ⌈c⌉₊, (affineRamanujanPrimeShell q n (shift h) φ c h X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q (shift h) / (q.totient : ℝ)) *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u) := by
    simp only [affinePrimeShellCorrectionOfShift, shellCorrectionOfShift, M, sum_sub_distrib,
      mul_sub, mul_sum, div_eq_mul_inv, mul_inv_rev]
    congr 1
    exact sum_congr rfl fun h _ => by ring
  rw [heq, abs_mul, abs_of_pos (div_pos zero_lt_two hM)]
  calc
    _ ≤ (2 / M) * ∑ h ∈ Ico 1 ⌈c⌉₊, |affineRamanujanPrimeShell q n (shift h) φ c h X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q (shift h) / (q.totient : ℝ)) *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (2 / M) * ∑ _h ∈ Ico 1 ⌈c⌉₊, B :=
      mul_le_mul_of_nonneg_left (sum_le_sum hsingle) (by positivity)
    _ ≤ (2 / M) * (2 * c * B) := by
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hB) (by positivity)
    _ = C * c / Real.log Y ^ k := by dsimp only [C, B]; ring

/-- The literal shifted affine error has a quadratic overlap budget with one logarithmic loss. -/
theorem exists_shiftedReciprocalUpwardRowError_quadratic_log_harmonic_budget {m : ℕ} (hm : 0 < m)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 1 ≤ c → ∀ shift : ℕ → ℕ,
      (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) ≤ K * c ^ 2 * (1 + Real.log c) := by
  obtain ⟨C, hC, hsource⟩ := exists_affineShellCorrection_linear_log_rate hm hφ hsupp hM
  obtain ⟨Ybase, hbase⟩ := eventually_atTop.mp (hsource 2)
  let Y₀ := max 1 Ybase
  have hY₀ : 1 ≤ Y₀ := le_max_left _ _
  have hY₀0 : 0 < Y₀ := zero_lt_one.trans_le hY₀
  let D : ℝ := 4 * (Real.log 4 + 4) * m.totient
  have hD : 0 ≤ D := by
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [D]
    positivity
  let J := |Real.log (4 * Y₀)| + 2
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  let H := 1 + 2 * Real.pi ^ 2
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  refine ⟨C ^ 2 * H + D ^ 2 * J + 1, by positivity, ?_⟩
  intro N hN c hc shift
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let T := 2 * c * Y₀ * Real.exp 1
  have hexp : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr zero_le_one
  have hTbase : 2 * c * Y₀ ≤ T := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
      (show 0 ≤ 2 * c * Y₀ by positivity)
  have hT : 1 ≤ T := by
    have hcy := mul_le_mul hc hY₀ zero_le_one hc0.le
    nlinarith only [hcy, hTbase]
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hglobal : ∀ n ∈ Icc 1 N,
      |shiftedReciprocalUpwardRowError φ c shift N m n| ≤ D * c / Real.sqrt n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hquot : 1 ≤ (N : ℝ) / n := (le_div_iff₀ hn0).mpr
      (by simpa only [one_mul] using hnN)
    rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    exact div_le_div_of_nonneg_right
      (abs_affineShellCorrection_error_le_linear hm hφ hsupp hM n shift hc0 hquot)
      (Real.sqrt_nonneg _)
  have hgood : ∀ n ∈ Icc 1 N, T ≤ (N : ℝ) / n →
      |shiftedReciprocalUpwardRowError φ c shift N m n| ≤
        (C * c / (1 + Real.log (((N : ℝ) / T) / n))) / Real.sqrt n := by
    intro n hn ht
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    let X := (N : ℝ) / n
    let Y := X / (2 * c)
    let t := Real.log (((N : ℝ) / T) / n)
    have hX0 : 0 < X := div_pos hN0 hn0
    have hY : Y₀ ≤ Y := (le_div_iff₀ (by positivity : 0 < 2 * c)).mpr
      (by have h := hTbase.trans ht; dsimp only [X] at *; nlinarith only [h])
    have hY0 : 0 < Y := hY₀0.trans_le hY
    have hYn : Ybase ≤ Y := (le_max_right _ _).trans hY
    have ht0 : 0 ≤ t := by
      apply Real.log_nonneg
      apply (one_le_div hn0).mpr
      apply (le_div_iff₀ hT0).mpr
      have h := (le_div_iff₀ hn0).mp ht
      simpa only [mul_comm] using h
    have hlogid : Real.log Y = Real.log Y₀ + 1 + t := by
      have hyid : Y = (Y₀ * Real.exp 1) * (((N : ℝ) / T) / n) := by
        dsimp only [Y, X, T]
        field_simp
      rw [hyid, Real.log_mul (by positivity : Y₀ * Real.exp 1 ≠ 0)
        (by positivity : ((N : ℝ) / T) / n ≠ 0),
        Real.log_mul hY₀0.ne' (Real.exp_pos _).ne', Real.log_exp]
    have hloglower : 1 + t ≤ Real.log Y := by
      rw [hlogid]
      have h := Real.log_nonneg hY₀
      linarith only [h]
    have hlogY : 0 < Real.log Y := (by positivity : 0 < 1 + t).trans_le hloglower
    have hsq : 1 + t ≤ Real.log Y ^ 2 := by
      have hs := mul_self_le_mul_self (by positivity : 0 ≤ 1 + t) hloglower
      nlinarith only [hs, ht0, sq_nonneg t]
    have hfrac : C * c / Real.log Y ^ 2 ≤ C * c / (1 + t) := by
      exact div_le_div_of_nonneg_left (mul_nonneg hC.le hc0.le)
        (by positivity : 0 < 1 + t) hsq
    have hX : 2 * c * Y ≤ X := by
      have hid : 2 * c * Y = X := by
        dsimp only [Y]
        field_simp
      exact hid.le
    have hb := (hbase Y hYn).2 c X hc hX shift n
    rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    exact div_le_div_of_nonneg_right (hb.trans hfrac) (Real.sqrt_nonneg _)
  have hsum := HTGeometry.sum_sq_le_harmonic_log_envelope hN hT
    (shiftedReciprocalUpwardRowError φ c shift N m) hglobal hgood
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlogT : 1 + Real.log (2 * T) ≤ J * (1 + Real.log c) := by
    have hid : 2 * T = (4 * Y₀) * c * Real.exp 1 := by dsimp only [T]; ring
    rw [hid, Real.log_mul (by positivity : (4 * Y₀) * c ≠ 0) (Real.exp_pos _).ne',
      Real.log_mul (by positivity : 4 * Y₀ ≠ 0) hc0.ne', Real.log_exp]
    have ha := le_abs_self (Real.log (4 * Y₀))
    have hm := mul_nonneg (abs_nonneg (Real.log (4 * Y₀))) hlogc
    dsimp only [J]
    nlinarith only [ha, hm, hlogc]
  have hhead : (C * c) ^ 2 * H ≤ C ^ 2 * H * c ^ 2 * (1 + Real.log c) := by
    have h := mul_nonneg (show 0 ≤ C ^ 2 * H * c ^ 2 by positivity) hlogc
    nlinarith only [h]
  have htail : (D * c) ^ 2 * (1 + Real.log (2 * T)) ≤
      D ^ 2 * J * c ^ 2 * (1 + Real.log c) := by
    have h := mul_le_mul_of_nonneg_left hlogT (sq_nonneg (D * c))
    nlinarith only [h]
  have hpay : 0 ≤ c ^ 2 * (1 + Real.log c) := by positivity
  change _ ≤ (C ^ 2 * H + D ^ 2 * J + 1) * c ^ 2 * (1 + Real.log c)
  change _ ≤ (C * c) ^ 2 * H + (D * c) ^ 2 * (1 + Real.log (2 * T)) at hsum
  nlinarith only [hsum, hhead, htail, hpay]

/-- The explicit tilted spline satisfies the same quadratic logarithmic budget. -/
theorem exists_tiltedUnitSpline_shiftedReciprocalUpwardRowError_quadratic_log_harmonic_budget
    {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 1 ≤ c → ∀ shift : ℕ → ℕ,
      (∑ n ∈ Icc 1 N,
        shiftedReciprocalUpwardRowError tiltedUnitSpline c shift N m n ^ 2) ≤
          K * c ^ 2 * (1 + Real.log c) :=
  exists_shiftedReciprocalUpwardRowError_quadratic_log_harmonic_budget hm contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_reciprocalShellWeight_variation_bounds
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_affineShellCorrection_linear_log_rate
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_shiftedReciprocalUpwardRowError_quadratic_log_harmonic_budget
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_shiftedReciprocalUpwardRowError_quadratic_log_harmonic_budget
