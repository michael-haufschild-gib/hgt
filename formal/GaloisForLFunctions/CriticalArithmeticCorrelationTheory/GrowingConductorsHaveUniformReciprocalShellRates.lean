import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReciprocalShellVariationControlsTheActualSource
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.GrowingConductorMertensErrorsHaveUniformLogarithmicDecay

/-!
# Reciprocal shell transfer on growing conductor families

Uniform residue Mertens errors pass through Abel summation with the reciprocal weight's
bounded total variation. Absorbing the Ramanujan mass into extra logarithmic decay
leaves a profile-dependent constant, uniformly over every logarithmic conductor range.
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
theorem eventually_conductor_uniform_weightedResiduePrimeReading_variation_log_bound
    {A : ℝ} (hA : 0 ≤ A) (k : ℕ) :
    ∀ᶠ Y : ℝ in atTop, 1 < Real.log Y ∧
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log Y ^ A → ∀ a B D : ℝ, 0 < a → 0 ≤ B → 0 ≤ D → ∀ W : ℝ → ℝ, ContDiff ℝ 1 W →
      (∀ u, |u| < a → W u = 0) → |W 1| ≤ B →
      (∫ u in (0 : ℝ)..1, |deriv W u|) ≤ D →
      ∀ X : ℝ, Y ≤ X → Y ≤ X * a → ∀ F : ZMod q → ℝ,
      |weightedResiduePrimeReading q F W X -
          primeClassKappa q F * ∫ u in (0 : ℝ)..1, W u / u| ≤
        (2 * (B + D) / Real.log Y ^ k) * ∑ r : ZMod q, |F r| := by
  filter_upwards [eventually_conductor_uniform_residuePrimeRealError_log_bound hA k,
    eventually_ge_atTop (1 : ℝ)] with Y hY hY1
  refine ⟨hY.1, ?_⟩
  intro q _ hq a B D ha hB _ W hW hflat hW1 hWD X hYX hYXa F
  have hX0 : 0 < X := zero_lt_one.trans_le (hY1.trans hYX)
  let E : ℝ := (2 / Real.log Y ^ k) * ∑ r : ZMod q, |F r|
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (div_nonneg zero_le_two (pow_nonneg (zero_lt_one.trans hY.1).le _))
      (sum_nonneg fun r _ => abs_nonneg _)
  have hEX : |residuePrimeRealError q F X| ≤ E := hY.2 X hYX q hq F
  have hpoint : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      ‖deriv W u * residuePrimeRealError q F (X * u)‖ ≤ |deriv W u| * E := by
    intro u hu
    by_cases hua : u < a
    · rw [deriv_zero_of_flat hflat (by rw [abs_of_pos hu.1]; exact hua),
        zero_mul, norm_zero, abs_zero, zero_mul]
    · have hXu : Y ≤ X * u := hYXa.trans
        (mul_le_mul_of_nonneg_left (le_of_not_gt hua) hX0.le)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hY.2 (X * u) hXu q hq F) (abs_nonneg _)
  have hcont : Continuous (fun u => |deriv W u| * E) :=
    (hW.continuous_deriv (by norm_num)).abs.mul continuous_const
  have hI := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) zero_le_one
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

/-- Uniform shell error with the exact conductor mass retained. -/
theorem exists_conductor_uniform_affineShellCorrection_linear_log_rate_raw
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, ∀ᶠ Y : ℝ in atTop,
      1 < Real.log Y ∧ ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log Y ^ A → ∀ c X : ℝ, 1 ≤ c → 2 * c * Y ≤ X →
      ∀ shift : ℕ → ℕ, ∀ n : ℕ,
      |affinePrimeShellCorrectionOfShift q n shift φ c X -
        ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| ≤
        C * ((q : ℝ) * q.totient) * c / Real.log Y ^ k := by
  obtain ⟨L, hL, hweights⟩ := exists_reciprocalShellWeight_variation_bounds hφ hsupp
  let M := ∫ u, φ u ^ 2
  let C := 8 * (M + 2 * L) / M
  have hC : 0 < C := by dsimp only [C, M]; positivity
  refine ⟨C, hC, ?_⟩
  intro A hA k
  filter_upwards [eventually_conductor_uniform_weightedResiduePrimeReading_variation_log_bound hA k,
    eventually_ge_atTop (1 : ℝ)] with Y hY hY1
  refine ⟨hY.1, ?_⟩
  intro q hq hqY c X hc hX shift n
  haveI : NeZero q := ⟨hq.ne'⟩
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
    have hs := hY.2 q hqY (1 / (2 * c)) M (2 * L) (by positivity) hM.le (by positivity)
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
    _ = C * ((q : ℝ) * q.totient) * c / Real.log Y ^ k := by dsimp only [C, B]; ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_conductor_uniform_weightedResiduePrimeReading_variation_log_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_conductor_uniform_affineShellCorrection_linear_log_rate_raw
