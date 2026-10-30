import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ResidueMertensFinitePartsHaveLogarithmicRates

/-!
# Logarithmic rates for growing signed shell sources

Quantitative residue Mertens errors pass through the exact weighted Abel
identity. Reciprocal shell weights have quadratic derivative cost, giving
a cubic overlap cost for the complete signed affine correction.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  BezoutValuationIncidence SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

private theorem deriv_zero_on_flat {W : ℝ → ℝ} {a : ℝ}
    (hflat : ∀ u, |u| < a → W u = 0) {u : ℝ} (hu : |u| < a) : deriv W u = 0 := by
  have hlocal : W =ᶠ[𝓝 u] fun _ => 0 := by
    filter_upwards [continuous_abs.continuousAt.eventually (gt_mem_nhds hu)] with v hv
    exact hflat v hv
  exact ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hlocal).deriv

/-- Quantitative Abel transfer with a movable flat neighborhood and explicit weight costs. -/
theorem eventually_weightedResiduePrimeReading_log_bound {q : ℕ} [NeZero q] (k : ℕ) :
    ∀ᶠ Y : ℝ in atTop, 1 < Real.log Y ∧
      ∀ a B D : ℝ, 0 < a → 0 ≤ B → 0 ≤ D → ∀ W : ℝ → ℝ, ContDiff ℝ 1 W →
      (∀ u, |u| < a → W u = 0) → |W 1| ≤ B →
      (∀ u ∈ Set.Icc (0 : ℝ) 1, |deriv W u| ≤ D) →
      ∀ X : ℝ, Y ≤ X → Y ≤ X * a → ∀ F : ZMod q → ℝ,
      |weightedResiduePrimeReading q F W X -
          primeClassKappa q F * ∫ u in (0 : ℝ)..1, W u / u| ≤
        (2 * (B + D) / Real.log Y ^ k) * ∑ r : ZMod q, |F r| := by
  filter_upwards [eventually_residuePrimeRealError_log_bound (q := q) k,
    eventually_ge_atTop (1 : ℝ)] with Y hY hY1
  refine ⟨hY.1, ?_⟩
  intro a B D ha hB hD W hW hflat hW1 hWD X hYX hYXa F
  have hX0 : 0 < X := zero_lt_one.trans_le (hY1.trans hYX)
  let E : ℝ := (2 / Real.log Y ^ k) * ∑ r : ZMod q, |F r|
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (div_nonneg zero_le_two (pow_nonneg (zero_lt_one.trans hY.1).le _))
      (sum_nonneg fun r _ => abs_nonneg _)
  have hEX : |residuePrimeRealError q F X| ≤ E := hY.2 X hYX F
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
      ‖deriv W u * residuePrimeRealError q F (X * u)‖ ≤ D * E := by
    intro u hu
    rw [Set.uIoc_of_le zero_le_one] at hu
    by_cases hua : u < a
    · rw [deriv_zero_on_flat hflat (by rw [abs_of_pos hu.1]; exact hua), zero_mul, norm_zero]
      exact mul_nonneg hD hE
    · have hXu : Y ≤ X * u := hYXa.trans
        (mul_le_mul_of_nonneg_left (le_of_not_gt hua) hX0.le)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hWD u ⟨hu.1.le, hu.2⟩) (hY.2 (X * u) hXu F) (abs_nonneg _) hD
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simp only [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at hI
  rw [weightedResiduePrimeReading_sub_mean_eq F hW ha hflat hX0]
  calc
    _ ≤ |W 1| * |residuePrimeRealError q F X| +
        |∫ u in (0 : ℝ)..1, deriv W u * residuePrimeRealError q F (X * u)| := by
      simpa only [abs_mul] using abs_sub (W 1 * residuePrimeRealError q F X)
        (∫ u in (0 : ℝ)..1, deriv W u * residuePrimeRealError q F (X * u))
    _ ≤ B * E + D * E := add_le_add (mul_le_mul hW1 hEX (abs_nonneg _) hB) hI
    _ = _ := by dsimp only [E]; ring

/-- Reciprocal shell weights have a derivative cost quadratic in the overlap. -/
theorem exists_reciprocalShellWeight_polynomial_bounds {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ c a : ℝ, 1 ≤ c → 1 / c ≤ a → a ≤ 1 →
      |reciprocalShellWeight φ a 1| ≤ ∫ u, φ u ^ 2 ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, |deriv (reciprocalShellWeight φ a) u| ≤ 4 * L * c ^ 2 := by
  obtain ⟨L, hLip⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  refine ⟨L, L.coe_nonneg, ?_⟩
  intro c a hc hlow hhigh
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have ha : 0 < a := (one_div_pos.mpr hc0).trans_le hlow
  constructor
  · rw [reciprocalShellWeight, if_neg one_ne_zero, div_one]
    exact abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) a
  · intro u hu
    let τ := 1 / (2 * c)
    have hτ : 0 < τ := by dsimp only [τ]; positivity
    have hτa : τ < a := by
      have h : 1 / (2 * c) < 1 / c := one_div_lt_one_div_of_lt hc0 (by linarith only [hc0])
      exact h.trans_le hlow
    by_cases hsmall : u < τ
    · rw [deriv_zero_on_flat (fun v hv => reciprocalShellWeight_zero_near hφ hsupp ha hv)
        (by rw [abs_of_nonneg hu.1]; exact hsmall.trans hτa), abs_zero]
      positivity
    · have hτu : τ ≤ u := le_of_not_gt hsmall
      have hu0 : 0 < u := hτ.trans_le hτu
      have htwo : 1 ≤ u * (2 * c) := (div_le_iff₀ (mul_pos zero_lt_two hc0)).mp hτu
      have hsq := mul_le_mul htwo htwo (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : 0 ≤ u * (2 * c))
      have hquot : a / u ^ 2 ≤ 4 * c ^ 2 := by
        apply (div_le_iff₀ (sq_pos_of_pos hu0)).mpr
        nlinarith only [hsq, hhigh]
      have hderiv : |deriv (shellAutocorr φ) (a / u)| ≤ L := by
        simpa only [Real.norm_eq_abs] using (norm_deriv_le_of_lipschitz (x₀ := a / u) hLip)
      rw [deriv_reciprocalShellWeight_of_ne_zero hφ hsupp a hu0.ne', abs_mul, abs_div,
        abs_neg, abs_of_pos ha, abs_of_nonneg (sq_nonneg u)]
      calc
        _ ≤ (L : ℝ) * (4 * c ^ 2) :=
          mul_le_mul hderiv hquot (div_nonneg ha.le (sq_nonneg _)) L.coe_nonneg
        _ = _ := by ring

/-- The literal signed affine shells have every inverse-logarithmic source rate with
only a cubic overlap cost, uniformly over all shifts and affine multipliers. -/
theorem exists_affineShellCorrection_polynomial_log_rate {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ᶠ Y : ℝ in atTop,
      1 < Real.log Y ∧ ∀ c X : ℝ, 1 ≤ c → 2 * c * Y ≤ X →
      ∀ shift : ℕ → ℕ, ∀ n : ℕ,
      |affinePrimeShellCorrectionOfShift q n shift φ c X -
        ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| ≤
        C * c ^ 3 / Real.log Y ^ k := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htot : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  obtain ⟨L, hL, hweights⟩ := exists_reciprocalShellWeight_polynomial_bounds hφ hsupp
  let M := ∫ u, φ u ^ 2
  let C := 8 * q * q.totient * (M + 4 * L) / M
  have hC : 0 < C := by dsimp only [C, M]; positivity
  refine ⟨C, hC, ?_⟩
  intro k
  filter_upwards [eventually_weightedResiduePrimeReading_log_bound (q := q) k,
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
  let B := (2 * (M + 4 * L) * c ^ 2 / Real.log Y ^ k) * ((q : ℝ) * q.totient)
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
    have hs := hY.2 (1 / (2 * c)) M (4 * L * c ^ 2) (by positivity) hM.le (by positivity)
      (reciprocalShellWeight φ (h / c)) hw hflat
      (hweights c (h / c) hc hlow hhigh).1 (hweights c (h / c) hc hlow hhigh).2 X hYX hXa
      (affineRamanujanResidue q n (shift h))
    rw [← weightedAffineRamanujanPrimeReading_eq_residue, primeClassKappa_affineRamanujanResidue,
      integral_reciprocalShellWeight hφ hsupp ha] at hs
    rw [affineRamanujanPrimeShell_eq_weighted q n (shift h) φ hc0 h hX0]
    have hresidue : (∑ r : ZMod q, |affineRamanujanResidue q n (shift h) r|) ≤
        (q : ℝ) * q.totient := by
      have hsum := sum_le_sum (s := (univ : Finset (ZMod q))) fun r _ =>
        BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient q (r.val * n + shift h)
      simpa only [affineRamanujanResidue, sum_const, card_univ, ZMod.card, nsmul_eq_mul] using hsum
    have hmass : M + 4 * L * c ^ 2 ≤ (M + 4 * L) * c ^ 2 := by
      have hc2 : 1 ≤ c ^ 2 := by nlinarith only [hc]
      have hm := mul_le_mul_of_nonneg_left hc2 hM.le
      nlinarith only [hm]
    have hbound := mul_le_mul
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass zero_le_two)
        (pow_nonneg hlog.le _)) hresidue (sum_nonneg fun r _ => abs_nonneg _)
        (show 0 ≤ 2 * ((M + 4 * L) * c ^ 2) / Real.log Y ^ k by positivity)
    exact hs.trans (by simpa only [B, mul_assoc] using hbound)
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
    _ = C * c ^ 3 / Real.log Y ^ k := by dsimp only [C, B]; ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_weightedResiduePrimeReading_log_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_affineShellCorrection_polynomial_log_rate
