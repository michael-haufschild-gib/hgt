import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.WeightedBaseCollapse
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheWeilEnergiesOfTheArithmeticModes
import GaloisForLFunctions.HTGeometry.FiniteShiftedHarmonicAbelBounds
import GaloisForLFunctions.SignedArithmeticHodgeTheory.OneArithmeticRemainderControlsEveryRamanujanResidual

/-!
# Nonpolar top-band cancellation uniform in overlap

A bounded base profile and a mean-zero periodic top-band perturbation have
joint shell–pole coefficient `Oφ(B q U G (1+log N))`, uniformly for
`1≤c≤N/4` and `N≥8`. Periodic cancellation is taken in the partner variable;
the remaining positive Mangoldt convolution costs at most `B log ℓ`.
Both literal polar cross terms obey the same bound.

For the Ramanujan profile `c_m(n)/sqrt(φ(m)n)`, the conductor cost is
`m φ(m)`. The exact quadratic witness identity identifies the bounded
quantity with half the actual linear coefficient.
-/

open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
noncomputable section

private theorem shellPartnerKernel_eq_zero_of_small_product
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    {w : ℝ} (hw : 0 < w) {N ℓ n : ℕ} (hℓ : 1 ≤ ℓ)
    (hsmall : 2 * (ℓ : ℝ) ≤ N) (hn : n ∈ topBand N w) :
    shellPartnerKernel (atomDilate φ w) ℓ n = 0 := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp (mem_topBand.mp hn).1).1
  have he := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos w).le
  have htop := (mem_topBand.mp hn).2
  have hlt : (ℓ : ℝ) * Real.exp w < n := by linarith only [he, htop]
  have hlog := Real.log_lt_log (mul_pos hℓ0 (Real.exp_pos w)) hlt
  rw [Real.log_mul hℓ0.ne' (Real.exp_pos w).ne', Real.log_exp] at hlog
  rw [shellPartnerKernel, bumpCorr_atomDilate_eq_zero_of_le hφ hsupp hw, mul_zero]
  exact (by linarith only [hlog] : w ≤ Real.log n - Real.log ℓ).trans (le_abs_self _)

/-- The positive divisor mass costs one logarithm after summing the periodic partner first. -/
theorem abs_shellTop_product_sum_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2)
    {q : ℕ} (hq : 1 ≤ q) (a ψ : ℕ → ℝ) {B U : ℝ}
    (ha : ∀ n, |a n| ≤ B)
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0)
    (hU : ∀ n, |ψ n| ≤ U) {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    (hA₁0 : 0 ≤ A₁) (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {N : ℕ} (hN : 8 ≤ N) (hwN : 1 ≤ w * N) :
    |∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)), horizonDivisorCoefficient a N ℓ *
      (poleVector ℓ * ∑ n ∈ topBand N w, shellPartnerKernel (atomDilate φ w) ℓ n * ψ n)| ≤
      4 * (4 + 56 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) * B * q * U *
        (∫ u, atomDilate φ w u ^ 2) * (1 + Real.log N) := by
  set K := 4 + 56 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))
  set G := ∫ u, atomDilate φ w u ^ 2
  set L := Nat.ceil ((N : ℝ) * Real.exp w)
  have hB : 0 ≤ B := (abs_nonneg _).trans (ha 0)
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hG : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hNR : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith only [hNR]
  have hem : 3 / 4 ≤ Real.exp (-w) := by
    have := Real.add_one_le_exp (-w)
    linarith only [this, hw4]
  have hep : Real.exp w ≤ 4 / 3 := by
    have h : Real.exp w * Real.exp (-w) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith only [h, hem, Real.exp_pos w]
  have hL : (L : ℝ) ≤ 2 * N := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ (N : ℝ) * Real.exp w by positivity)
    nlinarith only [h, hep, hNR]
  let C := 2 * K * B * q * U * G * (1 + Real.log N) / (N : ℝ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hterm (ℓ : ℕ) (hℓ : ℓ ∈ Icc 1 L) :
      |horizonDivisorCoefficient a N ℓ *
        (poleVector ℓ * ∑ n ∈ topBand N w, shellPartnerKernel (atomDilate φ w) ℓ n * ψ n)| ≤ C := by
    by_cases hsmall : 2 * (ℓ : ℝ) ≤ N
    · have hz (n : ℕ) (hn : n ∈ topBand N w) : shellPartnerKernel (atomDilate φ w) ℓ n = 0 :=
        shellPartnerKernel_eq_zero_of_small_product hφ hsupp hw (mem_Icc.mp hℓ).1 hsmall hn
      have hs : (∑ n ∈ topBand N w, shellPartnerKernel (atomDilate φ w) ℓ n * ψ n) = 0 :=
        sum_eq_zero fun n hn => by rw [hz n hn, zero_mul]
      simpa only [hs, mul_zero, abs_zero] using hC
    have hlarge : (N : ℝ) < 2 * ℓ := lt_of_not_ge hsmall
    have hℓ0 : (0 : ℝ) < ℓ := by linarith only [hlarge, hN0]
    have hℓ4 : 4 ≤ ℓ := by exact_mod_cast (by linarith only [hlarge, hNR] : (4 : ℝ) ≤ ℓ)
    have hwℓ : 1 / 2 ≤ w * ℓ := by nlinarith only [hw, hwN, hlarge]
    have hℓL : (ℓ : ℝ) ≤ L := by exact_mod_cast (mem_Icc.mp hℓ).2
    have hlogℓ : Real.log ℓ ≤ 1 + Real.log N := by
      have h := Real.log_le_log hℓ0 (hℓL.trans hL)
      rw [Real.log_mul two_ne_zero hN0.ne'] at h
      have htwo := Real.log_two_lt_d9
      linarith only [h, htwo]
    have hH : |horizonDivisorCoefficient a N ℓ| ≤ B * (1 + Real.log N) :=
      (abs_horizonDivisorCoefficient_le a ha N ℓ).trans (mul_le_mul_of_nonneg_left hlogℓ hB)
    have hpartner := abs_topBand_shellPartnerKernel_sum_le hφ hsupp hM hq ψ hper hmean hU
      hw hw4 hA₁0 hA₁ hℓ4 hwℓ N
    have hinv : 1 / (ℓ : ℝ) ≤ 2 / N := by
      rw [div_le_div_iff₀ hℓ0 hN0]
      linarith only [hlarge]
    rw [abs_mul]
    calc
      _ ≤ (B * (1 + Real.log N)) * (K * q * U * G / ℓ) :=
        mul_le_mul hH hpartner (abs_nonneg _) (by positivity)
      _ = (1 / (ℓ : ℝ)) * (K * B * q * U * G * (1 + Real.log N)) := by ring
      _ ≤ (2 / N) * (K * B * q * U * G * (1 + Real.log N)) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = C := by dsimp only [C]; ring
  calc
    _ ≤ ∑ ℓ ∈ Icc 1 L, |horizonDivisorCoefficient a N ℓ *
        (poleVector ℓ * ∑ n ∈ topBand N w, shellPartnerKernel (atomDilate φ w) ℓ n * ψ n)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ℓ ∈ Icc 1 L, C := sum_le_sum hterm
    _ = (L : ℝ) * C := by simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ (2 * N) * C := mul_le_mul_of_nonneg_right hL hC
    _ = _ := by dsimp only [C, K, G]; field_simp [hN0.ne']; ring


/-- Removing ratio pairs costs only the bounded harmonic mass of the top band. -/
theorem abs_shellTop_diagonal_le (a ψ : ℕ → ℝ) {B U : ℝ}
    (ha : ∀ n, |a n| ≤ B) (hψ : ∀ n, |ψ n| ≤ U)
    {w : ℝ} (hw : 0 ≤ w) (N : ℕ) :
    |∑ n ∈ topBand N w, ψ n * horizonDivisorCoefficient a N n / (n : ℝ)| ≤
      2 * B * U * Real.log N := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (ha 0)
  have hU : 0 ≤ U := (abs_nonneg _).trans (hψ 0)
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hpoint (n : ℕ) (hn : n ∈ topBand N w) :
      |ψ n * horizonDivisorCoefficient a N n / (n : ℝ)| ≤
        (B * U * Real.log N) * (1 / (n : ℝ)) := by
    have hnI := mem_Icc.mp (mem_topBand.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hnI.1
    have hH : |horizonDivisorCoefficient a N n| ≤ B * Real.log N :=
      (abs_horizonDivisorCoefficient_le a ha N n).trans
        (mul_le_mul_of_nonneg_left (Real.log_le_log hn0 (by exact_mod_cast hnI.2)) hB)
    rw [abs_div, abs_mul, abs_of_pos hn0]
    exact (div_le_div_of_nonneg_right (mul_le_mul (hψ n) hH (abs_nonneg _) hU) hn0.le).trans_eq (by ring)
  calc
    _ ≤ ∑ n ∈ topBand N w, |ψ n * horizonDivisorCoefficient a N n / (n : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ topBand N w, (B * U * Real.log N) * (1 / (n : ℝ)) := sum_le_sum hpoint
    _ = (B * U * Real.log N) * ∑ n ∈ topBand N w, 1 / (n : ℝ) := (mul_sum _ _ _).symm
    _ ≤ (B * U * Real.log N) * 2 := mul_le_mul_of_nonneg_left (sum_topBand_inv_le_two hw N) (by positivity)
    _ = _ := by ring

/-- Mean-zero periodic top-band perturbations have logarithmic shell cost, uniformly in overlap. -/
theorem abs_shellTopCoefficient_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2)
    {q : ℕ} (hq : 1 ≤ q) (a ψ : ℕ → ℝ) {B U : ℝ}
    (ha : ∀ n, |a n| ≤ B)
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0)
    (hU : ∀ n, |ψ n| ≤ U) {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    (hA₁0 : 0 ≤ A₁) (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {N : ℕ} (hN : 8 ≤ N) (hwN : 1 ≤ w * N) :
    |shellTopCoefficient (atomDilate φ w) a ψ N w| ≤
      (18 + 224 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) * B * q * U *
        (∫ u, atomDilate φ w u ^ 2) * (1 + Real.log N) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (ha 0)
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  have hG : 0 ≤ ∫ u, atomDilate φ w u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hfull := abs_shellTop_product_sum_le hφ hsupp hM hq a ψ ha hper hmean hU
    hw hw4 hA₁0 hA₁ hN hwN
  have hdiag := mul_le_mul_of_nonneg_left (abs_shellTop_diagonal_le a ψ ha hU hw.le N) hG
  have hscale := le_mul_of_one_le_left
    (show 0 ≤ B * U * (∫ u, atomDilate φ w u ^ 2) * (1 + Real.log N) by positivity) hqR
  have hlogscale := mul_le_mul_of_nonneg_left
    (show Real.log N ≤ 1 + Real.log N by linarith)
    (show 0 ≤ B * U * (∫ u, atomDilate φ w u ^ 2) by positivity)
  rw [shellTopCoefficient_eq_product_sum hw.le]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hG]
  nlinarith only [hfull, hdiag, hscale, hlogscale]

#print axioms abs_shellTopCoefficient_le

/-- Periodic interval sums have a bound independent of their endpoints. -/
theorem abs_sum_Ico_periodic_mean_zero_le
    {q : ℕ} (hq : 1 ≤ q) (ψ : ℕ → ℝ) {U : ℝ}
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0)
    (hU : ∀ n, |ψ n| ≤ U) (A B : ℕ) :
    |∑ n ∈ Ico A B, ψ n| ≤ 2 * q * U := by
  rw [sum_Ico_eq_sum_range]
  have hm : (∑ i ∈ range q, ψ (A + i)) = 0 :=
    (sum_range_shift_of_periodic ψ hper A).trans hmean
  have hp : ∀ i, ψ (A + (i + q)) = ψ (A + i) := fun i => by
    simpa only [Nat.add_assoc] using hper (A + i)
  simpa only [hm, zero_div, mul_zero, sub_zero] using
    abs_sum_range_sub_mul_mean_le hq (fun i => ψ (A + i)) hp (fun i => hU (A + i)) (B - A)

/-- The two top-band pole moments retain the harmonic endpoint factor. -/
theorem abs_topBand_periodic_moments_le
    {q : ℕ} (hq : 1 ≤ q) (ψ : ℕ → ℝ) {U : ℝ}
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0)
    (hU : ∀ n, |ψ n| ≤ U) {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw : 0 ≤ w) :
    |∑ n ∈ topBand N w, ψ n| ≤ 2 * q * U ∧
      |∑ n ∈ topBand N w, ψ n / (n : ℝ)| ≤ 4 * q * U / N := by
  set A := Nat.floor ((N : ℝ) * Real.exp w / 2) + 1
  have hA1 : 1 ≤ A := by dsimp only [A]; omega
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  have hNA : (N : ℝ) < 2 * A := by
    have hfloor := Nat.lt_floor_add_one ((N : ℝ) * Real.exp w / 2)
    have he : (N : ℝ) ≤ N * Real.exp w :=
      le_mul_of_one_le_right hN0.le (Real.one_le_exp_iff.mpr hw)
    have hcast : (A : ℝ) = Nat.floor ((N : ℝ) * Real.exp w / 2) + 1 := by
      dsimp only [A]
      push_cast
      rfl
    rw [hcast]
    linarith only [hfloor, he]
  have hinterval : topBand N w = Ico A (N + 1) := by
    rw [Ico_add_one_right_eq_Icc]
    exact topBand_eq_Icc N w
  rw [hinterval]
  refine ⟨abs_sum_Ico_periodic_mean_zero_le hq ψ hper hmean hU A (N + 1), ?_⟩
  have hh := HTGeometry.abs_sum_Ico_div_add_le (r := 0)
    (fun l k _ => abs_sum_Ico_periodic_mean_zero_le hq ψ hper hmean hU l k) A (N + 1)
    (by simpa only [zero_add] using hA0)
  simp only [zero_add] at hh
  have hinv : 1 / (A : ℝ) ≤ 2 / N := by
    rw [div_le_div_iff₀ hA0 hN0]
    linarith only [hNA]
  exact hh.trans (by
    have h := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 2 * (q : ℝ) * U by positivity)
    convert h using 1 <;> ring)

/-- A bounded base profile has harmonic and counting pole moments. -/
theorem abs_bounded_profile_moments_le (a : ℕ → ℝ) {B : ℝ}
    (hB : ∀ n, |a n| ≤ B) (N : ℕ) :
    |∑ n ∈ Icc 1 N, a n / (n : ℝ)| ≤ B * (1 + Real.log N) ∧
      |∑ n ∈ Icc 1 N, a n| ≤ B * N := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  constructor
  · calc
      _ ≤ ∑ n ∈ Icc 1 N, |a n / (n : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 N, B * (1 / (n : ℝ)) := by
        apply sum_le_sum
        intro n _
        rw [abs_div, Nat.abs_cast]
        exact (div_le_div_of_nonneg_right (hB n) (Nat.cast_nonneg n)).trans_eq (by ring)
      _ = B * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_sum_bounds N).2 hB0
  · calc
      _ ≤ ∑ n ∈ Icc 1 N, |a n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Icc 1 N, B := sum_le_sum fun n _ => hB n
      _ = _ := by simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring

/-- The product of the two atom moments is bounded by its autocorrelation mass. -/
theorem abs_poleWeight_product_le_mass
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    {w : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4) :
    |poleWeightMinus (atomDilate φ w) * poleWeightPlus (atomDilate φ w)| ≤
      ∫ u, atomDilate φ w u ^ 2 := by
  let g := atomDilate φ w
  have hg : Continuous g := hφ.continuous.comp (continuous_id.div_const w)
  have hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0 := by
    intro u hu
    apply hsupp
    intro h
    apply hu
    rw [Set.mem_Icc, le_div_iff₀ hw, div_le_iff₀ hw] at h
    exact ⟨by nlinarith only [h.1, hw], by nlinarith only [h.2, hw]⟩
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc 0 w)) fun u hu => hgsupp u hu
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hexp : Real.exp (w / 2) ≤ 2 := by
    have h := Real.exp_le_exp.mpr (show w / 2 ≤ Real.log 2 by
      have htwo := Real.log_two_gt_d9
      linarith only [htwo, hw4])
    rwa [Real.exp_log two_pos] at h
  have h := abs_integral_le_of_vanish (f := fun u => Real.exp (u / 2) * bumpCorr g u)
    (C := 2 * ∫ u, g u ^ 2) hw.le
    (fun u hu => by rw [bumpCorr_atomDilate_eq_zero_of_le hφ hsupp hw hu, mul_zero])
    (fun u hu => by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul
        ((Real.exp_le_exp.mpr (by linarith only [(abs_le.mp hu).2])).trans hexp)
        (abs_bumpCorr_le hg hgc u) (abs_nonneg _) zero_le_two)
  have he : poleWeightMinus g * poleWeightPlus g = ∫ u, Real.exp (u / 2) * bumpCorr g u :=
    (integral_exp_half_mul_bumpCorr hg hgc).symm
  rw [he]
  refine h.trans ?_
  nlinarith only [hw4, hG]

/-- Both literal polar cross terms are uniformly logarithmic on periodic top-band perturbations. -/
theorem abs_topBand_polar_coefficient_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    {q : ℕ} (hq : 1 ≤ q) (a ψ : ℕ → ℝ) {B U : ℝ}
    (ha : ∀ n, |a n| ≤ B)
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0)
    (hU : ∀ n, |ψ n| ≤ U) {w : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    {N : ℕ} (hN : 1 ≤ N) :
    |poleWeightMinus (atomDilate φ w) * poleWeightPlus (atomDilate φ w) *
      ((∑ n ∈ Icc 1 N, a n / (n : ℝ)) * (∑ n ∈ topBand N w, ψ n) +
        (∑ n ∈ Icc 1 N, a n) * (∑ n ∈ topBand N w, ψ n / (n : ℝ)))| ≤
      6 * B * q * U * (∫ u, atomDilate φ w u ^ 2) * (1 + Real.log N) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (ha 0)
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  have hG : 0 ≤ ∫ u, atomDilate φ w u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hb1, hb2⟩ := abs_bounded_profile_moments_le a ha N
  obtain ⟨hp1, hp2⟩ := abs_topBand_periodic_moments_le hq ψ hper hmean hU hN hw.le
  have h1 := mul_le_mul hb1 hp1 (abs_nonneg _) (show 0 ≤ B * (1 + Real.log N) by positivity)
  have h2 := mul_le_mul hb2 hp2 (abs_nonneg _) (show 0 ≤ B * N by positivity)
  have hcancel : B * N * (4 * q * U / N) = 4 * B * q * U := by
    field_simp [hN0.ne']
  rw [hcancel] at h2
  have hbracket : |(∑ n ∈ Icc 1 N, a n / (n : ℝ)) * (∑ n ∈ topBand N w, ψ n) +
      (∑ n ∈ Icc 1 N, a n) * (∑ n ∈ topBand N w, ψ n / (n : ℝ))| ≤
      6 * B * q * U * (1 + Real.log N) := by
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul]
    have hpos : 0 ≤ B * (q : ℝ) * U * Real.log N := by positivity
    nlinarith only [h1, h2, hpos]
  rw [abs_mul]
  exact (mul_le_mul (abs_poleWeight_product_le_mass hφ hsupp hw hw4) hbracket
    (abs_nonneg _) hG).trans_eq (by ring)

#print axioms abs_topBand_polar_coefficient_le

/-- A single profile constant pays all mean-zero periodic top-band perturbations. -/
theorem exists_abs_jointTopCoefficient_le_uniform_overlap
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ), 1 ≤ q → ∀ (a ψ : ℕ → ℝ) (B U : ℝ),
      (∀ n, |a n| ≤ B) → (∀ n, ψ (n + q) = ψ n) →
      (∑ r ∈ range q, ψ r = 0) → (∀ n, |ψ n| ≤ U) →
      ∀ (c : ℝ) (N : ℕ), 1 ≤ c → 8 ≤ N → 4 * c ≤ N →
      |jointTopCoefficient (atomDilate φ (c / N)) a ψ N (c / N)| ≤
        K * B * q * U * (∫ u, atomDilate φ (c / N) u ^ 2) * (1 + Real.log N) := by
  obtain ⟨A₁, hA₁0, hA₁⟩ := exists_abs_deriv_shellAutocorr_le hφ hsupp
  refine ⟨24 + 224 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2)), by positivity,
    fun q hq a ψ B U ha hper hmean hU c N hc hN hNc => ?_⟩
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw : 0 < c / (N : ℝ) := div_pos hc0 hN0
  have hw4 : c / (N : ℝ) ≤ 1 / 4 := by
    rw [div_le_iff₀ hN0]
    linarith only [hNc]
  have hwN : 1 ≤ c / (N : ℝ) * N := by rwa [div_mul_cancel₀ c hN0.ne']
  have hs := abs_shellTopCoefficient_le hφ hsupp hM hq a ψ ha hper hmean hU hw hw4 hA₁0 hA₁ hN hwN
  have hp := abs_topBand_polar_coefficient_le hφ hsupp hq a ψ ha hper hmean hU hw hw4 (by omega : 1 ≤ N)
  rw [jointTopCoefficient]
  refine (abs_sub _ _).trans ?_
  nlinarith only [hs, hp]

/-- Every nonpolar Ramanujan mode has a polynomial-conductor top-band joint bound. -/
theorem exists_abs_ramanujan_jointTopCoefficient_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ), 2 ≤ m → ∀ (c : ℝ) (N : ℕ),
      1 ≤ c → 8 ≤ N → 4 * c ≤ N →
      |jointTopCoefficient (atomDilate φ (c / N)) (normalizedRamanujanMode m)
        (normalizedRamanujanMode m) N (c / N)| ≤
        K * m * m.totient * (∫ u, atomDilate φ (c / N) u ^ 2) * (1 + Real.log N) := by
  obtain ⟨K, hK, hbound⟩ := exists_abs_jointTopCoefficient_le_uniform_overlap hφ hsupp hM
  refine ⟨K, hK, fun m hm c N hc hN hNc => ?_⟩
  have hm0 : 0 < m := by omega
  have h := hbound m (by omega) (normalizedRamanujanMode m) (normalizedRamanujanMode m)
    (Real.sqrt (m.totient : ℝ)) (Real.sqrt (m.totient : ℝ))
    (SignedArithmeticHodgeTheory.abs_normalizedRamanujanMode_le_sqrt_totient hm0)
    (normalizedRamanujanMode_periodic hm0) (sum_range_normalizedRamanujanMode hm)
    (SignedArithmeticHodgeTheory.abs_normalizedRamanujanMode_le_sqrt_totient hm0) c N hc hN hNc
  refine h.trans_eq ?_
  rw [show K * Real.sqrt (m.totient : ℝ) * m * Real.sqrt (m.totient : ℝ) =
      K * m * (Real.sqrt (m.totient : ℝ) ^ 2) by ring,
    Real.sq_sqrt (Nat.cast_nonneg _)]

#print axioms exists_abs_jointTopCoefficient_le_uniform_overlap
#print axioms exists_abs_ramanujan_jointTopCoefficient_le

/-- The Ramanujan pole profile multiplied by `1+η` on the top band. -/
def ramanujanTopBandProfile (m N : ℕ) (w η : ℝ) (n : ℕ) : ℝ :=
  ramanujanPoleProfile m n + η *
    (if n ∈ topBand N w then ramanujanPoleProfile m n else 0)

theorem ramanujanTopBandProfile_eq (m N : ℕ) (w η : ℝ) :
    ramanujanTopBandProfile m N w η =
      topBandPerturbedProfile (normalizedRamanujanMode m) (normalizedRamanujanMode m) N w η := by
  funext n
  simp only [ramanujanTopBandProfile, topBandPerturbedProfile, ramanujanPoleProfile,
    poleVector, div_eq_mul_inv, one_mul, mul_comm]

/-- The bounded coefficient is exactly the linear coefficient of the actual Ramanujan witness. -/
theorem jointBlock_ramanujanTopBandProfile {g : ℝ → ℝ} {w : ℝ} (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    {N : ℕ} (hN : 1 ≤ N) (m : ℕ) (η : ℝ) :
    2 * ((∫ u, atomicTest N (ramanujanTopBandProfile m N w η) g u * Real.exp (-(u / 2))) *
        (∫ u, atomicTest N (ramanujanTopBandProfile m N w η) g u * Real.exp (u / 2))) -
      nonRatioForm g N (ramanujanTopBandProfile m N w η) =
    (2 * ((∫ u, atomicTest N (ramanujanPoleProfile m) g u * Real.exp (-(u / 2))) *
        (∫ u, atomicTest N (ramanujanPoleProfile m) g u * Real.exp (u / 2))) -
      nonRatioForm g N (ramanujanPoleProfile m)) +
      2 * η * jointTopCoefficient g (normalizedRamanujanMode m) (normalizedRamanujanMode m) N w +
      2 * η ^ 2 * (poleWeightMinus g * poleWeightPlus g *
        (∑ n ∈ topBand N w, normalizedRamanujanMode m n / (n : ℝ)) *
          ∑ n ∈ topBand N w, normalizedRamanujanMode m n) := by
  have he : (fun n => poleVector n * normalizedRamanujanMode m n) = ramanujanPoleProfile m := by
    funext n
    simp only [poleVector, ramanujanPoleProfile, div_eq_mul_inv, one_mul, mul_comm]
  rw [ramanujanTopBandProfile_eq]
  simpa only [he] using jointBlock_topBandPerturbedProfile hg hgsupp hw hN
    (normalizedRamanujanMode m) (normalizedRamanujanMode m) η

#print axioms jointBlock_ramanujanTopBandProfile

end
end GaloisForLFunctions.SuccessorShellArithmetic
