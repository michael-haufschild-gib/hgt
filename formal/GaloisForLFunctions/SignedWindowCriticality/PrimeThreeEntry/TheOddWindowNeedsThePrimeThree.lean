import GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry.TheSliverPotentialCannotCarryThePrimeThree

/-!
# The odd window needs the prime 3

For an odd test `F` supported in `[−c, c]`, `2c < log 4`, Weil's form reads
`W(F) = Γ A(0) + 𝒥(F) − 2w₂ A(log 2) − 2w₃ A(log 3) − 2 S(F)²`, with `A` the autocorrelation of `F`,
`w_p = Λ(p)/√p`, `𝒥` the archimedean Lévy energy and `S(F) = ∫ F sinh(x/2)` the pole moment.
Deleting the prime `3` means passing to `W(F) + 2w₃ A(log 3)`. This module proves that the deleted form
is negative on an odd test supported in `[−3/5, 3/5]`, a window only `2c − log 3 ≈ 0.10` past the entry
of the prime `3` (`exists_odd_test_without_prime_three_neg`), hence on every window of half-width
`c ≥ 3/5` (`not_nonneg_without_prime_three`).

So on these windows the prime `3` is a payer of the odd sector, not a cost: wherever `W(F) ≥ 0` on such
a test, its reflection correlation `A(log 3)` is negative and `−2w₃ A(log 3) > 0` closes the gap. With
`not_sliverPotentialCertificate` this pins the mechanism: the prime `3` pays through the sign of
its reflection, and its size alone (its collar mass) cannot be what pays it.

The witness is the mollification of `F(x) = P(x/c₂)`, `c₂ = 599/1000`, `P(u) = u(1 − u²)(1 − 9u²/2)`.
Its deleted form `Γ A(0) + 𝒥(F) − 2w₂ A(log 2) − 2S(F)²` is certified below `−1/200`: exact
polynomial autocorrelation `A(t) = c₂ C(t/c₂)`, quartic majorant of the archimedean density on
`(0, 2c₂]` with exponential tail, Taylor enclosure of `sinh` for `S(F)`, and a mean-value bound
for `A(log 2)`.
-/

open Real MeasureTheory Set Filter Topology intervalIntegral Zeta23
open scoped CompactlySupported
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilLevyPoleGauss _root_.RHTower.WeilMarkovPole

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry

open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.SignedWindowCriticality
open GaloisForLFunctions.SignedWindowCriticality.BelowLogFour
open GaloisForLFunctions.WindowTowerOfSpecZ
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open SpacingScaleHarmonicAnalysis

/-! ### 1. The witness `P(x/c₂)` -/

/-- Half-width of the unmollified witness. -/
private abbrev c₂ : ℝ := 599 / 1000

/-- `P(u) = u(1 − u²)(1 − 9u²/2)` expanded. -/
def delPoly (u : ℝ) : ℝ := u - (11 / 2) * u ^ 3 + (9 / 2) * u ^ 5

/-- The compact unit witness `u (1 − u²)₊ (1 − 9u²/2)`. -/
def delUnit (u : ℝ) : ℝ := u * max (1 - u ^ 2) 0 * (1 - (9 / 2) * u ^ 2)

/-- The scaled witness `F(x) = delUnit (x/c₂)`, supported in `[−c₂, c₂]`. -/
def delWitness (x : ℝ) : ℝ := delUnit (x / c₂)

private lemma delUnit_inside {u : ℝ} (hl : -1 ≤ u) (hr : u ≤ 1) : delUnit u = delPoly u := by
  unfold delUnit delPoly
  rw [max_eq_left (by nlinarith)]
  ring

private lemma delUnit_outside {u : ℝ} (hu : 1 ≤ |u|) : delUnit u = 0 := by
  unfold delUnit
  have hsq : 1 ≤ u ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one hu 2
    rwa [one_pow, sq_abs] at this
  rw [max_eq_right (by linarith), mul_zero, zero_mul]

lemma continuous_delWitness : Continuous delWitness := by
  unfold delWitness delUnit; fun_prop

lemma delWitness_odd (x : ℝ) : delWitness (-x) = -delWitness x := by
  unfold delWitness delUnit
  rw [neg_div, neg_sq]
  ring

lemma delWitness_eq_zero_of_far {x : ℝ} (hx : c₂ ≤ |x|) : delWitness x = 0 := by
  have hc : (0 : ℝ) < c₂ := by norm_num
  unfold delWitness
  apply delUnit_outside
  rw [abs_div, abs_of_pos hc, one_le_div hc]
  exact hx

lemma compact_delWitness : HasCompactSupport delWitness :=
  HasCompactSupport.intro (isCompact_Icc (a := -c₂) (b := c₂)) fun _ hx =>
    delWitness_eq_zero_of_far (le_of_lt (not_le.mp fun h => hx (abs_le.mp h)))

private lemma delWitness_inside {x : ℝ} (hl : -c₂ ≤ x) (hr : x ≤ c₂) :
    delWitness x = delPoly (x / c₂) := by
  have hc : (0 : ℝ) < c₂ := by norm_num
  exact delUnit_inside ((le_div_iff₀ hc).mpr (by linarith)) ((div_le_iff₀ hc).mpr (by linarith))

private lemma abs_delWitness_le (x : ℝ) : |delWitness x| ≤ 7 / 2 := by
  by_cases hx : c₂ ≤ |x|
  · rw [delWitness_eq_zero_of_far hx, abs_zero]; norm_num
  · push Not at hx
    have hc : (0 : ℝ) < c₂ := by norm_num
    unfold delWitness delUnit
    set u := x / c₂
    have hu : |u| < 1 := by
      rw [abs_div, abs_of_pos hc, div_lt_one hc]
      exact hx
    have hb := abs_lt.mp hu
    have hu2 : 0 ≤ 1 - u ^ 2 ∧ 1 - u ^ 2 ≤ 1 :=
      ⟨by nlinarith [hb.1, hb.2], by nlinarith [sq_nonneg u]⟩
    have hq : |1 - (9 / 2) * u ^ 2| ≤ 7 / 2 := by
      have h2 : u ^ 2 ≤ 1 := by nlinarith [hb.1, hb.2]
      rw [abs_le]
      exact ⟨by nlinarith [sq_nonneg u], by nlinarith [sq_nonneg u]⟩
    rw [abs_mul, abs_mul, max_eq_left hu2.1, abs_of_nonneg hu2.1]
    have h1 : |u| * (1 - u ^ 2) ≤ 1 := by
      nlinarith [abs_nonneg u, hu.le, hu2.1, hu2.2]
    calc |u| * (1 - u ^ 2) * |1 - (9 / 2) * u ^ 2|
        ≤ 1 * (7 / 2) := mul_le_mul h1 hq (abs_nonneg _) zero_le_one
      _ = 7 / 2 := by ring

/-- The witness as a compactly supported continuous function. -/
private def ccDel : C_c(ℝ, ℝ) :=
  ⟨⟨delWitness, continuous_delWitness⟩, compact_delWitness⟩

/-! ### 2. The exact autocorrelation `A(t) = c₂ C(t/c₂)` -/

private lemma hasDerivAt_scaled_del {G G' : ℝ → ℝ} {x : ℝ}
    (hG : HasDerivAt G (G' (x / c₂)) (x / c₂)) :
    HasDerivAt (fun z : ℝ => c₂ * G (z / c₂)) (G' (x / c₂)) x := by
  have hc : (c₂ : ℝ) ≠ 0 := by norm_num
  have h1 := (hG.comp x ((hasDerivAt_id x).div_const c₂)).const_mul c₂
  exact h1.congr_deriv (by field_simp [hc])

/-- The unit autocorrelation `C(s) = ∫_{−1}^{1−s} P(v) P(v + s) dv`, `0 ≤ s ≤ 2`. -/
def delCorr (s : ℝ) : ℝ :=
  (188 / 1155 : ℝ) +
    (-127 / 35 : ℝ) * s ^ 2 +
    (49 / 6 : ℝ) * s ^ 3 +
    (-39 / 7 : ℝ) * s ^ 4 +
    (23 / 40 : ℝ) * s ^ 5 +
    (241 / 560 : ℝ) * s ^ 7 +
    (-11 / 112 : ℝ) * s ^ 9 +
    (9 / 1232 : ℝ) * s ^ 11

/-- An antiderivative in `x` of `P(x) P(x + s)`. -/
private def delCorrAnti (s x : ℝ) : ℝ :=
  ((81 / 44 : ℝ)) * x ^ 11 +
    ((81 / 8 : ℝ) * s ^ 1) * x ^ 10 +
    ((-11 / 2 : ℝ) +
      (45 / 2 : ℝ) * s ^ 2) * x ^ 9 +
    ((-99 / 4 : ℝ) * s ^ 1 +
      (405 / 16 : ℝ) * s ^ 3) * x ^ 8 +
    ((157 / 28 : ℝ) +
      (-1287 / 28 : ℝ) * s ^ 2 +
      (405 / 28 : ℝ) * s ^ 4) * x ^ 7 +
    ((157 / 8 : ℝ) * s ^ 1 +
      (-363 / 8 : ℝ) * s ^ 3 +
      (27 / 8 : ℝ) * s ^ 5) * x ^ 6 +
    ((-11 / 5 : ℝ) +
      (543 / 20 : ℝ) * s ^ 2 +
      (-99 / 4 : ℝ) * s ^ 4) * x ^ 5 +
    ((-11 / 2 : ℝ) * s ^ 1 +
      (301 / 16 : ℝ) * s ^ 3 +
      (-99 / 16 : ℝ) * s ^ 5) * x ^ 4 +
    ((1 / 3 : ℝ) +
      (-11 / 2 : ℝ) * s ^ 2 +
      (15 / 2 : ℝ) * s ^ 4) * x ^ 3 +
    ((1 / 2 : ℝ) * s ^ 1 +
      (-11 / 4 : ℝ) * s ^ 3 +
      (9 / 4 : ℝ) * s ^ 5) * x ^ 2

private lemma hasDerivAt_delCorrAnti (s x : ℝ) :
    HasDerivAt (delCorrAnti s) (delPoly x * delPoly (x + s)) x := by
  unfold delCorrAnti
  refine (((((((((((hasDerivAt_succ_pow' _ 10 x).add
    (hasDerivAt_succ_pow' _ 9 x)).add
    (hasDerivAt_succ_pow' _ 8 x)).add
    (hasDerivAt_succ_pow' _ 7 x)).add
    (hasDerivAt_succ_pow' _ 6 x)).add
    (hasDerivAt_succ_pow' _ 5 x)).add
    (hasDerivAt_succ_pow' _ 4 x)).add
    (hasDerivAt_succ_pow' _ 3 x)).add
    (hasDerivAt_succ_pow' _ 2 x)).add
    (hasDerivAt_succ_pow' _ 1 x))).congr_deriv ?_
  unfold delPoly
  ring

/-- **Exact autocorrelation**: `A(t) = c₂ C(t/c₂)` for `0 ≤ t ≤ 2c₂`. -/
theorem autocorr_delWitness {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 2 * c₂) :
    autocorr delWitness t = c₂ * delCorr (t / c₂) := by
  change (∫ x, delWitness x * delWitness (x + t)) = c₂ * delCorr (t / c₂)
  set s : ℝ := t / c₂ with hs_def
  have hc : (c₂ : ℝ) ≠ 0 := by norm_num
  have he : (fun x => delWitness x * delWitness (x + t)) =
      (Icc (-c₂) (c₂ - t)).indicator (fun x => delPoly (x / c₂) * delPoly (x / c₂ + s)) := by
    funext x
    by_cases hx : x ∈ Icc (-c₂) (c₂ - t)
    · rw [indicator_of_mem hx, delWitness_inside hx.1 (by linarith [hx.2]),
        delWitness_inside (by linarith [hx.1]) (by linarith [hx.2]),
        show (x + t) / c₂ = x / c₂ + s by rw [hs_def, add_div]]
    · rw [indicator_of_notMem hx]
      by_cases hl : x < -c₂
      · rw [delWitness_eq_zero_of_far (by rw [abs_of_neg (by linarith)]; linarith), zero_mul]
      · have hr : c₂ < x + t := by
          have := not_le.mp (fun h => hx ⟨not_lt.mp hl, h⟩)
          linarith
        rw [delWitness_eq_zero_of_far (x := x + t)
          (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]
  have hle : -c₂ ≤ c₂ - t := by linarith
  rw [he, MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_scaled_del (G := delCorrAnti s)
        (G' := fun u => delPoly u * delPoly (u + s))
        (hasDerivAt_delCorrAnti s (x / c₂)))
      ((by unfold delPoly; fun_prop : Continuous fun x : ℝ =>
        delPoly (x / c₂) * delPoly (x / c₂ + s)).intervalIntegrable _ _)]
  have he1 : (c₂ - t) / c₂ = 1 - s := by rw [sub_div, div_self hc, ← hs_def]
  have he2 : (-c₂) / c₂ = -1 := by rw [neg_div, div_self hc]
  rw [he1, he2]
  unfold delCorrAnti delCorr
  ring

private lemma autocorr_delWitness_zero : autocorr delWitness 0 = c₂ * (188 / 1155 : ℝ) := by
  rw [autocorr_delWitness le_rfl (by norm_num)]
  unfold delCorr; norm_num

private lemma autocorr_delWitness_tail {t : ℝ} (ht : 2 * c₂ < t) : autocorr delWitness t = 0 :=
  autocorr_eq_zero_of_far (fun _ hx => delWitness_eq_zero_of_far hx.le)
    (by rw [abs_of_pos (lt_trans (by norm_num : (0 : ℝ) < 2 * c₂) ht)]; exact ht)

/-! ### 3. The Lévy energy: quartic majorant on `(0, 2c₂]` and exponential tail -/

private def delLevyReg (s : ℝ) : ℝ :=
  (1 / 2 : ℝ) - (c₂ / 24) * s - (c₂ ^ 2 / 16) * s ^ 2 +
    (c₂ ^ 3 / 576) * s ^ 3 + (c₂ ^ 4 / 128) * s ^ 4

/-- `(C(0) − C(s))/s`. -/
private def delDivS (s : ℝ) : ℝ :=
  (127 / 35 : ℝ) * s ^ 1 +
    (-49 / 6 : ℝ) * s ^ 2 +
    (39 / 7 : ℝ) * s ^ 3 +
    (-23 / 40 : ℝ) * s ^ 4 +
    (-241 / 560 : ℝ) * s ^ 6 +
    (11 / 112 : ℝ) * s ^ 8 +
    (-9 / 1232 : ℝ) * s ^ 10

private def delMajorant (s : ℝ) : ℝ :=
  delDivS s + c₂ * s * delDivS s * delLevyReg s

private def delMajAnti (s : ℝ) : ℝ :=
  (127 / 70 : ℝ) * s ^ 2 +
    (-1486781 / 630000 : ℝ) * s ^ 3 +
    (859954091 / 1120000000 : ℝ) * s ^ 4 +
    (5881648098743 / 25200000000000 : ℝ) * s ^ 5 +
    (-2923097622274673 / 120960000000000000 : ℝ) * s ^ 6 +
    (-60025062373859831429 / 846720000000000000000 : ℝ) * s ^ 7 +
    (-671156079884176657 / 43008000000000000000 : ℝ) * s ^ 8 +
    (869913351328764599 / 72576000000000000000 : ℝ) * s ^ 9 +
    (1249009235055117161 / 358400000000000000000 : ℝ) * s ^ 10 +
    (-31471075375800251 / 39029760000000000000 : ℝ) * s ^ 11 +
    (-989923711928116783 / 3153920000000000000000 : ℝ) * s ^ 12 +
    (93078333069721 / 9225216000000000000 : ℝ) * s ^ 13 +
    (24805182452762879 / 2207744000000000000000 : ℝ) * s ^ 14 +
    (-128738157601 / 1182720000000000000 : ℝ) * s ^ 15 +
    (-694027407626991 / 2523136000000000000000 : ℝ) * s ^ 16

private lemma hasDerivAt_delMajAnti (s : ℝ) : HasDerivAt delMajAnti (delMajorant s) s := by
  unfold delMajAnti
  refine ((((((((((((((((hasDerivAt_succ_pow' _ 1 s).add
    (hasDerivAt_succ_pow' _ 2 s)).add
    (hasDerivAt_succ_pow' _ 3 s)).add
    (hasDerivAt_succ_pow' _ 4 s)).add
    (hasDerivAt_succ_pow' _ 5 s)).add
    (hasDerivAt_succ_pow' _ 6 s)).add
    (hasDerivAt_succ_pow' _ 7 s)).add
    (hasDerivAt_succ_pow' _ 8 s)).add
    (hasDerivAt_succ_pow' _ 9 s)).add
    (hasDerivAt_succ_pow' _ 10 s)).add
    (hasDerivAt_succ_pow' _ 11 s)).add
    (hasDerivAt_succ_pow' _ 12 s)).add
    (hasDerivAt_succ_pow' _ 13 s)).add
    (hasDerivAt_succ_pow' _ 14 s)).add
    (hasDerivAt_succ_pow' _ 15 s))).congr_deriv ?_
  unfold delMajorant delDivS delLevyReg
  ring

/-- The tail value `T(c₂) = 2e^{−c₂} + (2/5) e^{−5c₂}/(1 − e^{−4c₂})` of `Ω(2c₂)`. -/
private def delTail : ℝ :=
  2 * Real.exp (-(1 / 2) * (2 * c₂)) +
    (2 / 5) * Real.exp (-(5 / 2) * (2 * c₂)) / (1 - Real.exp (-2 * (2 * c₂)))

/-- **Lévy bound**: `𝒥(F) ≤ c₂ ∫₀² (quartic majorant) + 2A(0) T(c₂)`, and the jump integrand is
integrable. -/
private lemma delWitness_levy_le :
    IntegrableOn (fun t => (autocorr delWitness 0 - autocorr delWitness t) * archLevySinhWeight t)
        (Ioi (0 : ℝ)) ∧
      biScaleLevyEnergy delWitness ≤ c₂ * delMajAnti 2 + 2 * autocorr delWitness 0 * delTail := by
  have hL : (0 : ℝ) < 2 * c₂ := by norm_num
  have hpt : ∀ t ∈ Ioc (0 : ℝ) (2 * c₂),
      0 ≤ (autocorr delWitness 0 - autocorr delWitness t) * archLevySinhWeight t ∧
        (autocorr delWitness 0 - autocorr delWitness t) * archLevySinhWeight t ≤
          delMajorant (t / c₂) := fun t ht => by
    have hd_nn := deficit_nonneg' compact_delWitness continuous_delWitness t
    have hw_eq : archLevySinhWeight t = 2 * archLevyDensity t := by
      rw [archLevySinhWeight, exp_half_div_sinh_eq ht.1]
    refine ⟨mul_nonneg hd_nn (archLevySinhWeight_pos ht.1).le, ?_⟩
    rw [hw_eq]
    have hlev := mul_le_mul_of_nonneg_left (two_mul_archLevyDensity_le_quartic ht.1) hd_nn
    rw [autocorr_delWitness_zero, autocorr_delWitness ht.1.le ht.2] at hlev ⊢
    refine hlev.trans_eq ?_
    unfold delMajorant delDivS delLevyReg delCorr
    field_simp [ht.1.ne']
    ring
  have hmaj_cont : Continuous fun t : ℝ => delMajorant (t / c₂) := by
    unfold delMajorant delDivS delLevyReg; fun_prop
  have hmaj_int : IntegrableOn (fun t : ℝ => delMajorant (t / c₂)) (Ioc (0 : ℝ) (2 * c₂)) :=
    hmaj_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmeas : AEStronglyMeasurable
      (fun t => (autocorr delWitness 0 - autocorr delWitness t) * archLevySinhWeight t)
      (volume.restrict (Ioc (0 : ℝ) (2 * c₂))) := by
    have hc : Continuous fun t : ℝ => c₂ * (188 / 1155 : ℝ) - c₂ * delCorr (t / c₂) := by
      unfold delCorr; fun_prop
    have hw := continuousOn_archLevySinhWeight_pos_halfLine.mono
      (show Ioc (0 : ℝ) (2 * c₂) ⊆ Ioi 0 from fun _ ht => ht.1)
    refine ((hc.continuousOn.mul hw).aestronglyMeasurable measurableSet_Ioc).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [Pi.mul_apply, autocorr_delWitness_zero, autocorr_delWitness ht.1.le ht.2]
  have hint_in : IntegrableOn
      (fun t => (autocorr delWitness 0 - autocorr delWitness t) * archLevySinhWeight t)
      (Ioc (0 : ℝ) (2 * c₂)) := by
    refine hmaj_int.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hpt t ht).1]
    exact (hpt t ht).2
  have htail_eq : ∀ t ∈ Ioi (2 * c₂),
      (autocorr delWitness 0 - autocorr delWitness t) * archLevySinhWeight t =
        (autocorr delWitness 0 * 2) * archLevyDensity t := fun t ht => by
    have ht0 : 0 < t := lt_trans hL ht
    rw [autocorr_delWitness_tail ht, sub_zero, archLevySinhWeight, exp_half_div_sinh_eq ht0]
    ring
  have hint_tail : IntegrableOn
      (fun t => (autocorr delWitness 0 - autocorr delWitness t) * archLevySinhWeight t)
      (Ioi (2 * c₂)) := by
    refine ((WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hL).const_mul
      (autocorr delWitness 0 * 2)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (htail_eq t ht).symm
  have hint_all : IntegrableOn
      (fun t => (autocorr delWitness 0 - autocorr delWitness t) * archLevySinhWeight t)
      (Ioi (0 : ℝ)) := by
    have h := hint_in.union hint_tail
    rwa [Ioc_union_Ioi_eq_Ioi hL.le] at h
  refine ⟨hint_all, ?_⟩
  have hin_le : (∫ t in Ioc (0 : ℝ) (2 * c₂),
      (autocorr delWitness 0 - autocorr delWitness t) * archLevySinhWeight t) ≤
        c₂ * delMajAnti 2 := by
    have hm := setIntegral_mono_on hint_in hmaj_int measurableSet_Ioc fun t ht => (hpt t ht).2
    have hval : (∫ t in Ioc (0 : ℝ) (2 * c₂), delMajorant (t / c₂)) = c₂ * delMajAnti 2 := by
      rw [← intervalIntegral.integral_of_le hL.le,
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => hasDerivAt_scaled_del (G := delMajAnti) (G' := delMajorant)
            (hasDerivAt_delMajAnti (t / c₂)))
          (hmaj_cont.intervalIntegrable _ _)]
      have h2 : (2 * c₂) / c₂ = 2 := by norm_num
      rw [h2, zero_div]
      unfold delMajAnti; ring
    exact hm.trans_eq hval
  have hA0 : 0 ≤ autocorr delWitness 0 := by rw [autocorr_delWitness_zero]; norm_num
  have htail_le : (∫ t in Ioi (2 * c₂),
      (autocorr delWitness 0 - autocorr delWitness t) * archLevySinhWeight t) ≤
        2 * autocorr delWitness 0 * delTail := by
    rw [setIntegral_congr_fun measurableSet_Ioi htail_eq, MeasureTheory.integral_const_mul]
    have h := levyTail_le_exp hL
    have h2 : 0 ≤ autocorr delWitness 0 * 2 := by linarith
    calc autocorr delWitness 0 * 2 * ∫ t in Ioi (2 * c₂), archLevyDensity t
        ≤ autocorr delWitness 0 * 2 * delTail := mul_le_mul_of_nonneg_left h h2
      _ = 2 * autocorr delWitness 0 * delTail := by ring
  unfold biScaleLevyEnergy
  rw [← Ioc_union_Ioi_eq_Ioi hL.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_in hint_tail]
  linarith

/-! ### 4. Weil's form of the odd witness in autocorrelation form -/

/-- `W(F) + 2S(F)² = Γ A(0) + 𝒥(F) − 2w₂ A(log 2) − 2w₃ A(log 3)` for the odd witness (support length
`2c₂ < log 4`, so only the primes `2` and `3` meet it). -/
private lemma delWitness_weilQuad_add_two_oddPole_sq_eq :
    weilQuad delWitness + 2 * oddPoleMoment delWitness ^ 2 =
      EF.gammaBracket 0 * autocorr delWitness 0 + biScaleLevyEnergy delWitness -
        2 * primeJumpWeight 2 * autocorr delWitness (Real.log 2) -
        2 * primeJumpWeight 3 * autocorr delWitness (Real.log 3) := by
  have hfull := re_weilFullFunctional_eq_of_compact_finite_jump ccDel delWitness_levy_le.1
  change weilQuad delWitness = EF.gammaBracket 0 * autocorr delWitness 0 +
    biScaleLevyEnergy delWitness - 2 * fullPairing (autocorr delWitness) at hfull
  have hprime : (∑' n : ℕ, primeTerm (autocorr delWitness) n) =
      primeJumpWeight 2 * autocorr delWitness (Real.log 2) +
        primeJumpWeight 3 * autocorr delWitness (Real.log 3) := by
    rw [tsum_eq_sum (s := ({2, 3} : Finset ℕ)) (fun n hn => ?_),
      Finset.sum_pair (by decide : (2 : ℕ) ≠ 3)]
    · unfold primeTerm SignedPrimePolar.primeWeight primeJumpWeight
      rw [if_pos (by norm_num : 2 ≤ (2 : ℕ)), if_pos (by norm_num : 2 ≤ (3 : ℕ))]
      norm_num only [Nat.cast_ofNat]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      by_cases h2 : 2 ≤ n
      · have h4 : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
        have hlog4 : 2 * c₂ < Real.log 4 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
          norm_num
          linarith [Real.log_two_gt_d9]
        have hlog : 2 * c₂ < |Real.log n| := by
          have hln : 2 * c₂ < Real.log n :=
            lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) h4)
          rw [abs_of_pos (lt_trans (by norm_num : (0 : ℝ) < 2 * c₂) hln)]
          exact hln
        have hz : autocorr delWitness (Real.log n) = 0 :=
          autocorr_eq_zero_of_far (fun _ hx => delWitness_eq_zero_of_far hx.le) hlog
        simp only [primeTerm, if_pos h2, hz, mul_zero]
      · simp only [primeTerm, if_neg h2]
  have hpolar : 2 * (∫ t in Ici (0 : ℝ), polarDensity t * autocorr delWitness t) =
      -(2 * oddPoleMoment delWitness ^ 2) := by
    have hm := integral_polar_autocorr_eq_moments ccDel
    have hp := pole_eq_pairings delWitness continuous_delWitness compact_delWitness
    have hc := coshPairing_eq_zero_of_odd delWitness_odd
    have he1 : (∫ u, Real.exp (u / 2) * delWitness u) = ∫ u, delWitness u * Real.exp (u / 2) :=
      integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
    have he2 : (∫ u, Real.exp (-(u / 2)) * delWitness u) =
        ∫ u, delWitness u * Real.exp (-u / 2) :=
      integral_congr_ae (Eventually.of_forall fun u => by
        show Real.exp (-(u / 2)) * delWitness u = delWitness u * Real.exp (-u / 2)
        rw [neg_div]; ring)
    change (∫ t in Ici (0 : ℝ), polarDensity t * autocorr delWitness t) =
      (∫ u, Real.exp (u / 2) * delWitness u) * (∫ u, Real.exp (-(u / 2)) * delWitness u) at hm
    rw [he1, he2] at hm
    have hsp : sinhPairing delWitness = 2 * oddPoleMoment delWitness := by
      unfold sinhPairing oddPoleMoment
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun _ => by ring)
    rw [hm]
    rw [hc, hsp] at hp
    nlinarith [hp]
  rw [fullPairing, hprime] at hfull
  linarith

/-! ### 5. The pole moment -/

/-- `P(x/c₂) · (x/2 + (x/2)³/6 + (x/2)⁵/120)` expanded. -/
private def delTPoly (x : ℝ) : ℝ :=
  (500 / 599 : ℝ) * x ^ 2 +
    (-16455149875 / 1289530794 : ℝ) * x ^ 4 +
    (212056407453940025 / 7402959014687904 : ℝ) * x ^ 6 +
    (279708276953125 / 231342469208997 : ℝ) * x ^ 8 +
    (1171875000000 / 77114156402999 : ℝ) * x ^ 10

private def delTAnti (x : ℝ) : ℝ :=
  (500 / 1797 : ℝ) * x ^ 3 +
    (-3291029975 / 1289530794 : ℝ) * x ^ 5 +
    (212056407453940025 / 51820713102815328 : ℝ) * x ^ 7 +
    (279708276953125 / 2082082222880973 : ℝ) * x ^ 9 +
    (1171875000000 / 848255720432989 : ℝ) * x ^ 11

private lemma hasDerivAt_delTAnti (x : ℝ) : HasDerivAt delTAnti (delTPoly x) x := by
  unfold delTAnti
  refine ((((((hasDerivAt_succ_pow' _ 2 x).add
    (hasDerivAt_succ_pow' _ 4 x)).add
    (hasDerivAt_succ_pow' _ 6 x)).add
    (hasDerivAt_succ_pow' _ 8 x)).add
    (hasDerivAt_succ_pow' _ 10 x))).congr_deriv ?_
  unfold delTPoly; ring

private lemma delTPoly_eq (x : ℝ) :
    delPoly (x / c₂) * (x / 2 + (x / 2) ^ 3 / 6 + (x / 2) ^ 5 / 120) = delTPoly x := by
  unfold delPoly delTPoly; ring

/-- `|P(u)| ≤ |u|` on `[−1, 1]`. -/
private lemma abs_delPoly_le {u : ℝ} (hu : |u| ≤ 1) : |delPoly u| ≤ |u| := by
  have ht1 : u ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg u) hu
  have ht0 : 0 ≤ u ^ 2 := sq_nonneg u
  have hq : |1 - (11 / 2) * u ^ 2 + (9 / 2) * (u ^ 2) ^ 2| ≤ 1 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (u ^ 2 - 11 / 18)]
    · nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have he : delPoly u = u * (1 - (11 / 2) * u ^ 2 + (9 / 2) * (u ^ 2) ^ 2) := by
    unfold delPoly; ring
  rw [he, abs_mul]
  calc |u| * |1 - (11 / 2) * u ^ 2 + (9 / 2) * (u ^ 2) ^ 2| ≤ |u| * 1 :=
        mul_le_mul_of_nonneg_left hq (abs_nonneg u)
    _ = |u| := mul_one _

/-- **Pole moment**: `S(F) = ∫ F sinh(x/2)` is at most its Taylor value plus the remainder. -/
private lemma delWitness_oddPoleMoment_le :
    oddPoleMoment delWitness ≤
      (delTAnti c₂ - delTAnti (-c₂)) + (8 / 35280) / (128 * c₂) * (2 * c₂ ^ 9 / 9) := by
  have hc : (0 : ℝ) < c₂ := by norm_num
  have he : (fun x => delWitness x * Real.sinh (x / 2)) =
      (Icc (-c₂) c₂).indicator (fun x => delPoly (x / c₂) * Real.sinh (x / 2)) := by
    funext x
    by_cases hx : x ∈ Icc (-c₂) c₂
    · rw [indicator_of_mem hx, delWitness_inside hx.1 hx.2]
    · rw [indicator_of_notMem hx,
        delWitness_eq_zero_of_far (le_of_lt (not_le.mp fun h => hx (abs_le.mp h))), zero_mul]
  unfold oddPoleMoment
  rw [he, MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -c₂ ≤ c₂)]
  -- pointwise majorant on `[−c₂, c₂]`
  set g : ℝ → ℝ := fun x => delTPoly x + (8 / 35280) / (128 * c₂) * x ^ 8
  have hpt : ∀ x ∈ Icc (-c₂) c₂, delPoly (x / c₂) * Real.sinh (x / 2) ≤ g x := by
    intro x hx
    have hxc : |x / c₂| ≤ 1 := by
      rw [abs_div, abs_of_pos hc, div_le_one hc]; exact abs_le.mpr hx
    have hz : |x / 2| ≤ 1 := by
      have h1 := abs_le.mpr hx
      have h2 : c₂ ≤ 2 := by norm_num
      rw [abs_div, abs_two]; linarith
    have hs := abs_sinh_sub_quintic_le hz
    have hp := abs_delPoly_le hxc
    have hsplit : delPoly (x / c₂) * Real.sinh (x / 2) =
        delTPoly x + delPoly (x / c₂) *
          (Real.sinh (x / 2) - (x / 2 + (x / 2) ^ 3 / 6 + (x / 2) ^ 5 / 120)) := by
      rw [← delTPoly_eq]; ring
    have hrem : delPoly (x / c₂) *
        (Real.sinh (x / 2) - (x / 2 + (x / 2) ^ 3 / 6 + (x / 2) ^ 5 / 120)) ≤
          (8 / 35280) / (128 * c₂) * x ^ 8 := by
      have hab := le_abs_self (delPoly (x / c₂) *
        (Real.sinh (x / 2) - (x / 2 + (x / 2) ^ 3 / 6 + (x / 2) ^ 5 / 120)))
      rw [abs_mul] at hab
      have hprod := mul_le_mul hp hs (abs_nonneg _) (abs_nonneg _)
      have hpow : |x / c₂| * (|x / 2| ^ 7 * (8 / 35280)) = (8 / 35280) / (128 * c₂) * x ^ 8 := by
        rw [abs_div x c₂, abs_div x 2, abs_of_pos hc, abs_two, div_pow]
        have h8 : |x| ^ 8 = x ^ 8 := by
          rw [pow_abs]; exact abs_of_nonneg (by positivity)
        rw [← h8]
        field_simp
        ring
      linarith
    show _ ≤ delTPoly x + _
    linarith
  have hcont : Continuous fun x => delPoly (x / c₂) * Real.sinh (x / 2) := by
    unfold delPoly; fun_prop
  have hgc : Continuous g := by simp only [g]; unfold delTPoly; fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : -c₂ ≤ c₂)
    (hcont.intervalIntegrable _ _) (hgc.intervalIntegrable _ _) hpt
  have hg_int : (∫ x in (-c₂)..c₂, g x) =
      (delTAnti c₂ - delTAnti (-c₂)) + (8 / 35280) / (128 * c₂) * (2 * c₂ ^ 9 / 9) := by
    simp only [g]
    rw [intervalIntegral.integral_add
        ((by unfold delTPoly; fun_prop : Continuous delTPoly).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun x : ℝ =>
          (8 / 35280) / (128 * c₂) * x ^ 8).intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_delTAnti x)
        ((by unfold delTPoly; fun_prop : Continuous delTPoly).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_pow]
    ring
  linarith

/-- `S(F) ≤ −0.04488`, so `S(F)² ≥ 0.04488²`. -/
private lemma delWitness_oddPoleMoment_sq_ge :
    (4488 / 100000 : ℝ) ^ 2 ≤ oddPoleMoment delWitness ^ 2 := by
  have h := delWitness_oddPoleMoment_le
  have hv : (delTAnti c₂ - delTAnti (-c₂)) + (8 / 35280) / (128 * c₂) * (2 * c₂ ^ 9 / 9) ≤
      -(4488 / 100000 : ℝ) := by
    unfold delTAnti; norm_num
  nlinarith

/-! ### 6. The prime-2 correlation -/

private def delCorrDeriv (u : ℝ) : ℝ :=
  (-254 / 35 : ℝ) * u ^ 1 +
    (49 / 2 : ℝ) * u ^ 2 +
    (-156 / 7 : ℝ) * u ^ 3 +
    (23 / 8 : ℝ) * u ^ 4 +
    (241 / 80 : ℝ) * u ^ 6 +
    (-99 / 112 : ℝ) * u ^ 8 +
    (9 / 112 : ℝ) * u ^ 10

private lemma hasDerivAt_delCorr (u : ℝ) : HasDerivAt delCorr (delCorrDeriv u) u := by
  unfold delCorr
  refine ((((((((hasDerivAt_const u (188 / 1155 : ℝ)).add
    (hasDerivAt_succ_pow' (-127 / 35) 1 u)).add
    (hasDerivAt_succ_pow' (49 / 6) 2 u)).add
    (hasDerivAt_succ_pow' (-39 / 7) 3 u)).add
    (hasDerivAt_succ_pow' (23 / 40) 4 u)).add
    (hasDerivAt_succ_pow' (241 / 560) 6 u)).add
    (hasDerivAt_succ_pow' (-11 / 112) 8 u)).add
    (hasDerivAt_succ_pow' (9 / 1232) 10 u)) |>.congr_deriv ?_
  unfold delCorrDeriv; ring

/-- `A(log 2) ≥ 0.0168`. -/
private lemma delWitness_autocorr_log_two_ge :
    (168 / 10000 : ℝ) ≤ autocorr delWitness (Real.log 2) := by
  have hl2 := Real.log_two_gt_d9
  have hu2 := Real.log_two_lt_d9
  rw [autocorr_delWitness (by linarith) (by norm_num; linarith)]
  set s := Real.log 2 / c₂
  have hc : (0 : ℝ) < c₂ := by norm_num
  have hs_in : s ∈ Icc (23 / 20 : ℝ) (117 / 100) := by
    simp only [s, mem_Icc]
    constructor
    · rw [le_div_iff₀ hc]; norm_num; linarith
    · rw [div_le_iff₀ hc]; norm_num; linarith
  have hs_ball : |s - (11571739 / 10000000 : ℝ)| ≤ 1 / 10000000 := by
    rw [abs_le]; simp only [s]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hc]; norm_num; linarith
    · rw [sub_le_iff_le_add, div_le_iff₀ hc]; norm_num; linarith
  have hb : ∀ u ∈ Icc (23 / 20 : ℝ) (117 / 100), |delCorrDeriv u| ≤ 95 := fun u hu => by
    have ha : (0 : ℝ) ≤ 23 / 20 := by norm_num
    have h0 : 0 ≤ u := by linarith [hu.1]
    have p2l := pow_le_pow_left₀ ha hu.1 2
    have p2u := pow_le_pow_left₀ h0 hu.2 2
    have p3l := pow_le_pow_left₀ ha hu.1 3
    have p3u := pow_le_pow_left₀ h0 hu.2 3
    have p4l := pow_le_pow_left₀ ha hu.1 4
    have p4u := pow_le_pow_left₀ h0 hu.2 4
    have p6l := pow_le_pow_left₀ ha hu.1 6
    have p6u := pow_le_pow_left₀ h0 hu.2 6
    have p8l := pow_le_pow_left₀ ha hu.1 8
    have p8u := pow_le_pow_left₀ h0 hu.2 8
    have p10l := pow_le_pow_left₀ ha hu.1 10
    have p10u := pow_le_pow_left₀ h0 hu.2 10
    rw [abs_le]; unfold delCorrDeriv
    norm_num at p2l p2u p3l p3u p4l p4u p6l p6u p8l p8u p10l p10u
    exact ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
  have hcd : Continuous delCorrDeriv := by unfold delCorrDeriv; fun_prop
  have hmv := poly_ge_of_deriv_bound' (s₀ := 11571739 / 10000000) (s := s) (by norm_num)
    (by norm_num) hs_in.1 hs_in.2 hcd hasDerivAt_delCorr hb
  have hv : (168 / 10000 : ℝ) / c₂ ≤ delCorr (11571739 / 10000000) - 95 * (1 / 10000000) := by
    unfold delCorr; norm_num
  have hM : 95 * |s - 11571739 / 10000000| ≤ 95 * (1 / 10000000) :=
    mul_le_mul_of_nonneg_left hs_ball (by norm_num)
  have : (168 / 10000 : ℝ) / c₂ ≤ delCorr s := by linarith
  rw [div_le_iff₀ hc] at this
  linarith

/-! ### 7. The exponential tail -/

/-- `e^{−c₂} ≤ 1/1.8202`, `e^{−5c₂} ≤ 1/19.98`, `e^{−4c₂} ≤ 1/10.97`. -/
private lemma del_exp_neg_bounds :
    Real.exp (-(1 / 2) * (2 * c₂)) ≤ 1 / (18202 / 10000) ∧
      Real.exp (-(5 / 2) * (2 * c₂)) ≤ 1 / (1998 / 100) ∧
      Real.exp (-2 * (2 * c₂)) ≤ 1 / (1097 / 100) := by
  have key : ∀ (a S : ℝ) (n : ℕ), 0 ≤ a → 0 < S →
      S ≤ ∑ i ∈ Finset.range n, a ^ i / (i.factorial : ℝ) → Real.exp (-a) ≤ 1 / S := by
    intro a S n ha hS hle
    have h := (hle.trans (Real.sum_le_exp_of_nonneg ha n))
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le hS h
  refine ⟨?_, ?_, ?_⟩
  · rw [show -(1 / 2) * (2 * c₂) = -(599 / 1000 : ℝ) by norm_num]
    exact key _ _ 8 (by norm_num) (by norm_num)
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  · rw [show -(5 / 2) * (2 * c₂) = -(2995 / 1000 : ℝ) by norm_num]
    exact key _ _ 16 (by norm_num) (by norm_num)
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  · rw [show -2 * (2 * c₂) = -(2396 / 1000 : ℝ) by norm_num]
    exact key _ _ 14 (by norm_num) (by norm_num)
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)

private lemma delTail_le :
    delTail ≤ 2 * (1 / (18202 / 10000)) + (2 / 5) * (1 / (1998 / 100)) / (1 - 1 / (1097 / 100)) := by
  obtain ⟨h1, h5, h2⟩ := del_exp_neg_bounds
  unfold delTail
  have hq : (1 - 1 / (1097 / 100) : ℝ) ≤ 1 - Real.exp (-2 * (2 * c₂)) := by linarith
  have hqpos : (0 : ℝ) < 1 - 1 / (1097 / 100) := by norm_num
  have hd : (2 / 5) * Real.exp (-(5 / 2) * (2 * c₂)) / (1 - Real.exp (-2 * (2 * c₂))) ≤
      (2 / 5) * (1 / (1998 / 100)) / (1 - 1 / (1097 / 100)) := by
    have hpos := Real.exp_pos (-(5 / 2) * (2 * c₂))
    calc (2 / 5) * Real.exp (-(5 / 2) * (2 * c₂)) / (1 - Real.exp (-2 * (2 * c₂)))
        ≤ (2 / 5) * Real.exp (-(5 / 2) * (2 * c₂)) / (1 - 1 / (1097 / 100)) :=
          div_le_div_of_nonneg_left (by positivity) hqpos hq
      _ ≤ (2 / 5) * (1 / (1998 / 100)) / (1 - 1 / (1097 / 100)) := by
          apply div_le_div_of_nonneg_right _ hqpos.le; linarith
  linarith

/-! ### 8. The deleted form of the witness -/

/-- **The deleted form of the witness**: `W(F) + 2w₃ A(log 3) < −1/200`. -/
private lemma del_gap :
    weilQuad delWitness + 2 * vonMangoldtAtom 3 * autocorr delWitness (Real.log 3) <
      -(1 / 200) := by
  have hid := delWitness_weilQuad_add_two_oddPole_sq_eq
  have hlevy := delWitness_levy_le.2
  have hA0 : autocorr delWitness 0 = 28153 / 288750 := by
    rw [autocorr_delWitness_zero]; norm_num
  have hΓ := gammaBracket_zero_le
  have htail := delTail_le
  have hS := delWitness_oddPoleMoment_sq_ge
  have hA2 := delWitness_autocorr_log_two_ge
  have hw2 := primeJumpWeight_bounds.1
  rw [vonMangoldtAtom_three_eq]
  have hMaj : c₂ * delMajAnti 2 ≤ (31702 / 100000 : ℝ) := by unfold delMajAnti; norm_num
  have hJ : biScaleLevyEnergy delWitness ≤ 31702 / 100000 + 2 * (28153 / 288750) *
      (2 * (1 / (18202 / 10000)) + (2 / 5) * (1 / (1998 / 100)) / (1 - 1 / (1097 / 100))) := by
    have h := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 2 * (28153 / 288750))
    rw [hA0] at hlevy
    linarith
  have hΓA : EF.gammaBracket 0 * autocorr delWitness 0 ≤ -(5370 / 1000) * (28153 / 288750) := by
    rw [hA0]; exact mul_le_mul_of_nonneg_right hΓ (by norm_num)
  have hw2A : 2 * ((693147 / 1000000 : ℝ) / (141422 / 100000) * (168 / 10000)) ≤
      2 * primeJumpWeight 2 * autocorr delWitness (Real.log 2) := by
    have h := mul_le_mul hw2 hA2 (by norm_num) (primeJumpWeight_nonneg 2)
    have e : 2 * primeJumpWeight 2 * autocorr delWitness (Real.log 2) =
        2 * (primeJumpWeight 2 * autocorr delWitness (Real.log 2)) := by ring
    rw [e]; linarith
  norm_num at hJ hΓA hw2A hS
  linarith

/-! ### 9. Without the prime 3 the odd window fails -/

/-- **Deleting the prime 3 breaks the odd window of half-width `3/5`.** There is an odd `C²` test `F`
supported in `[−3/5, 3/5]` with `W(F) + 2w₃ ∫ F(t) F(t + log 3) dt < 0`. -/
theorem exists_odd_test_without_prime_three_neg :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧ (∀ x, F (-x) = -F x) ∧
      (∀ x, 3 / 5 < |x| → F x = 0) ∧
      weilQuad F + 2 * vonMangoldtAtom 3 * autocorr F (Real.log 3) < 0 := by
  have hf2 : MemLp delWitness 2 volume :=
    continuous_delWitness.memLp_of_hasCompactSupport compact_delWitness
  have hQ : Tendsto (fun k : ℕ => weilQuad (CHMDDoobGraph.smooth delWitness k)) atTop
      (𝓝 (weilQuad delWitness)) :=
    re_weilFullFunctional_smooth_tendsto ccDel delWitness_levy_le.1
  have hA : Tendsto (fun k : ℕ => autocorr (CHMDDoobGraph.smooth delWitness k) (Real.log 3))
      atTop (𝓝 (autocorr delWitness (Real.log 3))) :=
    autocorr_smooth_tendsto continuous_delWitness abs_delWitness_le
      (fun x hx => delWitness_eq_zero_of_far hx.le) (Real.log 3)
  have hlim := hQ.add (hA.const_mul (2 * vonMangoldtAtom 3))
  have hgap := del_gap
  have hev := hlim.eventually (Iio_mem_nhds (show
    weilQuad delWitness + 2 * vonMangoldtAtom 3 * autocorr delWitness (Real.log 3) < 0
    by linarith))
  obtain ⟨k, hk, hneg⟩ := ((eventually_ge_atTop 249).and hev).exists
  refine ⟨CHMDDoobGraph.smooth delWitness k,
    (CHMDDoobGraph.smooth_contDiff hf2 k).of_le (by simp),
    CHMDDoobGraph.smooth_compact compact_delWitness k, smooth_odd' delWitness_odd k,
    fun x hx => smooth_eq_zero_of_narrow' (R := c₂) (fun y hy => delWitness_eq_zero_of_far hy) hk
      (by rw [show c₂ + 1 / 1000 = 3 / 5 by norm_num]; exact hx), ?_⟩
  have h : weilQuad (CHMDDoobGraph.smooth delWitness k) +
      2 * vonMangoldtAtom 3 * autocorr (CHMDDoobGraph.smooth delWitness k) (Real.log 3) < 0 :=
    hneg
  exact h

/-- **No window of half-width `c ≥ 3/5` is odd-positive without the prime 3**: the deleted form
`W(F) + 2w₃ ∫ F(t) F(t + log 3) dt` is not nonnegative on the odd `C²` tests supported in
`[−c, c]`. -/
theorem not_nonneg_without_prime_three {c : ℝ} (hc : 3 / 5 ≤ c) :
    ¬ ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) →
        (∀ x, c < |x| → F x = 0) →
        0 ≤ weilQuad F + 2 * vonMangoldtAtom 3 * autocorr F (Real.log 3) := by
  intro h
  obtain ⟨F, hF, hFc, hFo, hFs, hneg⟩ := exists_odd_test_without_prime_three_neg
  have := h F hF hFc hFo (fun x hx => hFs x (by linarith))
  linarith

end GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry

end

#print axioms GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry.not_nonneg_without_prime_three
