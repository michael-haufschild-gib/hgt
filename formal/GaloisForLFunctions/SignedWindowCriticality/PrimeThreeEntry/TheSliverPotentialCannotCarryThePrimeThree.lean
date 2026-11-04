import GaloisForLFunctions.SignedWindowCriticality.BelowLogFour.TwoProfileRefutationBelowLogFour

/-!
# The sliver potential cannot carry the prime 3

On a window `[−c, c]` with `log 3 < 2c < log 4` the prime `3` enters the odd sector of Weil's form
through the kick `−2w₃ ∫ F(t) F(t + log 3) dt` (`w₃ = Λ(3)/√3`), which pairs the two collars
`[−c, c − log 3]` and `[log 3 − c, c]`. For odd `F` the kick is bounded by the collar mass,
`|∫ F(t) F(t + log 3) dt| ≤ ∫_{[log 3 − c, c]} F²` (`abs_autocorr_log_three_le_collarMass`), so the
cheapest certificate of the odd sector treats the prime `3` as a potential of height `2w₃` on its
collar (the **sliver-potential certificate**):

  `2w₃ ∫_{[log 3 − c, c]} F² ≤ W(F) + 2w₃ ∫ F(t) F(t + log 3) dt`  for every odd test `F`.

It would give `W(F) ≥ 0` on the odd sector. This module proves that it is false on every window of
half-width `c ≥ 287/500`, which contains the first windows `c ∈ (½ log 3, ½ log 3 + 1/40]` on which
the prime `3` acts and its own collar cannot pay it (`exists_prime_three_collar_unpaid`):
`exists_odd_test_sliverPotential_fails`, `not_sliverPotentialCertificate`. On these windows the
prime `3` has to enter through the sign of its reflection, not through its size.

The witness is the mollification of `F(x) = P(x/c₁)`, `c₁ = 573/1000`,
`P(u) = u(1 − u²)(1 − 5u²/2 − 29u⁴/4)`. For this odd source (support length `2c₁ < log 4`)
`W(F) + 2w₃ A(log 3) = Γ A(0) + 𝒥(F) − 2w₂ A(log 2) − 2 S(F)²` with the autocorrelation
`A(t) = c₁ C(t/c₁)` (exact polynomial `C`), the Lévy energy `𝒥` bounded by the quartic majorant of
the archimedean density on `(0, 2c₁]` and an exponential tail, the pole moment
`S(F) = ∫ F sinh(x/2)` bounded by its Taylor polynomial, and the exact collar mass; the certificate
gap is below `−1/100`.
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

/-! ### 1. The witness `P(x/c₁)` -/

/-- Half-width of the unmollified witness. -/
private abbrev c₁ : ℝ := 573 / 1000

/-- `P(u) = u(1 − u²)(1 − 5u²/2 − 29u⁴/4)` expanded. -/
def witnessPoly (u : ℝ) : ℝ := u - (7 / 2) * u ^ 3 - (19 / 4) * u ^ 5 + (29 / 4) * u ^ 7

/-- The compact unit witness `u (1 − u²)₊ (1 − 5u²/2 − 29u⁴/4)`. -/
def unitWitness (u : ℝ) : ℝ := u * max (1 - u ^ 2) 0 * (1 - (5 / 2) * u ^ 2 - (29 / 4) * u ^ 4)

/-- The scaled witness `F(x) = unitWitness (x/c₁)`, supported in `[−c₁, c₁]`. -/
def witness (x : ℝ) : ℝ := unitWitness (x / c₁)

private lemma unitWitness_inside {u : ℝ} (hl : -1 ≤ u) (hr : u ≤ 1) :
    unitWitness u = witnessPoly u := by
  unfold unitWitness witnessPoly
  rw [max_eq_left (by nlinarith)]
  ring

private lemma unitWitness_outside {u : ℝ} (hu : 1 ≤ |u|) : unitWitness u = 0 := by
  unfold unitWitness
  have hsq : 1 ≤ u ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one hu 2
    rwa [one_pow, sq_abs] at this
  rw [max_eq_right (by linarith), mul_zero, zero_mul]

lemma continuous_witness : Continuous witness := by
  unfold witness unitWitness; fun_prop

lemma witness_odd (x : ℝ) : witness (-x) = -witness x := by
  unfold witness unitWitness
  rw [neg_div, neg_sq]
  ring

lemma witness_eq_zero_of_far {x : ℝ} (hx : c₁ ≤ |x|) : witness x = 0 := by
  have hc : (0 : ℝ) < c₁ := by norm_num
  unfold witness
  apply unitWitness_outside
  rw [abs_div, abs_of_pos hc, one_le_div hc]
  exact hx

lemma compact_witness : HasCompactSupport witness :=
  HasCompactSupport.intro (isCompact_Icc (a := -c₁) (b := c₁)) fun _ hx =>
    witness_eq_zero_of_far (le_of_lt (not_le.mp fun h => hx (abs_le.mp h)))

private lemma witness_inside {x : ℝ} (hl : -c₁ ≤ x) (hr : x ≤ c₁) :
    witness x = witnessPoly (x / c₁) := by
  have hc : (0 : ℝ) < c₁ := by norm_num
  exact unitWitness_inside ((le_div_iff₀ hc).mpr (by linarith))
    ((div_le_iff₀ hc).mpr (by linarith))

private lemma abs_witness_le (x : ℝ) : |witness x| ≤ 43 / 4 := by
  by_cases hx : c₁ ≤ |x|
  · rw [witness_eq_zero_of_far hx, abs_zero]; norm_num
  · push Not at hx
    have hc : (0 : ℝ) < c₁ := by norm_num
    unfold witness unitWitness
    set u := x / c₁
    have hu : |u| < 1 := by
      rw [abs_div, abs_of_pos hc, div_lt_one hc]
      exact hx
    have hb := abs_lt.mp hu
    have hu2 : 0 ≤ 1 - u ^ 2 ∧ 1 - u ^ 2 ≤ 1 :=
      ⟨by nlinarith [hb.1, hb.2], by nlinarith [sq_nonneg u]⟩
    have hq : |1 - (5 / 2) * u ^ 2 - (29 / 4) * u ^ 4| ≤ 43 / 4 := by
      have h2 : u ^ 2 ≤ 1 := by nlinarith [hb.1, hb.2]
      have h4 : u ^ 4 ≤ 1 := by nlinarith [sq_nonneg u, h2]
      rw [abs_le]
      exact ⟨by nlinarith [sq_nonneg u, sq_nonneg (u ^ 2)], by nlinarith [sq_nonneg u, sq_nonneg (u ^ 2)]⟩
    rw [abs_mul, abs_mul, max_eq_left hu2.1, abs_of_nonneg hu2.1]
    have h1 : |u| * (1 - u ^ 2) ≤ 1 := by
      nlinarith [abs_nonneg u, hu.le, hu2.1, hu2.2]
    calc |u| * (1 - u ^ 2) * |1 - (5 / 2) * u ^ 2 - (29 / 4) * u ^ 4|
        ≤ 1 * (43 / 4) := mul_le_mul h1 hq (abs_nonneg _) zero_le_one
      _ = 43 / 4 := by ring

/-- The witness as a compactly supported continuous function. -/
private def ccWitness : C_c(ℝ, ℝ) :=
  ⟨⟨witness, continuous_witness⟩, compact_witness⟩

/-! ### 2. The exact autocorrelation `A(t) = c₁ C(t/c₁)` -/

lemma hasDerivAt_succ_pow' (c : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun u : ℝ => c * u ^ (k + 1)) (c * (((k : ℝ) + 1) * x ^ k)) x := by
  simpa [Nat.add_sub_cancel] using (hasDerivAt_pow (k + 1) x).const_mul c

private lemma hasDerivAt_scaled' {G G' : ℝ → ℝ} {x : ℝ}
    (hG : HasDerivAt G (G' (x / c₁)) (x / c₁)) :
    HasDerivAt (fun z : ℝ => c₁ * G (z / c₁)) (G' (x / c₁)) x := by
  have hc : (c₁ : ℝ) ≠ 0 := by norm_num
  have h1 := (hG.comp x ((hasDerivAt_id x).div_const c₁)).const_mul c₁
  exact h1.congr_deriv (by field_simp [hc])

/-- The unit autocorrelation `C(s) = ∫_{−1}^{1−s} P(v) P(v + s) dv`, `0 ≤ s ≤ 2`. -/
def witnessCorr (s : ℝ) : ℝ :=
  (451 / 819 : ℝ) +
    (-399727 / 25740 : ℝ) * s ^ 2 +
    (1225 / 24 : ℝ) * s ^ 3 +
    (-51437 / 693 : ℝ) * s ^ 4 +
    (28181 / 480 : ℝ) * s ^ 5 +
    (-4379 / 180 : ℝ) * s ^ 6 +
    (24443 / 6720 : ℝ) * s ^ 7 +
    (77 / 288 : ℝ) * s ^ 9 +
    (-611 / 20160 : ℝ) * s ^ 11 +
    (-551 / 82368 : ℝ) * s ^ 13 +
    (841 / 823680 : ℝ) * s ^ 15

/-- An antiderivative in `x` of `P(x) P(x + s)`. -/
private def witnessCorrAnti (s x : ℝ) : ℝ :=
  ((841 / 240 : ℝ)) * x ^ 15 +
    ((841 / 32 : ℝ) * s ^ 1) * x ^ 14 +
    ((-551 / 104 : ℝ) +
      (17661 / 208 : ℝ) * s ^ 2) * x ^ 13 +
    ((-551 / 16 : ℝ) * s ^ 1 +
      (29435 / 192 : ℝ) * s ^ 3) * x ^ 12 +
    ((-41 / 16 : ℝ) +
      (-17081 / 176 : ℝ) * s ^ 2 +
      (29435 / 176 : ℝ) * s ^ 4) * x ^ 11 +
    ((-451 / 32 : ℝ) * s ^ 1 +
      (-4959 / 32 : ℝ) * s ^ 3 +
      (17661 / 160 : ℝ) * s ^ 5) * x ^ 10 +
    ((191 / 36 : ℝ) +
      (-3067 / 72 : ℝ) * s ^ 2 +
      (-2755 / 18 : ℝ) * s ^ 4 +
      (5887 / 144 : ℝ) * s ^ 6) * x ^ 9 +
    ((191 / 8 : ℝ) * s ^ 1 +
      (-5503 / 64 : ℝ) * s ^ 3 +
      (-6061 / 64 : ℝ) * s ^ 5 +
      (841 / 128 : ℝ) * s ^ 7) * x ^ 8 +
    ((11 / 28 : ℝ) +
      (421 / 8 : ℝ) * s ^ 2 +
      (-12405 / 112 : ℝ) * s ^ 4 +
      (-551 / 16 : ℝ) * s ^ 6) * x ^ 7 +
    ((11 / 8 : ℝ) * s ^ 1 +
      (3493 / 48 : ℝ) * s ^ 3 +
      (-8165 / 96 : ℝ) * s ^ 5 +
      (-551 / 96 : ℝ) * s ^ 7) * x ^ 6 +
    ((-7 / 5 : ℝ) +
      (-43 / 20 : ℝ) * s ^ 2 +
      (539 / 8 : ℝ) * s ^ 4 +
      (-1421 / 40 : ℝ) * s ^ 6) * x ^ 5 +
    ((-7 / 2 : ℝ) * s ^ 1 +
      (-141 / 16 : ℝ) * s ^ 3 +
      (1351 / 32 : ℝ) * s ^ 5 +
      (-203 / 32 : ℝ) * s ^ 7) * x ^ 4 +
    ((1 / 3 : ℝ) +
      (-7 / 2 : ℝ) * s ^ 2 +
      (-95 / 12 : ℝ) * s ^ 4 +
      (203 / 12 : ℝ) * s ^ 6) * x ^ 3 +
    ((1 / 2 : ℝ) * s ^ 1 +
      (-7 / 4 : ℝ) * s ^ 3 +
      (-19 / 8 : ℝ) * s ^ 5 +
      (29 / 8 : ℝ) * s ^ 7) * x ^ 2

private lemma hasDerivAt_witnessCorrAnti (s x : ℝ) :
    HasDerivAt (witnessCorrAnti s) (witnessPoly x * witnessPoly (x + s)) x := by
  unfold witnessCorrAnti
  refine ((((((((((((((hasDerivAt_succ_pow' _ 14 x).add (hasDerivAt_succ_pow' _ 13 x)).add
    (hasDerivAt_succ_pow' _ 12 x)).add (hasDerivAt_succ_pow' _ 11 x)).add
    (hasDerivAt_succ_pow' _ 10 x)).add (hasDerivAt_succ_pow' _ 9 x)).add
    (hasDerivAt_succ_pow' _ 8 x)).add (hasDerivAt_succ_pow' _ 7 x)).add
    (hasDerivAt_succ_pow' _ 6 x)).add (hasDerivAt_succ_pow' _ 5 x)).add
    (hasDerivAt_succ_pow' _ 4 x)).add (hasDerivAt_succ_pow' _ 3 x)).add
    (hasDerivAt_succ_pow' _ 2 x)).add (hasDerivAt_succ_pow' _ 1 x)).congr_deriv ?_
  unfold witnessPoly
  ring

/-- **Exact autocorrelation**: `A(t) = c₁ C(t/c₁)` for `0 ≤ t ≤ 2c₁`. -/
theorem autocorr_witness {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 2 * c₁) :
    autocorr witness t = c₁ * witnessCorr (t / c₁) := by
  change (∫ x, witness x * witness (x + t)) = c₁ * witnessCorr (t / c₁)
  set s : ℝ := t / c₁ with hs_def
  have hc : (c₁ : ℝ) ≠ 0 := by norm_num
  have he : (fun x => witness x * witness (x + t)) =
      (Icc (-c₁) (c₁ - t)).indicator
        (fun x => witnessPoly (x / c₁) * witnessPoly (x / c₁ + s)) := by
    funext x
    by_cases hx : x ∈ Icc (-c₁) (c₁ - t)
    · rw [indicator_of_mem hx, witness_inside hx.1 (by linarith [hx.2]),
        witness_inside (by linarith [hx.1]) (by linarith [hx.2]),
        show (x + t) / c₁ = x / c₁ + s by rw [hs_def, add_div]]
    · rw [indicator_of_notMem hx]
      by_cases hl : x < -c₁
      · rw [witness_eq_zero_of_far (by rw [abs_of_neg (by linarith)]; linarith), zero_mul]
      · have hr : c₁ < x + t := by
          have := not_le.mp (fun h => hx ⟨not_lt.mp hl, h⟩)
          linarith
        rw [witness_eq_zero_of_far (x := x + t)
          (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]
  have hle : -c₁ ≤ c₁ - t := by linarith
  rw [he, MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_scaled' (G := witnessCorrAnti s)
        (G' := fun u => witnessPoly u * witnessPoly (u + s))
        (hasDerivAt_witnessCorrAnti s (x / c₁)))
      ((by unfold witnessPoly; fun_prop : Continuous fun x : ℝ =>
        witnessPoly (x / c₁) * witnessPoly (x / c₁ + s)).intervalIntegrable _ _)]
  have he1 : (c₁ - t) / c₁ = 1 - s := by rw [sub_div, div_self hc, ← hs_def]
  have he2 : (-c₁) / c₁ = -1 := by rw [neg_div, div_self hc]
  rw [he1, he2]
  unfold witnessCorrAnti witnessCorr
  ring

private lemma autocorr_witness_zero : autocorr witness 0 = c₁ * (451 / 819 : ℝ) := by
  rw [autocorr_witness le_rfl (by norm_num)]
  unfold witnessCorr; norm_num

private lemma autocorr_witness_tail {t : ℝ} (ht : 2 * c₁ < t) : autocorr witness t = 0 :=
  autocorr_eq_zero_of_far (fun _ hx => witness_eq_zero_of_far hx.le)
    (by rw [abs_of_pos (lt_trans (by norm_num : (0 : ℝ) < 2 * c₁) ht)]; exact ht)

/-! ### 3. The Lévy energy: quartic majorant on `(0, 2c₁]` and exponential tail -/

private def witnessLevyReg (s : ℝ) : ℝ :=
  (1 / 2 : ℝ) - (c₁ / 24) * s - (c₁ ^ 2 / 16) * s ^ 2 +
    (c₁ ^ 3 / 576) * s ^ 3 + (c₁ ^ 4 / 128) * s ^ 4

/-- `(C(0) − C(s))/s`. -/
private def witnessDivS (s : ℝ) : ℝ :=
  (399727 / 25740 : ℝ) * s ^ 1 +
    (-1225 / 24 : ℝ) * s ^ 2 +
    (51437 / 693 : ℝ) * s ^ 3 +
    (-28181 / 480 : ℝ) * s ^ 4 +
    (4379 / 180 : ℝ) * s ^ 5 +
    (-24443 / 6720 : ℝ) * s ^ 6 +
    (-77 / 288 : ℝ) * s ^ 8 +
    (611 / 20160 : ℝ) * s ^ 10 +
    (551 / 82368 : ℝ) * s ^ 12 +
    (-841 / 823680 : ℝ) * s ^ 14

private def witnessMajorant (s : ℝ) : ℝ :=
  witnessDivS s + c₁ * s * witnessDivS s * witnessLevyReg s

private def witnessMajAnti (s : ℝ) : ℝ :=
  (399727 / 51480 : ℝ) * s ^ 2 +
    (-799527143 / 51480000 : ℝ) * s ^ 3 +
    (85603920995573 / 5765760000000 : ℝ) * s ^ 4 +
    (-35487932435411671 / 4804800000000000 : ℝ) * s ^ 5 +
    (81815033431648004161 / 69189120000000000000 : ℝ) * s ^ 6 +
    (8356345031030026259253 / 17937920000000000000000 : ℝ) * s ^ 7 +
    (-6578958209031455449 / 75694080000000000000 : ℝ) * s ^ 8 +
    (-84947053113625480193 / 1596672000000000000000 : ℝ) * s ^ 9 +
    (-24776486297578619831 / 4300800000000000000000 : ℝ) * s ^ 10 +
    (259340152098066343 / 63360000000000000000 : ℝ) * s ^ 11 +
    (8663126882501644801 / 10321920000000000000000 : ℝ) * s ^ 12 +
    (114850898811317827 / 239855616000000000000 : ℝ) * s ^ 13 +
    (17603597674170544613 / 172204032000000000000000 : ℝ) * s ^ 14 +
    (-204222332320034123 / 2767564800000000000000 : ℝ) * s ^ 15 +
    (-43857380776298657437 / 1968046080000000000000000 : ℝ) * s ^ 16 +
    (26744333935733 / 29872128000000000000 : ℝ) * s ^ 17 +
    (5948536127575009 / 7028736000000000000000 : ℝ) * s ^ 18 +
    (-1119256086601 / 111288320000000000000 : ℝ) * s ^ 19 +
    (-5772003638601357 / 234291200000000000000000 : ℝ) * s ^ 20

private lemma hasDerivAt_witnessMajAnti (s : ℝ) :
    HasDerivAt witnessMajAnti (witnessMajorant s) s := by
  unfold witnessMajAnti
  refine (((((((((((((((((((hasDerivAt_succ_pow' _ 1 s).add (hasDerivAt_succ_pow' _ 2 s)).add
    (hasDerivAt_succ_pow' _ 3 s)).add (hasDerivAt_succ_pow' _ 4 s)).add
    (hasDerivAt_succ_pow' _ 5 s)).add (hasDerivAt_succ_pow' _ 6 s)).add
    (hasDerivAt_succ_pow' _ 7 s)).add (hasDerivAt_succ_pow' _ 8 s)).add
    (hasDerivAt_succ_pow' _ 9 s)).add (hasDerivAt_succ_pow' _ 10 s)).add
    (hasDerivAt_succ_pow' _ 11 s)).add (hasDerivAt_succ_pow' _ 12 s)).add
    (hasDerivAt_succ_pow' _ 13 s)).add (hasDerivAt_succ_pow' _ 14 s)).add
    (hasDerivAt_succ_pow' _ 15 s)).add (hasDerivAt_succ_pow' _ 16 s)).add
    (hasDerivAt_succ_pow' _ 17 s)).add (hasDerivAt_succ_pow' _ 18 s)).add
    (hasDerivAt_succ_pow' _ 19 s)).congr_deriv ?_
  unfold witnessMajorant witnessDivS witnessLevyReg
  ring

lemma deficit_nonneg' {G : ℝ → ℝ} (hGc : HasCompactSupport G) (hG : Continuous G)
    (t : ℝ) : 0 ≤ autocorr G 0 - autocorr G t := by
  have h := integral_sub_shift_sq hGc hG t
  have hn : 0 ≤ ∫ x, (G x - G (x + t)) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  linarith

/-- **Exponential tail of the Lévy density**:
`Ω(L) = ∫_L^∞ ω ≤ 2e^{−L/2} + (2/5) e^{−5L/2}/(1 − e^{−2L})`, from
`ω(t) = e^{−t/2} + e^{−5t/2}/(1 − e^{−2t})`. -/
theorem levyTail_le_exp {L : ℝ} (hL : 0 < L) :
    (∫ t in Ioi L, archLevyDensity t) ≤
      2 * Real.exp (-(1 / 2) * L) +
        (2 / 5) * Real.exp (-(5 / 2) * L) / (1 - Real.exp (-2 * L)) := by
  have hqL : 0 < 1 - Real.exp (-2 * L) := by
    have : Real.exp (-2 * L) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hpt : ∀ t ∈ Ioi L, archLevyDensity t ≤
      Real.exp (-(1 / 2) * t) + (1 / (1 - Real.exp (-2 * L))) * Real.exp (-(5 / 2) * t) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hL ht
    have hqt : 0 < 1 - Real.exp (-2 * t) := by
      have : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    have hle : 1 - Real.exp (-2 * L) ≤ 1 - Real.exp (-2 * t) := by
      have := Real.exp_le_exp.mpr (show -2 * t ≤ -2 * L by linarith [mem_Ioi.mp ht])
      linarith
    have hprod : Real.exp (-(1 / 2) * t) * Real.exp (-2 * t) = Real.exp (-(5 / 2) * t) := by
      rw [← Real.exp_add]; ring_nf
    have hid : archLevyDensity t =
        Real.exp (-(1 / 2) * t) + Real.exp (-(5 / 2) * t) / (1 - Real.exp (-2 * t)) := by
      unfold archLevyDensity
      rw [show -t / 2 = -(1 / 2) * t by ring, ← hprod, div_eq_iff hqt.ne', add_mul,
        div_mul_cancel₀ _ hqt.ne']
      ring
    rw [hid]
    have h5 := Real.exp_pos (-(5 / 2) * t)
    have : Real.exp (-(5 / 2) * t) / (1 - Real.exp (-2 * t)) ≤
        (1 / (1 - Real.exp (-2 * L))) * Real.exp (-(5 / 2) * t) := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_left h5.le hqL hle
    linarith
  have hi1 : IntegrableOn (fun t => Real.exp (-(1 / 2) * t)) (Ioi L) :=
    exp_neg_integrableOn_Ioi L (by norm_num : (0 : ℝ) < 1 / 2)
  have hi5 : IntegrableOn (fun t => Real.exp (-(5 / 2) * t)) (Ioi L) :=
    exp_neg_integrableOn_Ioi L (by norm_num : (0 : ℝ) < 5 / 2)
  have hmono : (∫ t in Ioi L, archLevyDensity t) ≤
      ∫ t in Ioi L, (Real.exp (-(1 / 2) * t) +
        (1 / (1 - Real.exp (-2 * L))) * Real.exp (-(5 / 2) * t)) :=
    setIntegral_mono_on (WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hL)
      (hi1.add (hi5.const_mul (1 / (1 - Real.exp (-2 * L))))) measurableSet_Ioi hpt
  have hrhs : (∫ t in Ioi L, (Real.exp (-(1 / 2) * t) +
        (1 / (1 - Real.exp (-2 * L))) * Real.exp (-(5 / 2) * t))) =
      2 * Real.exp (-(1 / 2) * L) +
        (2 / 5) * Real.exp (-(5 / 2) * L) / (1 - Real.exp (-2 * L)) := by
    rw [integral_add hi1 (hi5.const_mul _), MeasureTheory.integral_const_mul,
      integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) L,
      integral_exp_mul_Ioi (by norm_num : -(5 / 2 : ℝ) < 0) L]
    field_simp
  exact hmono.trans_eq hrhs

/-- The tail value `T(c₁) = 2e^{−c₁} + (2/5) e^{−5c₁}/(1 − e^{−4c₁})` of `Ω(2c₁)`. -/
private def witnessTail : ℝ :=
  2 * Real.exp (-(1 / 2) * (2 * c₁)) +
    (2 / 5) * Real.exp (-(5 / 2) * (2 * c₁)) / (1 - Real.exp (-2 * (2 * c₁)))

/-- **Lévy bound**: `𝒥(F) ≤ c₁ ∫₀² (quartic majorant) + 2A(0) T(c₁)`, and the jump integrand is
integrable. -/
private lemma witness_levy_le :
    IntegrableOn (fun t => (autocorr witness 0 - autocorr witness t) * archLevySinhWeight t)
        (Ioi (0 : ℝ)) ∧
      biScaleLevyEnergy witness ≤ c₁ * witnessMajAnti 2 + 2 * autocorr witness 0 * witnessTail := by
  have hL : (0 : ℝ) < 2 * c₁ := by norm_num
  have hpt : ∀ t ∈ Ioc (0 : ℝ) (2 * c₁),
      0 ≤ (autocorr witness 0 - autocorr witness t) * archLevySinhWeight t ∧
        (autocorr witness 0 - autocorr witness t) * archLevySinhWeight t ≤
          witnessMajorant (t / c₁) := fun t ht => by
    have hd_nn := deficit_nonneg' compact_witness continuous_witness t
    have hw_eq : archLevySinhWeight t = 2 * archLevyDensity t := by
      rw [archLevySinhWeight, exp_half_div_sinh_eq ht.1]
    refine ⟨mul_nonneg hd_nn (archLevySinhWeight_pos ht.1).le, ?_⟩
    rw [hw_eq]
    have hlev := mul_le_mul_of_nonneg_left (two_mul_archLevyDensity_le_quartic ht.1) hd_nn
    rw [autocorr_witness_zero, autocorr_witness ht.1.le ht.2] at hlev ⊢
    refine hlev.trans_eq ?_
    unfold witnessMajorant witnessDivS witnessLevyReg witnessCorr
    field_simp [ht.1.ne']
    ring
  have hmaj_cont : Continuous fun t : ℝ => witnessMajorant (t / c₁) := by
    unfold witnessMajorant witnessDivS witnessLevyReg; fun_prop
  have hmaj_int : IntegrableOn (fun t : ℝ => witnessMajorant (t / c₁)) (Ioc (0 : ℝ) (2 * c₁)) :=
    hmaj_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmeas : AEStronglyMeasurable
      (fun t => (autocorr witness 0 - autocorr witness t) * archLevySinhWeight t)
      (volume.restrict (Ioc (0 : ℝ) (2 * c₁))) := by
    have hc : Continuous fun t : ℝ => c₁ * (451 / 819 : ℝ) - c₁ * witnessCorr (t / c₁) := by
      unfold witnessCorr; fun_prop
    have hw := continuousOn_archLevySinhWeight_pos_halfLine.mono
      (show Ioc (0 : ℝ) (2 * c₁) ⊆ Ioi 0 from fun _ ht => ht.1)
    refine ((hc.continuousOn.mul hw).aestronglyMeasurable measurableSet_Ioc).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [Pi.mul_apply, autocorr_witness_zero, autocorr_witness ht.1.le ht.2]
  have hint_in : IntegrableOn
      (fun t => (autocorr witness 0 - autocorr witness t) * archLevySinhWeight t)
      (Ioc (0 : ℝ) (2 * c₁)) := by
    refine hmaj_int.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hpt t ht).1]
    exact (hpt t ht).2
  have htail_eq : ∀ t ∈ Ioi (2 * c₁),
      (autocorr witness 0 - autocorr witness t) * archLevySinhWeight t =
        (autocorr witness 0 * 2) * archLevyDensity t := fun t ht => by
    have ht0 : 0 < t := lt_trans hL ht
    rw [autocorr_witness_tail ht, sub_zero, archLevySinhWeight, exp_half_div_sinh_eq ht0]
    ring
  have hint_tail : IntegrableOn
      (fun t => (autocorr witness 0 - autocorr witness t) * archLevySinhWeight t)
      (Ioi (2 * c₁)) := by
    refine ((WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hL).const_mul
      (autocorr witness 0 * 2)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (htail_eq t ht).symm
  have hint_all : IntegrableOn
      (fun t => (autocorr witness 0 - autocorr witness t) * archLevySinhWeight t)
      (Ioi (0 : ℝ)) := by
    have h := hint_in.union hint_tail
    rwa [Ioc_union_Ioi_eq_Ioi hL.le] at h
  refine ⟨hint_all, ?_⟩
  have hin_le : (∫ t in Ioc (0 : ℝ) (2 * c₁),
      (autocorr witness 0 - autocorr witness t) * archLevySinhWeight t) ≤ c₁ * witnessMajAnti 2 := by
    have hm := setIntegral_mono_on hint_in hmaj_int measurableSet_Ioc fun t ht => (hpt t ht).2
    have hval : (∫ t in Ioc (0 : ℝ) (2 * c₁), witnessMajorant (t / c₁)) =
        c₁ * witnessMajAnti 2 := by
      rw [← intervalIntegral.integral_of_le hL.le,
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => hasDerivAt_scaled' (G := witnessMajAnti) (G' := witnessMajorant)
            (hasDerivAt_witnessMajAnti (t / c₁)))
          (hmaj_cont.intervalIntegrable _ _)]
      have h2 : (2 * c₁) / c₁ = 2 := by norm_num
      rw [h2, zero_div]
      unfold witnessMajAnti; ring
    exact hm.trans_eq hval
  have hA0 : 0 ≤ autocorr witness 0 := by rw [autocorr_witness_zero]; norm_num
  have htail_le : (∫ t in Ioi (2 * c₁),
      (autocorr witness 0 - autocorr witness t) * archLevySinhWeight t) ≤
        2 * autocorr witness 0 * witnessTail := by
    rw [setIntegral_congr_fun measurableSet_Ioi htail_eq, MeasureTheory.integral_const_mul]
    have h := levyTail_le_exp hL
    have h2 : 0 ≤ autocorr witness 0 * 2 := by linarith
    calc autocorr witness 0 * 2 * ∫ t in Ioi (2 * c₁), archLevyDensity t
        ≤ autocorr witness 0 * 2 * witnessTail := mul_le_mul_of_nonneg_left h h2
      _ = 2 * autocorr witness 0 * witnessTail := by ring
  unfold biScaleLevyEnergy
  rw [← Ioc_union_Ioi_eq_Ioi hL.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_in hint_tail]
  linarith

/-! ### 4. Weil's form of the odd witness in autocorrelation form -/

/-- `W(F) + 2S(F)² = Γ A(0) + 𝒥(F) − 2w₂ A(log 2) − 2w₃ A(log 3)` for the odd witness (support length
`2c₁ < log 4`, so only the primes `2` and `3` meet it). -/
private lemma witness_weilQuad_add_two_oddPole_sq_eq :
    weilQuad witness + 2 * oddPoleMoment witness ^ 2 =
      EF.gammaBracket 0 * autocorr witness 0 + biScaleLevyEnergy witness -
        2 * primeJumpWeight 2 * autocorr witness (Real.log 2) -
        2 * primeJumpWeight 3 * autocorr witness (Real.log 3) := by
  have hfull := re_weilFullFunctional_eq_of_compact_finite_jump ccWitness witness_levy_le.1
  change weilQuad witness = EF.gammaBracket 0 * autocorr witness 0 +
    biScaleLevyEnergy witness - 2 * fullPairing (autocorr witness) at hfull
  have hprime : (∑' n : ℕ, primeTerm (autocorr witness) n) =
      primeJumpWeight 2 * autocorr witness (Real.log 2) +
        primeJumpWeight 3 * autocorr witness (Real.log 3) := by
    rw [tsum_eq_sum (s := ({2, 3} : Finset ℕ)) (fun n hn => ?_),
      Finset.sum_pair (by decide : (2 : ℕ) ≠ 3)]
    · unfold primeTerm SignedPrimePolar.primeWeight primeJumpWeight
      rw [if_pos (by norm_num : 2 ≤ (2 : ℕ)), if_pos (by norm_num : 2 ≤ (3 : ℕ))]
      norm_num only [Nat.cast_ofNat]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      by_cases h2 : 2 ≤ n
      · have h4 : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
        have hlog4 : 2 * c₁ < Real.log 4 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
          norm_num
          linarith [Real.log_two_gt_d9]
        have hlog : 2 * c₁ < |Real.log n| := by
          have hln : 2 * c₁ < Real.log n :=
            lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) h4)
          rw [abs_of_pos (lt_trans (by norm_num : (0 : ℝ) < 2 * c₁) hln)]
          exact hln
        have hz : autocorr witness (Real.log n) = 0 :=
          autocorr_eq_zero_of_far (fun _ hx => witness_eq_zero_of_far hx.le) hlog
        simp only [primeTerm, if_pos h2, hz, mul_zero]
      · simp only [primeTerm, if_neg h2]
  have hpolar : 2 * (∫ t in Ici (0 : ℝ), polarDensity t * autocorr witness t) =
      -(2 * oddPoleMoment witness ^ 2) := by
    have hm := integral_polar_autocorr_eq_moments ccWitness
    have hp := pole_eq_pairings witness continuous_witness compact_witness
    have hc := coshPairing_eq_zero_of_odd witness_odd
    have he1 : (∫ u, Real.exp (u / 2) * witness u) = ∫ u, witness u * Real.exp (u / 2) :=
      integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
    have he2 : (∫ u, Real.exp (-(u / 2)) * witness u) = ∫ u, witness u * Real.exp (-u / 2) :=
      integral_congr_ae (Eventually.of_forall fun u => by
        show Real.exp (-(u / 2)) * witness u = witness u * Real.exp (-u / 2)
        rw [neg_div]; ring)
    change (∫ t in Ici (0 : ℝ), polarDensity t * autocorr witness t) =
      (∫ u, Real.exp (u / 2) * witness u) * (∫ u, Real.exp (-(u / 2)) * witness u) at hm
    rw [he1, he2] at hm
    have hsp : sinhPairing witness = 2 * oddPoleMoment witness := by
      unfold sinhPairing oddPoleMoment
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun _ => by ring)
    rw [hm]
    rw [hc, hsp] at hp
    nlinarith [hp]
  rw [fullPairing, hprime] at hfull
  linarith

/-! ### 5. Certified enclosures -/

/-- `|sinh z − (z + z³/6 + z⁵/120)| ≤ |z|⁷ · 8/35280` for `|z| ≤ 1`. -/
theorem abs_sinh_sub_quintic_le {z : ℝ} (hz : |z| ≤ 1) :
    |Real.sinh z - (z + z ^ 3 / 6 + z ^ 5 / 120)| ≤ |z| ^ 7 * (8 / 35280) := by
  have h1 := Real.exp_bound hz (n := 7) (by norm_num)
  have h2 := Real.exp_bound (x := -z) (by rwa [abs_neg]) (n := 7) (by norm_num)
  rw [abs_neg] at h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one]
    at h1 h2
  norm_num at h1 h2
  have hid : Real.sinh z - (z + z ^ 3 / 6 + z ^ 5 / 120) =
      ((Real.exp z - (1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120 + z ^ 6 / 720)) -
        (Real.exp (-z) - (1 + -z + (-z) ^ 2 / 2 + (-z) ^ 3 / 6 + (-z) ^ 4 / 24 + (-z) ^ 5 / 120 +
          (-z) ^ 6 / 720))) / 2 := by
    rw [Real.sinh_eq]; ring
  rw [hid, abs_div, abs_two]
  have h1' : |Real.exp z - (1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120 + z ^ 6 / 720)|
      ≤ |z| ^ 7 * (8 / 35280) := by
    convert h1 using 2; ring
  have h2' : |Real.exp (-z) - (1 + -z + (-z) ^ 2 / 2 + (-z) ^ 3 / 6 + (-z) ^ 4 / 24 +
      (-z) ^ 5 / 120 + (-z) ^ 6 / 720)| ≤ |z| ^ 7 * (8 / 35280) := by
    convert h2 using 2 <;> ring
  have := abs_sub _ _ |>.trans (add_le_add h1' h2')
  linarith

/-- `P(x/c₁) · (x/2 + (x/2)³/6 + (x/2)⁵/120)` expanded. -/
private def oddTPoly (x : ℝ) : ℝ :=
  (500 / 573 : ℝ) * x ^ 2 +
    (-3486319625 / 376265034 : ℝ) * x ^ 4 +
    (-76765202667231325 / 1976619557570976 : ℝ) * x ^ 6 +
    (3592410854228426171875 / 20280672584928780597 : ℝ) * x ^ 8 +
    (451906591601562500000 / 60842017754786341791 : ℝ) * x ^ 10 +
    (5664062500000000000 / 60842017754786341791 : ℝ) * x ^ 12

private def oddTAnti (x : ℝ) : ℝ :=
  (500 / 1719 : ℝ) * x ^ 3 +
    (-697263925 / 376265034 : ℝ) * x ^ 5 +
    (-76765202667231325 / 13836336902996832 : ℝ) * x ^ 7 +
    (3592410854228426171875 / 182526053264359025373 : ℝ) * x ^ 9 +
    (451906591601562500000 / 669262195302649759701 : ℝ) * x ^ 11 +
    (5664062500000000000 / 790946230812222443283 : ℝ) * x ^ 13

private lemma hasDerivAt_oddTAnti (x : ℝ) : HasDerivAt oddTAnti (oddTPoly x) x := by
  unfold oddTAnti
  refine ((((((hasDerivAt_succ_pow' _ 2 x).add (hasDerivAt_succ_pow' _ 4 x)).add
    (hasDerivAt_succ_pow' _ 6 x)).add (hasDerivAt_succ_pow' _ 8 x)).add
    (hasDerivAt_succ_pow' _ 10 x)).add (hasDerivAt_succ_pow' _ 12 x)).congr_deriv ?_
  unfold oddTPoly; ring

private lemma oddTPoly_eq (x : ℝ) :
    witnessPoly (x / c₁) * (x / 2 + (x / 2) ^ 3 / 6 + (x / 2) ^ 5 / 120) = oddTPoly x := by
  unfold witnessPoly oddTPoly; ring

/-- `|P(u)| ≤ (33/2)|u|` on `[−1, 1]`. -/
private lemma abs_witnessPoly_le {u : ℝ} (hu : |u| ≤ 1) : |witnessPoly u| ≤ (33 / 2) * |u| := by
  have ht1 : u ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg u) hu
  have ht0 : 0 ≤ u ^ 2 := sq_nonneg u
  have h22 : (u ^ 2) ^ 2 ≤ u ^ 2 := by nlinarith
  have h23 : (u ^ 2) ^ 3 ≤ u ^ 2 := by nlinarith
  have hq : |1 - (7 / 2) * u ^ 2 - (19 / 4) * (u ^ 2) ^ 2 + (29 / 4) * (u ^ 2) ^ 3| ≤ 33 / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u ^ 2), pow_nonneg ht0 3]
  have he : witnessPoly u = u * (1 - (7 / 2) * u ^ 2 - (19 / 4) * (u ^ 2) ^ 2 +
      (29 / 4) * (u ^ 2) ^ 3) := by unfold witnessPoly; ring
  rw [he, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hq (abs_nonneg u)

/-- **Pole moment**: `S(F) = ∫ F sinh(x/2) ≤ U < 0` with `U` the Taylor value plus remainder. -/
private lemma witness_oddPoleMoment_le :
    oddPoleMoment witness ≤
      (oddTAnti c₁ - oddTAnti (-c₁)) +
        (33 / 2) * (8 / 35280) / (128 * c₁) * (2 * c₁ ^ 9 / 9) := by
  have hc : (0 : ℝ) < c₁ := by norm_num
  have he : (fun x => witness x * Real.sinh (x / 2)) =
      (Icc (-c₁) c₁).indicator (fun x => witnessPoly (x / c₁) * Real.sinh (x / 2)) := by
    funext x
    by_cases hx : x ∈ Icc (-c₁) c₁
    · rw [indicator_of_mem hx, witness_inside hx.1 hx.2]
    · rw [indicator_of_notMem hx,
        witness_eq_zero_of_far (le_of_lt (not_le.mp fun h => hx (abs_le.mp h))), zero_mul]
  unfold oddPoleMoment
  rw [he, MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -c₁ ≤ c₁)]
  -- pointwise majorant on `[−c₁, c₁]`
  set g : ℝ → ℝ := fun x => oddTPoly x + (33 / 2) * (8 / 35280) / (128 * c₁) * x ^ 8
  have hpt : ∀ x ∈ Icc (-c₁) c₁, witnessPoly (x / c₁) * Real.sinh (x / 2) ≤ g x := by
    intro x hx
    have hxc : |x / c₁| ≤ 1 := by
      rw [abs_div, abs_of_pos hc, div_le_one hc]; exact abs_le.mpr hx
    have hz : |x / 2| ≤ 1 := by
      have h1 := abs_le.mpr hx
      have h2 : c₁ ≤ 2 := by norm_num
      rw [abs_div, abs_two]; linarith
    have hs := abs_sinh_sub_quintic_le hz
    have hp := abs_witnessPoly_le hxc
    have hsplit : witnessPoly (x / c₁) * Real.sinh (x / 2) =
        oddTPoly x + witnessPoly (x / c₁) *
          (Real.sinh (x / 2) - (x / 2 + (x / 2) ^ 3 / 6 + (x / 2) ^ 5 / 120)) := by
      rw [← oddTPoly_eq]; ring
    have hrem : witnessPoly (x / c₁) *
        (Real.sinh (x / 2) - (x / 2 + (x / 2) ^ 3 / 6 + (x / 2) ^ 5 / 120)) ≤
          (33 / 2) * (8 / 35280) / (128 * c₁) * x ^ 8 := by
      have hab := le_abs_self (witnessPoly (x / c₁) *
        (Real.sinh (x / 2) - (x / 2 + (x / 2) ^ 3 / 6 + (x / 2) ^ 5 / 120)))
      rw [abs_mul] at hab
      have hprod := mul_le_mul hp hs (abs_nonneg _) (by positivity)
      have hpow : (33 / 2) * |x / c₁| * (|x / 2| ^ 7 * (8 / 35280)) =
          (33 / 2) * (8 / 35280) / (128 * c₁) * x ^ 8 := by
        rw [abs_div x c₁, abs_div x 2, abs_of_pos hc, abs_two, div_pow]
        have h8 : |x| ^ 8 = x ^ 8 := by
          rw [pow_abs]; exact abs_of_nonneg (by positivity)
        rw [← h8]
        field_simp
        ring
      linarith
    show _ ≤ oddTPoly x + _
    linarith
  have hcont : Continuous fun x => witnessPoly (x / c₁) * Real.sinh (x / 2) := by
    unfold witnessPoly; fun_prop
  have hgc : Continuous g := by simp only [g]; unfold oddTPoly; fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : -c₁ ≤ c₁)
    (hcont.intervalIntegrable _ _) (hgc.intervalIntegrable _ _) hpt
  have hg_int : (∫ x in (-c₁)..c₁, g x) =
      (oddTAnti c₁ - oddTAnti (-c₁)) + (33 / 2) * (8 / 35280) / (128 * c₁) * (2 * c₁ ^ 9 / 9) := by
    simp only [g]
    rw [intervalIntegral.integral_add
        ((by unfold oddTPoly; fun_prop : Continuous oddTPoly).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun x : ℝ =>
          (33 / 2) * (8 / 35280) / (128 * c₁) * x ^ 8).intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_oddTAnti x)
        ((by unfold oddTPoly; fun_prop : Continuous oddTPoly).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_pow]
    ring
  linarith

/-- The Taylor value of the pole moment is `< −0.0794`. -/
private lemma witness_oddPoleMoment_sq_ge : (794 / 10000 : ℝ) ^ 2 ≤ oddPoleMoment witness ^ 2 := by
  have h := witness_oddPoleMoment_le
  have hv : (oddTAnti c₁ - oddTAnti (-c₁)) +
      (33 / 2) * (8 / 35280) / (128 * c₁) * (2 * c₁ ^ 9 / 9) ≤ -(794 / 10000 : ℝ) := by
    unfold oddTAnti; norm_num
  nlinarith

/-! ### 6. The prime-2 correlation -/

private def witnessCorrDeriv (u : ℝ) : ℝ :=
  (-399727 / 12870 : ℝ) * u ^ 1 +
    (1225 / 8 : ℝ) * u ^ 2 +
    (-205748 / 693 : ℝ) * u ^ 3 +
    (28181 / 96 : ℝ) * u ^ 4 +
    (-4379 / 30 : ℝ) * u ^ 5 +
    (24443 / 960 : ℝ) * u ^ 6 +
    (77 / 32 : ℝ) * u ^ 8 +
    (-6721 / 20160 : ℝ) * u ^ 10 +
    (-551 / 6336 : ℝ) * u ^ 12 +
    (841 / 54912 : ℝ) * u ^ 14

private lemma hasDerivAt_witnessCorr (u : ℝ) : HasDerivAt witnessCorr (witnessCorrDeriv u) u := by
  unfold witnessCorr
  refine ((((((((((hasDerivAt_const u (451 / 819 : ℝ)).add
    (hasDerivAt_succ_pow' (-399727 / 25740) 1 u)).add
    (hasDerivAt_succ_pow' (1225 / 24) 2 u)).add
    (hasDerivAt_succ_pow' (-51437 / 693) 3 u)).add
    (hasDerivAt_succ_pow' (28181 / 480) 4 u)).add
    (hasDerivAt_succ_pow' (-4379 / 180) 5 u)).add
    (hasDerivAt_succ_pow' (24443 / 6720) 6 u)).add
    (hasDerivAt_succ_pow' (77 / 288) 8 u)).add
    (hasDerivAt_succ_pow' (-611 / 20160) 10 u)).add
    (hasDerivAt_succ_pow' (-551 / 82368) 12 u)).add
    (hasDerivAt_succ_pow' (841 / 823680) 14 u) |>.congr_deriv ?_
  unfold witnessCorrDeriv; ring

/-- Mean-value lower bound for a polynomial with bounded derivative. -/
lemma poly_ge_of_deriv_bound' {Q Q' : ℝ → ℝ} {a b s₀ s M : ℝ}
    (ha : a ≤ s₀) (hs₀ : s₀ ≤ b) (has : a ≤ s) (hsb : s ≤ b)
    (hcQ' : Continuous Q') (hdQ : ∀ u, HasDerivAt Q (Q' u) u)
    (hbQ' : ∀ u ∈ Icc a b, |Q' u| ≤ M) :
    Q s₀ - M * |s - s₀| ≤ Q s := by
  rcases le_total s₀ s with hle | hle
  · have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hdQ u) (hcQ'.intervalIntegrable s₀ s)
    rw [intervalIntegral.integral_of_le hle] at hftc
    have hm := setIntegral_mono_on
      ((continuous_const : Continuous fun _ : ℝ => -M).integrableOn_Ioc (μ := volume))
      (hcQ'.integrableOn_Ioc (μ := volume)) measurableSet_Ioc
      fun u hu => (abs_le.mp (hbQ' u ⟨le_trans ha hu.1.le, le_trans hu.2 hsb⟩)).1
    rw [setIntegral_const, Real.volume_real_Ioc, max_eq_left (by linarith), smul_eq_mul, hftc] at hm
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hdQ u) (hcQ'.intervalIntegrable s s₀)
    rw [intervalIntegral.integral_of_le hle] at hftc
    have hm := setIntegral_mono_on
      (hcQ'.integrableOn_Ioc (μ := volume))
      ((continuous_const : Continuous fun _ : ℝ => M).integrableOn_Ioc (μ := volume))
      measurableSet_Ioc
      fun u hu => (abs_le.mp (hbQ' u ⟨le_trans has hu.1.le, le_trans hu.2 hs₀⟩)).2
    rw [setIntegral_const, Real.volume_real_Ioc, max_eq_left (by linarith), smul_eq_mul, hftc] at hm
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- `A(log 2) ≥ 0.0297`. -/
private lemma witness_autocorr_log_two_ge : (297 / 10000 : ℝ) ≤ autocorr witness (Real.log 2) := by
  have hl2 := Real.log_two_gt_d9
  have hu2 := Real.log_two_lt_d9
  rw [autocorr_witness (by linarith) (by norm_num; linarith)]
  set s := Real.log 2 / c₁
  have hc : (0 : ℝ) < c₁ := by norm_num
  have hs_in : s ∈ Icc (6 / 5 : ℝ) (61 / 50) := by
    simp only [s, mem_Icc]
    constructor
    · rw [le_div_iff₀ hc]; norm_num; linarith
    · rw [div_le_iff₀ hc]; norm_num; linarith
  have hs_ball : |s - (12096809 / 10000000 : ℝ)| ≤ 1 / 10000000 := by
    rw [abs_le]; simp only [s]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hc]; norm_num; linarith
    · rw [sub_le_iff_le_add, div_le_iff₀ hc]; norm_num; linarith
  have hb : ∀ u ∈ Icc (6 / 5 : ℝ) (61 / 50), |witnessCorrDeriv u| ≤ 2000 := fun u hu => by
    have ha : (0 : ℝ) ≤ 6 / 5 := by norm_num
    have h0 : 0 ≤ u := by linarith [hu.1]
    have p2l := pow_le_pow_left₀ ha hu.1 2
    have p2u := pow_le_pow_left₀ h0 hu.2 2
    have p3l := pow_le_pow_left₀ ha hu.1 3
    have p3u := pow_le_pow_left₀ h0 hu.2 3
    have p4l := pow_le_pow_left₀ ha hu.1 4
    have p4u := pow_le_pow_left₀ h0 hu.2 4
    have p5l := pow_le_pow_left₀ ha hu.1 5
    have p5u := pow_le_pow_left₀ h0 hu.2 5
    have p6l := pow_le_pow_left₀ ha hu.1 6
    have p6u := pow_le_pow_left₀ h0 hu.2 6
    have p8l := pow_le_pow_left₀ ha hu.1 8
    have p8u := pow_le_pow_left₀ h0 hu.2 8
    have p10l := pow_le_pow_left₀ ha hu.1 10
    have p10u := pow_le_pow_left₀ h0 hu.2 10
    have p12l := pow_le_pow_left₀ ha hu.1 12
    have p12u := pow_le_pow_left₀ h0 hu.2 12
    have p14l := pow_le_pow_left₀ ha hu.1 14
    have p14u := pow_le_pow_left₀ h0 hu.2 14
    rw [abs_le]; unfold witnessCorrDeriv
    norm_num at p2l p2u p3l p3u p4l p4u p5l p5u p6l p6u p8l p8u p10l p10u p12l p12u p14l p14u
    exact ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
  have hcd : Continuous witnessCorrDeriv := by unfold witnessCorrDeriv; fun_prop
  have hmv := poly_ge_of_deriv_bound' (s₀ := 12096809 / 10000000) (s := s) (by norm_num)
    (by norm_num) hs_in.1 hs_in.2 hcd hasDerivAt_witnessCorr hb
  have hv : (297 / 10000 : ℝ) / c₁ ≤ witnessCorr (12096809 / 10000000) - 2000 * (1 / 10000000) := by
    unfold witnessCorr; norm_num
  have hM : 2000 * |s - 12096809 / 10000000| ≤ 2000 * (1 / 10000000) :=
    mul_le_mul_of_nonneg_left hs_ball (by norm_num)
  have : (297 / 10000 : ℝ) / c₁ ≤ witnessCorr s := by linarith
  rw [div_le_iff₀ hc] at this
  linarith

/-! ### 7. The archimedean constant and the exponential tail -/

/-- `Γ = gammaBracket 0 ≤ −5.370`. -/
lemma gammaBracket_zero_le : EF.gammaBracket 0 ≤ -(5370 / 1000 : ℝ) := by
  have hγ : (5769 / 10000 : ℝ) < Real.eulerMascheroniConstant := by
    have h := RHTower.harmonic_mascheroni_le_half_sub_twelfth (n := 8) (by norm_num)
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
    norm_num [harmonic, Finset.sum_range_succ, hlog8] at h
    linarith [Real.log_two_lt_d9]
  -- `log π ≥ log 3 + (1 − 3/π)`
  have hlog_pi : Real.log 3 + (1 - 3 / Real.pi) ≤ Real.log Real.pi := by
    have hq := Real.one_sub_inv_le_log_of_pos (show 0 < Real.pi / 3 by positivity)
    rw [Real.log_div Real.pi_ne_zero (by norm_num), inv_div] at hq
    linarith
  have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4; norm_num at h; linarith
  have h3pi : 1 - 3 / Real.pi ≥ (1 - 3 / (31415 / 10000) : ℝ) := by
    have : 3 / Real.pi ≤ 3 / (31415 / 10000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi
    linarith
  have he := neg_gammaBracket_zero_eq
  have hl3 := Real.log_three_gt_d9
  have hl2 := Real.log_two_gt_d9
  norm_num at h3pi
  linarith

/-- `e^{−c₁} ≤ 1/1.7735`, `e^{−5c₁} ≤ 1/17.5`, `e^{−4c₁} ≤ 1/9.89`. -/
private lemma exp_neg_bounds :
    Real.exp (-(1 / 2) * (2 * c₁)) ≤ 1 / (17735 / 10000) ∧
      Real.exp (-(5 / 2) * (2 * c₁)) ≤ 1 / (175 / 10) ∧
      Real.exp (-2 * (2 * c₁)) ≤ 1 / (989 / 100) := by
  have key : ∀ (a S : ℝ) (n : ℕ), 0 ≤ a → 0 < S →
      S ≤ ∑ i ∈ Finset.range n, a ^ i / (i.factorial : ℝ) → Real.exp (-a) ≤ 1 / S := by
    intro a S n ha hS hle
    have h := (hle.trans (Real.sum_le_exp_of_nonneg ha n))
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le hS h
  refine ⟨?_, ?_, ?_⟩
  · rw [show -(1 / 2) * (2 * c₁) = -(573 / 1000 : ℝ) by norm_num]
    exact key _ _ 8 (by norm_num) (by norm_num)
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  · rw [show -(5 / 2) * (2 * c₁) = -(2865 / 1000 : ℝ) by norm_num]
    exact key _ _ 14 (by norm_num) (by norm_num)
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  · rw [show -2 * (2 * c₁) = -(2292 / 1000 : ℝ) by norm_num]
    exact key _ _ 12 (by norm_num) (by norm_num)
      (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)

private lemma witnessTail_le :
    witnessTail ≤ 2 * (1 / (17735 / 10000)) + (2 / 5) * (1 / (175 / 10)) / (1 - 1 / (989 / 100)) := by
  obtain ⟨h1, h5, h2⟩ := exp_neg_bounds
  unfold witnessTail
  have hq : (1 - 1 / (989 / 100) : ℝ) ≤ 1 - Real.exp (-2 * (2 * c₁)) := by linarith
  have hqpos : (0 : ℝ) < 1 - 1 / (989 / 100) := by norm_num
  have hd : (2 / 5) * Real.exp (-(5 / 2) * (2 * c₁)) / (1 - Real.exp (-2 * (2 * c₁))) ≤
      (2 / 5) * (1 / (175 / 10)) / (1 - 1 / (989 / 100)) := by
    have hpos := Real.exp_pos (-(5 / 2) * (2 * c₁))
    calc (2 / 5) * Real.exp (-(5 / 2) * (2 * c₁)) / (1 - Real.exp (-2 * (2 * c₁)))
        ≤ (2 / 5) * Real.exp (-(5 / 2) * (2 * c₁)) / (1 - 1 / (989 / 100)) :=
          div_le_div_of_nonneg_left (by positivity) hqpos hq
      _ ≤ (2 / 5) * (1 / (175 / 10)) / (1 - 1 / (989 / 100)) := by
          apply div_le_div_of_nonneg_right _ hqpos.le; linarith
  linarith

/-! ### 8. The collar mass -/

private def witnessSqAnti (u : ℝ) : ℝ :=
  (1 / 3 : ℝ) * u ^ 3 +
    (-7 / 5 : ℝ) * u ^ 5 +
    (11 / 28 : ℝ) * u ^ 7 +
    (191 / 36 : ℝ) * u ^ 9 +
    (-41 / 16 : ℝ) * u ^ 11 +
    (-551 / 104 : ℝ) * u ^ 13 +
    (841 / 240 : ℝ) * u ^ 15

private lemma hasDerivAt_witnessSqAnti (u : ℝ) :
    HasDerivAt witnessSqAnti (witnessPoly u ^ 2) u := by
  unfold witnessSqAnti
  refine (((((((hasDerivAt_succ_pow' _ 2 u).add (hasDerivAt_succ_pow' _ 4 u)).add
    (hasDerivAt_succ_pow' _ 6 u)).add (hasDerivAt_succ_pow' _ 8 u)).add
    (hasDerivAt_succ_pow' _ 10 u)).add (hasDerivAt_succ_pow' _ 12 u)).add
    (hasDerivAt_succ_pow' _ 14 u)).congr_deriv ?_
  unfold witnessPoly; ring

/-- The collar of the window `[−287/500, 287/500]` carries witness mass at least `0.0176`. -/
private lemma witness_collarMass_ge :
    (176 / 10000 : ℝ) ≤ ∫ x in Icc (Real.log 3 - 287 / 500) (287 / 500), witness x ^ 2 := by
  have hc : (0 : ℝ) < c₁ := by norm_num
  have hl3 := Real.log_three_lt_d9
  set a' : ℝ := 5246123 / 10000000
  have hc574 : c₁ ≤ 287 / 500 := by norm_num
  have hsub : Icc a' c₁ ⊆ Icc (Real.log 3 - 287 / 500) (287 / 500) := fun x hx =>
    ⟨by simp only [a'] at hx; linarith [hx.1], le_trans hx.2 hc574⟩
  have hint : IntegrableOn (fun x => witness x ^ 2) (Icc (Real.log 3 - 287 / 500) (287 / 500)) :=
    (continuous_witness.pow 2).integrableOn_Icc
  have hmono := setIntegral_mono_set (s := Icc a' c₁) hint
    (ae_restrict_of_forall_mem measurableSet_Icc fun x _ => sq_nonneg (witness x))
    (Eventually.of_forall hsub)
  have hval : (∫ x in Icc a' c₁, witness x ^ 2) =
      c₁ * (witnessSqAnti 1 - witnessSqAnti (a' / c₁)) := by
    have hle : a' ≤ c₁ := by simp only [a']; norm_num
    have he : ∀ x ∈ Icc a' c₁, witness x ^ 2 = witnessPoly (x / c₁) ^ 2 := fun x hx => by
      rw [witness_inside (by simp only [a'] at hx; linarith [hx.1]) hx.2]
    rw [setIntegral_congr_fun measurableSet_Icc he, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hasDerivAt_scaled' (G := witnessSqAnti) (G' := fun u => witnessPoly u ^ 2)
          (hasDerivAt_witnessSqAnti (x / c₁)))
        ((by unfold witnessPoly; fun_prop : Continuous fun x : ℝ =>
          witnessPoly (x / c₁) ^ 2).intervalIntegrable _ _)]
    rw [div_self hc.ne']
    ring
  have hnum : (176 / 10000 : ℝ) ≤ c₁ * (witnessSqAnti 1 - witnessSqAnti (a' / c₁)) := by
    simp only [a']; unfold witnessSqAnti; norm_num
  linarith

/-! ### 9. The certificate gap of the witness -/

lemma vonMangoldtAtom_three_eq : vonMangoldtAtom 3 = primeJumpWeight 3 := by
  unfold vonMangoldtAtom primeJumpWeight
  rw [if_pos (by norm_num)]

lemma primeJumpWeight_bounds :
    (693147 / 1000000 : ℝ) / (141422 / 100000) ≤ primeJumpWeight 2 ∧
      (1098612 / 1000000 : ℝ) / (173206 / 100000) ≤ primeJumpWeight 3 := by
  have hs2_hi : Real.sqrt 2 ≤ 141422 / 100000 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hs3_hi : Real.sqrt 3 ≤ 173206 / 100000 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  refine ⟨?_, ?_⟩
  · unfold primeJumpWeight
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num only [Nat.cast_ofNat]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [Real.log_two_gt_d9, Real.sqrt_nonneg 2]
  · unfold primeJumpWeight
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
    norm_num only [Nat.cast_ofNat]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [Real.log_three_gt_d9, Real.sqrt_nonneg 3]

/-- **Certificate gap of the witness**: `W(F) + 2w₃A(log 3) − 2w₃ (collar mass) < −1/100`. -/
private lemma witness_gap :
    weilQuad witness + 2 * vonMangoldtAtom 3 * autocorr witness (Real.log 3) -
        2 * vonMangoldtAtom 3 * ∫ x in Icc (Real.log 3 - 287 / 500) (287 / 500), witness x ^ 2 <
      -(1 / 100) := by
  have hid := witness_weilQuad_add_two_oddPole_sq_eq
  have hlevy := witness_levy_le.2
  have hA0 : autocorr witness 0 = 86141 / 273000 := by rw [autocorr_witness_zero]; norm_num
  have hΓ := gammaBracket_zero_le
  have htail := witnessTail_le
  have hS := witness_oddPoleMoment_sq_ge
  have hA2 := witness_autocorr_log_two_ge
  have hm := witness_collarMass_ge
  obtain ⟨hw2, hw3⟩ := primeJumpWeight_bounds
  rw [vonMangoldtAtom_three_eq]
  have hMaj : c₁ * witnessMajAnti 2 ≤ (10196 / 10000 : ℝ) := by unfold witnessMajAnti; norm_num
  have hJ : biScaleLevyEnergy witness ≤ 10196 / 10000 + 2 * (86141 / 273000) *
      (2 * (1 / (17735 / 10000)) + (2 / 5) * (1 / (175 / 10)) / (1 - 1 / (989 / 100))) := by
    have h := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 2 * (86141 / 273000))
    rw [hA0] at hlevy
    linarith
  have hΓA : EF.gammaBracket 0 * autocorr witness 0 ≤ -(5370 / 1000) * (86141 / 273000) := by
    rw [hA0]; exact mul_le_mul_of_nonneg_right hΓ (by norm_num)
  have hw2A : 2 * ((693147 / 1000000 : ℝ) / (141422 / 100000) * (297 / 10000)) ≤
      2 * primeJumpWeight 2 * autocorr witness (Real.log 2) := by
    have h := mul_le_mul hw2 hA2 (by norm_num) (primeJumpWeight_nonneg 2)
    have e : 2 * primeJumpWeight 2 * autocorr witness (Real.log 2) =
        2 * (primeJumpWeight 2 * autocorr witness (Real.log 2)) := by ring
    rw [e]; linarith
  have hw3m : 2 * ((1098612 / 1000000 : ℝ) / (173206 / 100000) * (176 / 10000)) ≤
      2 * primeJumpWeight 3 * ∫ x in Icc (Real.log 3 - 287 / 500) (287 / 500), witness x ^ 2 := by
    have h := mul_le_mul hw3 hm (by norm_num) (primeJumpWeight_nonneg 3)
    have e : 2 * primeJumpWeight 3 *
        (∫ x in Icc (Real.log 3 - 287 / 500) (287 / 500), witness x ^ 2) =
        2 * (primeJumpWeight 3 *
          ∫ x in Icc (Real.log 3 - 287 / 500) (287 / 500), witness x ^ 2) := by ring
    rw [e]; linarith
  norm_num at hJ hΓA hw2A hw3m hS
  linarith

/-! ### 10. The collar bound behind the certificate -/

/-- For odd `F` vanishing outside `[−c, c]`, the prime-`ℓ` correlation is bounded by the collar mass:
`|∫ F(t) F(t + ℓ) dt| ≤ ∫_{[ℓ − c, c]} F²`. This is what makes the sliver-potential certificate the
natural local certificate for the kick of `ℓ`. -/
theorem abs_autocorr_le_collarMass {F : ℝ → ℝ} (hF : Continuous F) {c ℓ : ℝ}
    (hodd : ∀ x, F (-x) = -F x) (hFs : ∀ x, c < |x| → F x = 0) :
    |autocorr F ℓ| ≤ ∫ x in Icc (ℓ - c) c, F x ^ 2 := by
  let g : ℝ → ℝ := (Icc (ℓ - c) c).indicator fun v => F v ^ 2
  have hg0 : ∀ v, 0 ≤ g v := fun v => indicator_nonneg (fun w _ => sq_nonneg (F w)) v
  have hgi : Integrable g := ((hF.pow 2).integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hg1 : Integrable fun t => g (-t) := hgi.comp_neg
  have hg2 : Integrable fun t => g (t + ℓ) := hgi.comp_add_right ℓ
  have hpt : ∀ t, |F t * F (t + ℓ)| ≤ (g (-t) + g (t + ℓ)) / 2 := by
    intro t
    by_cases h : F t * F (t + ℓ) = 0
    · rw [h, abs_zero]; linarith [hg0 (-t), hg0 (t + ℓ)]
    · have ht : |t| ≤ c := by
        by_contra hc; rw [hFs t (not_le.mp hc), zero_mul] at h; exact h rfl
      have htl : |t + ℓ| ≤ c := by
        by_contra hc; rw [hFs (t + ℓ) (not_le.mp hc), mul_zero] at h; exact h rfl
      have h1 : -t ∈ Icc (ℓ - c) c := by
        constructor <;> linarith [(abs_le.mp ht).1, (abs_le.mp ht).2, (abs_le.mp htl).2]
      have h2 : t + ℓ ∈ Icc (ℓ - c) c := by
        constructor <;> linarith [(abs_le.mp ht).1, (abs_le.mp htl).2]
      have e1 : g (-t) = F t ^ 2 := by
        rw [show g (-t) = F (-t) ^ 2 from indicator_of_mem h1 _, hodd, neg_sq]
      have e2 : g (t + ℓ) = F (t + ℓ) ^ 2 := indicator_of_mem h2 _
      rw [e1, e2, abs_mul]
      nlinarith [sq_nonneg (|F t| - |F (t + ℓ)|), sq_abs (F t), sq_abs (F (t + ℓ))]
  have hi1 : (∫ t, g (-t)) = ∫ t, g t := integral_neg_eq_self g volume
  have hi2 : (∫ t, g (t + ℓ)) = ∫ t, g t := integral_add_right_eq_self g ℓ
  have hmass : (∫ t, g t) = ∫ x in Icc (ℓ - c) c, F x ^ 2 := integral_indicator measurableSet_Icc
  calc |autocorr F ℓ| = |∫ t, F t * F (t + ℓ)| := rfl
    _ ≤ ∫ t, |F t * F (t + ℓ)| := abs_integral_le_integral_abs
    _ ≤ ∫ t, (g (-t) + g (t + ℓ)) / 2 :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          ((hg1.add hg2).div_const 2) (Eventually.of_forall hpt)
    _ = ∫ x in Icc (ℓ - c) c, F x ^ 2 := by
        rw [MeasureTheory.integral_div, integral_add hg1 hg2, hi1, hi2, hmass]; ring

/-! ### 11. Mollification and the failure of the certificate -/

lemma mollifier_even'' (k : ℕ) (t : ℝ) :
    CHMDDoobGraph.mollifier k (-t) = CHMDDoobGraph.mollifier k t := by
  unfold CHMDDoobGraph.mollifier
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, ContDiffBump.neg]

lemma smooth_odd' {G : ℝ → ℝ} (hodd : ∀ x, G (-x) = -G x) (k : ℕ) (x : ℝ) :
    CHMDDoobGraph.smooth G k (-x) = -CHMDDoobGraph.smooth G k x := by
  change (∫ t, CHMDDoobGraph.mollifier k t * G (-x - t)) =
    -(∫ t, CHMDDoobGraph.mollifier k t * G (x - t))
  rw [← integral_neg_eq_self (fun t => CHMDDoobGraph.mollifier k t * G (-x - t)) volume,
    ← MeasureTheory.integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [mollifier_even'', show -x - -t = -(x - t) by ring, hodd, mul_neg]

/-- Mollification at level `k ≥ 249` widens the support by at most `1/1000`. -/
lemma smooth_eq_zero_of_narrow' {G : ℝ → ℝ} {R : ℝ} (hR : ∀ x, R ≤ |x| → G x = 0)
    {k : ℕ} (hk : 249 ≤ k) {x : ℝ} (hx : R + 1 / 1000 < |x|) :
    CHMDDoobGraph.smooth G k x = 0 := by
  have hkr : (249 : ℝ) ≤ k := by exact_mod_cast hk
  have hrad : 1 / (4 * ((k : ℝ) + 1)) ≤ (1 / 1000 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  change (∫ t, CHMDDoobGraph.mollifier k t * G (x - t)) = 0
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  dsimp only [Pi.zero_apply]
  by_cases ht : 1 / (4 * ((k : ℝ) + 1)) ≤ |t|
  · have hm : CHMDDoobGraph.mollifier k t = 0 := by
      apply Function.notMem_support.mp
      change t ∉ Function.support ((_root_.RHTower.WeilOneSided.narrowBump k).normed volume)
      rw [(_root_.RHTower.WeilOneSided.narrowBump k).support_normed_eq, Metric.mem_ball,
        dist_zero_right, Real.norm_eq_abs]
      exact not_lt.mpr ht
    rw [hm, zero_mul]
  · have hsub : R ≤ |x - t| := by linarith [abs_sub_abs_le_abs_sub x t, not_le.mp ht]
    rw [hR (x - t) hsub, mul_zero]

private lemma collarMass_smooth_tendsto (a b : ℝ) :
    Tendsto (fun k : ℕ => ∫ x in Icc a b, CHMDDoobGraph.smooth witness k x ^ 2) atTop
      (𝓝 (∫ x in Icc a b, witness x ^ 2)) := by
  have hf2 : MemLp witness 2 volume := continuous_witness.memLp_of_hasCompactSupport compact_witness
  refine tendsto_integral_of_dominated_convergence (fun _ => (43 / 4 : ℝ) ^ 2) (fun k => ?_)
    (continuous_const.integrableOn_Icc) (fun k => ?_) ?_
  · exact ((CHMDDoobGraph.smooth_contDiff hf2 k).continuous.pow 2).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (CHMDDoobGraph.smooth_bound (by norm_num) abs_witness_le k x) 2
  · exact Eventually.of_forall fun x => (smooth_tendsto_of_continuous continuous_witness x).pow 2

/-- **The sliver-potential certificate fails on an explicit odd test.** There is an odd `C²` test
`F` supported in `[−287/500, 287/500]` with
`W(F) + 2w₃ ∫ F(t) F(t + log 3) dt < 2w₃ ∫_{[log 3 − 287/500, 287/500]} F²`. -/
theorem exists_odd_test_sliverPotential_fails :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧ (∀ x, F (-x) = -F x) ∧
      (∀ x, 287 / 500 < |x| → F x = 0) ∧
      weilQuad F + 2 * vonMangoldtAtom 3 * autocorr F (Real.log 3) <
        2 * vonMangoldtAtom 3 * ∫ x in Icc (Real.log 3 - 287 / 500) (287 / 500), F x ^ 2 := by
  have hf2 : MemLp witness 2 volume := continuous_witness.memLp_of_hasCompactSupport compact_witness
  have hQ : Tendsto (fun k : ℕ => weilQuad (CHMDDoobGraph.smooth witness k)) atTop
      (𝓝 (weilQuad witness)) :=
    re_weilFullFunctional_smooth_tendsto ccWitness witness_levy_le.1
  have hA : Tendsto (fun k : ℕ => autocorr (CHMDDoobGraph.smooth witness k) (Real.log 3)) atTop
      (𝓝 (autocorr witness (Real.log 3))) :=
    autocorr_smooth_tendsto continuous_witness abs_witness_le
      (fun x hx => witness_eq_zero_of_far hx.le) (Real.log 3)
  have hM := collarMass_smooth_tendsto (Real.log 3 - 287 / 500) (287 / 500)
  have hlim := (hQ.add (hA.const_mul (2 * vonMangoldtAtom 3))).sub
    (hM.const_mul (2 * vonMangoldtAtom 3))
  have hgap := witness_gap
  have hev := hlim.eventually (Iio_mem_nhds (show
    weilQuad witness + 2 * vonMangoldtAtom 3 * autocorr witness (Real.log 3) -
      2 * vonMangoldtAtom 3 * (∫ x in Icc (Real.log 3 - 287 / 500) (287 / 500), witness x ^ 2) < 0
    by linarith))
  obtain ⟨k, hk, hneg⟩ := ((eventually_ge_atTop 249).and hev).exists
  refine ⟨CHMDDoobGraph.smooth witness k, (CHMDDoobGraph.smooth_contDiff hf2 k).of_le (by simp),
    CHMDDoobGraph.smooth_compact compact_witness k, smooth_odd' witness_odd k,
    fun x hx => smooth_eq_zero_of_narrow' (R := c₁) (fun y hy => witness_eq_zero_of_far hy) hk
      (by rw [show c₁ + 1 / 1000 = 287 / 500 by norm_num]; exact hx), ?_⟩
  have h : weilQuad (CHMDDoobGraph.smooth witness k) +
      2 * vonMangoldtAtom 3 * autocorr (CHMDDoobGraph.smooth witness k) (Real.log 3) -
      2 * vonMangoldtAtom 3 * (∫ x in Icc (Real.log 3 - 287 / 500) (287 / 500),
        CHMDDoobGraph.smooth witness k x ^ 2) < 0 := hneg
  linarith

/-- **No window of half-width `c ≥ 287/500` admits the sliver-potential certificate of the prime `3`**:
it is not true that `2w₃ ∫_{[log 3 − c, c]} F² ≤ W(F) + 2w₃ ∫ F(t) F(t + log 3) dt` for every odd
`C²` test supported in `[−c, c]`. In particular it fails on the windows
`c ∈ [287/500, ½ log 3 + 1/40]`, where the prime `3` is collar-unpaid
(`exists_prime_three_collar_unpaid`). -/
theorem not_sliverPotentialCertificate {c : ℝ} (hc : 287 / 500 ≤ c) :
    ¬ ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) →
        (∀ x, c < |x| → F x = 0) →
        2 * vonMangoldtAtom 3 * ∫ x in Icc (Real.log 3 - c) c, F x ^ 2 ≤
          weilQuad F + 2 * vonMangoldtAtom 3 * autocorr F (Real.log 3) := by
  intro hcert
  obtain ⟨F, hF, hFc, hFo, hFs, hgap⟩ := exists_odd_test_sliverPotential_fails
  have h := hcert F hF hFc hFo (fun x hx => hFs x (by linarith))
  have hsub : Icc (Real.log 3 - 287 / 500) (287 / 500) ⊆ Icc (Real.log 3 - c) c :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hint : IntegrableOn (fun x => F x ^ 2) (Icc (Real.log 3 - c) c) :=
    (hF.continuous.pow 2).integrableOn_Icc
  have hmono := setIntegral_mono_set (s := Icc (Real.log 3 - 287 / 500) (287 / 500)) hint
    (ae_restrict_of_forall_mem measurableSet_Icc fun x _ => sq_nonneg (F x))
    (Eventually.of_forall hsub)
  have hw : 0 ≤ vonMangoldtAtom 3 := RHTower.vonMangoldtAtom_nonneg' 3
  have := mul_le_mul_of_nonneg_left hmono (by linarith : (0 : ℝ) ≤ 2 * vonMangoldtAtom 3)
  linarith

end GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry

end

#print axioms GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry.not_sliverPotentialCertificate
