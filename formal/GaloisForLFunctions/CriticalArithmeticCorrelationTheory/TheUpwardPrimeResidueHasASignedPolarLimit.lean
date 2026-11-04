import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheLogarithmicHorizonMeanIsPolar
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheDivisorJetHasAPolarNearMean
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheNonRatioPrimesOnConductorPackets

/-!
# The signed polar residue of the upward prime operator

At growing overlap, the logarithmic horizon mean and the conductor-lowering
jet cancel every off-diagonal harmonic Gram finite part. The remaining
signed residue is supported on the conductor-one pair and has coefficient
`-(γ + 1)` times the normalized squared integral of the test function.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedIntersectionTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CompletedArithmeticForms
  SpacingScaleHarmonicAnalysis BezoutValuationIncidence ArithmeticElectrostatics
  ArithmeticIntersectionTheory SignedArithmeticHodgeTheory

private def conductorGramFinitePart (m l : ℕ) : ℝ :=
  if m = l then Real.eulerMascheroniConstant - Real.log m + tameDifferent m
  else -(if l ∣ m then Real.sqrt ((l.totient : ℝ) / m.totient) *
      (ArithmeticFunction.vonMangoldt (m / l) : ℝ)
    else if m ∣ l then Real.sqrt ((m.totient : ℝ) / l.totient) *
      (ArithmeticFunction.vonMangoldt (l / m) : ℝ)
    else 0)

private theorem log_mul_gram_sub_diag_eq {m l N : ℕ} (hm : 0 < m) (hl : 0 < l)
    (hml : m * l ≤ N) (hL : 0 < Real.log N) :
    Real.log N * (⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
      (if m = l then 1 else 0)) = conductorGramFinitePart m l +
        Real.log N * conductorGramFloorError m l N := by
  rw [normalizedRamanujanHorizonVector_gram_exact hm hl hml hL]
  unfold conductorGramFinitePart
  split_ifs <;> field_simp [hL.ne'] <;> ring

private theorem tendsto_log_mul_gram_sub_diag {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => Real.log N *
      (⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
        (if m = l then 1 else 0))) atTop (𝓝 (conductorGramFinitePart m l)) := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun N : ℕ => Real.log N * conductorGramFloorError m l N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat
      (4 * (floorAmplitude m * floorAmplitude l)))
    filter_upwards [eventually_ge_atTop (m * l), hlog.eventually_gt_atTop 0] with N hml hL
    simp only [Function.comp_apply] at hL
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hL]
    calc
      _ ≤ Real.log N * (4 / ((N : ℝ) * Real.log N) * (floorAmplitude m * floorAmplitude l)) :=
        mul_le_mul_of_nonneg_left (abs_conductorGramFloorError_le hm hl hml hL) hL.le
      _ = _ := by field_simp [hL.ne']
  have h := (tendsto_const_nhds (x := conductorGramFinitePart m l)).add hz
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (m * l), hlog.eventually_gt_atTop 0] with N hml hL
  exact (log_mul_gram_sub_diag_eq hm hl hml hL).symm

private theorem conductorGramFinitePart_polar (l : ℕ) :
    conductorGramFinitePart 1 l = if l = 1 then Real.eulerMascheroniConstant
      else -(ArithmeticFunction.vonMangoldt l : ℝ) / Real.sqrt (l.totient : ℝ) := by
  by_cases hl1 : l = 1
  · subst l
    simp [conductorGramFinitePart, tameDifferent]
  have h1l : 1 ≠ l := Ne.symm hl1
  have hnot : ¬l ∣ 1 := fun h => hl1 (Nat.dvd_one.mp h)
  simp only [conductorGramFinitePart, if_neg h1l, if_neg hnot, if_pos (one_dvd l),
    Nat.totient_one, Nat.cast_one, Nat.div_one, if_neg hl1]
  rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
  ring

private def upwardLogPair (φ : ℝ → ℝ) (c : ℝ) (N m l : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
    fixedWidthNearPair φ (c / N) m l n j * (Real.log N - Real.log j)

private def upwardJetPair (φ : ℝ → ℝ) (c : ℝ) (N m l : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, fixedWidthNearJetPair φ (c / N) m l n j

private def upwardExteriorPair (φ : ℝ → ℝ) (c : ℝ) (N m l : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n *
    (regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n /
      Real.sqrt (l.totient : ℝ))

private theorem upward_residual_eq_raw_pairs {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N m l : ℕ} (hN : 1 ≤ N) (hL : 0 < Real.log N) (hl : 0 < l) :
    ⟪upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
        shellCorrection φ c m • normalizedRamanujanHorizonVector m N,
      normalizedRamanujanHorizonVector l N⟫ =
      (Real.log N * fixedWidthNearGram φ (c / N) N m l - upwardLogPair φ c N m l -
        upwardJetPair φ c N m l + upwardExteriorPair φ c N m l) / Real.log N -
      shellCorrection φ c m *
        ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  obtain ⟨_, hgsupp, _⟩ := atomDilate_facts hφ hsupp hw
  have hprofile (j : ℕ) : ramanujanPoleProfile l j =
      ramanujanLagCoefficient l j / Real.sqrt (l.totient : ℝ) / Real.sqrt j := by
    rw [ramanujanPoleProfile, normalizedRamanujanMode,
      TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hl]
  have hdown : ∀ n ∈ Icc 1 N,
      primeHorizonExtension (downwardPrimeVector φ c N (normalizedRamanujanHorizonVector l N)) n =
        (Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
          (interiorDownwardPrimeRow (atomDilate φ (c / N)) N l n +
            regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n) := by
    intro n hn
    rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    change downwardPrimeRow (atomDilate φ (c / N)) N
        (primeHorizonExtension (normalizedRamanujanHorizonVector l N)) n /
        (∫ u, (atomDilate φ (c / N)) u ^ 2) = _
    have hvl : ∀ j ∈ Icc 1 N,
        primeHorizonExtension (normalizedRamanujanHorizonVector l N) j =
          (Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
            (ramanujanLagCoefficient l j / Real.sqrt j) := by
      intro j hj
      rw [primeHorizonExtension_normalizedRamanujan hj, hprofile, mul_inv]
      ring
    rw [downwardPrimeRow_congr_smul hvl, mul_div_assoc]
    congr 1
    have h := downwardRamanujanRow_sub_interior_eq hc hn hgsupp l
    linarith only [h]
  have hinterior : ∀ n ∈ Icc 1 N,
      ramanujanPoleProfile m n / Real.sqrt (l.totient : ℝ) *
        interiorDownwardPrimeRow (atomDilate φ (c / N)) N l n =
      ∑ j ∈ Icc 1 N, (Real.log j * fixedWidthNearPair φ (c / N) m l n j -
        fixedWidthNearJetPair φ (c / N) m l n j) := by
    intro n hn
    rw [interiorDownwardPrimeRow_eq_divisors, mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet l (mem_Icc.mp hj).1]
    by_cases hnear : j ≠ n ∧ |Real.log j - Real.log n| ≤ 2 * (c / N)
    · rw [fixedWidthNearPair, fixedWidthNearJetPair, if_pos hnear, if_pos hnear,
        if_neg hnear.1, normalized_bumpCorr_atomDilate hw, hprofile]
      ring
    · rw [fixedWidthNearPair, fixedWidthNearJetPair, if_neg hnear, if_neg hnear]
      by_cases hjeq : j = n
      · rw [if_pos hjeq]
        ring
      · have hgap : c / N < |Real.log j - Real.log n| := by
          have hgt : 2 * (c / N) < |Real.log j - Real.log n| :=
            lt_of_not_ge fun h => hnear ⟨hjeq, h⟩
          linarith only [hgt, hw]
        rw [if_neg hjeq, bumpCorr_eq_zero hgsupp hgap]
        ring
  have hraw : (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n / Real.sqrt (l.totient : ℝ) *
      interiorDownwardPrimeRow (atomDilate φ (c / N)) N l n) =
      Real.log N * fixedWidthNearGram φ (c / N) N m l -
        upwardLogPair φ c N m l - upwardJetPair φ c N m l := by
    rw [sum_congr rfl hinterior]
    unfold fixedWidthNearGram upwardLogPair upwardJetPair
    simp only [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => sum_congr rfl fun j _ => by ring
  have hinner : ⟪normalizedRamanujanHorizonVector m N,
      downwardPrimeVector φ c N (normalizedRamanujanHorizonVector l N)⟫ =
      ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        primeHorizonExtension (downwardPrimeVector φ c N (normalizedRamanujanHorizonVector l N)) n := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ i : PrimeHorizonIndex N,
      downwardPrimeVector φ c N (normalizedRamanujanHorizonVector l N) i *
        normalizedRamanujanHorizonVector m N i) = _
    rw [← sum_coe_sort (Icc 1 N)]
    exact sum_congr rfl fun i _ => by
      rw [primeHorizonExtension_coe, primeHorizonExtension_coe, mul_comm]
  have hcancel : Real.log N * ((Real.sqrt (Real.log N))⁻¹ *
      (Real.sqrt (Real.log N))⁻¹) = 1 := by
    rw [← mul_inv, ← sq, Real.sq_sqrt hL.le, mul_inv_cancel₀ hL.ne']
  have hscaled : Real.log N * ⟪normalizedRamanujanHorizonVector m N,
      downwardPrimeVector φ c N (normalizedRamanujanHorizonVector l N)⟫ =
      Real.log N * fixedWidthNearGram φ (c / N) N m l - upwardLogPair φ c N m l -
        upwardJetPair φ c N m l + upwardExteriorPair φ c N m l := by
    rw [← hraw, hinner, mul_sum, upwardExteriorPair, ← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    rw [hdown n hn, primeHorizonExtension_normalizedRamanujan hn, mul_inv]
    calc
      _ = (Real.log N * ((Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹)) *
          (ramanujanPoleProfile m n / Real.sqrt (l.totient : ℝ) *
            (interiorDownwardPrimeRow (atomDilate φ (c / N)) N l n +
              regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n)) := by ring
      _ = _ := by rw [hcancel]; ring
  rw [inner_sub_left, real_inner_smul_left, upwardPrimeVector_inner_eq_downward hφ hsupp hc hN]
  congr 1
  apply (eq_div_iff hL.ne').2
  simpa only [mul_comm (Real.log N)] using hscaled

private theorem upwardExteriorPair_eq_nrExterior {φ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {N m l : ℕ} (hN : 1 ≤ N) (hm : 0 < m) :
    upwardExteriorPair φ c N m l =
      ArithmeticHodgeTheoryOfDegenerations.nrExterior φ c N l m /
        (Real.sqrt (l.totient : ℝ) * Real.sqrt (m.totient : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  simp only [upwardExteriorPair, regroupedExteriorDownwardPrimeRow,
    ArithmeticHodgeTheoryOfDegenerations.nrExterior, sum_div, mul_sum]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro j hj
  rw [ramanujanPoleProfile, normalizedRamanujanMode,
    TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hm,
    ArithmeticHodgeTheoryOfDegenerations.bumpCorr_atomDilate_eq φ hw,
    integral_atomDilate_sq hw]
  field_simp [hw.ne']

private theorem upward_clock_error_bound {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => c N ^ 4 * Real.log N / N) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun N => by
    have := Real.log_natCast_nonneg N
    positivity) _ he
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with N hL
  simp only [Function.comp_apply] at hL
  have hLL : Real.log N ≤ Real.log N ^ 2 := by nlinarith only [hL]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hLL (pow_nonneg (zero_le_one.trans (hc N)) 4)) (Nat.cast_nonneg N)

private theorem tendsto_upwardExteriorPair_div_overlap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N ^ 2 / N) atTop (𝓝 0))
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => upwardExteriorPair φ (c N) N m l / c N) atTop (𝓝 0) := by
  have he1 := upward_clock_error_bound hc he
  let S : ℝ := ∑ t ∈ m.divisors, (t : ℝ)
  let D : ℝ := Real.sqrt (l.totient : ℝ) * Real.sqrt (m.totient : ℝ)
  let K : ℝ := 12 * S * l.totient * (1 + Real.log 4) / D
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hD : 0 < D := by
    have hmφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
    have hlφ : (0 : ℝ) < l.totient := by exact_mod_cast Nat.totient_pos.mpr hl
    dsimp [D]
    positivity
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlim : Tendsto (fun N : ℕ => K * (c N ^ 4 * Real.log N ^ 2 / N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul K
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    he1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN hL heN
  simp only [Function.comp_apply] at hL
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hL0 : 0 ≤ Real.log N := zero_le_one.trans hL
  have h14 : c N ≤ c N ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ (hc N) (by norm_num : 1 ≤ 4)
  have hLL : Real.log N ≤ Real.log N ^ 2 := by nlinarith only [hL]
  have hcN : c N ≤ N := by
    apply (div_le_one hN0).mp
    exact (div_le_div_of_nonneg_right
      (h14.trans (le_mul_of_one_le_right (by positivity) hL)) hN0.le).trans heN.le
  have hb := ArithmeticHodgeTheoryOfDegenerations.abs_nrExterior_le hφ hsupp hM hc0 hN hcN l m
  have hp : 2 * (2 * c N + 1) * (c N + 1) ≤ 12 * c N ^ 2 := by
    have h1 : 2 * c N + 1 ≤ 3 * c N := by linarith [hc N]
    have h2 : c N + 1 ≤ 2 * c N := by linarith [hc N]
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul h1 h2 (by positivity) (by positivity)) (by norm_num : (0 : ℝ) ≤ 2)
    exact (show 2 * (2 * c N + 1) * (c N + 1) = 2 * ((2 * c N + 1) * (c N + 1)) by ring).trans_le
      (h.trans_eq (by ring))
  have hlog : Real.log (4 * (N : ℝ)) ≤ (1 + Real.log 4) * Real.log N := by
    rw [Real.log_mul (by norm_num) hN0.ne']
    have h := mul_le_mul_of_nonneg_left hL hlog4
    nlinarith only [h]
  have hpoly : 2 * (2 * c N + 1) * (c N + 1) * S * l.totient * Real.log (4 * (N : ℝ)) ≤
      12 * c N ^ 2 * S * l.totient * ((1 + Real.log 4) * Real.log N) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hS) (Nat.cast_nonneg l.totient))
      hlog (Real.log_nonneg (by nlinarith only [hN0, (show (1 : ℝ) ≤ N by exact_mod_cast hN)]))
      (by positivity)
  rw [upwardExteriorPair_eq_nrExterior hc0 hN hm, Real.norm_eq_abs, abs_div, abs_div,
    abs_of_pos hD, abs_of_pos hc0]
  calc
    _ ≤ (2 * (2 * c N + 1) * (c N + 1) * S * l.totient * Real.log (4 * (N : ℝ)) / N) / D / c N :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hb hD.le) hc0.le
    _ ≤ (12 * c N ^ 2 * S * l.totient * ((1 + Real.log 4) * Real.log N) / N) / D / c N :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hpoly hN0.le) hD.le) hc0.le
    _ = K * (c N * Real.log N / N) := by dsimp only [K]; field_simp [hc0.ne']
    _ ≤ K * (c N ^ 4 * Real.log N ^ 2 / N) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (mul_le_mul h14 hLL hL0 (pow_nonneg hc0.le 4)) hN0.le) hK

/-- The signed upward-prime residue is supported only on the polar conductor pair. -/
theorem tendsto_upwardPrime_residual_signed_limit {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N ^ 2 / N) atTop (𝓝 0))
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => (Real.log N / c N) *
      ⟪upwardPrimeVector φ (c N) N (normalizedRamanujanHorizonVector m N) -
          shellCorrection φ (c N) m • normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫) atTop
      (𝓝 (if m = 1 ∧ l = 1 then -((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (Real.eulerMascheroniConstant + 1) else 0)) := by
  have he1 := upward_clock_error_bound hc he
  obtain ⟨C, hC, herr⟩ := exists_fixedWidthNearGram_shell_error hφ hsupp hM
  have hz : Tendsto (fun N : ℕ => (Real.log N / c N) *
      (fixedWidthNearGram φ (c N / N) N m l -
        (if m = l then shellCorrection φ (c N) m else 0))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => C * ((m : ℝ) * l) ^ 5 *
        (c N ^ 4 * Real.log N ^ 2 / N)) atTop (𝓝 0) := by
      simpa only [mul_zero] using he.const_mul (C * ((m : ℝ) * l) ^ 5)
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_nearGram_admissible hc he1 m l] with N hN
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
    have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg hL0, abs_of_pos hc0]
    calc
      _ ≤ (Real.log N / c N) *
          (C * ((m : ℝ) * l) ^ 5 * (c N ^ 5 * Real.log N / N)) :=
        mul_le_mul_of_nonneg_left (herr hm hl hN.1 hN.2.1 (hc N) hN.2.2) (by positivity)
      _ = _ := by field_simp [hc0.ne']
  have hsc := (tendsto_shellCorrection_div_overlap hφ hsupp hM hm).comp hcinf
  have hGram := tendsto_log_mul_gram_sub_diag hm hl
  have hfirst : Tendsto (fun N : ℕ => (Real.log N / c N) *
      (fixedWidthNearGram φ (c N / N) N m l - shellCorrection φ (c N) m *
        ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫)) atTop
      (𝓝 (-(if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0) * conductorGramFinitePart m l)) := by
    have h := hz.sub (hsc.mul hGram)
    simp only [zero_sub] at h
    rw [← neg_mul] at h
    apply h.congr
    intro N
    dsimp only [Function.comp_apply]
    split_ifs <;> ring
  have hlog : Tendsto (fun N : ℕ => upwardLogPair φ (c N) N m l / c N) atTop
      (𝓝 (if m = l then if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0 else 0)) :=
    tendsto_fixedWidthNearPair_log_row_div_overlap hφ hsupp hM hc hcinf he1 hm hl
  have hjet : Tendsto (fun N : ℕ => upwardJetPair φ (c N) N m l / c N) atTop
      (𝓝 (if m = 1 then ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (ArithmeticFunction.vonMangoldt l : ℝ) / Real.sqrt (l.totient : ℝ) else 0)) :=
    tendsto_fixedWidthNearJetPair_sum_div_overlap hφ hsupp hM hc hcinf he1 hm hl
  have hext := tendsto_upwardExteriorPair_div_overlap hφ hsupp hM hc he hm hl
  have hlim := ((hfirst.sub hlog).sub hjet).add hext
  have hconstant : (-(if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0) *
        conductorGramFinitePart m l -
      (if m = l then if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0 else 0) -
      (if m = 1 then ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (ArithmeticFunction.vonMangoldt l : ℝ) / Real.sqrt (l.totient : ℝ) else 0)) + 0 =
      (if m = 1 ∧ l = 1 then -((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (Real.eulerMascheroniConstant + 1) else 0) := by
    by_cases hm1 : m = 1
    · subst m
      rw [conductorGramFinitePart_polar]
      by_cases hl1 : l = 1
      · subst l
        simp
        ring
      · have h1l : 1 ≠ l := Ne.symm hl1
        simp [hl1, h1l]
        ring
    · simp [hm1]
  rw [hconstant] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0] with N hN hL
  simp only [Function.comp_apply] at hL
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  rw [upward_residual_eq_raw_pairs hφ hsupp hc0 hN hL hl]
  field_simp [hc0.ne', hL.ne']
  ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_upwardPrime_residual_signed_limit
