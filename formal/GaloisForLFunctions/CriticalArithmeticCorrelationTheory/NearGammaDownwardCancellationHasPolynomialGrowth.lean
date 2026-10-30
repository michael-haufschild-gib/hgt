import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SmallWidthKeepsPrimeGeometryPolynomial
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheNearGammaDownwardCancellationIsUniformOnBoundedOverlap

/-!
# Near-Gamma/downward cancellation has polynomial growth

The Mangoldt divisor identity cancels the near-pair logarithm. At small
physical width the remaining numerator is linear in overlap, and near-row
geometry gives a fifth-power squared-mass bound. Exterior products occupy
a linear strip and have cubic squared mass. These are bounds on the full
signed downward source, including exterior products and all prime powers.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

/-- Exact logarithmic cancellation leaves a coefficient growing at most linearly in overlap. -/
theorem exists_nearGammaDownwardCoefficient_polynomial_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (m : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 1 ≤ N → c / N ≤ 1 / 3 →
      ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
        |nearGammaDownwardCoefficient φ c N m n j| ≤ E * c := by
  obtain ⟨C, hC, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  let R : ℝ := 2 * Real.exp 2
  let A : ℝ := m.totient
  let J := ramanujanJetBound m
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hJ : 0 ≤ J := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(C + R + 1) * A + J, by positivity, ?_⟩
  intro c hc1 N hN hw1 n hn j hj
  have hc : 0 < c := zero_lt_one.trans_le hc1
  let B := linearNearRowRadius c
  have hB : 0 ≤ B := by dsimp only [B, linearNearRowRadius]; positivity
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hlogc : |Real.log c| ≤ c := by
    rw [abs_of_nonneg (Real.log_nonneg hc1)]
    exact (Real.log_le_sub_one_of_pos hc).trans (by linarith only [hc])
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hjN := (mem_filter.mp hj).1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
  have hw0 : 0 < c / N := div_pos hc hN0
  have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
    have h := (mem_filter.mp hj).2.2
    change |Real.log j - Real.log n| ≤ 2 * c / N at h
    simpa only [mul_div_assoc] using h
  let q := shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)
  let a := atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2)
  have hrem : |a - Real.log (1 / (c / N)) * q| ≤ C := by
    simpa only [a, q, mul_div_assoc] using hpair (c / N) hw0 hw1 n j hs
  have hq : |q| ≤ 1 := by
    have h := abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp)
      (|Real.log j - Real.log n| / (c / N))
    change |shellAutocorr φ (|Real.log j - Real.log n| / (c / N))| ≤ ∫ u, φ u ^ 2 at h
    dsimp only [q]
    rw [abs_div, abs_of_pos hM, div_le_one hM]
    exact h
  have hcm : |ramanujanLagCoefficient m j| ≤ A :=
    BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m j
  have hjb : |ramanujanLogDivisorJet m j| ≤ J := abs_ramanujanLogDivisorJet_le m j
  have hquot : (N : ℝ) / j ≤ B :=
    (div_le_iff₀ hj0).mpr (nearRow_geometry_small_width hc hn hj hw).2.2
  have hloglow : 0 ≤ Real.log N - Real.log j := sub_nonneg.mpr
    (Real.log_le_log hj0 (by exact_mod_cast (mem_Icc.mp hjN).2))
  have hloghigh : Real.log N - Real.log j ≤ B := by
    have h := Real.log_le_sub_one_of_pos (div_pos hN0 hj0)
    rw [Real.log_div hN0.ne' hj0.ne'] at h
    linarith only [h, hquot]
  have hlogeq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
    rw [one_div, Real.log_inv, Real.log_div hc.ne' hN0.ne']
    ring
  have hlog : |Real.log (1 / (c / N)) - Real.log j| ≤ B + |Real.log c| := by
    rw [hlogeq, show Real.log N - Real.log c - Real.log j =
      (Real.log N - Real.log j) - Real.log c by ring]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hloglow]; linarith only [hloghigh])
  have heq : nearGammaDownwardCoefficient φ c N m n j =
      (a - Real.log (1 / (c / N)) * q) * ramanujanLagCoefficient m j +
      (Real.log (1 / (c / N)) - Real.log j) * q * ramanujanLagCoefficient m j +
      q * ramanujanLogDivisorJet m j := by
    rw [nearGammaDownwardCoefficient, sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m
      (mem_Icc.mp hjN).1]
    dsimp only [a, q]
    ring
  rw [heq]
  calc
    _ ≤ |(a - Real.log (1 / (c / N)) * q) * ramanujanLagCoefficient m j| +
        |(Real.log (1 / (c / N)) - Real.log j) * q * ramanujanLagCoefficient m j| +
        |q * ramanujanLogDivisorJet m j| := abs_add_three _ _ _
    _ ≤ C * A + (B + |Real.log c|) * A + J := by
      simp only [abs_mul]
      have h1 := mul_le_mul hrem hcm (abs_nonneg _) hC
      have h2 := mul_le_mul (mul_le_mul hlog hq (abs_nonneg _) (by positivity))
        hcm (abs_nonneg _) (by positivity)
      have h3 := mul_le_mul hq hjb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simp only [mul_one, one_mul] at h2 h3
      linarith only [h1, h2, h3]
    _ ≤ _ := by
      have hlog := mul_le_mul_of_nonneg_right hlogc hA
      have hCmul := mul_le_mul_of_nonneg_left hc1 (mul_nonneg hC hA)
      have hJmul := mul_le_mul_of_nonneg_left hc1 hJ
      dsimp only [B, linearNearRowRadius, R]
      nlinarith only [hlog, hCmul, hJmul]

/-- Interior near-Gamma cancellation has fifth-power overlap growth in squared row mass. -/
theorem exists_nearGammaDownwardRow_sq_polynomial_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 1 ≤ N → c / N ≤ 1 / 3 →
      (∑ n ∈ Icc 1 N, nearGammaDownwardRow φ c N m n ^ 2) ≤ C * c ^ 5 := by
  obtain ⟨E, hE, hbound⟩ := exists_nearGammaDownwardCoefficient_polynomial_bound hφ hsupp hM m
  refine ⟨4 * (2 * Real.exp 2) ^ 3 * E ^ 2, by positivity, ?_⟩
  intro c hc N hN hw
  have hb := sum_near_div_sqrt_sq_le_small_width (zero_lt_one.trans_le hc) hN
    (hw.trans (by norm_num)) (nearGammaDownwardCoefficient φ c N m) (hbound c hc N hN hw)
  exact hb.trans_eq (by unfold linearNearRowRadius; ring)

/-- Bounded product count and `log ℓ/√ℓ≤2` give a uniform row bound. -/
theorem abs_regroupedExteriorDownwardPrimeRow_le_small_width {g : ℝ → ℝ} (hg : Continuous g)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0)
    (hG : 0 < ∫ u, g u ^ 2) (hw : c / N ≤ 1) (m n : ℕ) :
    |regroupedExteriorDownwardPrimeRow g c N m n| ≤
      2 * m.totient * linearPrimeStrip c := by
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
  have hterm : ∀ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
      |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
        (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))| ≤ 2 * m.totient := by
    intro ℓ hℓ
    have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hN.trans (mem_Ioc.mp hℓ).1.le
    have hℓ0 : (0 : ℝ) < ℓ := zero_lt_one.trans_le hℓ1
    have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ0
    have hcorr : |bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2)| ≤ 1 := by
      rw [abs_div, abs_of_pos hG, div_le_one hG]
      exact abs_bumpCorr_le hg hgc _
    have hjet : |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ| ≤ 2 * m.totient := by
      rw [abs_div, abs_of_pos hs]
      calc
        _ ≤ (m.totient : ℝ) * Real.log ℓ / Real.sqrt ℓ :=
          div_le_div_of_nonneg_right (abs_horizonRamanujanMangoldt_le m N ℓ) hs.le
        _ = (m.totient : ℝ) * (Real.log ℓ * (Real.sqrt ℓ)⁻¹) := by ring
        _ ≤ (m.totient : ℝ) * 2 := mul_le_mul_of_nonneg_left
          (_root_.RHTower.WeilAbscissa.log_div_sqrt_le hℓ1) (Nat.cast_nonneg _)
        _ = _ := by ring
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul hjet hcorr (abs_nonneg _) (by positivity)
  have hcard : ((Ioc N (exteriorPrimeCutoff c N)).card : ℝ) ≤ linearPrimeStrip c := by
    have hbound := (exteriorPrimeCutoff_bounds_small_width hc hN hw).2
    rw [Nat.card_Ioc]
    exact_mod_cast (show exteriorPrimeCutoff c N - N ≤ linearPrimeStrip c by omega)
  unfold regroupedExteriorDownwardPrimeRow
  calc
    _ ≤ ∑ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
        |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
          (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ℓ ∈ Ioc N (exteriorPrimeCutoff c N), 2 * (m.totient : ℝ) := sum_le_sum hterm
    _ ≤ _ := by
      rw [sum_const, nsmul_eq_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ 2 * (m.totient : ℝ))

/-- Rows outside the fixed boundary strip receive no exterior prime product. -/
theorem regroupedExteriorDownwardPrimeRow_eq_zero_small_width {g : ℝ → ℝ}
    {c : ℝ} (hc : 0 < c) {N n : ℕ} (hn : n ∈ Icc 1 N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0)
    (hw : c / N ≤ 1) (hout : n < N - linearPrimeStrip c) (m : ℕ) :
    regroupedExteriorDownwardPrimeRow g c N m n = 0 := by
  unfold regroupedExteriorDownwardPrimeRow
  apply sum_eq_zero
  intro ℓ hℓ
  have hgap : c / N < |Real.log ℓ - Real.log n| := by
    by_contra h
    exact (not_lt_of_ge (exterior_prime_near_boundary_small_width hc hn (mem_Ioc.mp hℓ).1
      (le_of_not_gt h) hw)) hout
  rw [bumpCorr_eq_zero hgsupp hgap, zero_div, mul_zero]

/-- The exterior action has uniformly bounded squared row mass. -/
theorem sum_regroupedExteriorDownwardPrimeRow_sq_le_small_width {g : ℝ → ℝ} (hg : Continuous g)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0)
    (hG : 0 < ∫ u, g u ^ 2) (hw : c / N ≤ 1) (m : ℕ) :
    (∑ n ∈ Icc 1 N, regroupedExteriorDownwardPrimeRow g c N m n ^ 2) ≤
      ((linearPrimeStrip c : ℝ) + 1) * (2 * m.totient * linearPrimeStrip c) ^ 2 := by
  let S := (Icc 1 N).filter (fun n => N - linearPrimeStrip c ≤ n)
  have hsub : S ⊆ Icc 1 N := filter_subset _ _
  have hrestrict : (∑ n ∈ Icc 1 N, regroupedExteriorDownwardPrimeRow g c N m n ^ 2) =
      ∑ n ∈ S, regroupedExteriorDownwardPrimeRow g c N m n ^ 2 := by
    symm
    apply sum_subset hsub
    intro n hn hnS
    have hout : n < N - linearPrimeStrip c := by
      exact lt_of_not_ge fun h => hnS (mem_filter.mpr ⟨hn, h⟩)
    rw [regroupedExteriorDownwardPrimeRow_eq_zero_small_width hc hn hgsupp hw hout m, zero_pow (by decide)]
  have hcard : (S.card : ℝ) ≤ (linearPrimeStrip c : ℝ) + 1 := by
    have hcontain : S ⊆ Icc (N - linearPrimeStrip c) N := fun n hn =>
      mem_Icc.mpr ⟨(mem_filter.mp hn).2, (mem_Icc.mp (mem_filter.mp hn).1).2⟩
    have hnat : S.card ≤ linearPrimeStrip c + 1 := by
      have h := card_le_card hcontain
      rw [Nat.card_Icc] at h
      omega
    exact_mod_cast hnat
  rw [hrestrict]
  calc
    _ ≤ ∑ _n ∈ S, (2 * (m.totient : ℝ) * linearPrimeStrip c) ^ 2 := by
      apply sum_le_sum
      intro n _
      have hb := abs_regroupedExteriorDownwardPrimeRow_le_small_width hg hc hN hgsupp hG hw m n
      have h := mul_self_le_mul_self (abs_nonneg _) hb
      simpa only [← sq, sq_abs] using h
    _ ≤ _ := by
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)

/-- The boundary estimate holds for the literal infinite prime-power source. -/
theorem sum_actualExteriorDownwardRow_sq_le_small_width {g : ℝ → ℝ} (hg : Continuous g)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0)
    (hG : 0 < ∫ u, g u ^ 2) (hw : c / N ≤ 1) (m : ℕ) :
    (∑ n ∈ Icc 1 N, actualExteriorDownwardRow g N m n ^ 2) ≤
      ((linearPrimeStrip c : ℝ) + 1) * (2 * m.totient * linearPrimeStrip c) ^ 2 := by
  have heq : (∑ n ∈ Icc 1 N, actualExteriorDownwardRow g N m n ^ 2) =
      ∑ n ∈ Icc 1 N, regroupedExteriorDownwardPrimeRow g c N m n ^ 2 := by
    exact sum_congr rfl fun n hn => congrArg (fun t : ℝ => t ^ 2)
      (downwardRamanujanRow_sub_interior_eq hc hn hgsupp m)
  rw [heq]
  exact sum_regroupedExteriorDownwardPrimeRow_sq_le_small_width hg hc hN hgsupp hG hw m

/-- A strip of width `ceil(ec)` has a linear overlap bound. -/
theorem linearPrimeStrip_le {c : ℝ} (hc : 1 ≤ c) :
    (linearPrimeStrip c : ℝ) ≤ (Real.exp 1 + 1) * c := by
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have h := (Nat.ceil_lt_add_one (show 0 ≤ c * Real.exp 1 by positivity)).le
  change (linearPrimeStrip c : ℝ) ≤ c * Real.exp 1 + 1 at h
  nlinarith only [h, hc]

/-- Every exterior product and prime power obeys a cubic squared-mass bound. -/
theorem sum_actualExteriorDownwardRow_sq_le_polynomial {g : ℝ → ℝ} (hg : Continuous g)
    {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hN : 1 ≤ N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0)
    (hG : 0 < ∫ u, g u ^ 2) (hw : c / N ≤ 1) (m : ℕ) :
    (∑ n ∈ Icc 1 N, actualExteriorDownwardRow g N m n ^ 2) ≤
      ((Real.exp 1 + 2) * (2 * m.totient * (Real.exp 1 + 1)) ^ 2) * c ^ 3 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hB := linearPrimeStrip_le hc
  have hB1 : (linearPrimeStrip c : ℝ) + 1 ≤ (Real.exp 1 + 2) * c := by
    nlinarith only [hB, hc]
  have hcoef : 2 * (m.totient : ℝ) * linearPrimeStrip c ≤
      2 * m.totient * ((Real.exp 1 + 1) * c) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  calc
    _ ≤ ((linearPrimeStrip c : ℝ) + 1) * (2 * m.totient * linearPrimeStrip c) ^ 2 :=
      sum_actualExteriorDownwardRow_sq_le_small_width hg hc0 hN hgsupp hG hw m
    _ ≤ ((Real.exp 1 + 2) * c) * (2 * m.totient * ((Real.exp 1 + 1) * c)) ^ 2 :=
      mul_le_mul hB1 (pow_le_pow_left₀ (by positivity) hcoef 2) (sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- Full near-Gamma/downward cancellation has a fifth-power overlap bound after normalization. -/
theorem exists_fullNearGammaDownward_norm_sq_polynomial_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 1 ≤ N → c / N ≤ 1 / 3 →
      ‖normalizedFullNearGammaDownwardVector φ c N m‖ ^ 2 ≤ C * c ^ 5 / Real.log N := by
  obtain ⟨A, hA, hnear⟩ := exists_nearGammaDownwardRow_sq_polynomial_bound hφ hsupp hM m
  let B : ℝ := (Real.exp 1 + 2) * (2 * m.totient * (Real.exp 1 + 1)) ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨2 * (A + B), by positivity, ?_⟩
  intro c hc N hN hw
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp (div_pos hc0 hN0)
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq (div_pos hc0 hN0)]
    exact mul_pos (div_pos hc0 hN0) hM
  have hnear' : ‖normalizedNearGammaDownwardVector φ c N m‖ ^ 2 ≤ A * c ^ 5 / Real.log N := by
    rw [normalizedNearGammaDownwardVector_norm_sq]
    exact div_le_div_of_nonneg_right (hnear c hc N hN hw) (Real.log_natCast_nonneg N)
  have hext : ‖normalizedExteriorDownwardVector φ c N m‖ ^ 2 ≤ B * c ^ 5 / Real.log N := by
    rw [normalizedExteriorDownwardVector_norm_sq]
    apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
    exact (sum_actualExteriorDownwardRow_sq_le_polynomial hg.continuous hc hN hgsupp hG
      (hw.trans (by norm_num)) m).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc (by norm_num : 3 ≤ 5)) hB)
  rw [normalizedFullNearGammaDownwardVector_eq_sub hφ hsupp hc0]
  have htriangle := norm_sub_le (normalizedNearGammaDownwardVector φ c N m)
    (normalizedExteriorDownwardVector φ c N m)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  have hdiff := sq_nonneg (‖normalizedNearGammaDownwardVector φ c N m‖ -
    ‖normalizedExteriorDownwardVector φ c N m‖)
  calc
    _ ≤ 2 * (‖normalizedNearGammaDownwardVector φ c N m‖ ^ 2 +
        ‖normalizedExteriorDownwardVector φ c N m‖ ^ 2) := by
      nlinarith only [hsq, hdiff]
    _ ≤ 2 * (A * c ^ 5 / Real.log N + B * c ^ 5 / Real.log N) :=
      mul_le_mul_of_nonneg_left (add_le_add hnear' hext) zero_le_two
    _ = _ := by ring

/-- The actual near-center block has the same fifth-power overlap control. -/
theorem exists_nearCenterVector_norm_sq_polynomial_bound {φ : ℝ → ℝ}
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 1 ≤ N → 2 * c ≤ (N : ℝ) →
      ‖nearCenterVector φ c N m‖ ^ 2 ≤ C * c ^ 5 / Real.log N := by
  let A := completeWeilPoleShift φ 1 * (1 + Real.exp (1 / 2)) *
    ∑ i ∈ range m, |normalizedRamanujanMode m i|
  refine ⟨4 * (2 * Real.exp 2) ^ 3 * A ^ 2, by positivity, ?_⟩
  intro c hc N hN hcN
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : c / N ≤ 1 := (div_le_one hN0).mpr (by linarith only [hcN, hc0])
  have hα : |completeWeilPoleShift φ c| = c * completeWeilPoleShift φ 1 := by
    rw [abs_of_nonneg (show 0 ≤ completeWeilPoleShift φ c by unfold completeWeilPoleShift; positivity)]
    unfold completeWeilPoleShift
    ring
  have hentry (n : ℕ) (hn : n ∈ Icc 1 N) (j : ℕ) (hj : j ∈ nearRowIndices c N n) :
      |completeWeilPoleShift φ c / N * archimedeanCenterKernel n j * normalizedRamanujanMode m j| ≤ A * c := by
    have h := abs_nearCenter_entry_le (φ := φ) hm hN hcN hn hj
    rw [hα] at h
    exact h.trans_eq (by dsimp only [A]; ring)
  rw [nearCenterVector_norm_sq]
  apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
  exact (sum_near_div_sqrt_sq_le_small_width hc0 hN hw
    (fun n j => completeWeilPoleShift φ c / N * archimedeanCenterKernel n j * normalizedRamanujanMode m j)
    hentry).trans_eq (by unfold linearNearRowRadius; ring)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_nearGammaDownwardCoefficient_polynomial_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_nearGammaDownwardRow_sq_polynomial_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_actualExteriorDownwardRow_sq_le_small_width

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_fullNearGammaDownward_norm_sq_polynomial_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_nearCenterVector_norm_sq_polynomial_bound
