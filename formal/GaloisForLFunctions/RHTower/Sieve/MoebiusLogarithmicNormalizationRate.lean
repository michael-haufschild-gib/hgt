import GaloisForLFunctions.RHTower.Sieve.MoebiusLogarithmicNormalization

/-!
# Quantitative logarithmic Möbius normalization

The corpus's zero-free-region Mertens estimate gives a two-logarithm rate for
`-∑_{n ≤ N} μ(n) log n / n → 1`.  The proof keeps exact finite Abel sums and controls their
tails uniformly, which is the rate input required in Graham's hard Barban--Vehov range.
-/

namespace RHTower.Sieve

open ArithmeticFunction Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

private theorem moebiusLogHarmonicPartial_eq_abel (N : ℕ) :
    moebiusLogHarmonicPartial N =
      RHTower.deningerHarmonicPartial N * (-Real.log (N : ℝ)) +
        ∑ i ∈ Finset.range N, RHTower.deningerHarmonicPartial i *
          (Real.log ((i : ℝ) + 1) - Real.log (i : ℝ)) := by
  have habel := RHTower.deningerAbelSummation
    (fun n : ℕ => ((moebius n : ℤ) : ℝ) / (n : ℝ))
    (fun n : ℕ => -Real.log (n : ℝ)) N
  have hpartial : RHTower.deningerPartialSum
      (fun n : ℕ => ((moebius n : ℤ) : ℝ) / (n : ℝ)) N =
    RHTower.deningerHarmonicPartial N := by rfl
  rw [hpartial] at habel
  rw [moebiusLogHarmonicPartial]
  calc
    ∑ n ∈ Finset.range (N + 1), moebiusLogHarmonicTerm n =
        ∑ n ∈ Finset.range (N + 1),
          ((moebius n : ℤ) : ℝ) / (n : ℝ) * -Real.log (n : ℝ) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp [moebiusLogHarmonicTerm]
      · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
        rw [moebiusLogHarmonicTerm, Real.rpow_neg_one]
        field_simp
    _ = RHTower.deningerHarmonicPartial N * (-Real.log (N : ℝ)) +
        ∑ i ∈ Finset.range N, RHTower.deningerHarmonicPartial i *
          (-Real.log (i : ℝ) - -Real.log ((i + 1 : ℕ) : ℝ)) := habel
    _ = RHTower.deningerHarmonicPartial N * (-Real.log (N : ℝ)) +
        ∑ i ∈ Finset.range N, RHTower.deningerHarmonicPartial i *
          (Real.log ((i : ℝ) + 1) - Real.log (i : ℝ)) := by
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      push_cast
      ring

private theorem abs_harmonic_log_boundary_le {B : ℝ} (hB : 0 ≤ B) {N : ℕ}
    (hN : Real.exp 1 ≤ (N : ℝ))
    (hpartial : |RHTower.deningerHarmonicPartial N| ≤
      2 * B / (Real.log (N : ℝ)) ^ 4 + B / (3 * (Real.log (N : ℝ)) ^ 3)) :
    |RHTower.deningerHarmonicPartial N * (-Real.log (N : ℝ))| ≤
      (2 * B + B / 3) / (Real.log (N : ℝ)) ^ 2 := by
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hN
  have hlog0 : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  rw [abs_mul, abs_neg, abs_of_pos hlog0]
  have hmul := mul_le_mul_of_nonneg_right hpartial hlog0.le
  calc
    |RHTower.deningerHarmonicPartial N| * Real.log (N : ℝ) ≤
        (2 * B / (Real.log (N : ℝ)) ^ 4 +
          B / (3 * (Real.log (N : ℝ)) ^ 3)) * Real.log (N : ℝ) := hmul
    _ = 2 * B / (Real.log (N : ℝ)) ^ 3 +
          B / (3 * (Real.log (N : ℝ)) ^ 2) := by field_simp
    _ ≤ 2 * B / (Real.log (N : ℝ)) ^ 2 +
          B / (3 * (Real.log (N : ℝ)) ^ 2) := by
      have hp2 : 0 < (Real.log (N : ℝ)) ^ 2 := pow_pos hlog0 2
      have hp23 : (Real.log (N : ℝ)) ^ 2 ≤ (Real.log (N : ℝ)) ^ 3 := by
        calc
          (Real.log (N : ℝ)) ^ 2 ≤
              (Real.log (N : ℝ)) ^ 2 * Real.log (N : ℝ) :=
            le_mul_of_one_le_right (pow_nonneg hlog0.le 2) hlog
          _ = (Real.log (N : ℝ)) ^ 3 := by ring
      exact add_le_add
        (by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left
            (by simpa only [one_div] using one_div_le_one_div_of_le hp2 hp23)
            (mul_nonneg (by norm_num) hB))
        le_rfl
    _ = (2 * B + B / 3) / (Real.log (N : ℝ)) ^ 2 := by ring

private theorem abs_harmonic_log_increment_le {B : ℝ} (hB : 0 ≤ B) {N : ℕ}
    (hN : Real.exp 1 ≤ (N : ℝ))
    (hpartial : |RHTower.deningerHarmonicPartial N| ≤
      2 * B / (Real.log (N : ℝ)) ^ 4 + B / (3 * (Real.log (N : ℝ)) ^ 3)) :
    |RHTower.deningerHarmonicPartial N *
        (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ))| ≤
      (2 * B + B / 3) /
        ((N : ℝ) * (Real.log (N : ℝ)) ^ 3) := by
  have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hN1 : 1 < N := by exact_mod_cast (lt_of_lt_of_le he1 hN)
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hN
  have hlog0 : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hdiff0 : 0 ≤ Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log (by positivity) (by linarith))
  have hdiff := log_natCast_succ_sub_log_natCast_le_inv N (by omega)
  have hcollapse :
      2 * B / (Real.log (N : ℝ)) ^ 4 + B / (3 * (Real.log (N : ℝ)) ^ 3) ≤
        (2 * B + B / 3) / (Real.log (N : ℝ)) ^ 3 := by
    have hp3 : 0 < (Real.log (N : ℝ)) ^ 3 := pow_pos hlog0 3
    have hp34 : (Real.log (N : ℝ)) ^ 3 ≤ (Real.log (N : ℝ)) ^ 4 := by
      calc
        (Real.log (N : ℝ)) ^ 3 ≤
            (Real.log (N : ℝ)) ^ 3 * Real.log (N : ℝ) :=
          le_mul_of_one_le_right (pow_nonneg hlog0.le 3) hlog
        _ = (Real.log (N : ℝ)) ^ 4 := by ring
    have hfirst : 2 * B / (Real.log (N : ℝ)) ^ 4 ≤
        2 * B / (Real.log (N : ℝ)) ^ 3 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [one_div] using one_div_le_one_div_of_le hp3 hp34)
        (mul_nonneg (by norm_num) hB)
    calc
      2 * B / (Real.log (N : ℝ)) ^ 4 + B / (3 * (Real.log (N : ℝ)) ^ 3) ≤
          2 * B / (Real.log (N : ℝ)) ^ 3 + B / (3 * (Real.log (N : ℝ)) ^ 3) :=
        add_le_add hfirst le_rfl
      _ = (2 * B + B / 3) / (Real.log (N : ℝ)) ^ 3 := by ring
  rw [abs_mul, abs_of_nonneg hdiff0]
  calc
    |RHTower.deningerHarmonicPartial N| *
        (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) ≤
      ((2 * B + B / 3) / (Real.log (N : ℝ)) ^ 3) * (1 / (N : ℝ)) :=
        mul_le_mul (le_trans hpartial hcollapse) hdiff hdiff0 (by positivity)
    _ = (2 * B + B / 3) /
        ((N : ℝ) * (Real.log (N : ℝ)) ^ 3) := by ring

/-- Quantitative logarithmic normalization needed in Graham's hard Barban--Vehov range. -/
theorem exists_abs_moebiusLogHarmonicPartial_sub_one_log_sq_rate :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |moebiusLogHarmonicPartial N - 1| ≤ C / (Real.log (N : ℝ)) ^ 2 := by
  obtain ⟨B, hB, hpartial⟩ := exists_abs_deningerHarmonicPartial_log_rate
  rw [Filter.eventually_atTop] at hpartial
  obtain ⟨K, hK⟩ := hpartial
  let C : ℝ := 2 * B + B / 3
  refine ⟨4 * C, mul_nonneg (by norm_num) (by dsimp [C]; positivity), ?_⟩
  filter_upwards [eventually_ge_atTop K,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 1)] with N hNK hNe
  have hlogN : 1 ≤ Real.log (N : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hNe
  have hlogN0 : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlogN
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlimit : Tendsto (fun m : ℕ =>
      |moebiusLogHarmonicPartial N - moebiusLogHarmonicPartial (N + m)|)
      atTop (𝓝 |moebiusLogHarmonicPartial N - 1|) := by
    simpa only [Function.comp_apply, Nat.add_comm] using
      (((tendsto_const_nhds : Tendsto (fun _ : ℕ => moebiusLogHarmonicPartial N)
          atTop (𝓝 (moebiusLogHarmonicPartial N))).sub
        (tendsto_moebiusLogHarmonicPartial_one.comp (tendsto_add_atTop_nat N))).abs)
  apply le_of_tendsto' hlimit
  intro m
  let M := N + m
  have hNM : N ≤ M := by dsimp [M]; omega
  have hKM : K ≤ M := le_trans hNK hNM
  have hMe : Real.exp 1 ≤ (M : ℝ) := le_trans hNe (by exact_mod_cast hNM)
  have hlogM : 1 ≤ Real.log (M : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hMe
  have hlogM0 : 0 < Real.log (M : ℝ) := lt_of_lt_of_le zero_lt_one hlogM
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hNe
  have hlogNM : Real.log (N : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log hN0 (by exact_mod_cast hNM)
  have hdenNM : (Real.log (N : ℝ)) ^ 2 ≤ (Real.log (M : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hlogN0.le hlogNM 2
  have hrecipNM : C / (Real.log (M : ℝ)) ^ 2 ≤ C / (Real.log (N : ℝ)) ^ 2 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using
        one_div_le_one_div_of_le (pow_pos hlogN0 2) hdenNM) hC
  have hboundaryN :
      |RHTower.deningerHarmonicPartial N * (-Real.log (N : ℝ))| ≤
        C / (Real.log (N : ℝ)) ^ 2 := by
    exact abs_harmonic_log_boundary_le hB hNe (hK N hNK)
  have hboundaryM :
      |RHTower.deningerHarmonicPartial M * (-Real.log (M : ℝ))| ≤
        C / (Real.log (N : ℝ)) ^ 2 :=
    le_trans (abs_harmonic_log_boundary_le hB hMe (hK M hKM)) hrecipNM
  let t : ℕ → ℝ := fun i => RHTower.deningerHarmonicPartial i *
    (Real.log ((i : ℝ) + 1) - Real.log (i : ℝ))
  have hinterval : |∑ i ∈ Finset.Ico N M, t i| ≤
      2 * C / (Real.log (N : ℝ)) ^ 2 := by
    calc
      |∑ i ∈ Finset.Ico N M, t i| ≤ ∑ i ∈ Finset.Ico N M, |t i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ Finset.range m, |t (N + j)| := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [M, Nat.add_sub_cancel_left]
      _ ≤ ∑ j ∈ Finset.range m,
          C / (((N + j : ℕ) : ℝ) * (Real.log ((N + j : ℕ) : ℝ)) ^ 3) := by
        refine Finset.sum_le_sum fun j hj => ?_
        dsimp [t]
        exact abs_harmonic_log_increment_le hB
          (le_trans hNe (by exact_mod_cast (show N ≤ N + j by omega)))
          (hK (N + j) (le_trans hNK (by omega)))
      _ ≤ 2 * C / (Real.log (N : ℝ)) ^ 2 := by
        rcases m with _ | m
        · simp
          exact div_nonneg (mul_nonneg (by norm_num) hC) (pow_nonneg hlogN0.le 2)
        · rw [Finset.sum_range_succ']
          have htail := sum_one_div_mul_log_three_le hNe m
          have hmul := mul_le_mul_of_nonneg_left htail hC
          have hzero : C /
              ((N : ℝ) * (Real.log (N : ℝ)) ^ 3) ≤
                C / (Real.log (N : ℝ)) ^ 2 := by
            have hN1 : (1 : ℝ) ≤ (N : ℝ) :=
              le_trans (Real.one_le_exp zero_le_one) hNe
            have hden : (Real.log (N : ℝ)) ^ 2 ≤
                (N : ℝ) * (Real.log (N : ℝ)) ^ 3 := by
              have hlog3 : (Real.log (N : ℝ)) ^ 2 ≤
                  (Real.log (N : ℝ)) ^ 3 := by
                calc
                  (Real.log (N : ℝ)) ^ 2 ≤
                      (Real.log (N : ℝ)) ^ 2 * Real.log (N : ℝ) :=
                    le_mul_of_one_le_right (pow_nonneg hlogN0.le 2) hlogN
                  _ = (Real.log (N : ℝ)) ^ 3 := by ring
              exact le_trans hlog3
                (le_mul_of_one_le_left (pow_nonneg hlogN0.le 3) hN1)
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left
              (by simpa only [one_div] using
                one_div_le_one_div_of_le (pow_pos hlogN0 2) hden) hC
          have htail' : ∑ j ∈ Finset.range m,
              C / (((N + (j + 1) : ℕ) : ℝ) *
                (Real.log ((N + (j + 1) : ℕ) : ℝ)) ^ 3) ≤
              C / (2 * (Real.log (N : ℝ)) ^ 2) := by
            calc
              ∑ j ∈ Finset.range m,
                  C / (((N + (j + 1) : ℕ) : ℝ) *
                    (Real.log ((N + (j + 1) : ℕ) : ℝ)) ^ 3) =
                  C * ∑ j ∈ Finset.range m,
                    1 / (((N : ℝ) + ((j : ℝ) + 1)) *
                      (Real.log ((N : ℝ) + ((j : ℝ) + 1))) ^ 3) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun j hj => ?_
                push_cast
                ring
              _ ≤ C * (1 / (2 * (Real.log (N : ℝ)) ^ 2)) := hmul
              _ = C / (2 * (Real.log (N : ℝ)) ^ 2) := by ring
          calc
            (∑ j ∈ Finset.range m,
                  C / (((N + (j + 1) : ℕ) : ℝ) *
                    (Real.log ((N + (j + 1) : ℕ) : ℝ)) ^ 3)) +
                C / (((N + 0 : ℕ) : ℝ) * (Real.log ((N + 0 : ℕ) : ℝ)) ^ 3) ≤
              C / (2 * (Real.log (N : ℝ)) ^ 2) +
                C / (Real.log (N : ℝ)) ^ 2 :=
              add_le_add htail' (by simpa using hzero)
            _ ≤ 2 * C / (Real.log (N : ℝ)) ^ 2 := by
              have hden : 0 < (Real.log (N : ℝ)) ^ 2 := pow_pos hlogN0 2
              have hfrac : 0 ≤ C / (2 * (Real.log (N : ℝ)) ^ 2) := by positivity
              calc
                C / (2 * (Real.log (N : ℝ)) ^ 2) + C / (Real.log (N : ℝ)) ^ 2 ≤
                    C / (Real.log (N : ℝ)) ^ 2 + C / (Real.log (N : ℝ)) ^ 2 := by
                  gcongr
                  linarith
                _ = 2 * C / (Real.log (N : ℝ)) ^ 2 := by ring
  rw [moebiusLogHarmonicPartial_eq_abel N,
    moebiusLogHarmonicPartial_eq_abel M]
  have hsumdiff :
      (∑ i ∈ Finset.range N, t i) - ∑ i ∈ Finset.range M, t i =
        -(∑ i ∈ Finset.Ico N M, t i) := by
    rw [Finset.sum_Ico_eq_sub t hNM]
    ring
  change |(RHTower.deningerHarmonicPartial N * (-Real.log (N : ℝ)) +
      ∑ i ∈ Finset.range N, t i) -
    (RHTower.deningerHarmonicPartial M * (-Real.log (M : ℝ)) +
      ∑ i ∈ Finset.range M, t i)| ≤ _
  rw [show
      (RHTower.deningerHarmonicPartial N * (-Real.log (N : ℝ)) +
          ∑ i ∈ Finset.range N, t i) -
        (RHTower.deningerHarmonicPartial M * (-Real.log (M : ℝ)) +
          ∑ i ∈ Finset.range M, t i) =
        RHTower.deningerHarmonicPartial N * (-Real.log (N : ℝ)) -
          RHTower.deningerHarmonicPartial M * (-Real.log (M : ℝ)) -
            ∑ i ∈ Finset.Ico N M, t i by
      calc
        _ = RHTower.deningerHarmonicPartial N * (-Real.log (N : ℝ)) -
              RHTower.deningerHarmonicPartial M * (-Real.log (M : ℝ)) +
                ((∑ i ∈ Finset.range N, t i) - ∑ i ∈ Finset.range M, t i) := by ring
        _ = _ := by rw [hsumdiff]; ring]
  calc
    |RHTower.deningerHarmonicPartial N * (-Real.log (N : ℝ)) -
        RHTower.deningerHarmonicPartial M * (-Real.log (M : ℝ)) -
          ∑ i ∈ Finset.Ico N M, t i| ≤
      |RHTower.deningerHarmonicPartial N * (-Real.log (N : ℝ))| +
        |RHTower.deningerHarmonicPartial M * (-Real.log (M : ℝ))| +
          |∑ i ∈ Finset.Ico N M, t i| := by
      calc
        |_ - _ - _| ≤
            |RHTower.deningerHarmonicPartial N * (-Real.log (N : ℝ)) -
              RHTower.deningerHarmonicPartial M * (-Real.log (M : ℝ))| +
                |∑ i ∈ Finset.Ico N M, t i| := abs_sub _ _
        _ ≤ (|RHTower.deningerHarmonicPartial N * (-Real.log (N : ℝ))| +
              |RHTower.deningerHarmonicPartial M * (-Real.log (M : ℝ))|) +
                |∑ i ∈ Finset.Ico N M, t i| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ C / (Real.log (N : ℝ)) ^ 2 + C / (Real.log (N : ℝ)) ^ 2 +
          2 * C / (Real.log (N : ℝ)) ^ 2 :=
      add_le_add (add_le_add hboundaryN hboundaryM) hinterval
    _ = 4 * C / (Real.log (N : ℝ)) ^ 2 := by ring

end

end RHTower.Sieve
