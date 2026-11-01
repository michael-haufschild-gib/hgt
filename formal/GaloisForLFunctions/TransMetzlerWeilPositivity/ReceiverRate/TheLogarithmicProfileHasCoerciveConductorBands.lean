import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheLogarithmicProfileConfinesItsLowEnergyVectors

/-!
# Coercivity above the low conductor band

After removing the low conductor projection, the prime-packet energy grows as
one quarter of the logarithm of the conductor cutoff. Intermediate-band overlap
estimates control the signed terms for the smooth logarithmic profile.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped BigOperators RealInnerProductSpace Matrix Classical

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.LogarithmicConductorSplit

open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CriticalArithmeticCorrelationTheory
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

private theorem smooth_profile : ContDiff ℝ 2 zeroFreeLogProfile :=
  contDiff_zeroFreeLogProfile.of_le (natCast_le_infty 2)

/-- Exact complete-Weil quadratic reduction on `conductorSubspace R' N ⊓ (conductorSubspace 1 N)ᗮ`
to `renormalizedPrimeEnergy N u - ⟪overlapMatrix u, u⟫ - log c - O(1)`. -/
private theorem exists_completeWeilEnergy_ge_prime_sub_overlap :
    ∃ C_dec C_err : ℝ, 0 < C_dec ∧ 0 < C_err ∧
      ∀ {R' N : ℕ} {c : ℝ},
        2 ≤ R' → R' ^ 6 ≤ N → 18 * (1 + Real.log R') ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        C_err * (c * (1 + Real.log R') / Real.sqrt (Real.log N) +
          c ^ 2 / Real.log N +
          c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) ≤ 1 →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R' N → u ∈ (conductorSubspace 1 N)ᗮ → ‖u‖ ≤ 1 →
        renormalizedPrimeEnergy N u -
            ⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) u, u⟫ -
            Real.log c - C_dec ≤
          completeWeilEnergy zeroFreeLogProfile c N u := by
  obtain ⟨C_od, hC_od, hod⟩ := exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace
    smooth_profile zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos
  let C_sep' := 36 * (152 * (∫ t, |zeroFreeLogProfile t|) ^ 2 / (∫ t, zeroFreeLogProfile t ^ 2))
  have hC_sep'0 : 0 ≤ C_sep' := by
    have := integral_zeroFreeLogProfile_sq_pos; dsimp only [C_sep']; positivity
  let C_err := 144 + C_sep' + 2 * C_od + 1
  let C_dec := |completeWeilSelfFinitePart zeroFreeLogProfile 1| +
    |Real.eulerMascheroniConstant| + 3
  refine ⟨C_dec, C_err, by dsimp only [C_dec]; positivity,
    by dsimp only [C_err]; positivity, ?_⟩
  intro R' N c hR' hR6N hlog hc1 hw1 hRNT herr u hu hu1 hu_le1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hRR_N : R' * R' ≤ N := by
    have : R' ^ 2 ≤ R' ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    simpa only [sq] using this.trans hR6N
  have hR4_N : R' ^ 4 ≤ N :=
    (Nat.pow_le_pow_right (by omega) (by norm_num : 4 ≤ 6)).trans hR6N
  have hN2 : 2 ≤ N := by have := Nat.mul_le_mul hR' hR'; omega
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcN : c ≤ N := by have := (div_le_iff₀ hN0).mp hw1; linarith only [this, hc0]
  have hu_sq_le1 : ‖u‖ ^ 2 ≤ 1 := by nlinarith only [hu_le1, norm_nonneg u]
  -- Self-energy term
  have hself_eq : completeWeilSelfFinitePart zeroFreeLogProfile c =
      completeWeilSelfFinitePart zeroFreeLogProfile 1 - Real.log c := by
    unfold completeWeilSelfFinitePart
    rw [mul_one, Real.log_div one_ne_zero (by positivity), Real.log_one,
      Real.log_mul (by positivity : 2 * Real.pi ≠ 0) hc0.ne',
      Real.log_div one_ne_zero (by positivity), Real.log_one]
    ring
  have hself_err : |completeWeilSelfError zeroFreeLogProfile c N| ≤ 1 := by
    have h1 := abs_completeWeilSelfError_le_of_width_le_one smooth_profile
      zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos hc0 hN1 hcN
    have he12 : Real.exp (1 / 2) ≤ 3 := by
      have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      exact (Real.exp_le_exp.mpr (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans he1
    calc
      |completeWeilSelfError zeroFreeLogProfile c N| ≤
          Real.exp (1 / 2) / 2 * (c / N) := h1
      _ ≤ (3 / 2) * (1 / 3) :=
        mul_le_mul (by linarith only [he12]) hw1 (by positivity) (by norm_num)
      _ ≤ 1 := by norm_num
  have hself_term :
      -Real.log c - (|completeWeilSelfFinitePart zeroFreeLogProfile 1| +
        |Real.eulerMascheroniConstant| + 1) ≤
      (completeWeilSelfFinitePart zeroFreeLogProfile c - Real.eulerMascheroniConstant +
        completeWeilSelfError zeroFreeLogProfile c N) * ‖u‖ ^ 2 := by
    rw [hself_eq]
    have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
    have hlc_u : Real.log c * ‖u‖ ^ 2 ≤ Real.log c :=
      (mul_le_mul_of_nonneg_left hu_sq_le1 hlc0).trans_eq (mul_one _)
    have hconst_lb : -(|completeWeilSelfFinitePart zeroFreeLogProfile 1| +
        |Real.eulerMascheroniConstant| + 1) ≤
      (completeWeilSelfFinitePart zeroFreeLogProfile 1 - Real.eulerMascheroniConstant +
        completeWeilSelfError zeroFreeLogProfile c N) := by
      linarith only [neg_abs_le (completeWeilSelfFinitePart zeroFreeLogProfile 1),
        le_abs_self Real.eulerMascheroniConstant, (abs_le.mp hself_err).1]
    have hconst_u :
        -(|completeWeilSelfFinitePart zeroFreeLogProfile 1| +
          |Real.eulerMascheroniConstant| + 1) ≤
        (completeWeilSelfFinitePart zeroFreeLogProfile 1 - Real.eulerMascheroniConstant +
          completeWeilSelfError zeroFreeLogProfile c N) * ‖u‖ ^ 2 := by
      have hA0 : 0 ≤ |completeWeilSelfFinitePart zeroFreeLogProfile 1| +
          |Real.eulerMascheroniConstant| + 1 := by positivity
      calc
        -(|completeWeilSelfFinitePart zeroFreeLogProfile 1| +
            |Real.eulerMascheroniConstant| + 1) ≤
          -(|completeWeilSelfFinitePart zeroFreeLogProfile 1| +
            |Real.eulerMascheroniConstant| + 1) * ‖u‖ ^ 2 := by
          nlinarith only [hA0, hu_sq_le1, sq_nonneg ‖u‖]
        _ ≤ _ := mul_le_mul_of_nonneg_right hconst_lb (sq_nonneg _)
    linarith only [hlc_u, hconst_u]
  -- Center + separated cross + overlap-minus-downward
  have hcen := abs_fullWeilCenterMatrix_inner_le_of_mem_conductorSubspace
    (completeWeilPoleShift zeroFreeLogProfile c) hR' hR6N hlog hu hu1 hu1
  have hpole_le : |completeWeilPoleShift zeroFreeLogProfile c| ≤ c := by
    rw [abs_of_nonneg (completeWeilPoleShift_nonneg zeroFreeLogProfile hc0.le)]
    exact completeWeilPoleShift_le smooth_profile.continuous
      zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos hc0.le
  have hcen' :
      |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix
          (completeWeilPoleShift zeroFreeLogProfile c) N) u, u⟫| ≤
        144 * (c * (1 + Real.log R') / Real.sqrt (Real.log N)) := by
    have h1R0 : 0 ≤ (1 + Real.log R') / Real.sqrt (Real.log N) := by
      have := Real.log_natCast_nonneg R'; positivity
    have h1 : 144 * |completeWeilPoleShift zeroFreeLogProfile c| *
        (1 + Real.log R') / Real.sqrt (Real.log N) ≤
      144 * (c * (1 + Real.log R') / Real.sqrt (Real.log N)) := by
      calc
        144 * |completeWeilPoleShift zeroFreeLogProfile c| *
            (1 + Real.log R') / Real.sqrt (Real.log N) =
          144 * |completeWeilPoleShift zeroFreeLogProfile c| *
            ((1 + Real.log R') / Real.sqrt (Real.log N)) := by ring
        _ ≤ 144 * c * ((1 + Real.log R') / Real.sqrt (Real.log N)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hpole_le]) h1R0
        _ = 144 * (c * (1 + Real.log R') / Real.sqrt (Real.log N)) := by ring
    calc
      _ ≤ 144 * |completeWeilPoleShift zeroFreeLogProfile c| *
            (1 + Real.log R') / Real.sqrt (Real.log N) * ‖u‖ * ‖u‖ := hcen
      _ = (144 * |completeWeilPoleShift zeroFreeLogProfile c| *
            (1 + Real.log R') / Real.sqrt (Real.log N)) * ‖u‖ ^ 2 := by ring
      _ ≤ 144 * (c * (1 + Real.log R') / Real.sqrt (Real.log N)) * 1 :=
        mul_le_mul h1 hu_sq_le1 (sq_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hsep' :
      |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix zeroFreeLogProfile c N) u, u⟫| ≤
        C_sep' * (c ^ 2 / Real.log N) := by
    have h1 := abs_separatedCrossErrorMatrix_inner_le_of_mem_conductorSubspace
      smooth_profile zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos
      hc0 hR' hR4_N hlog hu
    have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    calc
      _ ≤ C_sep' * c ^ 2 / Real.log N * ‖u‖ ^ 2 := h1
      _ = C_sep' * (c ^ 2 / Real.log N) * ‖u‖ ^ 2 := by ring
      _ ≤ C_sep' * (c ^ 2 / Real.log N) * 1 :=
        mul_le_mul_of_nonneg_left hu_sq_le1 (by positivity)
      _ = _ := mul_one _
  have hod' :
      2 * |⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) u -
          downwardPrimeVector zeroFreeLogProfile c N u, u⟫| ≤
        2 * C_od * (c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) := by
    have h1 := hod hR' hRR_N hlog hc1 hw1 hRNT hu
    have hcs := (abs_real_inner_le_norm _ u).trans
      (mul_le_mul_of_nonneg_right h1 (norm_nonneg u))
    have hX0 : 0 ≤ c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
        c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) := by
      have := Real.log_natCast_nonneg R'; positivity
    calc
      _ ≤ 2 * (C_od * (c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
            c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) * ‖u‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left hcs zero_le_two
      _ = 2 * C_od * (c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
            c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) * ‖u‖ ^ 2 := by ring
      _ ≤ 2 * C_od * (c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
            c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) * 1 :=
        mul_le_mul_of_nonneg_left hu_sq_le1 (by positivity)
      _ = _ := mul_one _
  have hsum_err_le1 :
      |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix
          (completeWeilPoleShift zeroFreeLogProfile c) N) u, u⟫| +
      |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix zeroFreeLogProfile c N) u, u⟫| +
      2 * |⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) u -
          downwardPrimeVector zeroFreeLogProfile c N u, u⟫| ≤ 1 := by
    have ht1 : 0 ≤ c * (1 + Real.log R') / Real.sqrt (Real.log N) := by
      have := Real.log_natCast_nonneg R'; positivity
    have ht2 : 0 ≤ c ^ 2 / Real.log N := by
      have := Real.log_natCast_nonneg N; positivity
    have ht3 : 0 ≤ c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) := by
      have := Real.log_natCast_nonneg R'; positivity
    have ht4 : 0 ≤ c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) := by positivity
    dsimp only [C_err] at herr
    nlinarith only [hcen', hsep', hod', herr, ht1, ht2, ht3, ht4, hC_sep'0, hC_od]
  have hpole0 := fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one
    zeroFreeLogProfile c hN2 hu1 hu1
  have hdecomp := completeWeilMatrix_inner_eq_decomposition_at_every_overlap
    smooth_profile zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos
    hc0 hN1 u
  rw [overlap_sub_nonRatio_inner_eq smooth_profile zeroFreeLogProfile_eq_zero
      integral_zeroFreeLogProfile_sq_pos hc0 hN1 u, hpole0] at hdecomp
  change completeWeilEnergy zeroFreeLogProfile c N u =
    renormalizedPrimeEnergy N u +
    (completeWeilSelfFinitePart zeroFreeLogProfile c - Real.eulerMascheroniConstant +
      completeWeilSelfError zeroFreeLogProfile c N) * ‖u‖ ^ 2 +
    ⟪Matrix.toEuclideanLin
      (fullWeilCenterMatrix (completeWeilPoleShift zeroFreeLogProfile c) N) u, u⟫ -
    ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix zeroFreeLogProfile c N) u, u⟫ + 0 +
    (-⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) u, u⟫ +
      2 * ⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) u -
        downwardPrimeVector zeroFreeLogProfile c N u, u⟫) at hdecomp
  have habs_c := (abs_le.mp (le_rfl : |⟪Matrix.toEuclideanLin
    (fullWeilCenterMatrix (completeWeilPoleShift zeroFreeLogProfile c) N) u, u⟫| ≤ _)).1
  have habs_s := (abs_le.mp (le_rfl : |⟪Matrix.toEuclideanLin
    (separatedCrossErrorMatrix zeroFreeLogProfile c N) u, u⟫| ≤ _)).2
  have habs_o := (abs_le.mp (le_rfl : |⟪Matrix.toEuclideanLin
    (overlapMatrix zeroFreeLogProfile c N) u -
    downwardPrimeVector zeroFreeLogProfile c N u, u⟫| ≤ _)).1
  dsimp only [C_dec]
  linarith only [hdecomp, hself_term, hsum_err_le1, habs_c, habs_s, habs_o]

private theorem abs_add_three_le (x₁ x₂ x₃ : ℝ) :
    |x₁ + x₂ + x₃| ≤ |x₁| + |x₂| + |x₃| :=
  (abs_add_le (x₁ + x₂) x₃).trans (add_le_add (abs_add_le x₁ x₂) le_rfl)

private theorem mul_le_one_of_le_mul_le_one {A C T S : ℝ}
    (hA : A ≤ C) (hC0 : 0 ≤ C) (hT0 : 0 ≤ T) (hTS : T ≤ S) (hCS : C * S ≤ 1) :
    A * T ≤ 1 :=
  (mul_le_mul hA hTS hT0 hC0).trans hCS

private def lowBandPacket (Q₁ N : ℕ) (a : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N

private def highBandCoeffs (Q₁ : ℕ) (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m ≤ Q₁ then 0 else a m

private def highBandPacket (Q₁ R' N : ℕ) (a : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ m ∈ Icc 1 R', highBandCoeffs Q₁ a m • normalizedRamanujanHorizonVector m N

private def lowBandDiagPacket (Q₁ N : ℕ) (a : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ m ∈ Icc 1 Q₁,
    (a m * (Real.log N - ramanujanAdjunctionEnergy m)) •
      normalizedRamanujanHorizonVector m N

private def lowBandAdjPacket (Q₁ N : ℕ) (a : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ m ∈ Icc 1 Q₁,
    (a m * ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N

private theorem lowBand_highBand_packet_split {Q₁ R' N : ℕ} {a : ℕ → ℝ}
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hQ₁ : 2 ≤ Q₁) (hQR' : Q₁ ≤ R') (hRR_N : R' * R' ≤ N)
    (hlog18_R' : 18 * (1 + Real.log R') ≤ Real.log N)
    (hu_eq : u = ∑ m ∈ Icc 1 R', a m • normalizedRamanujanHorizonVector m N)
    (huQ : u ∈ (conductorSubspace Q₁ N)ᗮ)
    (hu_sq_ge : 3 / 4 ≤ ‖u‖ ^ 2) (hu_le1 : ‖u‖ ≤ 1)
    (h1080 : 1080 * ((1 + Real.log R') / Real.log N) ≤ 1) :
    u = lowBandPacket Q₁ N a + highBandPacket Q₁ R' N a ∧
    lowBandPacket Q₁ N a ∈ conductorSubspace R' N ∧
    highBandPacket Q₁ R' N a ∈ conductorSubspace R' N ∧
    ‖lowBandPacket Q₁ N a‖ ≤ 54 * (1 + Real.log R') / Real.log N ∧
    ‖lowBandPacket Q₁ N a‖ ≤ 1 / 20 ∧
    1 / 2 ≤ ‖highBandPacket Q₁ R' N a‖ ^ 2 ∧
    ‖highBandPacket Q₁ R' N a‖ ≤ 2 := by
  have hR'2 : 2 ≤ R' := hQ₁.trans hQR'
  have huLow_R' : lowBandPacket Q₁ N a = ∑ m ∈ Icc 1 R',
      (if m ≤ Q₁ then a m else 0) • normalizedRamanujanHorizonVector m N := by
    unfold lowBandPacket
    have hsub : Icc 1 Q₁ ⊆ Icc 1 R' := Icc_subset_Icc le_rfl hQR'
    calc
      (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) =
          ∑ m ∈ Icc 1 Q₁,
            (if m ≤ Q₁ then a m else 0) • normalizedRamanujanHorizonVector m N :=
        sum_congr rfl fun m hm => by rw [if_pos (mem_Icc.mp hm).2]
      _ = _ := sum_subset hsub fun m hmR hmQ => by
        have hnot : ¬m ≤ Q₁ := fun h => hmQ (mem_Icc.mpr ⟨(mem_Icc.mp hmR).1, h⟩)
        rw [if_neg hnot, zero_smul]
  have hu_split : u = lowBandPacket Q₁ N a + highBandPacket Q₁ R' N a := by
    rw [hu_eq, huLow_R', highBandPacket]
    unfold highBandCoeffs
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  have huLow_mem : lowBandPacket Q₁ N a ∈ conductorSubspace R' N := by
    unfold lowBandPacket
    exact conductorSubspace_mono hQR' N
      (sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q₁ N a)
  have hy_mem : highBandPacket Q₁ R' N a ∈ conductorSubspace R' N := by
    unfold highBandPacket
    exact sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R' N (highBandCoeffs Q₁ a)
  have huLow_bound : ‖lowBandPacket Q₁ N a‖ ≤ 54 * (1 + Real.log R') / Real.log N := by
    have hlow := (low_band_norm_le_of_mem_orthogonal (by omega : 1 ≤ Q₁) hQR' hR'2 hRR_N
      hlog18_R' (hu_eq ▸ huQ)).2
    rw [← hu_eq, show (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) =
      lowBandPacket Q₁ N a from rfl] at hlow
    have h0 : 0 ≤ 54 * (1 + Real.log R') / Real.log N := by
      have := Real.log_natCast_nonneg R'; positivity
    exact hlow.trans ((mul_le_mul_of_nonneg_left hu_le1 h0).trans_eq (mul_one _))
  have huLow_le20 : ‖lowBandPacket Q₁ N a‖ ≤ 1 / 20 := by
    have h54 : 54 * (1 + Real.log R') / Real.log N =
        54 * ((1 + Real.log R') / Real.log N) := by ring
    linarith only [huLow_bound, h1080, h54]
  have hy_bounds : 1 / 2 ≤ ‖highBandPacket Q₁ R' N a‖ ^ 2 ∧ ‖highBandPacket Q₁ R' N a‖ ≤ 2 := by
    have hu_ge : 17 / 20 ≤ ‖u‖ := by nlinarith only [hu_sq_ge, norm_nonneg u]
    have htri1 : ‖u‖ ≤ ‖lowBandPacket Q₁ N a‖ + ‖highBandPacket Q₁ R' N a‖ := by
      rw [hu_split]; exact norm_add_le _ _
    have hy_ge : 4 / 5 ≤ ‖highBandPacket Q₁ R' N a‖ := by
      linarith only [hu_ge, htri1, huLow_le20]
    have hy_eq : highBandPacket Q₁ R' N a = u - lowBandPacket Q₁ N a := by
      rw [hu_split]; abel
    have htri2 : ‖highBandPacket Q₁ R' N a‖ ≤ ‖u‖ + ‖lowBandPacket Q₁ N a‖ := by
      rw [hy_eq]; exact norm_sub_le _ _
    exact ⟨by nlinarith only [hy_ge], by linarith only [htri2, hu_le1, huLow_le20]⟩
  exact ⟨hu_split, huLow_mem, hy_mem, huLow_bound, huLow_le20, hy_bounds.1, hy_bounds.2⟩

private theorem overlap_diff_of_conductor_split {R' N : ℕ} {c C_ov : ℝ}
    (hC_ov : 0 < C_ov)
    (hov : ∀ {R₁ R₂ N : ℕ} {c : ℝ},
      2 ≤ R₁ → 2 ≤ R₂ →
      18 * (1 + Real.log R₁) ≤ Real.log N →
      18 * (1 + Real.log R₂) ≤ Real.log N →
      1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
      ((R₁ * R₁ : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ((R₂ * R₂ : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ {u v : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R₁ N → v ∈ conductorSubspace R₂ N →
        |⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) u, v⟫| ≤
          C_ov * c * (1 + Real.log c) * ‖u‖ * ‖v‖)
    (hR'2 : 2 ≤ R') (hlog18_R' : 18 * (1 + Real.log R') ≤ Real.log N)
    (hc1 : 1 ≤ c) (hcL : c ≤ Real.log N) (hw1 : c / N ≤ 1 / 3)
    (hRNT : ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N)
    {u v y : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu_split : u = v + y)
    (hv_mem : v ∈ conductorSubspace R' N) (hy_mem : y ∈ conductorSubspace R' N)
    (hv_bound : ‖v‖ ≤ 54 * (1 + Real.log R') / Real.log N)
    (hv_le20 : ‖v‖ ≤ 1 / 20) (hy_le2 : ‖y‖ ≤ 2)
    (h270 : 270 * C_ov * (c * (1 + Real.log c) * (1 + Real.log R') / Real.log N) ≤ 1) :
    |⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) u, u⟫ -
      ⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) y, y⟫| ≤ 1 := by
  have hexp :
      ⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) u, u⟫ -
        ⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) y, y⟫ =
      ⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) v, v⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) v, y⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) y, v⟫ := by
    rw [hu_split, map_add, inner_add_left, inner_add_right, inner_add_right]
    ring
  have h1 := hov hR'2 hR'2 hlog18_R' hlog18_R' hc1 hcL hw1 hRNT hRNT hv_mem hv_mem
  have h2 := hov hR'2 hR'2 hlog18_R' hlog18_R' hc1 hcL hw1 hRNT hRNT hv_mem hy_mem
  have h3 := hov hR'2 hR'2 hlog18_R' hlog18_R' hc1 hcL hw1 hRNT hRNT hy_mem hv_mem
  have hnorm_sum : ‖v‖ * ‖v‖ + ‖v‖ * ‖y‖ + ‖y‖ * ‖v‖ ≤ 5 * ‖v‖ := by
    nlinarith only [hv_le20, hy_le2, norm_nonneg v]
  rw [hexp]
  calc
    |⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) v, v⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) v, y⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) y, v⟫| ≤
        |⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) v, v⟫| +
          |⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) v, y⟫| +
          |⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) y, v⟫| :=
      abs_add_three_le _ _ _
    _ ≤ C_ov * c * (1 + Real.log c) * (‖v‖ * ‖v‖ + ‖v‖ * ‖y‖ + ‖y‖ * ‖v‖) := by
      linarith only [h1, h2, h3]
    _ ≤ C_ov * c * (1 + Real.log c) * (5 * (54 * (1 + Real.log R') / Real.log N)) := by
      refine mul_le_mul_of_nonneg_left (hnorm_sum.trans (by linarith only [hv_bound])) ?_
      have := Real.log_nonneg hc1; positivity
    _ = 270 * C_ov * (c * (1 + Real.log c) * (1 + Real.log R') / Real.log N) := by ring
    _ ≤ 1 := h270

private theorem lowBandPacket_prime_cross_le {Q₁ R' N : ℕ} {C_pr : ℝ} {a : ℕ → ℝ}
    (hC_pr : 0 < C_pr)
    (hpr_res : ∀ {M N : ℕ}, 2 ≤ M → M ^ 6 ≤ N → 18 * (1 + Real.log M) ≤ Real.log N →
      ∀ a : ℕ → ℝ,
        ‖Matrix.toEuclideanLin (fullPrimeMatrix N)
            (∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N) -
          ∑ m ∈ Icc 1 M,
            (a m * (Real.log N - ramanujanAdjunctionEnergy m)) •
              normalizedRamanujanHorizonVector m N‖ ≤
          C_pr * (1 + (1 + Real.log M) ^ 2 / Real.sqrt (Real.log N)) *
            ‖∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N‖)
    (hQ₁ : 2 ≤ Q₁) (hQR' : Q₁ ≤ R') (hQ6N : Q₁ ^ 6 ≤ N) (hQQ_N : Q₁ * Q₁ ≤ N)
    (hlog18_Q : 18 * (1 + Real.log Q₁) ≤ Real.log N)
    (ht2_1 : (1 + Real.log Q₁) ^ 2 / Real.sqrt (Real.log N) ≤ 1)
    (h864 : 864 * ((1 + Real.log R') ^ 2 / Real.log N) ≤ 1)
    (h432 : 432 * C_pr * ((1 + Real.log R') / Real.log N) ≤ 1)
    (huLow_bound : ‖lowBandPacket Q₁ N a‖ ≤ 54 * (1 + Real.log R') / Real.log N)
    {y : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hy_le2 : ‖y‖ ≤ 2) :
    2 * |⟪Real.log N • lowBandPacket Q₁ N a -
      Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket Q₁ N a), y⟫| ≤ 2 := by
  have hlog_Q_le_R' : Real.log Q₁ ≤ Real.log R' :=
    Real.log_le_log (by exact_mod_cast (show 0 < Q₁ by omega)) (by exact_mod_cast hQR')
  have hid : Real.log N • lowBandPacket Q₁ N a -
        Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket Q₁ N a) =
      lowBandAdjPacket Q₁ N a -
        (Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket Q₁ N a) -
          lowBandDiagPacket Q₁ N a) := by
    have hsub : Real.log N • lowBandPacket Q₁ N a - lowBandDiagPacket Q₁ N a =
        lowBandAdjPacket Q₁ N a := by
      unfold lowBandPacket lowBandDiagPacket lowBandAdjPacket
      rw [Finset.smul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun m _ => ?_
      rw [smul_smul, ← sub_smul]
      congr 1; ring
    rw [← hsub]; abel
  have hadj_norm : ‖lowBandAdjPacket Q₁ N a‖ ≤
      4 * (1 + Real.log R') * ‖lowBandPacket Q₁ N a‖ := by
    have hγ : |Real.eulerMascheroniConstant| ≤ 1 := by
      rw [abs_le]
      have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 0
      simp [Real.eulerMascheroniSeq] at h1
      exact ⟨by linarith, by linarith [Real.eulerMascheroniConstant_lt_two_thirds]⟩
    have hadj_m : ∀ m ∈ Icc 1 Q₁, |ramanujanAdjunctionEnergy m| ≤ 2 * (1 + Real.log R') := by
      intro m hm
      obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
      have hlm0 : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
      have hlmR : Real.log m ≤ Real.log R' :=
        (Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmQ)).trans hlog_Q_le_R'
      have htd0 := tameDifferent_nonneg m
      have htd := (CompletedArithmeticForms.tameDifferent_le_log hm1).trans hlmR
      unfold ramanujanAdjunctionEnergy
      exact (abs_add_le _ _).trans (by
        rw [abs_of_nonneg (add_nonneg hlm0 htd0)]
        linarith only [hγ, hlmR, htd])
    have hadj_sq : (∑ m ∈ Icc 1 Q₁, (a m * ramanujanAdjunctionEnergy m) ^ 2) ≤
        (2 * (1 + Real.log R')) ^ 2 * ∑ m ∈ Icc 1 Q₁, a m ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun m hm => ?_
      have hsq := pow_le_pow_left₀ (abs_nonneg _) (hadj_m m hm) 2
      rw [sq_abs] at hsq
      nlinarith only [hsq, sq_nonneg (a m)]
    have hru_lo := (half_and_three_halves_riesz_of_log_le hQ₁ hQQ_N hlog18_Q a).1
    have hru_hi := (half_and_three_halves_riesz_of_log_le hQ₁ hQQ_N hlog18_Q
      (fun m => a m * ramanujanAdjunctionEnergy m)).2
    rw [show (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) =
      lowBandPacket Q₁ N a from rfl] at hru_lo
    rw [show (∑ m ∈ Icc 1 Q₁, (a m * ramanujanAdjunctionEnergy m) •
      normalizedRamanujanHorizonVector m N) = lowBandAdjPacket Q₁ N a from rfl] at hru_hi
    have hnorm_sq : ‖lowBandAdjPacket Q₁ N a‖ ^ 2 ≤
        (4 * (1 + Real.log R') * ‖lowBandPacket Q₁ N a‖) ^ 2 := by
      calc
        ‖lowBandAdjPacket Q₁ N a‖ ^ 2 ≤ (3 / 2 : ℝ) *
            ∑ m ∈ Icc 1 Q₁, (a m * ramanujanAdjunctionEnergy m) ^ 2 := hru_hi
        _ ≤ (3 / 2 : ℝ) * ((2 * (1 + Real.log R')) ^ 2 * ∑ m ∈ Icc 1 Q₁, a m ^ 2) :=
          mul_le_mul_of_nonneg_left hadj_sq (by norm_num)
        _ ≤ (3 / 2 : ℝ) * ((2 * (1 + Real.log R')) ^ 2 * (2 * ‖lowBandPacket Q₁ N a‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (by linarith only [hru_lo]) (sq_nonneg _)) (by norm_num)
        _ ≤ (4 * (1 + Real.log R') * ‖lowBandPacket Q₁ N a‖) ^ 2 := by
          nlinarith only [sq_nonneg ((1 + Real.log R') * ‖lowBandPacket Q₁ N a‖)]
    have hrhs0 : 0 ≤ 4 * (1 + Real.log R') * ‖lowBandPacket Q₁ N a‖ := by
      have := Real.log_natCast_nonneg R'; positivity
    nlinarith only [hnorm_sq, norm_nonneg (lowBandAdjPacket Q₁ N a), hrhs0]
  have hres_norm :
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket Q₁ N a) -
        lowBandDiagPacket Q₁ N a‖ ≤ 2 * C_pr * ‖lowBandPacket Q₁ N a‖ := by
    have h1 := hpr_res hQ₁ hQ6N hlog18_Q a
    rw [show (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) =
      lowBandPacket Q₁ N a from rfl,
      show (∑ m ∈ Icc 1 Q₁, (a m * (Real.log N - ramanujanAdjunctionEnergy m)) •
        normalizedRamanujanHorizonVector m N) = lowBandDiagPacket Q₁ N a from rfl] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (by nlinarith only [hC_pr, ht2_1]) (norm_nonneg _))
  have hadj_part : 2 * |⟪lowBandAdjPacket Q₁ N a, y⟫| ≤ 1 := by
    calc
      2 * |⟪lowBandAdjPacket Q₁ N a, y⟫| ≤ 2 * (‖lowBandAdjPacket Q₁ N a‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) zero_le_two
      _ ≤ 2 * ((4 * (1 + Real.log R') * (54 * (1 + Real.log R') / Real.log N)) * 2) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le_two
        exact mul_le_mul
          (hadj_norm.trans (mul_le_mul_of_nonneg_left huLow_bound
            (by have := Real.log_natCast_nonneg R'; positivity)))
          hy_le2 (norm_nonneg y) (by have := Real.log_natCast_nonneg R'; positivity)
      _ = 864 * ((1 + Real.log R') ^ 2 / Real.log N) := by ring
      _ ≤ 1 := h864
  have hres_part :
      2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket Q₁ N a) -
        lowBandDiagPacket Q₁ N a, y⟫| ≤ 1 := by
    calc
      2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket Q₁ N a) -
          lowBandDiagPacket Q₁ N a, y⟫| ≤
          2 * (‖Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket Q₁ N a) -
            lowBandDiagPacket Q₁ N a‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) zero_le_two
      _ ≤ 2 * ((2 * C_pr * (54 * (1 + Real.log R') / Real.log N)) * 2) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le_two
        exact mul_le_mul
          (hres_norm.trans (mul_le_mul_of_nonneg_left huLow_bound (by positivity)))
          hy_le2 (norm_nonneg y) (by have := Real.log_natCast_nonneg R'; positivity)
      _ = 432 * C_pr * ((1 + Real.log R') / Real.log N) := by ring
      _ ≤ 1 := h432
  rw [hid, inner_sub_left]
  calc
    2 * |⟪lowBandAdjPacket Q₁ N a, y⟫ -
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket Q₁ N a) -
          lowBandDiagPacket Q₁ N a, y⟫| ≤
        2 * |⟪lowBandAdjPacket Q₁ N a, y⟫| +
          2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket Q₁ N a) -
            lowBandDiagPacket Q₁ N a, y⟫| := by
      linarith only [abs_sub ⟪lowBandAdjPacket Q₁ N a, y⟫
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket Q₁ N a) -
          lowBandDiagPacket Q₁ N a, y⟫]
    _ ≤ 2 := by linarith only [hadj_part, hres_part]

private theorem highBandPacket_prime_and_overlap_bounds {Q₁ R' N : ℕ} {c C_mid C_prime : ℝ} {a : ℕ → ℝ}
    (hmid : ∀ {Q₁ Q₂ N : ℕ} {c : ℝ},
      2 ≤ Q₁ → Q₁ ≤ Q₂ → Q₂ * Q₂ ≤ N →
      18 * (1 + Real.log Q₂) ≤ Real.log N →
      1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
      4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ((Q₂ * Q₂ : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ {a : ℕ → ℝ}, (∀ m ∈ Icc 1 Q₁, a m = 0) →
        |⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N)
            (∑ m ∈ Icc 1 Q₂, a m • normalizedRamanujanHorizonVector m N),
          ∑ m ∈ Icc 1 Q₂, a m • normalizedRamanujanHorizonVector m N⟫| ≤
          C_mid * (c ^ 2 * (1 + Real.log c) / Real.log N +
            c ^ 5 * Real.log N / N +
            c ^ 4 / Real.sqrt Q₁ +
            c ^ 3 * (Q₂ : ℝ) ^ 4 / N) *
          ‖∑ m ∈ Icc 1 Q₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2)
    (hC_prime : 0 < C_prime)
    (hprime : (Real.log Q₁ / 2 - C_prime) * ‖highBandPacket Q₁ R' N a‖ ^ 2 ≤
      renormalizedPrimeEnergy N (highBandPacket Q₁ R' N a))
    (hQ₁ : 2 ≤ Q₁) (hQR' : Q₁ ≤ R') (hRR_N : R' * R' ≤ N)
    (hlog36 : 36 * (1 + Real.log R') ≤ Real.log N)
    (hc1 : 1 ≤ c) (hcL : c ≤ Real.log N) (hw1 : c / N ≤ 1 / 3)
    (hradN : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N)
    (hRNT : ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N)
    (hmid_le1 : C_mid * (c ^ 2 * (1 + Real.log c) / Real.log N +
      c ^ 5 * Real.log N / N + c ^ 4 / Real.sqrt Q₁ + c ^ 3 * (R' : ℝ) ^ 4 / N) ≤ 1)
    (hy_sq_ge : 1 / 2 ≤ ‖highBandPacket Q₁ R' N a‖ ^ 2)
    (hy_le2 : ‖highBandPacket Q₁ R' N a‖ ≤ 2) :
    |⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N)
        (highBandPacket Q₁ R' N a), highBandPacket Q₁ R' N a⟫| ≤ 4 ∧
    (1 / 4) * Real.log Q₁ - 4 * C_prime ≤
      renormalizedPrimeEnergy N (highBandPacket Q₁ R' N a) := by
  have hlog18_R' : 18 * (1 + Real.log R') ≤ Real.log N := by
    have := Real.log_natCast_nonneg R'; linarith only [hlog36, this]
  have ha0 : ∀ m ∈ Icc 1 Q₁, highBandCoeffs Q₁ a m = 0 := fun m hm => by
    unfold highBandCoeffs; exact if_pos (mem_Icc.mp hm).2
  have hov_y :
      |⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N)
          (highBandPacket Q₁ R' N a), highBandPacket Q₁ R' N a⟫| ≤ 4 := by
    have hm := hmid hQ₁ hQR' hRR_N hlog18_R' hc1 hcL hw1 hradN hRNT ha0
    rw [show (∑ m ∈ Icc 1 R', highBandCoeffs Q₁ a m • normalizedRamanujanHorizonVector m N) =
      highBandPacket Q₁ R' N a from rfl] at hm
    have hy_sq4 : ‖highBandPacket Q₁ R' N a‖ ^ 2 ≤ 4 := by
      nlinarith only [hy_le2, norm_nonneg (highBandPacket Q₁ R' N a)]
    calc
      |⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N)
          (highBandPacket Q₁ R' N a), highBandPacket Q₁ R' N a⟫| ≤
          C_mid * (c ^ 2 * (1 + Real.log c) / Real.log N +
            c ^ 5 * Real.log N / N + c ^ 4 / Real.sqrt Q₁ +
            c ^ 3 * (R' : ℝ) ^ 4 / N) * ‖highBandPacket Q₁ R' N a‖ ^ 2 := hm
      _ ≤ 1 * 4 := mul_le_mul hmid_le1 hy_sq4 (sq_nonneg _) zero_le_one
      _ = 4 := one_mul 4
  have hprime_y :
      (1 / 4) * Real.log Q₁ - 4 * C_prime ≤
        renormalizedPrimeEnergy N (highBandPacket Q₁ R' N a) := by
    have hy_sq4 : ‖highBandPacket Q₁ R' N a‖ ^ 2 ≤ 4 := by
      nlinarith only [hy_le2, norm_nonneg (highBandPacket Q₁ R' N a)]
    have hlead := mul_le_mul_of_nonneg_left hy_sq_ge
      (div_nonneg (Real.log_natCast_nonneg Q₁) zero_le_two)
    have hloss := mul_le_mul_of_nonneg_left hy_sq4 hC_prime.le
    nlinarith only [hprime, hlead, hloss]
  exact ⟨hov_y, hprime_y⟩

/-- Coercivity above `Q₁`: every `u ∈ conductorSubspace R' N ⊓ (conductorSubspace Q₁ N)ᗮ` with
`3 / 4 ≤ ‖u‖ ^ 2 ≤ 1` has complete Weil energy bounded below by
`(1 / 4) * log Q₁ - log c - C_coerc`. -/
theorem exists_high_band_coercivity :
    ∃ C_coerc C_small : ℝ, 0 < C_coerc ∧ 0 < C_small ∧
      ∀ {Q₁ R' N : ℕ} {c : ℝ},
        2 ≤ Q₁ → Q₁ ≤ R' → R' ^ 6 ≤ N → 36 * (1 + Real.log R') ≤ Real.log N →
        1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        C_small * (c * (1 + Real.log c) * (1 + Real.log R') / Real.log N +
          ((1 + Real.log R') ^ 2 / Real.log N + (1 + Real.log Q₁) ^ 2 / Real.sqrt (Real.log N)) +
          c * (1 + Real.log R') / Real.sqrt (Real.log N) +
          c ^ 2 / Real.log N +
          c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) +
          c ^ 5 * Real.log N / N +
          c ^ 4 / Real.sqrt Q₁ +
          c ^ 3 * (R' : ℝ) ^ 4 / N +
          c ^ 2 * (1 + Real.log c) / Real.log N) ≤ 1 →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R' N → u ∈ (conductorSubspace Q₁ N)ᗮ →
        3 / 4 ≤ ‖u‖ ^ 2 → ‖u‖ ≤ 1 →
        (1 / 4) * Real.log Q₁ - Real.log c - C_coerc ≤
          completeWeilEnergy zeroFreeLogProfile c N u := by
  obtain ⟨C_dec, C_err, hC_dec, hC_err, hdec⟩ := exists_completeWeilEnergy_ge_prime_sub_overlap
  obtain ⟨C_ov, hC_ov, hov⟩ := exists_overlapMatrix_inner_le_of_mem_conductorSubspace
    smooth_profile zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos
  obtain ⟨C_pr, hC_pr, hpr_res⟩ := exists_fullPrimeMatrix_packet_residual_norm_le
  obtain ⟨C_mid, hC_mid, hmid⟩ := exists_overlapMatrix_midBand_inner_le
    smooth_profile zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos
  obtain ⟨C_prime, hC_prime, hprime⟩ := exists_primePacket_energy_ge_log
  have hlog4_0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨C_dec + (Real.log 4 + 4) + 8 + 4 * C_prime,
    C_err + 1080 + 270 * C_ov + 864 + 432 * C_pr + C_mid + 1,
    by positivity, by positivity, ?_⟩
  intro Q₁ R' N c hQ₁ hQR' hR6N hlog36 hc1 hcL hw1 hradN hRNT hsmall
    u hu huQ hu_sq_ge hu_le1
  have hR'2 : 2 ≤ R' := hQ₁.trans hQR'
  have hRR_N : R' * R' ≤ N := by
    have : R' ^ 2 ≤ R' ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    simpa only [sq] using this.trans hR6N
  have hQ6N : Q₁ ^ 6 ≤ N := (Nat.pow_le_pow_left hQR' 6).trans hR6N
  have hQQ_N : Q₁ * Q₁ ≤ N := (Nat.mul_le_mul hQR' hQR').trans hRR_N
  have hlog18_R' : 18 * (1 + Real.log R') ≤ Real.log N := by
    have := Real.log_natCast_nonneg R'; linarith only [hlog36, this]
  have hlog_Q_le_R' : Real.log Q₁ ≤ Real.log R' :=
    Real.log_le_log (by exact_mod_cast (show 0 < Q₁ by omega)) (by exact_mod_cast hQR')
  have hlog18_Q : 18 * (1 + Real.log Q₁) ≤ Real.log N := by
    linarith only [hlog18_R', hlog_Q_le_R']
  have hL1 : 1 ≤ Real.log N := by
    have := Real.log_natCast_nonneg R'; linarith only [hlog36, this]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hsL_le_L : Real.sqrt (Real.log N) ≤ Real.log N := by
    have hs1 : 1 ≤ Real.sqrt (Real.log N) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL1
    nlinarith only [Real.sq_sqrt hL0.le, hs1]
  have hu1 : u ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    huQ v (conductorSubspace_mono (by omega : 1 ≤ Q₁) N hv)
  -- Nonnegativity of all 10 smallness summands
  have ht1 : 0 ≤ c * (1 + Real.log c) * (1 + Real.log R') / Real.log N := by
    have := Real.log_nonneg hc1; have := Real.log_natCast_nonneg R'; positivity
  have ht2 : 0 ≤ ((1 + Real.log R') ^ 2 / Real.log N + (1 + Real.log Q₁) ^ 2 / Real.sqrt (Real.log N)) := by positivity
  have ht3 : 0 ≤ c * (1 + Real.log R') / Real.sqrt (Real.log N) := by
    have := Real.log_natCast_nonneg R'; positivity
  have ht4 : 0 ≤ c ^ 2 / Real.log N := by positivity
  have ht5 : 0 ≤ c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) := by
    have := Real.log_natCast_nonneg R'; positivity
  have ht6 : 0 ≤ c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) := by positivity
  have ht7 : 0 ≤ c ^ 5 * Real.log N / N := by positivity
  have ht8 : 0 ≤ c ^ 4 / Real.sqrt Q₁ := by positivity
  have ht9 : 0 ≤ c ^ 3 * (R' : ℝ) ^ 4 / N := by positivity
  have ht10 : 0 ≤ c ^ 2 * (1 + Real.log c) / Real.log N := by
    have := Real.log_nonneg hc1; positivity
  have h1R_div_le : (1 + Real.log R') / Real.log N ≤
      c * (1 + Real.log c) * (1 + Real.log R') / Real.log N := by
    have h1cc : 1 ≤ c * (1 + Real.log c) := by
      have := Real.log_nonneg hc1; nlinarith only [hc1, this]
    have h1R0 : 0 ≤ (1 + Real.log R') / Real.log N := by
      have := Real.log_natCast_nonneg R'; positivity
    calc
      (1 + Real.log R') / Real.log N = 1 * ((1 + Real.log R') / Real.log N) := (one_mul _).symm
      _ ≤ (c * (1 + Real.log c)) * ((1 + Real.log R') / Real.log N) :=
        mul_le_mul_of_nonneg_right h1cc h1R0
      _ = _ := by ring
  have h1R_sq_div : (1 + Real.log R') ^ 2 / Real.log N ≤
      ((1 + Real.log R') ^ 2 / Real.log N + (1 + Real.log Q₁) ^ 2 / Real.sqrt (Real.log N)) :=
    le_add_of_nonneg_right (by positivity)
  -- Extract individual smallness consequences from hsmall
  have hC0 : 0 ≤ C_err + 1080 + 270 * C_ov + 864 + 432 * C_pr + C_mid + 1 := by positivity
  have h1R0 : 0 ≤ (1 + Real.log R') / Real.log N := by
    have := Real.log_natCast_nonneg R'; positivity
  have herr_dec : C_err * (c * (1 + Real.log R') / Real.sqrt (Real.log N) +
      c ^ 2 / Real.log N +
      c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
      c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) ≤ 1 :=
    mul_le_one_of_le_mul_le_one
      (by linarith only [hC_ov, hC_pr, hC_mid]) hC0
      (by linarith only [ht3, ht4, ht5, ht6])
      (by linarith only [ht1, ht2, ht7, ht8, ht9, ht10]) hsmall
  have h1080 : 1080 * ((1 + Real.log R') / Real.log N) ≤ 1 :=
    mul_le_one_of_le_mul_le_one
      (by linarith only [hC_err, hC_ov, hC_pr, hC_mid]) hC0 h1R0
      (by linarith only [h1R_div_le, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10]) hsmall
  have h270 : 270 * C_ov * (c * (1 + Real.log c) * (1 + Real.log R') / Real.log N) ≤ 1 :=
    mul_le_one_of_le_mul_le_one
      (by linarith only [hC_err, hC_pr, hC_mid]) hC0 ht1
      (by linarith only [ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10]) hsmall
  have ht2_1 : (1 + Real.log Q₁) ^ 2 / Real.sqrt (Real.log N) ≤ 1 := by
    have hboth : ((1 + Real.log R') ^ 2 / Real.log N +
        (1 + Real.log Q₁) ^ 2 / Real.sqrt (Real.log N)) ≤ 1 := by
      simpa only [one_mul] using mul_le_one_of_le_mul_le_one (A := 1)
        (by linarith only [hC_err, hC_ov, hC_pr, hC_mid]) hC0 ht2
        (by linarith only [ht1, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10]) hsmall
    exact (le_add_of_nonneg_left (by positivity)).trans hboth
  have h864 : 864 * ((1 + Real.log R') ^ 2 / Real.log N) ≤ 1 :=
    mul_le_one_of_le_mul_le_one
      (by linarith only [hC_err, hC_ov, hC_pr, hC_mid]) hC0 (by positivity)
      (by linarith only [h1R_sq_div, ht1, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10]) hsmall
  have h432 : 432 * C_pr * ((1 + Real.log R') / Real.log N) ≤ 1 :=
    mul_le_one_of_le_mul_le_one
      (by linarith only [hC_err, hC_ov, hC_mid]) hC0 h1R0
      (by linarith only [h1R_div_le, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10]) hsmall
  have hmid_le1 : C_mid * (c ^ 2 * (1 + Real.log c) / Real.log N +
      c ^ 5 * Real.log N / N + c ^ 4 / Real.sqrt Q₁ + c ^ 3 * (R' : ℝ) ^ 4 / N) ≤ 1 :=
    mul_le_one_of_le_mul_le_one
      (by linarith only [hC_err, hC_ov, hC_pr]) hC0
      (by linarith only [ht10, ht7, ht8, ht9])
      (by linarith only [ht1, ht2, ht3, ht4, ht5, ht6]) hsmall
  have hbase_dec := hdec hR'2 hR6N hlog18_R' hc1 hw1 hRNT herr_dec hu hu1 hu_le1
  obtain ⟨a, -, hu_eq⟩ := (mem_conductorSubspace_iff (M := R') (N := N) (x := u)).mp hu
  obtain ⟨hu_split, huLow_mem, hy_mem, huLow_bound, huLow_le20, hy_sq_ge, hy_le2⟩ :=
    lowBand_highBand_packet_split hQ₁ hQR' hRR_N hlog18_R' hu_eq huQ hu_sq_ge hu_le1 h1080
  have hov_diff := overlap_diff_of_conductor_split hC_ov hov hR'2 hlog18_R' hc1 hcL hw1 hRNT
    hu_split huLow_mem hy_mem huLow_bound huLow_le20 hy_le2 h270
  have hprime_uLow : -(Real.log 4 + 4) ≤ renormalizedPrimeEnergy N (lowBandPacket Q₁ N a) := by
    have hp := poleDefect_le_primeEnergy_add_row_cost (lowBandPacket Q₁ N a)
    have hd0 := poleDefect_nonneg N (primeHorizonExtension (lowBandPacket Q₁ N a))
    have huL_sq1 : ‖lowBandPacket Q₁ N a‖ ^ 2 ≤ 1 := by
      nlinarith only [huLow_le20, norm_nonneg (lowBandPacket Q₁ N a)]
    nlinarith only [hp, hd0, huL_sq1, hlog4_0]
  have hprime_cross := lowBandPacket_prime_cross_le hC_pr hpr_res hQ₁ hQR' hQ6N hQQ_N
    hlog18_Q ht2_1 h864 h432 huLow_bound hy_le2
  have hpacket_prime : (Real.log Q₁ / 2 - C_prime) * ‖highBandPacket Q₁ R' N a‖ ^ 2 ≤
      renormalizedPrimeEnergy N (highBandPacket Q₁ R' N a) :=
    hprime hQ₁ hQR' hRR_N hlog18_R' (highBandCoeffs Q₁ a)
      (fun m hm => by unfold highBandCoeffs; exact if_pos (mem_Icc.mp hm).2)
  obtain ⟨hov_y, hprime_y⟩ := highBandPacket_prime_and_overlap_bounds hmid hC_prime hpacket_prime hQ₁ hQR' hRR_N
    hlog36 hc1 hcL hw1 hradN hRNT hmid_le1 hy_sq_ge hy_le2
  have hprime_u :
      (1 / 4) * Real.log Q₁ - 4 * C_prime -
        (Real.log 4 + 4) - 2 ≤ renormalizedPrimeEnergy N u := by
    have hexp := renormalizedPrimeEnergy_add_eq (lowBandPacket Q₁ N a) (highBandPacket Q₁ R' N a)
    rw [← hu_split] at hexp
    have hcr_lb : -2 ≤ 2 * ⟪Real.log N • lowBandPacket Q₁ N a -
        Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket Q₁ N a),
        highBandPacket Q₁ R' N a⟫ := by
      linarith only [neg_abs_le ⟪Real.log N • lowBandPacket Q₁ N a -
        Matrix.toEuclideanLin (fullPrimeMatrix N) (lowBandPacket Q₁ N a),
        highBandPacket Q₁ R' N a⟫, hprime_cross]
    linarith only [hexp, hprime_uLow, hprime_y, hcr_lb]
  have hov_u : ⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) u, u⟫ ≤ 5 := by
    linarith only [(abs_le.mp hov_diff).2, (abs_le.mp hov_y).2]
  linarith only [hbase_dec, hprime_u, hov_u]

end GaloisForLFunctions.TransMetzlerWeilPositivity.LogarithmicConductorSplit

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.LogarithmicConductorSplit.exists_high_band_coercivity
