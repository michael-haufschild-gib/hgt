import GaloisForLFunctions.CompletedArithmeticForms.HighConductorAdjunctionCoercivity
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandQuadraticCenterBounds
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandQuadraticCancellation

/-!
# Every compact profile has a logarithmic high-conductor gap

Quadratic center and near-cancellation bounds lose only one cutoff logarithm.
Together with the cubic lag bound, these estimates leave only logarithmic overlap loss
for every nonzero compact profile, including profiles with real Fourier zeros.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped Classical RealInnerProductSpace
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics

/-- Quadratic collar cancellation bounds the complete energy below by prime
energy minus overlap, with only a logarithmic self-energy loss. -/
theorem exists_profile_completeWeilEnergy_ge_prime_sub_overlap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ x, x ∉ Set.Icc 0 1 → φ x = 0) (hM : 0 < ∫ x, φ x ^ 2) :
    ∃ C_dec C_err : ℝ, 0 < C_dec ∧ 0 < C_err ∧
      ∀ {R' N : ℕ} {c : ℝ},
        2 ≤ R' → R' ^ 6 ≤ N → 18 * (1 + Real.log R') ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        C_err * (c * (1 + Real.log R') / Real.log N +
          c ^ 2 / Real.log N +
          c ^ 2 * (1 + Real.log R') * (1 + Real.log c) / Real.log N +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) ≤ 1 →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R' N → u ∈ (conductorSubspace 1 N)ᗮ → ‖u‖ ≤ 1 →
        renormalizedPrimeEnergy N u -
            ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫ -
            Real.log c - C_dec ≤
          completeWeilEnergy φ c N u := by
  obtain ⟨C_od, hC_od, hod⟩ := exists_overlap_sub_downward_inner_le_of_mem_conductorSubspace
    hφ hsupp hM
  let C_sep' := 36 * (152 * (∫ t, |φ t|) ^ 2 / (∫ t, φ t ^ 2))
  have hC_sep'0 : 0 ≤ C_sep' := by
    have := hM; dsimp only [C_sep']; positivity
  let C_err := 600 + C_sep' + 2 * C_od + 1
  let C_dec := |completeWeilSelfFinitePart φ 1| +
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
  have hself_eq : completeWeilSelfFinitePart φ c =
      completeWeilSelfFinitePart φ 1 - Real.log c := by
    unfold completeWeilSelfFinitePart
    rw [mul_one, Real.log_div one_ne_zero (by positivity), Real.log_one,
      Real.log_mul (by positivity : 2 * Real.pi ≠ 0) hc0.ne',
      Real.log_div one_ne_zero (by positivity), Real.log_one]
    ring
  have hself_err : |completeWeilSelfError φ c N| ≤ 1 := by
    have h1 := abs_completeWeilSelfError_le_of_width_le_one hφ
      hsupp hM hc0 hN1 hcN
    have he12 : Real.exp (1 / 2) ≤ 3 := by
      have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      exact (Real.exp_le_exp.mpr (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans he1
    calc
      |completeWeilSelfError φ c N| ≤
          Real.exp (1 / 2) / 2 * (c / N) := h1
      _ ≤ (3 / 2) * (1 / 3) :=
        mul_le_mul (by linarith only [he12]) hw1 (by positivity) (by norm_num)
      _ ≤ 1 := by norm_num
  have hself_term :
      -Real.log c - (|completeWeilSelfFinitePart φ 1| +
        |Real.eulerMascheroniConstant| + 1) ≤
      (completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
        completeWeilSelfError φ c N) * ‖u‖ ^ 2 := by
    rw [hself_eq]
    have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
    have hlc_u : Real.log c * ‖u‖ ^ 2 ≤ Real.log c :=
      (mul_le_mul_of_nonneg_left hu_sq_le1 hlc0).trans_eq (mul_one _)
    have hconst_lb : -(|completeWeilSelfFinitePart φ 1| +
        |Real.eulerMascheroniConstant| + 1) ≤
      (completeWeilSelfFinitePart φ 1 - Real.eulerMascheroniConstant +
        completeWeilSelfError φ c N) := by
      linarith only [neg_abs_le (completeWeilSelfFinitePart φ 1),
        le_abs_self Real.eulerMascheroniConstant, (abs_le.mp hself_err).1]
    have hconst_u :
        -(|completeWeilSelfFinitePart φ 1| +
          |Real.eulerMascheroniConstant| + 1) ≤
        (completeWeilSelfFinitePart φ 1 - Real.eulerMascheroniConstant +
          completeWeilSelfError φ c N) * ‖u‖ ^ 2 := by
      have hA0 : 0 ≤ |completeWeilSelfFinitePart φ 1| +
          |Real.eulerMascheroniConstant| + 1 := by positivity
      calc
        -(|completeWeilSelfFinitePart φ 1| +
            |Real.eulerMascheroniConstant| + 1) ≤
          -(|completeWeilSelfFinitePart φ 1| +
            |Real.eulerMascheroniConstant| + 1) * ‖u‖ ^ 2 := by
          nlinarith only [hA0, hu_sq_le1, sq_nonneg ‖u‖]
        _ ≤ _ := mul_le_mul_of_nonneg_right hconst_lb (sq_nonneg _)
    linarith only [hlc_u, hconst_u]
  -- Center + separated cross + overlap-minus-downward
  have hcen := abs_fullWeilCenterMatrix_self_inner_le_of_mem_conductorSubspace
    (completeWeilPoleShift φ c) hR' hR4_N hlog hu hu1
  have hpole_le : |completeWeilPoleShift φ c| ≤ c := by
    rw [abs_of_nonneg (completeWeilPoleShift_nonneg φ hc0.le)]
    exact completeWeilPoleShift_le hφ.continuous
      hsupp hM hc0.le
  have hcen' :
      |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix
          (completeWeilPoleShift φ c) N) u, u⟫| ≤
        600 * (c * (1 + Real.log R') / Real.log N) := by
    have hcoef : 600 * |completeWeilPoleShift φ c| *
        (1 + Real.log R') / Real.log N ≤ 600 * (c * (1 + Real.log R') / Real.log N) := by
      apply (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpole_le (by norm_num))
          (by have := Real.log_natCast_nonneg R'; positivity)) (Real.log_natCast_nonneg N)).trans_eq
      ring
    exact hcen.trans ((mul_le_mul hcoef hu_sq_le1 (sq_nonneg _) (by positivity)).trans_eq (mul_one _))
  have hsep' :
      |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u, u⟫| ≤
        C_sep' * (c ^ 2 / Real.log N) := by
    have h1 := abs_separatedCrossErrorMatrix_inner_le_of_mem_conductorSubspace
      hφ hsupp hM
      hc0 hR' hR4_N hlog hu
    have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    calc
      _ ≤ C_sep' * c ^ 2 / Real.log N * ‖u‖ ^ 2 := h1
      _ = C_sep' * (c ^ 2 / Real.log N) * ‖u‖ ^ 2 := by ring
      _ ≤ C_sep' * (c ^ 2 / Real.log N) * 1 :=
        mul_le_mul_of_nonneg_left hu_sq_le1 (by positivity)
      _ = _ := mul_one _
  have hod' :
      2 * |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u -
          downwardPrimeVector φ c N u, u⟫| ≤
        2 * C_od * (c ^ 2 * (1 + Real.log R') * (1 + Real.log c) / Real.log N +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) := by
    have hh := hod hR' hRR_N hlog hc1 hw1 hRNT hu
    have hcoef : 0 ≤ C_od * (c ^ 2 * (1 + Real.log R') * (1 + Real.log c) / Real.log N +
        c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) := by
      have := Real.log_nonneg hc1
      have := Real.log_natCast_nonneg R'
      positivity
    have hs := hh.trans ((mul_le_mul_of_nonneg_left hu_sq_le1 hcoef).trans_eq (mul_one _))
    exact (mul_le_mul_of_nonneg_left hs zero_le_two).trans_eq (by ring)
  have hsum_err_le1 :
      |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix
          (completeWeilPoleShift φ c) N) u, u⟫| +
      |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u, u⟫| +
      2 * |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u -
          downwardPrimeVector φ c N u, u⟫| ≤ 1 := by
    have ht1 : 0 ≤ c * (1 + Real.log R') / Real.log N := by
      have := Real.log_natCast_nonneg R'; positivity
    have ht2 : 0 ≤ c ^ 2 / Real.log N := by
      have := Real.log_natCast_nonneg N; positivity
    have ht3 : 0 ≤ c ^ 2 * (1 + Real.log R') * (1 + Real.log c) / Real.log N := by
      have := Real.log_natCast_nonneg R'; have := Real.log_nonneg hc1; positivity
    have ht4 : 0 ≤ c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) := by positivity
    dsimp only [C_err] at herr
    nlinarith only [hcen', hsep', hod', herr, ht1, ht2, ht3, ht4, hC_sep'0, hC_od]
  have hpole0 := fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one
    φ c hN2 hu1 hu1
  have hdecomp := completeWeilMatrix_inner_eq_decomposition_at_every_overlap
    hφ hsupp hM
    hc0 hN1 u
  rw [overlap_sub_nonRatio_inner_eq hφ hsupp
      hM hc0 hN1 u, hpole0] at hdecomp
  change completeWeilEnergy φ c N u =
    renormalizedPrimeEnergy N u +
    (completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
      completeWeilSelfError φ c N) * ‖u‖ ^ 2 +
    ⟪Matrix.toEuclideanLin
      (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) u, u⟫ -
    ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u, u⟫ + 0 +
    (-⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫ +
      2 * ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u -
        downwardPrimeVector φ c N u, u⟫) at hdecomp
  have habs_c := (abs_le.mp (le_rfl : |⟪Matrix.toEuclideanLin
    (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) u, u⟫| ≤ _)).1
  have habs_s := (abs_le.mp (le_rfl : |⟪Matrix.toEuclideanLin
    (separatedCrossErrorMatrix φ c N) u, u⟫| ≤ _)).2
  have habs_o := (abs_le.mp (le_rfl : |⟪Matrix.toEuclideanLin
    (overlapMatrix φ c N) u -
    downwardPrimeVector φ c N u, u⟫| ≤ _)).1
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

private theorem overlap_diff_of_conductor_split {φ : ℝ → ℝ} {R' N : ℕ} {c C_ov : ℝ}
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
        |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, v⟫| ≤
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
    |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫ -
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) y, y⟫| ≤ 1 := by
  have hexp :
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫ -
        ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) y, y⟫ =
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v, v⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v, y⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) y, v⟫ := by
    rw [hu_split, map_add, inner_add_left, inner_add_right, inner_add_right]
    ring
  have h1 := hov hR'2 hR'2 hlog18_R' hlog18_R' hc1 hcL hw1 hRNT hRNT hv_mem hv_mem
  have h2 := hov hR'2 hR'2 hlog18_R' hlog18_R' hc1 hcL hw1 hRNT hRNT hv_mem hy_mem
  have h3 := hov hR'2 hR'2 hlog18_R' hlog18_R' hc1 hcL hw1 hRNT hRNT hy_mem hv_mem
  have hnorm_sum : ‖v‖ * ‖v‖ + ‖v‖ * ‖y‖ + ‖y‖ * ‖v‖ ≤ 5 * ‖v‖ := by
    nlinarith only [hv_le20, hy_le2, norm_nonneg v]
  rw [hexp]
  calc
    |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v, v⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v, y⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) y, v⟫| ≤
        |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v, v⟫| +
          |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v, y⟫| +
          |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) y, v⟫| :=
      abs_add_three_le _ _ _
    _ ≤ C_ov * c * (1 + Real.log c) * (‖v‖ * ‖v‖ + ‖v‖ * ‖y‖ + ‖y‖ * ‖v‖) := by
      linarith only [h1, h2, h3]
    _ ≤ C_ov * c * (1 + Real.log c) * (5 * (54 * (1 + Real.log R') / Real.log N)) := by
      refine mul_le_mul_of_nonneg_left (hnorm_sum.trans (by linarith only [hv_bound])) ?_
      have := Real.log_nonneg hc1; positivity
    _ = 270 * C_ov * (c * (1 + Real.log c) * (1 + Real.log R') / Real.log N) := by ring
    _ ≤ 1 := h270

/-- Above the low conductor space, the complete form retains adjunction energy
as well as a logarithmic gap. All error terms have one cutoff logarithm. -/
theorem exists_profile_completeWeilEnergy_ge_adjunction_and_log {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ x, x ∉ Set.Icc 0 1 → φ x = 0) (hM : 0 < ∫ x, φ x ^ 2) :
    ∃ C_coerc C_small : ℝ, 0 < C_coerc ∧ 0 < C_small ∧
      ∀ {Q R N : ℕ} {c : ℝ},
        2 ≤ Q → Q ≤ R → R ^ 6 ≤ N → 36 * (1 + Real.log R) ≤ Real.log N →
        1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        C_small * (c * (1 + Real.log c) * (1 + Real.log R) / Real.log N +
          c * (1 + Real.log R) / Real.log N + c ^ 2 / Real.log N +
          c ^ 2 * (1 + Real.log R) * (1 + Real.log c) / Real.log N +
          c ^ 2 * (R : ℝ) * Real.sqrt (Real.log N / N) +
          c ^ 5 * Real.log N / N + c ^ 3 / Real.sqrt Q +
          c ^ 3 * (R : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / Real.log N) ≤ 1 →
      ∀ a : ℕ → ℝ,
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace Q N)ᗮ →
        3 / 4 ≤ ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 →
        ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ≤ 1 →
        (1 / 8 : ℝ) * primeAdjunctionMass R a + (1 / 4 : ℝ) * Real.log Q -
          Real.log c - C_coerc ≤
        completeWeilEnergy φ c N
          (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) := by
  obtain ⟨C_dec, C_err, hC_dec, hC_err, hdec⟩ :=
    exists_profile_completeWeilEnergy_ge_prime_sub_overlap hφ hsupp hM
  obtain ⟨C_ov, hC_ov, hov⟩ := exists_overlapMatrix_inner_le_of_mem_conductorSubspace
    hφ hsupp hM
  obtain ⟨C_mid, hC_mid, hmid⟩ := exists_overlapMatrix_midBand_inner_le_cubic
    hφ hsupp hM
  refine ⟨C_dec + (Real.log 4 + 4) + 5,
    C_err + 1080 + 270 * C_ov + C_mid + 1, ?_, by positivity, ?_⟩
  · have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    positivity
  intro Q R N c hQ hQR hR6 hlog36 hc1 hcL hw hrad hsize hsmall a huQ hu_lo hu_hi
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  have hu : u ∈ conductorSubspace R N := sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N a
  have hR : 2 ≤ R := hQ.trans hQR
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have h18 : 18 * (1 + Real.log R) ≤ Real.log N := by
    have hh := Real.log_natCast_nonneg R
    linarith only [hlog36, hh]
  have hL : 0 < Real.log N := by
    have hh := Real.log_natCast_nonneg R
    linarith only [hlog36, hh]
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hlogR : 0 ≤ Real.log R := Real.log_natCast_nonneg R
  have hu1 : u ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    huQ v (conductorSubspace_mono (by omega : 1 ≤ Q) N hv)
  have ht1 : 0 ≤ c * (1 + Real.log c) * (1 + Real.log R) / Real.log N := by positivity
  have ht2 : 0 ≤ c * (1 + Real.log R) / Real.log N := by positivity
  have ht3 : 0 ≤ c ^ 2 / Real.log N := by positivity
  have ht4 : 0 ≤ c ^ 2 * (1 + Real.log R) * (1 + Real.log c) / Real.log N := by positivity
  have ht5 : 0 ≤ c ^ 2 * (R : ℝ) * Real.sqrt (Real.log N / N) := by positivity
  have ht6 : 0 ≤ c ^ 5 * Real.log N / N := by positivity
  have ht7 : 0 ≤ c ^ 3 / Real.sqrt Q := by positivity
  have ht8 : 0 ≤ c ^ 3 * (R : ℝ) ^ 4 / N := by positivity
  have ht9 : 0 ≤ c ^ 2 * (1 + Real.log c) / Real.log N := by positivity
  have hsumC : 0 ≤ C_err + 1080 + 270 * C_ov + C_mid + 1 := by positivity
  have hratio : 0 ≤ (1 + Real.log R) / Real.log N := by positivity
  have hratio_le : (1 + Real.log R) / Real.log N ≤
      c * (1 + Real.log c) * (1 + Real.log R) / Real.log N := by
    have hh : 1 ≤ c * (1 + Real.log c) := by nlinarith only [hc1, hlogc]
    have hm := mul_le_mul_of_nonneg_right hh hratio
    convert hm using 2 <;> first | rfl | ring
  have h1080 : 1080 * ((1 + Real.log R) / Real.log N) ≤ 1 :=
    mul_le_one_of_le_mul_le_one
      (by linarith only [hC_err, hC_ov, hC_mid]) hsumC hratio
      (by linarith only [hratio_le, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9]) hsmall
  have hlog1080 : 1080 * (1 + Real.log R) ≤ Real.log N := by
    rw [← mul_div_assoc, div_le_one hL] at h1080
    exact h1080
  have herr : C_err * (c * (1 + Real.log R) / Real.log N + c ^ 2 / Real.log N +
      c ^ 2 * (1 + Real.log R) * (1 + Real.log c) / Real.log N +
      c ^ 2 * (R : ℝ) * Real.sqrt (Real.log N / N)) ≤ 1 :=
    mul_le_one_of_le_mul_le_one
      (by linarith only [hC_ov, hC_mid]) hsumC (by linarith only [ht2, ht3, ht4, ht5])
      (by linarith only [ht1, ht6, ht7, ht8, ht9]) hsmall
  have h270 : 270 * C_ov * (c * (1 + Real.log c) * (1 + Real.log R) / Real.log N) ≤ 1 :=
    mul_le_one_of_le_mul_le_one
      (by linarith only [hC_err, hC_mid]) hsumC ht1
      (by linarith only [ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9]) hsmall
  have hmid1 : C_mid * (c ^ 2 * (1 + Real.log c) / Real.log N +
      c ^ 5 * Real.log N / N + c ^ 3 / Real.sqrt Q + c ^ 3 * (R : ℝ) ^ 4 / N) ≤ 1 :=
    mul_le_one_of_le_mul_le_one
      (by linarith only [hC_err, hC_ov]) hsumC (by linarith only [ht9, ht6, ht7, ht8])
      (by linarith only [ht1, ht2, ht3, ht4, ht5]) hsmall
  have hbase := hdec hR hR6 h18 hc1 hw hsize herr hu hu1 hu_hi
  have hprime := primePacket_energy_ge_adjunction_and_log_of_orthogonal
    hQ hQR hRR hlog1080 a huQ hu_lo hu_hi
  obtain ⟨hsplit, hv_mem, hy_mem, hv_bound, hv20, -, hy2⟩ :=
    lowBand_highBand_packet_split hQ hQR hRR h18 (show u = _ from rfl) huQ hu_lo hu_hi h1080
  have hdiff := overlap_diff_of_conductor_split hC_ov hov hR h18 hc1 hcL hw hsize
    hsplit hv_mem hy_mem hv_bound hv20 hy2 h270
  have ha0 : ∀ m ∈ Icc 1 Q, highBandCoeffs Q a m = 0 := fun m hm => if_pos (mem_Icc.mp hm).2
  have hmy := hmid hQ hQR hRR h18 hc1 hcL hw hrad hsize ha0
  change |⟪Matrix.toEuclideanLin (overlapMatrix φ c N)
      (highBandPacket Q R N a), highBandPacket Q R N a⟫| ≤
    C_mid * (c ^ 2 * (1 + Real.log c) / Real.log N +
      c ^ 5 * Real.log N / N + c ^ 3 / Real.sqrt Q + c ^ 3 * (R : ℝ) ^ 4 / N) *
      ‖highBandPacket Q R N a‖ ^ 2 at hmy
  have hy4 : ‖highBandPacket Q R N a‖ ^ 2 ≤ 4 := by
    nlinarith only [hy2, norm_nonneg (highBandPacket Q R N a)]
  have hov_y : |⟪Matrix.toEuclideanLin (overlapMatrix φ c N)
      (highBandPacket Q R N a), highBandPacket Q R N a⟫| ≤ 4 :=
    hmy.trans ((mul_le_mul hmid1 hy4 (sq_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hov_u : ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫ ≤ 5 := by
    linarith only [(abs_le.mp hdiff).2, (abs_le.mp hov_y).2]
  change (1 / 8 : ℝ) * primeAdjunctionMass R a + (1 / 4 : ℝ) * Real.log Q -
    Real.log c - (C_dec + (Real.log 4 + 4) + 5) ≤ completeWeilEnergy φ c N u
  linarith only [hbase, hprime, hov_u]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

