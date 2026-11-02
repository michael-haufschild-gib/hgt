import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompleteWeilSplitCrossBounds
import GaloisForLFunctions.CompletedArithmeticForms.HighConductorAdjunctionCoercivity

/-!
# A polynomial overlap loss on high-conductor spans

Logarithmic coefficient weights retain a fixed fraction of prime adjunction energy.
The remaining overlap loss is at most a profile constant times `c⁴(1 + log c)`,
uniformly across the conductor span and horizon.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics CriticalScaleArithmeticRigidity

private theorem weighted_pairing_payment {z E B : ℝ} (hB : 0 < B)
    (hz : z ^ 2 ≤ B * (2 + E)) :
    |z| ≤ E / 32 + 8 * B + 1 / 16 := by
  by_contra hn
  have hlt : E / 32 + 8 * B + 1 / 16 < |z| := lt_of_not_ge hn
  have hm := mul_lt_mul_of_pos_left hlt hB
  nlinarith only [hz, sq_abs z, sq_nonneg (|z| - 16 * B), hm]

/-- Every compact profile retains prime adjunction and logarithmic conductor energy,
with an explicit polynomial overlap loss. No spectral nonvanishing condition is needed. -/
theorem exists_profile_highConductor_polynomial_loss {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ x, x ∉ Set.Icc 0 1 → φ x = 0) (hM : 0 < ∫ x, φ x ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Q R N : ℕ} {c : ℝ},
      2 ≤ Q → Q ≤ R → R ^ 6 ≤ N → 1080 * (1 + Real.log R) ≤ Real.log N →
      1 ≤ c → c / N ≤ 1 / 3 →
      ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
      (1 + Real.log R) * (R : ℝ) ^ 2 * (Real.log N / N) ≤ 1 →
      ∀ a : ℕ → ℝ,
      (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace Q N)ᗮ →
      ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ = 1 →
      (1 / 16 : ℝ) * primeAdjunctionMass R a + (1 / 4 : ℝ) * Real.log Q - C * c ^ 4 * (1 + Real.log c) ≤
        completeWeilEnergy φ c N
          (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) := by
  obtain ⟨Cnear, hCnear, hnear⟩ :=
    exists_overlap_sub_downward_sq_le_logarithmic_weight hφ hsupp hM
  obtain ⟨Cup, hCup, hup⟩ :=
    exists_upwardPrimeVector_norm_le_of_mem_conductorSubspace hφ hsupp hM
  let Csep := 4 * (152 * (∫ x, |φ x|) ^ 2 / (∫ x, φ x ^ 2))
  let D₀ := |completeWeilSelfFinitePart φ 1| +
    |Real.eulerMascheroniConstant| + Real.exp (1 / 2) / 2
  let C := Real.log 4 + 4 + D₀ + Csep + Cup +
    8 * ((32 * 288 ^ 2 : ℝ) + 2 * Cnear + 2) + 2
  have hD₀ : 0 ≤ D₀ := by dsimp only [D₀]; positivity
  have hCsep : 0 ≤ Csep := by dsimp only [Csep]; positivity
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Q R N c hQ hQR hR6 hlog hc1 hw hsizeNear hsizeUp htail a huQ huNorm
  let K := c
  have hK : 1 ≤ K := hc1
  have hcK : c ≤ K := le_rfl
  let Bcen := (32 * 288 ^ 2 : ℝ) * K ^ 2 + 1
  let Bnear := Cnear * K ^ 4 * (2 + Real.log K) + 1
  let D := |completeWeilSelfFinitePart φ 1| + Real.log K +
    |Real.eulerMascheroniConstant| + Real.exp (1 / 2) / 2
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hBcen : 0 < Bcen := by dsimp only [Bcen]; positivity
  have hBnear : 0 < Bnear := by dsimp only [Bnear]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let E := primeAdjunctionMass R a
  let G := ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2
  have huN : ‖u‖ = 1 := huNorm
  have huSq : ‖u‖ ^ 2 = 1 := by rw [huN, one_pow]
  have hR : 2 ≤ R := hQ.trans hQR
  have hRR : R * R ≤ N := by
    have hp := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hp
  have hN2 : 2 ≤ N := by have hh := Nat.mul_le_mul hR hR; omega
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hlogcK : Real.log c ≤ Real.log K := Real.log_le_log hc0 hcK
  have hH : 0 ≤ 1 + Real.log R := by positivity
  have hL : 0 < Real.log N := by linarith only [hlog, Real.log_natCast_nonneg R]
  have h18 : 18 * (1 + Real.log R) ≤ Real.log N := by linarith only [hlog, hH]
  have hratio : (1 + Real.log R) / Real.log N ≤ 1 :=
    (div_le_one hL).mpr (by linarith only [hlog, hH])
  have hu : u ∈ conductorSubspace R N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N a
  have hu1 : u ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    huQ v (conductorSubspace_mono (by omega : 1 ≤ Q) N hv)
  have hE : 0 ≤ E := primeAdjunctionMass_nonneg R a
  have hG : 0 ≤ G := sum_nonneg fun m _ =>
    mul_nonneg (by positivity) (sq_nonneg _)
  have hGle : G ≤ 2 + E := by
    have hframe := (half_and_three_halves_riesz_of_log_le hR hRR h18 a).1
    change (1 / 2 : ℝ) * (∑ m ∈ Icc 1 R, a m ^ 2) ≤ ‖u‖ ^ 2 at hframe
    rw [huSq] at hframe
    have hdiag : G ≤ (∑ m ∈ Icc 1 R, a m ^ 2) + E := by
      dsimp only [G, E, primeAdjunctionMass]
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro m hm
      have ht := mul_nonneg (tameDifferent_nonneg m) (sq_nonneg (a m))
      nlinarith only [ht]
    linarith only [hframe, hdiag]
  have hpole : |completeWeilPoleShift φ c| ≤ K := by
    rw [abs_of_nonneg (completeWeilPoleShift_nonneg φ hc0.le)]
    exact (completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le).trans hcK
  have hpoleSq : completeWeilPoleShift φ c ^ 2 ≤ K ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hpole 2
  have hcenSq : ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      u, u⟫ ^ 2 ≤ Bcen * (2 + E) := by
    have hh := fullWeilCenterMatrix_cross_sq_le_logarithmic_weight
      (completeWeilPoleShift φ c) hR hR6 h18 a hu1 hu1
    rw [sq_abs] at hh
    change _ ≤ (32 * 288 ^ 2 : ℝ) * completeWeilPoleShift φ c ^ 2 *
      (1 + Real.log R) / Real.log N * G * ‖u‖ ^ 2 at hh
    rw [huSq, mul_one] at hh
    have hcoef : (32 * 288 ^ 2 : ℝ) * completeWeilPoleShift φ c ^ 2 *
        (1 + Real.log R) / Real.log N ≤ Bcen := by
      calc
        _ = (32 * 288 ^ 2 : ℝ) * completeWeilPoleShift φ c ^ 2 *
          ((1 + Real.log R) / Real.log N) := by ring
        _ ≤ (32 * 288 ^ 2 : ℝ) * K ^ 2 * 1 := by gcongr
        _ ≤ Bcen := by dsimp only [Bcen]; linarith
    exact hh.trans ((mul_le_mul_of_nonneg_right hcoef hG).trans
      (mul_le_mul_of_nonneg_left hGle hBcen.le))
  have hnearCoef : (1 + Real.log R) * ((1 + Real.log c) / Real.log N +
      (R : ℝ) ^ 2 * (Real.log N / N)) ≤ 2 + Real.log K := by
    have hfirst : (1 + Real.log c) * ((1 + Real.log R) / Real.log N) ≤ 1 + Real.log K := by
      calc
        _ ≤ (1 + Real.log K) * 1 := by gcongr
        _ = _ := mul_one _
    calc
      _ = (1 + Real.log c) * ((1 + Real.log R) / Real.log N) +
        (1 + Real.log R) * (R : ℝ) ^ 2 * (Real.log N / N) := by ring
      _ ≤ 2 + Real.log K := by linarith only [hfirst, htail]
  have hnearSq : ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u -
      downwardPrimeVector φ c N u, u⟫ ^ 2 ≤ Bnear * (2 + E) := by
    have hn := hnear hR hRR h18 hc1 hw hsizeNear a
    have hh := pow_le_pow_left₀ (abs_nonneg _)
      (abs_real_inner_le_norm (Matrix.toEuclideanLin (overlapMatrix φ c N) u -
        downwardPrimeVector φ c N u) u) 2
    rw [sq_abs, huN, mul_one] at hh
    have hcoef : Cnear * c ^ 4 * (1 + Real.log R) *
        ((1 + Real.log c) / Real.log N + (R : ℝ) ^ 2 * (Real.log N / N)) ≤ Bnear := by
      calc
        _ = Cnear * c ^ 4 * ((1 + Real.log R) *
          ((1 + Real.log c) / Real.log N + (R : ℝ) ^ 2 * (Real.log N / N))) := by ring
        _ ≤ Cnear * K ^ 4 * (2 + Real.log K) := by gcongr
        _ ≤ Bnear := by dsimp only [Bnear]; linarith
    exact hh.trans (hn.trans ((mul_le_mul_of_nonneg_right hcoef hG).trans
      (mul_le_mul_of_nonneg_left hGle hBnear.le)))
  have hcen := weighted_pairing_payment hBcen hcenSq
  have hnearPay := weighted_pairing_payment hBnear hnearSq
  have hsep : |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u, u⟫| ≤ Csep * K ^ 2 := by
    have hn := norm_separatedCrossErrorMatrix_le hφ hsupp hM hc0 hN1 u
    have hh := (abs_real_inner_le_norm _ u).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg u))
    rw [huN, mul_one, mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0.le hcK 2) hCsep)
  have hupPay : |⟪upwardPrimeVector φ c N u, u⟫| ≤ Cup * K * Real.sqrt (1 + Real.log K) := by
    have hn := hup hR h18 hc1 hw hsizeUp hu
    have hh := (abs_real_inner_le_norm _ u).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg u))
    rw [huN, mul_one, mul_one] at hh
    apply hh.trans
    gcongr
  have hw1 : c / N ≤ 1 := hw.trans (by norm_num)
  have herr := abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM hc0 hN1
    ((div_le_one hNR).mp hw1)
  have herr' : |completeWeilSelfError φ c N| ≤ Real.exp (1 / 2) / 2 :=
    herr.trans (mul_le_of_le_one_right (by positivity) hw1)
  have hself : -D ≤ completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
      completeWeilSelfError φ c N := by
    rw [completeWeilSelfFinitePart_eq_at_one_sub_log φ hc0]
    dsimp only [D]
    linarith only [neg_abs_le (completeWeilSelfFinitePart φ 1), hlogcK,
      le_abs_self Real.eulerMascheroniConstant, neg_abs_le (completeWeilSelfError φ c N), herr']
  have hpole0 := fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one φ c hN2 hu1 hu1
  have hprime := primePacket_energy_ge_adjunction_and_log_of_orthogonal hQ hQR hRR hlog a huQ
    (by rw [huNorm]; norm_num) huNorm.le
  have hdecomp := completeWeilMatrix_inner_eq_decomposition_at_every_overlap hφ hsupp hM hc0 hN1 u
  rw [fullWeilNonRatioMatrix_eq_downward_add_upward hφ hsupp hM hc0 hN1 u,
    inner_add_left, hpole0, huSq, mul_one, add_zero] at hdecomp
  change completeWeilEnergy φ c N u = _ at hdecomp
  change (1 / 8 : ℝ) * E + (1 / 4 : ℝ) * Real.log Q - (Real.log 4 + 4) ≤
    renormalizedPrimeEnergy N u at hprime
  dsimp only [renormalizedPrimeEnergy] at hprime
  rw [huSq, mul_one] at hprime
  rw [inner_sub_left] at hnearPay
  have hcenLower := neg_abs_le
    ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) u, u⟫
  have hnearLower := neg_abs_le
    (⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫ - ⟪downwardPrimeVector φ c N u, u⟫)
  have hsepUpper := le_abs_self ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u, u⟫
  have hupUpper := le_abs_self ⟪upwardPrimeVector φ c N u, u⟫
  have hold : (1 / 16 : ℝ) * E + (1 / 4 : ℝ) * Real.log Q -
      (Real.log 4 + 4 + D + Csep * K ^ 2 + Cup * K * Real.sqrt (1 + Real.log K) +
        8 * (Bcen + Bnear) + 1) ≤ completeWeilEnergy φ c N u := by
    linarith only [hdecomp, hprime, hself, hcen, hnearPay, hsep, hupPay,
      hcenLower, hnearLower, hsepUpper, hupUpper]
  let w := c ^ 4 * (1 + Real.log c)
  have hc4 : 1 ≤ c ^ 4 := one_le_pow₀ hc1
  have hc24 : c ^ 2 ≤ c ^ 4 := pow_le_pow_right₀ hc1 (by norm_num)
  have hw4 : c ^ 4 ≤ w := le_mul_of_one_le_right (pow_nonneg hc0.le 4)
    (by linarith only [hlogc])
  have hw1 : 1 ≤ w := hc4.trans hw4
  have hw2 : c ^ 2 ≤ w := hc24.trans hw4
  have hwlog : 1 + Real.log c ≤ w :=
    le_mul_of_one_le_left (by linarith only [hlogc]) hc4
  have hroot : Real.sqrt (1 + Real.log c) ≤ c := by
    have hlogc_le : 1 + Real.log c ≤ c := by
      linarith only [Real.log_le_sub_one_of_pos hc0]
    have hc2 : c ≤ c ^ 2 := by nlinarith only [hc1]
    nlinarith only [Real.sq_sqrt (by linarith only [hlogc] : 0 ≤ 1 + Real.log c),
      Real.sqrt_nonneg (1 + Real.log c), hlogc_le, hc2, hc0]
  have hupCost : Cup * K * Real.sqrt (1 + Real.log K) ≤ Cup * w := by
    calc
      _ ≤ Cup * c ^ 2 := by
        have hh := mul_le_mul_of_nonneg_left hroot (mul_nonneg hCup.le hc0.le)
        dsimp only [K]
        nlinarith only [hh]
      _ ≤ _ := mul_le_mul_of_nonneg_left hw2 hCup.le
  have hcenCost : Bcen ≤ ((32 * 288 ^ 2 : ℝ) + 1) * w := by
    have hh := mul_le_mul_of_nonneg_left hw2 (by norm_num : (0 : ℝ) ≤ 32 * 288 ^ 2)
    dsimp only [Bcen, K]
    linarith only [hh, hw1]
  have hnearCost : Bnear ≤ (2 * Cnear + 1) * w := by
    have hh := mul_le_mul_of_nonneg_left
      (show 2 + Real.log c ≤ 2 * (1 + Real.log c) by linarith only [hlogc])
      (mul_nonneg hCnear.le (pow_nonneg hc0.le 4))
    change Cnear * c ^ 4 * (2 + Real.log c) ≤ Cnear * c ^ 4 * (2 * (1 + Real.log c)) at hh
    dsimp only [Bnear, K, w]
    dsimp only [w] at hw1
    nlinarith only [hh, hw1]
  have hDCost : D ≤ (D₀ + 1) * w := by
    have hh := mul_le_mul_of_nonneg_left hw1 hD₀
    dsimp only [D, K, D₀]
    dsimp only [D₀] at hh
    linarith only [hh, hwlog]
  have hbaseCost : Real.log 4 + 4 ≤ (Real.log 4 + 4) * w :=
    le_mul_of_one_le_right (by positivity) hw1
  have hsepCost := mul_le_mul_of_nonneg_left hw2 hCsep
  have hcost : Real.log 4 + 4 + D + Csep * K ^ 2 +
      Cup * K * Real.sqrt (1 + Real.log K) + 8 * (Bcen + Bnear) + 1 ≤ C * w := by
    dsimp only [C, K]
    linarith only [hbaseCost, hDCost, hsepCost, hupCost, hcenCost, hnearCost, hw1]
  change (1 / 16 : ℝ) * E + (1 / 4 : ℝ) * Real.log Q - C * c ^ 4 * (1 + Real.log c) ≤ _
  dsimp only [w] at hcost
  linarith only [hold, hcost]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
