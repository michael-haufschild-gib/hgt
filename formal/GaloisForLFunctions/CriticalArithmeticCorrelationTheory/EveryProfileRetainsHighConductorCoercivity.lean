import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompleteWeilSplitCrossBounds
import GaloisForLFunctions.CompletedArithmeticForms.HighConductorAdjunctionCoercivity

/-!
# High conductor coercivity for every compact profile

Logarithmic coefficient weights allow the center and near terms to spend a fixed fraction of
prime adjunction energy. Their remaining cost is bounded on bounded overlap intervals. The
complete form therefore retains a logarithmic conductor gap without a Fourier zero restriction.
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

/-- On bounded overlap, every compact profile retains adjunction energy and a high-conductor gap. -/
theorem exists_profile_highConductor_coercivity {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ x, x ∉ Set.Icc 0 1 → φ x = 0) (hM : 0 < ∫ x, φ x ^ 2)
    {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Q R N : ℕ} {c : ℝ},
      2 ≤ Q → Q ≤ R → R ^ 6 ≤ N → 1080 * (1 + Real.log R) ≤ Real.log N →
      1 ≤ c → c ≤ K → c / N ≤ 1 / 3 →
      ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
      (1 + Real.log R) * (R : ℝ) ^ 2 * (Real.log N / N) ≤ 1 →
      ∀ a : ℕ → ℝ,
      (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace Q N)ᗮ →
      ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ = 1 →
      (1 / 16 : ℝ) * primeAdjunctionMass R a + (1 / 4 : ℝ) * Real.log Q - C ≤
        completeWeilEnergy φ c N
          (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) := by
  obtain ⟨Cnear, hCnear, hnear⟩ :=
    exists_overlap_sub_downward_sq_le_logarithmic_weight hφ hsupp hM
  obtain ⟨Cup, hCup, hup⟩ :=
    exists_upwardPrimeVector_norm_le_of_mem_conductorSubspace hφ hsupp hM
  let Csep := 4 * (152 * (∫ x, |φ x|) ^ 2 / (∫ x, φ x ^ 2))
  let Bcen := (32 * 288 ^ 2 : ℝ) * K ^ 2 + 1
  let Bnear := Cnear * K ^ 4 * (2 + Real.log K) + 1
  let D := |completeWeilSelfFinitePart φ 1| + Real.log K +
    |Real.eulerMascheroniConstant| + Real.exp (1 / 2) / 2
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hCsep : 0 ≤ Csep := by dsimp only [Csep]; positivity
  have hBcen : 0 < Bcen := by dsimp only [Bcen]; positivity
  have hBnear : 0 < Bnear := by dsimp only [Bnear]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨Real.log 4 + 4 + D + Csep * K ^ 2 + Cup * K * Real.sqrt (1 + Real.log K) +
    8 * (Bcen + Bnear) + 1, ?_, ?_⟩
  · have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    positivity
  intro Q R N c hQ hQR hR6 hlog hc1 hcK hw hsizeNear hsizeUp htail a huQ huNorm
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
  change (1 / 16 : ℝ) * E + (1 / 4 : ℝ) * Real.log Q - _ ≤ completeWeilEnergy φ c N u
  linarith only [hdecomp, hprime, hself, hcen, hnearPay, hsep, hupPay,
    hcenLower, hnearLower, hsepUpper, hupUpper]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
