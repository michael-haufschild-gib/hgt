import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TerminalSupportSharpensTheWeightedNearPairing
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LinearOverlapComparisonRetainsItsCutoffRatio
import GaloisForLFunctions.CompletedArithmeticForms.HighConductorAdjunctionCoercivity
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandQuadraticCenterBounds

/-!
# Terminal payment retains the growing high-conductor gap

The near remainder is paid by prime adjunction. The overlap comparison keeps
its linear cutoff ratio, so its error can be compared with the growing
logarithmic conductor gap instead of an absolute constant.
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

/-- Terminal payment retains a growing high-conductor gap with an explicit
linear cutoff-ratio cost and cubic lag remainder. -/
theorem exists_profile_highConductor_gap_of_terminal_and_overlap_rates {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ x, x ∉ Set.Icc 0 1 → φ x = 0) (hM : 0 < ∫ x, φ x ^ 2) :
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧ ∀ {Q R N : ℕ} {c : ℝ},
      2 ≤ Q → Q ≤ R → R ^ 6 ≤ N → 1080 * (1 + Real.log R) ≤ Real.log N →
      1 ≤ c → c / N ≤ 1 / 3 →
      4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      c ^ 4 * (1 + Real.log R) *
        ((1 + Real.log c) ^ 2 / (Real.log N) ^ 2 +
          (R : ℝ) ^ 2 * (1 + Real.log c) / N) ≤ 1 →
      ∀ a : ℕ → ℝ,
      (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace Q N)ᗮ →
      ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ = 1 →
      (1 / 16 : ℝ) * primeAdjunctionMass R a + (1 / 4 : ℝ) * Real.log Q -
        Real.log c - D - C * (c * (1 + Real.log R) / Real.log N +
          c ^ 2 * (1 + Real.log c) / Real.log N + c ^ 5 * Real.log N / N +
          c ^ 3 / Real.sqrt Q + c ^ 3 * (R : ℝ) ^ 4 / N) ≤
        completeWeilEnergy φ c N
          (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) := by
  obtain ⟨Cnear, hCnear, hnear⟩ :=
    exists_overlap_sub_downward_inner_sq_le_logarithmic_terminal_weight hφ hsupp hM
  obtain ⟨Cov, hCov, hov⟩ := exists_overlapMatrix_high_inner_le_linear_cutoff_rate hφ hsupp hM
  let Csep := 36 * (152 * (∫ x, |φ x|) ^ 2 / (∫ x, φ x ^ 2))
  let D₀ := |completeWeilSelfFinitePart φ 1| +
    |Real.eulerMascheroniConstant| + Real.exp (1 / 2) / 2
  let D₁ := Real.log 4 + 4 + D₀ + Csep + 16 * (Cnear + 1) + 2
  let C := Cov + 600
  have hD₀ : 0 ≤ D₀ := by dsimp only [D₀]; positivity
  have hCsep : 0 ≤ Csep := by dsimp only [Csep]; positivity
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hD₁ : 0 < D₁ := by dsimp only [D₁]; positivity
  refine ⟨D₁, C, hD₁, hC, ?_⟩
  intro Q R N c hQ hQR hR6 hlog hc1 hw hrad hsizeNear hterminal a huQ huNorm
  let K := c
  have hK : 1 ≤ K := hc1
  have hcK : c ≤ K := le_rfl
  let Bnear := Cnear + 1
  let D := |completeWeilSelfFinitePart φ 1| + Real.log K +
    |Real.eulerMascheroniConstant| + Real.exp (1 / 2) / 2
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
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
  have hR4 : R ^ 4 ≤ N :=
    (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 4 ≤ 6)).trans hR6
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
  have hcen : |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      u, u⟫| ≤ 600 * (c * (1 + Real.log R) / Real.log N) := by
    have hh := abs_fullWeilCenterMatrix_self_inner_le_of_mem_conductorSubspace
      (completeWeilPoleShift φ c) hR hR4 h18 hu hu1
    rw [huSq, mul_one] at hh
    calc
      _ ≤ 600 * |completeWeilPoleShift φ c| * (1 + Real.log R) / Real.log N := hh
      _ ≤ 600 * c * (1 + Real.log R) / Real.log N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpole (by norm_num)) hH) hL.le
      _ = _ := by ring
  have hnearSq : ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u -
      downwardPrimeVector φ c N u, u⟫ ^ 2 ≤ Bnear * (2 + E) := by
    have hh := hnear hR hRR h18 hc1 hw hsizeNear a
    change |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u -
      downwardPrimeVector φ c N u, u⟫| ^ 2 ≤
      Cnear * c ^ 4 * (1 + Real.log R) *
        ((1 + Real.log c) ^ 2 / (Real.log N) ^ 2 +
          (R : ℝ) ^ 2 * (1 + Real.log c) / N) * G * ‖u‖ ^ 2 at hh
    rw [sq_abs, huSq, mul_one] at hh
    have hcoef : Cnear * c ^ 4 * (1 + Real.log R) *
        ((1 + Real.log c) ^ 2 / (Real.log N) ^ 2 +
          (R : ℝ) ^ 2 * (1 + Real.log c) / N) ≤ Bnear := by
      calc
        _ = Cnear * (c ^ 4 * (1 + Real.log R) *
            ((1 + Real.log c) ^ 2 / (Real.log N) ^ 2 +
              (R : ℝ) ^ 2 * (1 + Real.log c) / N)) := by ring
        _ ≤ Cnear * 1 := mul_le_mul_of_nonneg_left hterminal hCnear.le
        _ ≤ Bnear := by dsimp only [Bnear]; linarith only
    exact hh.trans ((mul_le_mul_of_nonneg_right hcoef hG).trans
      (mul_le_mul_of_nonneg_left hGle hBnear.le))
  have hnearPay := weighted_pairing_payment hBnear hnearSq
  have hcSq : c ^ 2 / Real.log N ≤ 1 := by
    have hlog1 : 1 ≤ (1 + Real.log c) ^ 2 := by nlinarith only [hlogc]
    have hfrac : 1 / (Real.log N) ^ 2 ≤
        (1 + Real.log c) ^ 2 / (Real.log N) ^ 2 +
          (R : ℝ) ^ 2 * (1 + Real.log c) / N := by
      exact (div_le_div_of_nonneg_right hlog1 (sq_nonneg _)).trans
        (le_add_of_nonneg_right (by positivity))
    have hs : (c ^ 2 / Real.log N) ^ 2 ≤ 1 := by
      calc
        _ = c ^ 4 * 1 * (1 / (Real.log N) ^ 2) := by rw [div_pow]; ring
        _ ≤ c ^ 4 * (1 + Real.log R) *
            ((1 + Real.log c) ^ 2 / (Real.log N) ^ 2 +
              (R : ℝ) ^ 2 * (1 + Real.log c) / N) :=
          mul_le_mul (mul_le_mul_of_nonneg_left
            (by linarith only [Real.log_natCast_nonneg R]) (by positivity))
            hfrac (by positivity) (by positivity)
        _ ≤ 1 := hterminal
    nlinarith only [hs, sq_nonneg (c ^ 2 / Real.log N - 1)]
  have hsep : |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u, u⟫| ≤ Csep := by
    have hh := abs_separatedCrossErrorMatrix_inner_le_of_mem_conductorSubspace
      hφ hsupp hM hc0 hR hR4 h18 hu
    rw [huSq, mul_one] at hh
    change _ ≤ Csep * c ^ 2 / Real.log N at hh
    calc
      _ ≤ Csep * c ^ 2 / Real.log N := hh
      _ = Csep * (c ^ 2 / Real.log N) := by ring
      _ ≤ Csep * 1 := mul_le_mul_of_nonneg_left hcSq hCsep
      _ = _ := mul_one _
  let rate := c * (1 + Real.log R) / Real.log N +
    c ^ 2 * (1 + Real.log c) / Real.log N + c ^ 5 * Real.log N / N +
    c ^ 3 / Real.sqrt Q + c ^ 3 * (R : ℝ) ^ 4 / N
  have hovPay : |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫| ≤ Cov * rate := by
    have hcL : c ≤ Real.log N := by
      have hc2 : c ≤ c ^ 2 := by nlinarith only [hc1]
      exact hc2.trans ((div_le_one hL).mp hcSq)
    exact hov hQ hQR hR6 hlog hc1 hcL hw hrad hsizeNear a huQ huNorm
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
  rw [overlap_sub_nonRatio_inner_eq hφ hsupp hM hc0 hN1 u,
    hpole0, huSq, mul_one, add_zero, inner_sub_left] at hdecomp
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
  have hovUpper := le_abs_self ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫
  have hold : (1 / 16 : ℝ) * E + (1 / 4 : ℝ) * Real.log Q -
      (Real.log 4 + 4 + D + 600 * (c * (1 + Real.log R) / Real.log N) + Csep +
        Cov * rate + 16 * Bnear + 1) ≤ completeWeilEnergy φ c N u := by
    linarith only [hdecomp, hprime, hself, hcen, hnearPay, hsep, hovPay,
      hcenLower, hnearLower, hsepUpper, hovUpper]
  have hrateTail : 0 ≤ rate - c * (1 + Real.log R) / Real.log N := by
    have h1 : 0 ≤ c ^ 2 * (1 + Real.log c) / Real.log N := by positivity
    have h2 : 0 ≤ c ^ 5 * Real.log N / N := by positivity
    have h3 : 0 ≤ c ^ 3 / Real.sqrt Q := by positivity
    have h4 : 0 ≤ c ^ 3 * (R : ℝ) ^ 4 / N := by positivity
    dsimp only [rate]
    linarith only [h1, h2, h3, h4]
  have hcost : 600 * (c * (1 + Real.log R) / Real.log N) + Cov * rate ≤ C * rate := by
    have hh := mul_nonneg (by norm_num : (0 : ℝ) ≤ 600) hrateTail
    dsimp only [C]
    linarith only [hh]
  have hD_eq : D = D₀ + Real.log c := by dsimp only [D, D₀, K]; ring
  change (1 / 16 : ℝ) * E + (1 / 4 : ℝ) * Real.log Q - Real.log c - D₁ - C * rate ≤ _
  dsimp only [D₁, Bnear] at *
  linarith only [hold, hcost, hD_eq]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
