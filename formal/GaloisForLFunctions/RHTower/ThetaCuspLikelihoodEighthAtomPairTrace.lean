import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthPairTraceIntegral

open MeasureTheory Set
open scoped BigOperators ENNReal

/-!
# Exact atom-pair realization of the eighth score trace

Shifted exponential moments of each mixed point-ray spectral atom are evaluated exactly.  Product
factorization then identifies the explicit ordered atom-pair mass, including its two-ray Taylor
operator, with the literal eighth-score integral on the product carrier.
-/

namespace RHTower

noncomputable section

private theorem integrableOn_pow_mul_exp_neg_rate_pairTrace
    (n : ℕ) {B : ℝ} (hB : 0 < B) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-(B * u))) (Ioi 0) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn : (-1 : ℝ) < (n : ℝ) := by linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (n : ℝ)) (b := B) hn (by norm_num) hB
  convert h using 1
  funext u
  simp only [Real.rpow_one]
  rw [Real.rpow_natCast]
  congr 1
  ring_nf

private theorem setIntegral_Ioi_comp_add_right_pairTrace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (a h : ℝ) :
    (∫ y in Ioi (a - h), F (y + h)) = ∫ x in Ioi a, F x := by
  have hmp : MeasurePreserving (fun y : ℝ => y + h) volume volume :=
    measurePreserving_add_right volume h
  have hemb : MeasurableEmbedding (fun y : ℝ => y + h) :=
    measurableEmbedding_addRight h
  have hpre : (fun y : ℝ => y + h) ⁻¹' Ioi a = Ioi (a - h) := by
    ext y
    simp [Set.mem_Ioi, sub_lt_iff_lt_add]
  have h1 := hmp.setIntegral_preimage_emb hemb F (Ioi a)
  rw [hpre] at h1
  exact h1

private theorem integral_Ioi_pow_mul_exp_neg_rate_shifted
    (q : ℕ) (d : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ in Ioi d, t ^ q * Real.exp (-(B * t))) =
      Real.exp (-(B * d)) *
        ∑ i ∈ Finset.range (q + 1),
          (q.choose i : ℝ) * d ^ (q - i) * (i.factorial : ℝ) / B ^ (i + 1) := by
  have htrans := setIntegral_Ioi_comp_add_right_pairTrace
    (fun t : ℝ => t ^ q * Real.exp (-(B * t))) d d
  rw [sub_self] at htrans
  rw [← htrans]
  have hfun : (fun u : ℝ =>
      (u + d) ^ q * Real.exp (-(B * (u + d)))) =
      fun u => Real.exp (-(B * d)) *
        ∑ i ∈ Finset.range (q + 1),
          ((q.choose i : ℝ) * d ^ (q - i)) *
            (u ^ i * Real.exp (-(B * u))) := by
    funext u
    rw [show Real.exp (-(B * (u + d))) =
        Real.exp (-(B * d)) * Real.exp (-(B * u)) by
      rw [← Real.exp_add]
      congr 1
      ring]
    rw [add_pow]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfun, integral_const_mul, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul, integral_Ioi_pow_mul_exp_neg_rate i hB]
    ring
  · intro i hi
    exact (integrableOn_pow_mul_exp_neg_rate_pairTrace i hB).const_mul _

private theorem integrable_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
    {n : ℕ} (hn : 2 ≤ n) (q : ℕ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => t ^ q * Real.exp (-(B * t)))
      (thetaCuspAtomLikelihoodSpectralMeasure n) := by
  have hglobal :=
    integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure q hB
  have hnEq : n - 2 + 2 = n := by omega
  rw [← hnEq]
  convert hglobal.mono_measure (Measure.le_sum _ (n - 2)) using 1
  funext t
  congr 2
  ring

/-- Exact exponentially tilted moment of one mixed atom-ray spectral carrier. -/
theorem integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure
    {n : ℕ} (hn : 2 ≤ n) (q : ℕ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, t ^ q * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure n) =
      Real.exp (-(3 / 2 : ℝ) * thetaCuspLikelihoodGap n) *
        Real.exp (-(B * thetaCuspLikelihoodGap n)) *
          ((n : ℝ) ^ 4 * thetaCuspLikelihoodGap n ^ q +
            (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n *
              (∑ i ∈ Finset.range (q + 1),
                (q.choose i : ℝ) * thetaCuspLikelihoodGap n ^ (q - i) *
                  (i.factorial : ℝ) / B ^ (i + 1))) := by
  let f : ℝ → ℝ := fun t => t ^ q * Real.exp (-(B * t))
  have hwhole :=
    integrable_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure hn q hB
  have hparts :
      Integrable f
          (ENNReal.ofReal (thetaCuspLikelihoodAtomWeight n) •
            Measure.dirac (thetaCuspLikelihoodGap n)) ∧
        Integrable f
          (ENNReal.ofReal (thetaCuspLikelihoodRayWeight n) •
            volume.restrict (Ioi (thetaCuspLikelihoodGap n))) := by
    simpa only [f, thetaCuspAtomLikelihoodSpectralMeasure,
      integrable_add_measure] using hwhole
  rw [thetaCuspAtomLikelihoodSpectralMeasure,
    integral_add_measure hparts.1 hparts.2,
    integral_smul_measure, integral_dirac, integral_smul_measure]
  change ENNReal.toReal (ENNReal.ofReal (thetaCuspLikelihoodAtomWeight n)) *
        f (thetaCuspLikelihoodGap n) +
      ENNReal.toReal (ENNReal.ofReal (thetaCuspLikelihoodRayWeight n)) *
        (∫ t : ℝ in Ioi (thetaCuspLikelihoodGap n), f t) = _
  rw [ENNReal.toReal_ofReal (thetaCuspLikelihoodAtomWeight_pos (by omega)).le,
    ENNReal.toReal_ofReal (thetaCuspLikelihoodRayWeight_pos hn).le,
    integral_Ioi_pow_mul_exp_neg_rate_shifted q (thetaCuspLikelihoodGap n) hB]
  unfold thetaCuspLikelihoodAtomWeight thetaCuspLikelihoodRayWeight
  dsimp only [f]
  ring

private theorem integrable_add_pow_mul_exp_neg_thetaCuspAtomPairMeasure
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (q : ℕ)
    {B : ℝ} (hB : 0 < B) :
    Integrable (fun z : ℝ × ℝ =>
      (z.1 + z.2) ^ q * Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)))
      ((thetaCuspAtomLikelihoodSpectralMeasure n).prod
        (thetaCuspAtomLikelihoodSpectralMeasure m)) := by
  rw [show (fun z : ℝ × ℝ =>
      (z.1 + z.2) ^ q * Real.exp (-(B * z.1)) * Real.exp (-(B * z.2))) =
      fun z => ∑ i ∈ Finset.range (q + 1),
        (q.choose i : ℝ) *
          (z.1 ^ i * Real.exp (-(B * z.1))) *
          (z.2 ^ (q - i) * Real.exp (-(B * z.2))) by
    funext z
    rw [add_pow]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  apply MeasureTheory.integrable_finsetSum
  intro i hi
  have hp :=
    (integrable_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure hn i hB).mul_prod
      (integrable_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure hm (q - i) hB)
  simpa only [mul_assoc] using hp.const_mul (q.choose i : ℝ)

private theorem integral_add_pow_mul_exp_neg_thetaCuspAtomPairMeasure
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (q : ℕ)
    {B : ℝ} (hB : 0 < B) :
    (∫ z : ℝ × ℝ,
      (z.1 + z.2) ^ q * Real.exp (-(B * z.1)) * Real.exp (-(B * z.2))
        ∂(thetaCuspAtomLikelihoodSpectralMeasure n).prod
          (thetaCuspAtomLikelihoodSpectralMeasure m)) =
      ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
        (∫ t : ℝ, t ^ i * Real.exp (-(B * t))
          ∂thetaCuspAtomLikelihoodSpectralMeasure n) *
        (∫ t : ℝ, t ^ (q - i) * Real.exp (-(B * t))
          ∂thetaCuspAtomLikelihoodSpectralMeasure m) := by
  letI : SFinite (thetaCuspAtomLikelihoodSpectralMeasure n) := by
    dsimp [thetaCuspAtomLikelihoodSpectralMeasure]
    infer_instance
  letI : SFinite (thetaCuspAtomLikelihoodSpectralMeasure m) := by
    dsimp [thetaCuspAtomLikelihoodSpectralMeasure]
    infer_instance
  rw [show (fun z : ℝ × ℝ =>
      (z.1 + z.2) ^ q * Real.exp (-(B * z.1)) * Real.exp (-(B * z.2))) =
      fun z => ∑ i ∈ Finset.range (q + 1),
        (q.choose i : ℝ) *
          ((z.1 ^ i * Real.exp (-(B * z.1))) *
            (z.2 ^ (q - i) * Real.exp (-(B * z.2)))) by
    funext z
    rw [add_pow]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  have hint : ∀ i ∈ Finset.range (q + 1),
      Integrable (fun z : ℝ × ℝ =>
        (q.choose i : ℝ) *
          ((z.1 ^ i * Real.exp (-(B * z.1))) *
            (z.2 ^ (q - i) * Real.exp (-(B * z.2)))))
        ((thetaCuspAtomLikelihoodSpectralMeasure n).prod
          (thetaCuspAtomLikelihoodSpectralMeasure m)) := by
    intro i hi
    exact ((integrable_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure hn i hB).mul_prod
      (integrable_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure hm (q - i) hB)).const_mul _
  rw [MeasureTheory.integral_finsetSum _ hint]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul]
  rw [MeasureTheory.integral_prod_mul
    (fun t : ℝ => t ^ i * Real.exp (-(B * t)))
    (fun t : ℝ => t ^ (q - i) * Real.exp (-(B * t)))]
  ring

set_option maxHeartbeats 400000 in
/-- The explicit atom-pair score mass is its literal product-measure eighth-score integral. -/
theorem thetaCuspLikelihoodAtomPairEighthScoreMass_eq_integral
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (A : ℝ)
    {B : ℝ} (hB : 0 < B) :
    thetaCuspLikelihoodAtomPairEighthScoreMass n m A B =
      ∫ z : ℝ × ℝ,
        thetaCuspLikelihoodEighthSourceScore (A * (z.1 + z.2)) *
          Real.exp (-(B * z.1)) * Real.exp (-(B * z.2))
        ∂(thetaCuspAtomLikelihoodSpectralMeasure n).prod
          (thetaCuspAtomLikelihoodSpectralMeasure m) := by
  let μ := thetaCuspAtomLikelihoodSpectralMeasure n
  let ν := thetaCuspAtomLikelihoodSpectralMeasure m
  let N : ℕ → ℝ := fun q => ∫ t : ℝ, t ^ q * Real.exp (-(B * t)) ∂μ
  let M : ℕ → ℝ := fun q => ∫ t : ℝ, t ^ q * Real.exp (-(B * t)) ∂ν
  have hpow (q : ℕ) : Integrable (fun z : ℝ × ℝ =>
      (z.1 + z.2) ^ q * Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)))
      (μ.prod ν) := by
    simpa only [μ, ν] using
      integrable_add_pow_mul_exp_neg_thetaCuspAtomPairMeasure hn hm q hB
  have heval (q : ℕ) :
      (∫ z : ℝ × ℝ,
        (z.1 + z.2) ^ q * Real.exp (-(B * z.1)) * Real.exp (-(B * z.2))
          ∂μ.prod ν) =
        ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * N i * M (q - i) := by
    simpa only [μ, ν, N, M] using
      integral_add_pow_mul_exp_neg_thetaCuspAtomPairMeasure hn hm q hB
  have hscore :
      (∫ z : ℝ × ℝ,
        thetaCuspLikelihoodEighthSourceScore (A * (z.1 + z.2)) *
          Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)) ∂μ.prod ν) =
        A ^ 8 * (∫ z : ℝ × ℝ, (z.1 + z.2) ^ 8 *
          Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)) ∂μ.prod ν) -
        28 * A ^ 7 * (∫ z : ℝ × ℝ, (z.1 + z.2) ^ 7 *
          Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)) ∂μ.prod ν) +
        266 * A ^ 6 * (∫ z : ℝ × ℝ, (z.1 + z.2) ^ 6 *
          Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)) ∂μ.prod ν) -
        1050 * A ^ 5 * (∫ z : ℝ × ℝ, (z.1 + z.2) ^ 5 *
          Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)) ∂μ.prod ν) +
        1701 * A ^ 4 * (∫ z : ℝ × ℝ, (z.1 + z.2) ^ 4 *
          Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)) ∂μ.prod ν) -
        966 * A ^ 3 * (∫ z : ℝ × ℝ, (z.1 + z.2) ^ 3 *
          Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)) ∂μ.prod ν) +
        127 * A ^ 2 * (∫ z : ℝ × ℝ, (z.1 + z.2) ^ 2 *
          Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)) ∂μ.prod ν) -
        A * (∫ z : ℝ × ℝ, (z.1 + z.2) *
          Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)) ∂μ.prod ν) := by
    unfold thetaCuspLikelihoodEighthSourceScore
    let g8 : ℝ × ℝ → ℝ := fun z => A ^ 8 * ((z.1 + z.2) ^ 8 *
      Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)))
    let g7 : ℝ × ℝ → ℝ := fun z => (28 * A ^ 7) * ((z.1 + z.2) ^ 7 *
      Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)))
    let g6 : ℝ × ℝ → ℝ := fun z => (266 * A ^ 6) * ((z.1 + z.2) ^ 6 *
      Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)))
    let g5 : ℝ × ℝ → ℝ := fun z => (1050 * A ^ 5) * ((z.1 + z.2) ^ 5 *
      Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)))
    let g4 : ℝ × ℝ → ℝ := fun z => (1701 * A ^ 4) * ((z.1 + z.2) ^ 4 *
      Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)))
    let g3 : ℝ × ℝ → ℝ := fun z => (966 * A ^ 3) * ((z.1 + z.2) ^ 3 *
      Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)))
    let g2 : ℝ × ℝ → ℝ := fun z => (127 * A ^ 2) * ((z.1 + z.2) ^ 2 *
      Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)))
    let g1 : ℝ × ℝ → ℝ := fun z => A * ((z.1 + z.2) *
      Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)))
    have h8 : Integrable g8 (μ.prod ν) := (hpow 8).const_mul _
    have h7 : Integrable g7 (μ.prod ν) := (hpow 7).const_mul _
    have h6 : Integrable g6 (μ.prod ν) := (hpow 6).const_mul _
    have h5 : Integrable g5 (μ.prod ν) := (hpow 5).const_mul _
    have h4 : Integrable g4 (μ.prod ν) := (hpow 4).const_mul _
    have h3 : Integrable g3 (μ.prod ν) := (hpow 3).const_mul _
    have h2 : Integrable g2 (μ.prod ν) := (hpow 2).const_mul _
    have h1 : Integrable g1 (μ.prod ν) := by
      simpa only [g1, pow_one] using (hpow 1).const_mul A
    rw [show (fun z : ℝ × ℝ =>
        ((A * (z.1 + z.2)) ^ 8 - 28 * (A * (z.1 + z.2)) ^ 7 +
          266 * (A * (z.1 + z.2)) ^ 6 - 1050 * (A * (z.1 + z.2)) ^ 5 +
          1701 * (A * (z.1 + z.2)) ^ 4 - 966 * (A * (z.1 + z.2)) ^ 3 +
          127 * (A * (z.1 + z.2)) ^ 2 - A * (z.1 + z.2)) *
          Real.exp (-(B * z.1)) * Real.exp (-(B * z.2))) =
        ((((((g8 - g7) + g6) - g5) + g4) - g3) + g2) - g1 by
      funext z
      simp only [Pi.add_apply, Pi.sub_apply, g8, g7, g6, g5, g4, g3, g2, g1]
      ring]
    rw [integral_sub' (((((h8.sub h7).add h6).sub h5).add h4).sub h3 |>.add h2) h1,
      integral_add' ((((h8.sub h7).add h6).sub h5).add h4 |>.sub h3) h2,
      integral_sub' (((h8.sub h7).add h6).sub h5 |>.add h4) h3,
      integral_add' (((h8.sub h7).add h6).sub h5) h4,
      integral_sub' ((h8.sub h7).add h6) h5,
      integral_add' (h8.sub h7) h6,
      integral_sub' h8 h7]
    simp only [g8, g7, g6, g5, g4, g3, g2, g1, integral_const_mul]
  rw [hscore, heval 8, heval 7, heval 6, heval 5, heval 4, heval 3, heval 2]
  have heval1 := heval 1
  simp only [pow_one] at heval1
  rw [heval1]
  norm_num [Finset.sum_range_succ, Nat.choose]
  have hN (q : ℕ) : N q =
      Real.exp (-(3 / 2 : ℝ) * thetaCuspLikelihoodGap n) *
        Real.exp (-(B * thetaCuspLikelihoodGap n)) *
          ((n : ℝ) ^ 4 * thetaCuspLikelihoodGap n ^ q +
            (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n *
              (∑ i ∈ Finset.range (q + 1),
                (q.choose i : ℝ) * thetaCuspLikelihoodGap n ^ (q - i) *
                  (i.factorial : ℝ) / B ^ (i + 1))) := by
    simpa only [N, μ] using
      integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure hn q hB
  have hM (q : ℕ) : M q =
      Real.exp (-(3 / 2 : ℝ) * thetaCuspLikelihoodGap m) *
        Real.exp (-(B * thetaCuspLikelihoodGap m)) *
          ((m : ℝ) ^ 4 * thetaCuspLikelihoodGap m ^ q +
            (3 / 2 : ℝ) * (m : ℝ) ^ 2 * thetaCuspLikelihoodGap m *
              (∑ i ∈ Finset.range (q + 1),
                (q.choose i : ℝ) * thetaCuspLikelihoodGap m ^ (q - i) *
                  (i.factorial : ℝ) / B ^ (i + 1))) := by
    simpa only [M, ν] using
      integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure hm q hB
  rw [hN 0, hN 1, hN 2, hN 3, hN 4, hN 5, hN 6, hN 7, hN 8,
    hM 0, hM 1, hM 2, hM 3, hM 4, hM 5, hM 6, hM 7, hM 8]
  norm_num [Finset.sum_range_succ, Nat.choose, Nat.factorial]
  have hExpGap :
      Real.exp (-(3 / 2 : ℝ) * thetaCuspLikelihoodGap n) *
          Real.exp (-(3 / 2 : ℝ) * thetaCuspLikelihoodGap m) =
        Real.exp (-(3 / 2 : ℝ) *
          (thetaCuspLikelihoodGap n + thetaCuspLikelihoodGap m)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hExpTilt :
      Real.exp (-(B * thetaCuspLikelihoodGap n)) *
          Real.exp (-(B * thetaCuspLikelihoodGap m)) =
        Real.exp (-(B *
          (thetaCuspLikelihoodGap n + thetaCuspLikelihoodGap m))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold thetaCuspLikelihoodAtomPairEighthScoreMass
    thetaCuspLikelihoodAtomPairEighthScoreCore
    thetaCuspLikelihoodEighthSourceScoreRayTransform
    thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform
    thetaCuspLikelihoodEighthSourceScore thetaCuspLikelihoodEighthSourceScoreDerivOne
    thetaCuspLikelihoodEighthSourceScoreDerivTwo
    thetaCuspLikelihoodEighthSourceScoreDerivThree
    thetaCuspLikelihoodEighthSourceScoreDerivFour
    thetaCuspLikelihoodEighthSourceScoreDerivFive
    thetaCuspLikelihoodEighthSourceScoreDerivSix
    thetaCuspLikelihoodEighthSourceScoreDerivSeven
    thetaCuspLikelihoodEighthSourceScoreDerivEight
  dsimp only
  rw [← hExpGap, ← hExpTilt]
  field_simp [hB.ne']
  ring

end

end RHTower
