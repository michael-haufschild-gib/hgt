import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodGapCumulantRiccati
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodProbabilityNondivisibility
import GaloisForLFunctions.HTGeometry.MonotoneLikelihoodRatio

/-!
# High-cumulant calibration of the theta likelihood source

Exact modular seam arithmetic gives a much sharper tail law than the former coarse estimate:
`60 m < 1` and `180 p < 1` on the nonnegative source half-line.  Positive half-line
spectral order supplies the all-pairs product inequality `e_i e_j ≤ p e_{i+j}`.
Together these facts force quantitative fifth- and sixth-cumulant domination:
`4 e₅ / 5 < κ₅ < e₅`, `3 e₆ / 4 < κ₆`, `2 κ₄ < κ₅`, and `2 κ₅ < κ₆`.

All results are source-defined and unconditional.  No Xi divisor, zero location, or RH premise
enters.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Sharp rational calibration extracted from the exact modular seam slope. -/
theorem thetaCuspFirstAtomBoundaryLogSlope_lt_one_tenth :
    thetaCuspFirstAtomBoundaryLogSlope < 1 / 10 := by
  have hpi : (157 / 50 : ℝ) < Real.pi := by
    have h := Real.pi_gt_d2
    norm_num at h ⊢
    exact h
  have hden : 0 < 2 * (2 * Real.pi - 3) := by nlinarith
  have hfactor : 0 < 20 * (Real.pi + 157 / 50) - 74 := by nlinarith
  have hprod :
      0 < (Real.pi - 157 / 50) *
        (20 * (Real.pi + 157 / 50) - 74) :=
    mul_pos (sub_pos.mpr hpi) hfactor
  have hpoly : 0 < 20 * Real.pi ^ (2 : ℕ) - 74 * Real.pi + 36 := by
    nlinarith
  rw [thetaCuspFirstAtomBoundaryLogSlope]
  rw [show 9 / 2 - 2 * Real.pi + 6 / (2 * Real.pi - 3) =
      (-8 * Real.pi ^ (2 : ℕ) + 30 * Real.pi - 15) /
        (2 * (2 * Real.pi - 3)) by
    field_simp [ne_of_gt (by nlinarith : 0 < 2 * Real.pi - 3)]
    ring]
  apply (div_lt_iff₀ hden).2
  nlinarith

theorem thetaCuspFirstAtomBoundaryLogSlope_lt_nine_two_hundredths :
    thetaCuspFirstAtomBoundaryLogSlope < 9 / 200 := by
  have hpi : (6283 / 2000 : ℝ) < Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h
  have hden : 0 < 2 * (2 * Real.pi - 3) := by nlinarith
  have hfactor : 0 < 800 * (Real.pi + 6283 / 2000) - 2982 := by nlinarith
  have hprod :
      0 < (Real.pi - 6283 / 2000) *
        (800 * (Real.pi + 6283 / 2000) - 2982) :=
    mul_pos (sub_pos.mpr hpi) hfactor
  have hpoly : 0 < 800 * Real.pi ^ (2 : ℕ) - 2982 * Real.pi + 1473 := by
    nlinarith
  rw [thetaCuspFirstAtomBoundaryLogSlope]
  rw [show 9 / 2 - 2 * Real.pi + 6 / (2 * Real.pi - 3) =
      (-8 * Real.pi ^ (2 : ℕ) + 30 * Real.pi - 15) /
        (2 * (2 * Real.pi - 3)) by
    field_simp [ne_of_gt (by nlinarith : 0 < 2 * Real.pi - 3)]
    ring]
  apply (div_lt_iff₀ hden).2
  nlinarith

theorem four_hundred_mul_thetaCuspLikelihoodMean_coordinate_lt_three {x : ℝ} (hx : 0 ≤ x) :
    400 * thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) < 3 := by
  let m := thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)
  have hm : 0 < m := by
    simpa only [m] using
      thetaCuspLikelihoodMean_pos (thetaCuspLikelihoodCoordinate_pos hx)
  have hcal := two_pi_mul_thetaCuspLikelihoodMean_coordinate_le_boundarySlope hx
  have hpi : 6 < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hmul : 6 * m < 2 * Real.pi * m :=
    mul_lt_mul_of_pos_right hpi hm
  have hslope := thetaCuspFirstAtomBoundaryLogSlope_lt_nine_two_hundredths
  dsimp only [m] at hcal hmul ⊢
  nlinarith

theorem four_hundred_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one {x : ℝ} (hx : 0 ≤ x) :
    400 * thetaCuspLikelihoodTailProbability
      (thetaCuspLikelihoodCoordinate x) < 1 := by
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let m := thetaCuspLikelihoodMean B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hp : 3 * p ≤ m := by
    simpa only [p, m] using three_mul_thetaCuspLikelihoodTailProbability_le_mean hB
  have hm : 400 * m < 3 := by simpa only [B, m] using four_hundred_mul_thetaCuspLikelihoodMean_coordinate_lt_three hx
  dsimp only [p] at hp ⊢
  nlinarith


theorem sixty_mul_thetaCuspLikelihoodMean_coordinate_lt_one {x : ℝ} (hx : 0 ≤ x) :
    60 * thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) < 1 := by
  let m := thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)
  have hm : 0 < m := by
    simpa only [m] using
      thetaCuspLikelihoodMean_pos (thetaCuspLikelihoodCoordinate_pos hx)
  have hcal := two_pi_mul_thetaCuspLikelihoodMean_coordinate_le_boundarySlope hx
  have hpi : 6 < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hmul : 6 * m < 2 * Real.pi * m :=
    mul_lt_mul_of_pos_right hpi hm
  have hslope := thetaCuspFirstAtomBoundaryLogSlope_lt_one_tenth
  dsimp only [m] at hcal hmul ⊢
  nlinarith

theorem one_hundred_eighty_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one {x : ℝ} (hx : 0 ≤ x) :
    180 * thetaCuspLikelihoodTailProbability
      (thetaCuspLikelihoodCoordinate x) < 1 := by
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let m := thetaCuspLikelihoodMean B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hp : 3 * p ≤ m := by
    simpa only [p, m] using three_mul_thetaCuspLikelihoodTailProbability_le_mean hB
  have hm : 60 * m < 1 := by simpa only [B, m] using sixty_mul_thetaCuspLikelihoodMean_coordinate_lt_one hx
  dsimp only [p] at hp ⊢
  nlinarith

private theorem ae_nonneg_fst_prod_of_ae
    {μ : Measure ℝ} [SFinite μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) :
    ∀ᵐ z : ℝ × ℝ ∂μ.prod μ, 0 ≤ z.1 := by
  have hsupp : μ (Iio 0) = 0 := by
    change μ {a : ℝ | a < 0} = 0
    simpa only [not_le] using ae_iff.mp hμ
  have hnull : (μ.prod μ) ((Iio (0 : ℝ)) ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.prod_prod, hsupp, zero_mul]
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hnull)
  intro z hz
  exact Set.mem_prod.mpr ⟨not_le.mp hz, Set.mem_univ _⟩

private theorem ae_nonneg_snd_prod_of_ae
    {μ : Measure ℝ} [SFinite μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) :
    ∀ᵐ z : ℝ × ℝ ∂μ.prod μ, 0 ≤ z.2 := by
  have hsupp : μ (Iio 0) = 0 := by
    change μ {a : ℝ | a < 0} = 0
    simpa only [not_le] using ae_iff.mp hμ
  have hnull : (μ.prod μ) ((univ : Set ℝ) ×ˢ (Iio (0 : ℝ))) = 0 := by
    rw [Measure.prod_prod, hsupp, mul_zero]
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hnull)
  intro z hz
  exact Set.mem_prod.mpr ⟨Set.mem_univ _, not_le.mp hz⟩

private theorem integral_pow_mul_integral_pow_le_mass_mul_integral_pow_add
    {μ : Measure ℝ} [SFinite μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (i j : ℕ) (hi : Integrable (fun x : ℝ => x ^ i) μ)
    (hj : Integrable (fun x : ℝ => x ^ j) μ)
    (hij : Integrable (fun x : ℝ => x ^ (i + j)) μ)
    (hzero : Integrable (fun _ : ℝ => (1 : ℝ)) μ) :
    (∫ x, x ^ i ∂μ) * (∫ x, x ^ j ∂μ) ≤
      (∫ _, (1 : ℝ) ∂μ) * (∫ x, x ^ (i + j) ∂μ) := by
  have hkernel : ∀ᵐ z : ℝ × ℝ ∂μ.prod μ,
      0 ≤ (z.2 ^ j - z.1 ^ j) * (z.2 ^ i - z.1 ^ i) := by
    filter_upwards [ae_nonneg_fst_prod_of_ae hμ,
      ae_nonneg_snd_prod_of_ae hμ] with z hx hy
    rcases le_total z.1 z.2 with hxy | hyx
    · exact mul_nonneg
        (sub_nonneg.mpr (pow_le_pow_left₀ hx hxy j))
        (sub_nonneg.mpr (pow_le_pow_left₀ hx hxy i))
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (pow_le_pow_left₀ hy hyx j))
        (sub_nonpos.mpr (pow_le_pow_left₀ hy hyx i))
  have h := HTGeometry.integral_mul_integral_le_of_monotoneLikelihoodKernel
    (μ := μ) (f := fun x : ℝ => x ^ i) (h := fun _ : ℝ => (1 : ℝ))
      (g := fun x : ℝ => x ^ j) hi hzero
      (by simpa only [← pow_add, add_comm] using hij)
      (by simpa only [mul_one] using hj) (by simpa only [one_mul] using hkernel)
  change
    (∫ x, x ^ j * 1 ∂μ) * (∫ x, x ^ i ∂μ) ≤
      (∫ x, x ^ j * x ^ i ∂μ) * (∫ x, 1 ∂μ) at h
  simp only [mul_one, ← pow_add] at h
  simpa only [add_comm, mul_comm] using h

theorem thetaCuspHigherLikelihoodSpectralMoment_mul_le_tailMass_mul {B : ℝ} (hB : 0 < B) (i j : ℕ) :
    thetaCuspHigherLikelihoodSpectralMoment B i *
        thetaCuspHigherLikelihoodSpectralMoment B j ≤
      thetaCuspHigherLikelihoodSpectralMoment B 0 *
        thetaCuspHigherLikelihoodSpectralMoment B (i + j) := by
  let μ := thetaCuspHigherLikelihoodTiltedMeasure B
  letI : SFinite μ := by
    dsimp [μ, thetaCuspHigherLikelihoodTiltedMeasure,
      thetaCuspHigherLikelihoodSpectralMeasure,
      thetaCuspAtomLikelihoodSpectralMeasure]
    infer_instance
  have h := integral_pow_mul_integral_pow_le_mass_mul_integral_pow_add
    (μ := μ) (ae_nonneg_thetaCuspHigherLikelihoodTiltedMeasure B) i j
      (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure i hB)
      (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure j hB)
      (integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure (i + j) hB)
      (by simpa using integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure 0 hB)
  unfold thetaCuspHigherLikelihoodSpectralMoment
  simpa only [μ, pow_zero] using h

theorem thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul {B : ℝ} (hB : 0 < B) (i j : ℕ) :
    thetaCuspLikelihoodNormalizedMoment B i *
        thetaCuspLikelihoodNormalizedMoment B j ≤
      thetaCuspLikelihoodTailProbability B *
        thetaCuspLikelihoodNormalizedMoment B (i + j) := by
  have hraw := thetaCuspHigherLikelihoodSpectralMoment_mul_le_tailMass_mul hB i j
  have hpart := thetaCuspLikelihoodPartition_pos hB
  change
    (thetaCuspHigherLikelihoodSpectralMoment B i /
        thetaCuspLikelihoodPartition B) *
      (thetaCuspHigherLikelihoodSpectralMoment B j /
        thetaCuspLikelihoodPartition B) ≤
    (thetaCuspHigherLikelihoodSpectralMoment B 0 /
        thetaCuspLikelihoodPartition B) *
      (thetaCuspHigherLikelihoodSpectralMoment B (i + j) /
        thetaCuspLikelihoodPartition B)
  rw [show
    (thetaCuspHigherLikelihoodSpectralMoment B i /
        thetaCuspLikelihoodPartition B) *
      (thetaCuspHigherLikelihoodSpectralMoment B j /
        thetaCuspLikelihoodPartition B) =
      (thetaCuspHigherLikelihoodSpectralMoment B i *
        thetaCuspHigherLikelihoodSpectralMoment B j) /
          thetaCuspLikelihoodPartition B ^ (2 : ℕ) by ring]
  rw [show
    (thetaCuspHigherLikelihoodSpectralMoment B 0 /
        thetaCuspLikelihoodPartition B) *
      (thetaCuspHigherLikelihoodSpectralMoment B (i + j) /
        thetaCuspLikelihoodPartition B) =
      (thetaCuspHigherLikelihoodSpectralMoment B 0 *
        thetaCuspHigherLikelihoodSpectralMoment B (i + j)) /
          thetaCuspLikelihoodPartition B ^ (2 : ℕ) by ring]
  exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hpart)).2 hraw

def thetaCuspLikelihoodFifthCumulant (B : ℝ) : ℝ :=
  thetaCuspLikelihoodNormalizedMoment B 5 -
    5 * thetaCuspLikelihoodMean B *
      thetaCuspLikelihoodNormalizedMoment B 4 -
    10 * thetaCuspLikelihoodNormalizedMoment B 2 *
      thetaCuspLikelihoodNormalizedMoment B 3 +
    20 * thetaCuspLikelihoodMean B ^ (2 : ℕ) *
      thetaCuspLikelihoodNormalizedMoment B 3 +
    30 * thetaCuspLikelihoodMean B *
      thetaCuspLikelihoodNormalizedMoment B 2 ^ (2 : ℕ) -
    60 * thetaCuspLikelihoodMean B ^ (3 : ℕ) *
      thetaCuspLikelihoodNormalizedMoment B 2 +
    24 * thetaCuspLikelihoodMean B ^ (5 : ℕ)

def thetaCuspLikelihoodSixthCumulant (B : ℝ) : ℝ :=
  thetaCuspLikelihoodNormalizedMoment B 6 -
    6 * thetaCuspLikelihoodMean B *
      thetaCuspLikelihoodNormalizedMoment B 5 -
    15 * thetaCuspLikelihoodNormalizedMoment B 2 *
      thetaCuspLikelihoodNormalizedMoment B 4 -
    10 * thetaCuspLikelihoodNormalizedMoment B 3 ^ (2 : ℕ) +
    30 * thetaCuspLikelihoodMean B ^ (2 : ℕ) *
      thetaCuspLikelihoodNormalizedMoment B 4 +
    120 * thetaCuspLikelihoodMean B *
      thetaCuspLikelihoodNormalizedMoment B 2 *
      thetaCuspLikelihoodNormalizedMoment B 3 -
    120 * thetaCuspLikelihoodMean B ^ (3 : ℕ) *
      thetaCuspLikelihoodNormalizedMoment B 3 +
    30 * thetaCuspLikelihoodNormalizedMoment B 2 ^ (3 : ℕ) -
    270 * thetaCuspLikelihoodMean B ^ (2 : ℕ) *
      thetaCuspLikelihoodNormalizedMoment B 2 ^ (2 : ℕ) +
    360 * thetaCuspLikelihoodMean B ^ (4 : ℕ) *
      thetaCuspLikelihoodNormalizedMoment B 2 -
    120 * thetaCuspLikelihoodMean B ^ (6 : ℕ)

theorem hasDerivAt_thetaCuspLikelihoodFourthCumulant
    {B : ℝ} (hB : 0 < B) :
    HasDerivAt thetaCuspLikelihoodFourthCumulant
      (-thetaCuspLikelihoodFifthCumulant B) B := by
  have hm := hasDerivAt_thetaCuspLikelihoodMean hB
  have he2 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 2
  have he3 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 3
  have he4 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 4
  have hraw :=
    (((he4.sub ((hm.mul he3).const_mul 4)).sub
        ((he2.pow 2).const_mul 3)).add
      (((hm.pow 2).mul he2).const_mul 12)).sub
        ((hm.pow 4).const_mul 6)
  unfold thetaCuspLikelihoodFourthCumulant thetaCuspLikelihoodFifthCumulant
  convert hraw using 1
  any_goals rfl
  · funext q
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [Nat.reduceAdd,
      thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq,
      Pi.pow_apply]
    ring

theorem hasDerivAt_thetaCuspLikelihoodFifthCumulant
    {B : ℝ} (hB : 0 < B) :
    HasDerivAt thetaCuspLikelihoodFifthCumulant (-thetaCuspLikelihoodSixthCumulant B) B := by
  have hm := hasDerivAt_thetaCuspLikelihoodMean hB
  have he2 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 2
  have he3 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 3
  have he4 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 4
  have he5 := hasDerivAt_thetaCuspLikelihoodNormalizedMoment hB 5
  have h0 := he5.sub ((hm.mul he4).const_mul 5)
  have h1 := h0.sub ((he2.mul he3).const_mul 10)
  have h2 := h1.add (((hm.pow 2).mul he3).const_mul 20)
  have h3 := h2.add ((hm.mul (he2.pow 2)).const_mul 30)
  have h4 := h3.sub (((hm.pow 3).mul he2).const_mul 60)
  have hraw := h4.add ((hm.pow 5).const_mul 24)
  unfold thetaCuspLikelihoodFifthCumulant thetaCuspLikelihoodSixthCumulant
  convert hraw using 1
  any_goals rfl
  · funext q
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [Nat.reduceAdd,
      thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq,
      Pi.pow_apply]
    ring

theorem thetaCuspLikelihoodFourthCumulant_lt_normalizedMoment_four_coordinate {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodFourthCumulant (thetaCuspLikelihoodCoordinate x) <
      thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 4 := by
  let B := thetaCuspLikelihoodCoordinate x
  let m := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hm : 0 < m := by simpa only [m] using thetaCuspLikelihoodMean_pos hB
  have hmSmall : 60 * m < 1 := by simpa only [B, m] using sixty_mul_thetaCuspLikelihoodMean_coordinate_lt_one hx
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he3 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have hmOne : m < 1 := by nlinarith
  have hgap : 3 * m * e2 < e3 := by
    have hprod : 0 < (1 - m) * e2 :=
      mul_pos (sub_pos.mpr hmOne) he2
    nlinarith
  have hdom : 12 * m ^ (2 : ℕ) * e2 < 4 * m * e3 := by
    have := mul_lt_mul_of_pos_left hgap (show 0 < 4 * m by positivity)
    nlinarith
  dsimp only [B, m, e2, e3, e4] at *
  unfold thetaCuspLikelihoodFourthCumulant
  nlinarith [sq_pos_of_pos he2, pow_pos hm 4]

theorem four_fifths_mul_thetaCuspLikelihoodNormalizedMoment_five_lt_fifthCumulant_coordinate {x : ℝ} (hx : 0 ≤ x) :
    (4 / 5 : ℝ) * thetaCuspLikelihoodNormalizedMoment
        (thetaCuspLikelihoodCoordinate x) 5 <
      thetaCuspLikelihoodFifthCumulant (thetaCuspLikelihoodCoordinate x) := by
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let m := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let e5 := thetaCuspLikelihoodNormalizedMoment B 5
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hm : 0 < m := by simpa only [m] using thetaCuspLikelihoodMean_pos hB
  have hmSmall : 60 * m < 1 := by simpa only [B, m] using sixty_mul_thetaCuspLikelihoodMean_coordinate_lt_one hx
  have hpSmall : 180 * p < 1 := by simpa only [B, p] using one_hundred_eighty_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one hx
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he23 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have he34 : 3 * e3 ≤ e4 := by
    simpa only [e3, e4] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have he45 : 3 * e4 ≤ e5 := by
    simpa only [e4, e5] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 4
  have he3 : 0 < e3 := lt_of_lt_of_le (mul_pos (by norm_num) he2) he23
  have he4 : 0 < e4 := lt_of_lt_of_le (mul_pos (by norm_num) he3) he34
  have he5 : 0 < e5 := lt_of_lt_of_le (mul_pos (by norm_num) he4) he45
  have hmomentProduct : e2 * e3 ≤ p * e5 := by
    simpa only [B, p, e2, e3, e5, show 2 + 3 = 5 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 3
  have hfirst : 5 * m * e4 < e5 / 36 := by
    have hprod : 0 < (1 - 60 * m) * e4 := by positivity
    nlinarith
  have hsecond : 10 * e2 * e3 < e5 / 18 := by
    have hprod : 0 < (1 - 180 * p) * e5 := by positivity
    nlinarith
  have hmOne : m < 1 := by nlinarith
  have hmSqOne : m ^ (2 : ℕ) < 1 := pow_lt_one₀ hm.le hmOne (by norm_num)
  have hmCube : m ^ (3 : ℕ) < m := by
    calc
      m ^ (3 : ℕ) = m * m ^ (2 : ℕ) := by ring
      _ < m * 1 := mul_lt_mul_of_pos_left hmSqOne hm
      _ = m := by ring
  have he25 : 27 * e2 ≤ e5 := by nlinarith
  have hthird : 60 * m ^ (3 : ℕ) * e2 < e5 / 27 := by
    have hcoef : 60 * m ^ (3 : ℕ) < 1 := by nlinarith
    have hmul := mul_lt_mul_of_pos_right hcoef he2
    nlinarith
  have hpos1 : 0 ≤ 20 * m ^ (2 : ℕ) * e3 := by positivity
  have hpos2 : 0 ≤ 30 * m * e2 ^ (2 : ℕ) := by positivity
  have hpos3 : 0 ≤ 24 * m ^ (5 : ℕ) := by positivity
  dsimp only [B, p, m, e2, e3, e4, e5] at *
  unfold thetaCuspLikelihoodFifthCumulant
  nlinarith

theorem thetaCuspLikelihoodFifthCumulant_lt_normalizedMoment_five_coordinate {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodFifthCumulant (thetaCuspLikelihoodCoordinate x) <
      thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 5 := by
  let B := thetaCuspLikelihoodCoordinate x
  let m := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let e5 := thetaCuspLikelihoodNormalizedMoment B 5
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hm : 0 < m := by simpa only [m] using thetaCuspLikelihoodMean_pos hB
  have hmSmall : 60 * m < 1 := by simpa only [B, m] using sixty_mul_thetaCuspLikelihoodMean_coordinate_lt_one hx
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he23 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have he12 : 3 * m ≤ e2 := by
    have h := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 1
    simpa only [thetaCuspLikelihoodNormalizedMoment_one_eq_mean, m, e2] using h
  have he34 : 3 * e3 ≤ e4 := by
    simpa only [e3, e4] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have he3 : 0 < e3 := lt_of_lt_of_le (mul_pos (by norm_num) he2) he23
  have he4 : 0 < e4 := lt_of_lt_of_le (mul_pos (by norm_num) he3) he34
  have hmOne : m < 1 := by nlinarith
  have hgap : 3 * m * e2 < e3 := by
    have hprod : 0 < (1 - m) * e2 :=
      mul_pos (sub_pos.mpr hmOne) he2
    nlinarith
  have hgroup1 : 20 * m ^ (2 : ℕ) * e3 < 5 * m * e4 := by
    have hbase : 4 * m * e3 < e4 := by
      have hcoef : 0 < 3 - 4 * m := by nlinarith
      have hprod : 0 < (3 - 4 * m) * e3 := mul_pos hcoef he3
      nlinarith
    have hmul := mul_lt_mul_of_pos_left hbase (show 0 < 5 * m by positivity)
    nlinarith
  have hgroup2 : 30 * m * e2 ^ (2 : ℕ) < 10 * e2 * e3 := by
    have hmul := mul_lt_mul_of_pos_left hgap (show 0 < 10 * e2 by positivity)
    nlinarith
  have hme2 : 2 * m ^ (2 : ℕ) < 5 * e2 := by
    have hmSq : m ^ (2 : ℕ) < m := by
      have hmul := mul_lt_mul_of_pos_left hmOne hm
      nlinarith
    nlinarith
  have hgroup3 : 24 * m ^ (5 : ℕ) < 60 * m ^ (3 : ℕ) * e2 := by
    have hmul := mul_lt_mul_of_pos_left hme2 (show 0 < 12 * m ^ (3 : ℕ) by positivity)
    nlinarith
  dsimp only [B, m, e2, e3, e4, e5] at *
  unfold thetaCuspLikelihoodFifthCumulant
  nlinarith

theorem two_mul_thetaCuspLikelihoodFourthCumulant_lt_fifthCumulant_coordinate {x : ℝ} (hx : 0 ≤ x) :
    2 * thetaCuspLikelihoodFourthCumulant (thetaCuspLikelihoodCoordinate x) <
      thetaCuspLikelihoodFifthCumulant (thetaCuspLikelihoodCoordinate x) := by
  let B := thetaCuspLikelihoodCoordinate x
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let e5 := thetaCuspLikelihoodNormalizedMoment B 5
  let k4 := thetaCuspLikelihoodFourthCumulant B
  let k5 := thetaCuspLikelihoodFifthCumulant B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have he45 : 3 * e4 ≤ e5 := by
    simpa only [e4, e5] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 4
  have he4 : 0 < e4 := by
    simpa only [e4] using thetaCuspLikelihoodNormalizedMoment_four_pos hB
  have hk4 : k4 < e4 := by simpa only [B, e4, k4] using thetaCuspLikelihoodFourthCumulant_lt_normalizedMoment_four_coordinate hx
  have hk5 : (4 / 5 : ℝ) * e5 < k5 := by
    simpa only [B, e5, k5] using four_fifths_mul_thetaCuspLikelihoodNormalizedMoment_five_lt_fifthCumulant_coordinate hx
  dsimp only [B, k4, k5] at *
  norm_num at hk5
  nlinarith

set_option maxHeartbeats 800000 in
theorem three_fourths_mul_thetaCuspLikelihoodNormalizedMoment_six_lt_sixthCumulant_coordinate {x : ℝ} (hx : 0 ≤ x) :
    (3 / 4 : ℝ) * thetaCuspLikelihoodNormalizedMoment
        (thetaCuspLikelihoodCoordinate x) 6 <
      thetaCuspLikelihoodSixthCumulant (thetaCuspLikelihoodCoordinate x) := by
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let m := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let e5 := thetaCuspLikelihoodNormalizedMoment B 5
  let e6 := thetaCuspLikelihoodNormalizedMoment B 6
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hm : 0 < m := by simpa only [m] using thetaCuspLikelihoodMean_pos hB
  have hmSmall : 60 * m < 1 := by simpa only [B, m] using sixty_mul_thetaCuspLikelihoodMean_coordinate_lt_one hx
  have hpSmall : 180 * p < 1 := by simpa only [B, p] using one_hundred_eighty_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one hx
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he12 : 3 * m ≤ e2 := by
    have h := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 1
    simpa only [thetaCuspLikelihoodNormalizedMoment_one_eq_mean, m, e2] using h
  have he23 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have he34 : 3 * e3 ≤ e4 := by
    simpa only [e3, e4] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have he45 : 3 * e4 ≤ e5 := by
    simpa only [e4, e5] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 4
  have he56 : 3 * e5 ≤ e6 := by
    simpa only [e5, e6] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 5
  have he3 : 0 < e3 := lt_of_lt_of_le (mul_pos (by norm_num) he2) he23
  have he4 : 0 < e4 := lt_of_lt_of_le (mul_pos (by norm_num) he3) he34
  have he5 : 0 < e5 := lt_of_lt_of_le (mul_pos (by norm_num) he4) he45
  have he6 : 0 < e6 := lt_of_lt_of_le (mul_pos (by norm_num) he5) he56
  have h24 : e2 * e4 ≤ p * e6 := by
    simpa only [B, p, e2, e4, e6, show 2 + 4 = 6 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 4
  have h33 : e3 ^ (2 : ℕ) ≤ p * e6 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 3 3
    simpa only [B, p, e3, e6, show 3 + 3 = 6 by norm_num, pow_two] using h
  have h22 : e2 ^ (2 : ℕ) ≤ p * e4 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 2
    simpa only [B, p, e2, e4, show 2 + 2 = 4 by norm_num, pow_two] using h
  have hp : 0 < p := by nlinarith [sq_pos_of_pos he2]
  have hfirst : 6 * m * e5 < e6 / 30 := by
    have hprod : 0 < (1 - 60 * m) * e5 := by positivity
    nlinarith
  have hsecond : 15 * e2 * e4 < e6 / 12 := by
    have hprod : 0 < (1 - 180 * p) * e6 := by positivity
    nlinarith
  have hthird : 10 * e3 ^ (2 : ℕ) < e6 / 18 := by
    have hprod : 0 < (1 - 180 * p) * e6 := by positivity
    nlinarith
  have hmOne : m < 1 := by nlinarith
  have hmSqSmall : 3600 * m ^ (2 : ℕ) < 1 := by
    have hminus : 0 < 1 - 60 * m := by nlinarith
    have hplus : 0 < 1 + 60 * m := by positivity
    have hprod := mul_pos hminus hplus
    nlinarith
  have hmCubeSq : m ^ (3 : ℕ) < m ^ (2 : ℕ) := by
    calc
      m ^ (3 : ℕ) = m ^ (2 : ℕ) * m := by ring
      _ < m ^ (2 : ℕ) * 1 := mul_lt_mul_of_pos_left hmOne (pow_pos hm 2)
      _ = m ^ (2 : ℕ) := by ring
  have he36 : 27 * e3 ≤ e6 := by nlinarith
  have hfourth : 120 * m ^ (3 : ℕ) * e3 < e6 / 810 := by
    have hcoef : 120 * m ^ (3 : ℕ) < 1 / 30 := by nlinarith
    have hmul := mul_lt_mul_of_pos_right hcoef he3
    nlinarith
  have hpOne : p < 1 := by nlinarith
  have he2sq_lt_e4 : e2 ^ (2 : ℕ) < e4 := by
    have hmul := mul_lt_mul_of_pos_right hpOne he4
    nlinarith
  have he46 : 9 * e4 ≤ e6 := by nlinarith
  have hfifth : 270 * m ^ (2 : ℕ) * e2 ^ (2 : ℕ) < e6 / 120 := by
    have hcoef : 270 * m ^ (2 : ℕ) < 3 / 40 := by nlinarith
    have hleft := mul_lt_mul_of_pos_left he2sq_lt_e4
      (show 0 < 270 * m ^ (2 : ℕ) by positivity)
    have hright := mul_lt_mul_of_pos_right hcoef he4
    nlinarith
  have hmFourOne : m ^ (4 : ℕ) < 1 := pow_lt_one₀ hm.le hmOne (by norm_num)
  have hmFive : m ^ (5 : ℕ) < m := by
    calc
      m ^ (5 : ℕ) = m * m ^ (4 : ℕ) := by ring
      _ < m * 1 := mul_lt_mul_of_pos_left hmFourOne hm
      _ = m := by ring
  have hmSixSq : m ^ (6 : ℕ) < m ^ (2 : ℕ) := by
    have hmul := mul_lt_mul_of_pos_left hmFive hm
    nlinarith
  have he16 : 243 * m ≤ e6 := by nlinarith
  have hsixth : 120 * m ^ (6 : ℕ) < (2 / 243 : ℝ) * e6 := by
    have hcoef : 120 * m ^ (6 : ℕ) < 2 * m := by
      have hsmallMul := mul_lt_mul_of_pos_left hmSmall
        (show 0 < 2 * m by positivity)
      nlinarith
    nlinarith
  have hpos1 : 0 ≤ 30 * m ^ (2 : ℕ) * e4 := by positivity
  have hpos2 : 0 ≤ 120 * m * e2 * e3 := by positivity
  have hpos3 : 0 ≤ 30 * e2 ^ (3 : ℕ) := by positivity
  have hpos4 : 0 ≤ 360 * m ^ (4 : ℕ) * e2 := by positivity
  dsimp only [B, p, m, e2, e3, e4, e5, e6] at *
  unfold thetaCuspLikelihoodSixthCumulant
  nlinarith

theorem two_mul_thetaCuspLikelihoodFifthCumulant_lt_sixthCumulant_coordinate {x : ℝ} (hx : 0 ≤ x) :
    2 * thetaCuspLikelihoodFifthCumulant (thetaCuspLikelihoodCoordinate x) <
      thetaCuspLikelihoodSixthCumulant (thetaCuspLikelihoodCoordinate x) := by
  let B := thetaCuspLikelihoodCoordinate x
  let e5 := thetaCuspLikelihoodNormalizedMoment B 5
  let e6 := thetaCuspLikelihoodNormalizedMoment B 6
  let k5 := thetaCuspLikelihoodFifthCumulant B
  let k6 := thetaCuspLikelihoodSixthCumulant B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have he56 : 3 * e5 ≤ e6 := by
    simpa only [e5, e6] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 5
  have he5 : 0 < e5 := by
    have he4 := thetaCuspLikelihoodNormalizedMoment_four_pos hB
    have hrec := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 4
    simpa only [e5] using lt_of_lt_of_le (mul_pos (by norm_num) he4) hrec
  have hk5 : k5 < e5 := by
    simpa only [B, e5, k5] using thetaCuspLikelihoodFifthCumulant_lt_normalizedMoment_five_coordinate hx
  have hk6 : (3 / 4 : ℝ) * e6 < k6 := by
    simpa only [B, e6, k6] using three_fourths_mul_thetaCuspLikelihoodNormalizedMoment_six_lt_sixthCumulant_coordinate hx
  dsimp only [B, k5, k6] at *
  norm_num at hk6
  nlinarith

end

end RHTower
