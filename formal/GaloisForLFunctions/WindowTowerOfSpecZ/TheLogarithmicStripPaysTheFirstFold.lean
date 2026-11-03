import GaloisForLFunctions.WindowTowerOfSpecZ.TheFirstFoldHasAPolynomialSpectralBracket

/-!
# The logarithmic principal energy pays the first fold

The first regional Legendre gap controls variation on the prime-two strip.
Its constant mode is paid by the reflected prime term, leaving a positive
strip mass floor without spending off-strip pairs or Gamma remainder.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open LatticeSectionTheory SelectivePositivityAndThresholdLaws

local notation "ν" => volume.restrict (Icc (-1 : ℝ) 1)


private theorem reference_reflect (f : ℝ → ℝ) :
    (∫ x in Icc (-1 : ℝ) 1, f (-x)) = ∫ x in Icc (-1 : ℝ) 1, f x := by
  have h := intervalIntegral.integral_comp_neg (f := f) (a := (-1 : ℝ)) (b := 1)
  norm_num only [neg_neg] at h
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] using h

private theorem reference_variance_gap {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H) :
    2 * (∫ x in Icc (-1 : ℝ) 1, H x ^ 2) -
      (∫ x in Icc (-1 : ℝ) 1, H x) ^ 2 ≤ regionalLogEnergy H := by
  let m : ℝ := ∫ x in Icc (-1 : ℝ) 1, H x
  let V : ℝ → ℝ := fun x => H x - m / 2
  have hV : ContDiff ℝ 1 V := hH.sub contDiff_const
  have hiH : Integrable H ν := hH.continuous.integrableOn_Icc
  have hiHH : Integrable (fun x => H x ^ 2) ν := (hH.continuous.pow 2).integrableOn_Icc
  have hm : regionalLegendreMoment V 0 = 0 := by
    unfold regionalLegendreMoment V
    simp only [legP, mul_one]
    rw [integral_sub hiH (integrable_const _)]
    simp [m]
    ring
  have hg := regionalLogEnergy_moment_gap hV 1 (fun n hn => by
    have : n = 0 := by omega
    subst n
    exact hm)
  have hmass : (∫ x in Icc (-1 : ℝ) 1, V x ^ 2) =
      (∫ x in Icc (-1 : ℝ) 1, H x ^ 2) - m ^ 2 / 2 := by
    have he : (fun x => V x ^ 2) = fun x => H x ^ 2 - m * H x + m ^ 2 / 4 := by
      funext x
      dsimp [V]
      ring
    rw [he, integral_add (f := fun x => H x ^ 2 - m * H x)
      (g := fun _ => m ^ 2 / 4) (hiHH.sub (hiH.const_mul _)) (integrable_const _),
      integral_sub (f := fun x => H x ^ 2) (g := fun x => m * H x)
        hiHH (hiH.const_mul _), integral_const_mul]
    simp [m]
    ring
  have he : regionalLogEnergy V = regionalLogEnergy H := by
    unfold regionalLogEnergy regionalLogPair
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by dsimp [V]; ring
  rw [hmass, he] at hg
  norm_num [regionalLogEigenvalue, Finset.sum_range_succ] at hg
  dsimp [m] at hg
  linarith only [hg]

private theorem reference_reflection_lower {H : ℝ → ℝ} (hH : Continuous H) :
    (∫ x in Icc (-1 : ℝ) 1, H x) ^ 2 - (∫ x in Icc (-1 : ℝ) 1, H x ^ 2) ≤
      ∫ x in Icc (-1 : ℝ) 1, H x * H (-x) := by
  let m : ℝ := ∫ x in Icc (-1 : ℝ) 1, H x
  have hn : Continuous (fun x => H (-x)) := hH.comp continuous_neg
  have h1 : Integrable H ν := hH.integrableOn_Icc
  have h2 : Integrable (fun x => H (-x)) ν := hn.integrableOn_Icc
  have h11 : Integrable (fun x => H x ^ 2) ν := (hH.pow 2).integrableOn_Icc
  have h22 : Integrable (fun x => H (-x) ^ 2) ν := (hn.pow 2).integrableOn_Icc
  have h12 : Integrable (fun x => H x * H (-x)) ν := (hH.mul hn).integrableOn_Icc
  have he : (fun x => (H x + H (-x) - m) ^ 2) = fun x =>
      H x ^ 2 + H (-x) ^ 2 + 2 * (H x * H (-x)) -
        (2 * m) * (H x + H (-x)) + m ^ 2 := by funext x; ring
  have h : 0 ≤ ∫ x in Icc (-1 : ℝ) 1, (H x + H (-x) - m) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  rw [he, integral_add
      (f := fun x => H x ^ 2 + H (-x) ^ 2 + 2 * (H x * H (-x)) -
        (2 * m) * (H x + H (-x))) (g := fun _ => m ^ 2)
      (((h11.add h22).add (h12.const_mul _)).sub
      ((h1.add h2).const_mul _)) (integrable_const _),
    integral_sub (f := fun x => H x ^ 2 + H (-x) ^ 2 + 2 * (H x * H (-x)))
      (g := fun x => (2 * m) * (H x + H (-x)))
      ((h11.add h22).add (h12.const_mul _)) ((h1.add h2).const_mul _),
    integral_add (f := fun x => H x ^ 2 + H (-x) ^ 2)
      (g := fun x => 2 * (H x * H (-x))) (h11.add h22) (h12.const_mul _),
    integral_add (f := fun x => H x ^ 2) (g := fun x => H (-x) ^ 2) h11 h22,
    integral_const_mul, integral_const_mul,
    integral_add (f := H) (g := fun x => H (-x)) h1 h2,
    reference_reflect (fun x => H x ^ 2), reference_reflect H] at h
  simp only [integral_const, Measure.real] at h
  norm_num at h
  dsimp [m] at h
  nlinarith only [h]

private def stripPoint (x : ℝ) : ℝ := Real.log 2 + (1 - Real.log 2) * x

private def stripLoss (H : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 - Real.log 2) / 4 * (H p.1 - H p.2) ^ 2 / (stripPoint p.1 + stripPoint p.2)

/-- The principal logarithmic strip energy in coordinates on `[-1,1]`. -/
def firstFoldStripLogEnergy (H : ℝ → ℝ) : ℝ :=
  (1 - Real.log 2) / 2 * ∫ p : ℝ × ℝ,
    principalOddKernel (stripPoint p.1) (stripPoint p.2) * (H p.1 - H p.2) ^ 2 ∂((ν).prod ν)

private theorem strip_constants :
    0 < Real.log 2 ∧ 0 < 1 - Real.log 2 ∧ 0 < 2 * Real.log 2 - 1 ∧
      1 - Real.log 2 ≤ (111 / 250 : ℝ) * Real.log 2 := by
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  constructor
  · linarith only [hl]
  constructor
  · linarith only [hu]
  constructor <;> linarith only [hl]

private theorem strip_point_lower {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    2 * Real.log 2 - 1 ≤ stripPoint x := by
  have h := mul_le_mul_of_nonneg_left hx.1 strip_constants.2.1.le
  unfold stripPoint
  linarith only [h]

private theorem strip_distance_bound {x y : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1) :
    (1 - Real.log 2) * |x - y| ≤
      (111 / 250 : ℝ) * (stripPoint x + stripPoint y) := by
  have hc := strip_constants
  have hbase : Real.log 2 * |x - y| ≤ stripPoint x + stripPoint y := by
    rcases le_total y x with hxy | hxy
    · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
      have h := mul_le_mul_of_nonneg_left hx.2 hc.2.2.1.le
      unfold stripPoint
      nlinarith only [h, hy.1]
    · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
      have h := mul_le_mul_of_nonneg_left hy.2 hc.2.2.1.le
      unfold stripPoint
      nlinarith only [h, hx.1]
  have h := mul_le_mul_of_nonneg_right hc.2.2.2 (abs_nonneg (x - y))
  linarith only [h, hbase]

private theorem strip_loss_bound (H : ℝ → ℝ) {x y : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1) :
    0 ≤ stripLoss H (x, y) ∧ stripLoss H (x, y) ≤
      (111 / 500 : ℝ) * ((H x - H y) ^ 2 / (2 * |x - y|)) := by
  have hs : 0 < stripPoint x + stripPoint y :=
    add_pos (strip_constants.2.2.1.trans_le (strip_point_lower hx))
      (strip_constants.2.2.1.trans_le (strip_point_lower hy))
  constructor
  · exact div_nonneg (mul_nonneg (by linarith only [strip_constants.2.1]) (sq_nonneg _)) hs.le
  by_cases hxy : x = y
  · subst y
    simp [stripLoss]
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hrate : (1 - Real.log 2) / (4 * (stripPoint x + stripPoint y)) ≤
      (111 / 500 : ℝ) / (2 * |x - y|) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [strip_distance_bound hx hy]
  have h := mul_le_mul_of_nonneg_right hrate (sq_nonneg (H x - H y))
  calc
    stripLoss H (x, y) = (1 - Real.log 2) / (4 * (stripPoint x + stripPoint y)) *
        (H x - H y) ^ 2 := by
      unfold stripLoss
      field_simp [hs.ne']
      ring
    _ ≤ _ := h
    _ = _ := by ring

private theorem strip_loss_integrable {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H) :
    Integrable (stripLoss H) ((ν).prod ν) := by
  have hb : Integrable (fun p : ℝ × ℝ => (H p.1 - H p.2) ^ 2 /
      (2 * |p.1 - p.2|)) ((ν).prod ν) := by
    simpa only [pow_two] using regionalLogPair_integrable hH hH
  apply (hb.const_mul (111 / 500 : ℝ)).mono'
  · have hc := hH.continuous
    have hm : Measurable (stripLoss H) := by
      unfold stripLoss stripPoint
      fun_prop
    exact hm.aestronglyMeasurable
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (strip_loss_bound H hp.1 hp.2).1]
  exact (strip_loss_bound H hp.1 hp.2).2

private theorem strip_density_identity (H : ℝ → ℝ) :
    (fun p : ℝ × ℝ => (1 - Real.log 2) / 2 *
      (principalOddKernel (stripPoint p.1) (stripPoint p.2) * (H p.1 - H p.2) ^ 2))
      =ᵐ[(ν).prod ν] fun p => (1 / 2 : ℝ) *
        ((H p.1 - H p.2) ^ 2 / (2 * |p.1 - p.2|)) - stripLoss H p := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    by_cases hxy : p.1 = p.2
    · simp [hxy, stripLoss]
    have hd : |p.1 - p.2| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hxy)
    have hs : stripPoint p.1 + stripPoint p.2 ≠ 0 := ne_of_gt
      (add_pos (strip_constants.2.2.1.trans_le (strip_point_lower hp.1))
        (strip_constants.2.2.1.trans_le (strip_point_lower hp.2)))
    have hu : stripPoint p.1 - stripPoint p.2 = (1 - Real.log 2) * (p.1 - p.2) := by
      unfold stripPoint
      ring
    simp only [principalOddKernel, hu, abs_mul, abs_of_pos strip_constants.2.1, stripLoss]
    field_simp [hd, hs, strip_constants.2.1.ne']
    ring

private theorem strip_kernel_integrable {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H) :
    Integrable (fun p : ℝ × ℝ => principalOddKernel (stripPoint p.1) (stripPoint p.2) *
      (H p.1 - H p.2) ^ 2) ((ν).prod ν) := by
  have hb : Integrable (fun p : ℝ × ℝ => (H p.1 - H p.2) ^ 2 /
      (2 * |p.1 - p.2|)) ((ν).prod ν) := by
    simpa only [pow_two] using regionalLogPair_integrable hH hH
  have hi := ((hb.const_mul (1 / 2 : ℝ)).sub (strip_loss_integrable hH)).congr
    (strip_density_identity H).symm
  apply (hi.const_mul (2 / (1 - Real.log 2))).congr
  exact Eventually.of_forall fun p => by
    dsimp only
    field_simp [strip_constants.2.1.ne']

private theorem strip_energy_identity {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H) :
    firstFoldStripLogEnergy H = regionalLogEnergy H / 2 - ∫ p, stripLoss H p ∂((ν).prod ν) := by
  have hb : Integrable (fun p : ℝ × ℝ => (H p.1 - H p.2) ^ 2 /
      (2 * |p.1 - p.2|)) ((ν).prod ν) := by
    simpa only [pow_two] using regionalLogPair_integrable hH hH
  unfold firstFoldStripLogEnergy
  rw [← integral_const_mul, integral_congr_ae (strip_density_identity H),
    integral_sub (hb.const_mul _) (strip_loss_integrable hH),
    integral_const_mul]
  unfold regionalLogEnergy regionalLogPair
  simp only [pow_two]
  ring

private theorem strip_energy_ge_regional {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H) :
    (139 / 500 : ℝ) * regionalLogEnergy H ≤ firstFoldStripLogEnergy H := by
  have hb : Integrable (fun p : ℝ × ℝ => (H p.1 - H p.2) ^ 2 /
      (2 * |p.1 - p.2|)) ((ν).prod ν) := by
    simpa only [pow_two] using regionalLogPair_integrable hH hH
  have h := integral_mono_ae (strip_loss_integrable hH) (hb.const_mul (111 / 500 : ℝ))
    (show ∀ᵐ p ∂((ν).prod ν), stripLoss H p ≤
      (111 / 500 : ℝ) * ((H p.1 - H p.2) ^ 2 / (2 * |p.1 - p.2|)) from by
      rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
      exact (strip_loss_bound H hp.1 hp.2).2)
  rw [integral_const_mul] at h
  have he : (∫ p : ℝ × ℝ, (H p.1 - H p.2) ^ 2 / (2 * |p.1 - p.2|) ∂((ν).prod ν)) =
      regionalLogEnergy H := by simp only [regionalLogEnergy, regionalLogPair, pow_two]
  rw [he, ← sub_nonneg] at h
  rw [strip_energy_identity hH]
  linarith only [h]

/-- The signed fold pays the strip mean while the regional gap pays its variation. -/
theorem firstFold_normalized_strip_mean_lower {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H) :
    (139 / 250 - Real.log 2 / Real.sqrt 2) * (∫ x in Icc (-1 : ℝ) 1, H x ^ 2) +
      (Real.log 2 / Real.sqrt 2 - 139 / 500) * (∫ x in Icc (-1 : ℝ) 1, H x) ^ 2 ≤
      firstFoldStripLogEnergy H +
      (Real.log 2 / Real.sqrt 2) * (∫ x in Icc (-1 : ℝ) 1, H x * H (-x)) := by
  have hg := reference_variance_gap hH
  have hr := reference_reflection_lower hH.continuous
  have hs := strip_energy_ge_regional hH
  have hp := mul_le_mul_of_nonneg_left hr firstFold_prime_weight_bounds.1
  nlinarith only [hg, hs, hp]

/-- The signed prime-two reflection is paid by the strip's logarithmic principal energy. -/
theorem firstFold_normalized_strip_coercive {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H) :
    (∫ x in Icc (-1 : ℝ) 1, H x ^ 2) / 16 ≤ firstFoldStripLogEnergy H +
      (Real.log 2 / Real.sqrt 2) * (∫ x in Icc (-1 : ℝ) 1, H x * H (-x)) := by
  have h := firstFold_normalized_strip_mean_lower hH
  have he : 0 ≤ ∫ x in Icc (-1 : ℝ) 1, H x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hw := firstFold_prime_weight_bounds
  have hsq : Real.sqrt 2 ≤ 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hwlo : (139 / 500 : ℝ) ≤ Real.log 2 / Real.sqrt 2 := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)).mpr
    linarith only [hsq, Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_right hwlo
    (sq_nonneg (∫ x in Icc (-1 : ℝ) 1, H x))
  have hu := mul_le_mul_of_nonneg_right hw.2 he
  nlinarith only [h, hm, hu, he]

private theorem reference_to_strip (f : ℝ → ℝ) :
    (1 - Real.log 2) * (∫ x in Icc (-1 : ℝ) 1, f (stripPoint x)) =
      ∫ u in Icc (2 * Real.log 2 - 1) 1, f u := by
  have h := intervalIntegral.smul_integral_comp_mul_add
    (a := (-1 : ℝ)) (b := 1) f (1 - Real.log 2) (Real.log 2)
  have hl : (1 - Real.log 2) * (-1) + Real.log 2 = 2 * Real.log 2 - 1 := by ring
  have hr : (1 - Real.log 2) * 1 + Real.log 2 = 1 := by ring
  have hf : (fun x => f ((1 - Real.log 2) * x + Real.log 2)) =
      fun x => f (stripPoint x) := by
    funext x
    congr 1
    unfold stripPoint
    ring
  rw [hl, hr, hf] at h
  simpa only [smul_eq_mul,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by linarith only [strip_constants.2.1] :
      2 * Real.log 2 - 1 ≤ 1), ← integral_Icc_eq_integral_Ioc] using h

private theorem strip_energy_rescale {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) :
    (1 - Real.log 2) * firstFoldStripLogEnergy (fun x => G (stripPoint x)) =
      (1 / 2 : ℝ) * ∫ u in Icc (2 * Real.log 2 - 1) 1,
        ∫ v in Icc (2 * Real.log 2 - 1) 1, principalOddKernel u v * (G u - G v) ^ 2 := by
  have hH : ContDiff ℝ 1 (fun x => G (stripPoint x)) := by
    apply hG.comp
    unfold stripPoint
    fun_prop
  have hrow (x : ℝ) := reference_to_strip
    (fun v => principalOddKernel (stripPoint x) v * (G (stripPoint x) - G v) ^ 2)
  have hout := reference_to_strip (fun u => ∫ v in Icc (2 * Real.log 2 - 1) 1,
    principalOddKernel u v * (G u - G v) ^ 2)
  have hdouble : (1 - Real.log 2) ^ 2 *
      (∫ x in Icc (-1 : ℝ) 1, ∫ y in Icc (-1 : ℝ) 1,
        principalOddKernel (stripPoint x) (stripPoint y) *
          (G (stripPoint x) - G (stripPoint y)) ^ 2) =
      ∫ u in Icc (2 * Real.log 2 - 1) 1,
        ∫ v in Icc (2 * Real.log 2 - 1) 1, principalOddKernel u v * (G u - G v) ^ 2 := by
    calc
      _ = (1 - Real.log 2) * (∫ x in Icc (-1 : ℝ) 1,
          (1 - Real.log 2) * (∫ y in Icc (-1 : ℝ) 1,
            principalOddKernel (stripPoint x) (stripPoint y) *
              (G (stripPoint x) - G (stripPoint y)) ^ 2)) := by
        rw [integral_const_mul]
        ring
      _ = (1 - Real.log 2) * (∫ x in Icc (-1 : ℝ) 1,
          ∫ v in Icc (2 * Real.log 2 - 1) 1,
            principalOddKernel (stripPoint x) v * (G (stripPoint x) - G v) ^ 2) := by
        congr 1
        exact integral_congr_ae (Eventually.of_forall hrow)
      _ = _ := hout
  unfold firstFoldStripLogEnergy
  rw [integral_prod _ (strip_kernel_integrable hH)]
  nlinarith only [hdouble]

private theorem strip_reflection_rescale (G : ℝ → ℝ) :
    (1 - Real.log 2) * (∫ x in Icc (-1 : ℝ) 1, G (stripPoint x) * G (stripPoint (-x))) =
      ∫ u in Icc (2 * Real.log 2 - 1) 1, G u * G (2 * Real.log 2 - u) := by
  have he (x : ℝ) : stripPoint (-x) = 2 * Real.log 2 - stripPoint x := by
    unfold stripPoint
    ring
  simp_rw [he]
  exact reference_to_strip (fun u => G u * G (2 * Real.log 2 - u))

/-- In physical strip coordinates, the signed fold retains a positive mean-square term. -/
theorem firstFold_strip_mean_lower {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) :
    (139 / 250 - Real.log 2 / Real.sqrt 2) *
        (∫ u in Icc (2 * Real.log 2 - 1) 1, G u ^ 2) +
      ((Real.log 2 / Real.sqrt 2 - 139 / 500) / (1 - Real.log 2)) *
        (∫ u in Icc (2 * Real.log 2 - 1) 1, G u) ^ 2 ≤
      (1 / 2 : ℝ) * (∫ u in Icc (2 * Real.log 2 - 1) 1,
        ∫ v in Icc (2 * Real.log 2 - 1) 1, principalOddKernel u v * (G u - G v) ^ 2) +
      (Real.log 2 / Real.sqrt 2) *
        (∫ u in Icc (2 * Real.log 2 - 1) 1, G u * G (2 * Real.log 2 - u)) := by
  have hH : ContDiff ℝ 1 (fun x => G (stripPoint x)) := by
    apply hG.comp
    unfold stripPoint
    fun_prop
  have h := mul_le_mul_of_nonneg_left (firstFold_normalized_strip_mean_lower hH)
    strip_constants.2.1.le
  have he := reference_to_strip (fun u => G u ^ 2)
  have hm := reference_to_strip G
  have ht := strip_energy_rescale hG
  have hr := strip_reflection_rescale G
  have hrw := congrArg (fun z : ℝ => (Real.log 2 / Real.sqrt 2) * z) hr
  have hm2 : (∫ u in Icc (2 * Real.log 2 - 1) 1, G u) ^ 2 / (1 - Real.log 2) =
      (1 - Real.log 2) * (∫ x in Icc (-1 : ℝ) 1, G (stripPoint x)) ^ 2 := by
    rw [← hm]
    field_simp [strip_constants.2.1.ne']
  have hmean : ((Real.log 2 / Real.sqrt 2 - 139 / 500) / (1 - Real.log 2)) *
      (∫ u in Icc (2 * Real.log 2 - 1) 1, G u) ^ 2 =
      (Real.log 2 / Real.sqrt 2 - 139 / 500) *
        ((1 - Real.log 2) * (∫ x in Icc (-1 : ℝ) 1, G (stripPoint x)) ^ 2) := by
    calc
      _ = (Real.log 2 / Real.sqrt 2 - 139 / 500) *
          ((∫ u in Icc (2 * Real.log 2 - 1) 1, G u) ^ 2 / (1 - Real.log 2)) := by ring
      _ = _ := by rw [hm2]
  calc
    _ = (1 - Real.log 2) *
        ((139 / 250 - Real.log 2 / Real.sqrt 2) *
          (∫ x in Icc (-1 : ℝ) 1, G (stripPoint x) ^ 2) +
        (Real.log 2 / Real.sqrt 2 - 139 / 500) *
          (∫ x in Icc (-1 : ℝ) 1, G (stripPoint x)) ^ 2) := by
      rw [hmean, ← he]
      ring
    _ ≤ _ := h
    _ = _ := by rw [mul_add, ht]; nlinarith only [hrw]

/-- Half the logarithmic principal energy and the first prime fold control strip mass. -/
theorem firstFold_strip_coercive {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) :
    (∫ u in Icc (2 * Real.log 2 - 1) 1, G u ^ 2) / 16 ≤
      (1 / 2 : ℝ) * (∫ u in Icc (2 * Real.log 2 - 1) 1,
        ∫ v in Icc (2 * Real.log 2 - 1) 1, principalOddKernel u v * (G u - G v) ^ 2) +
      (Real.log 2 / Real.sqrt 2) *
        (∫ u in Icc (2 * Real.log 2 - 1) 1, G u * G (2 * Real.log 2 - u)) := by
  have hH : ContDiff ℝ 1 (fun x => G (stripPoint x)) := by
    apply hG.comp
    unfold stripPoint
    fun_prop
  have h := mul_le_mul_of_nonneg_left (firstFold_normalized_strip_coercive hH)
    strip_constants.2.1.le
  have he := reference_to_strip (fun u => G u ^ 2)
  have ht := strip_energy_rescale hG
  have hr := strip_reflection_rescale G
  have hrw := congrArg (fun z : ℝ => (Real.log 2 / Real.sqrt 2) * z) hr
  nlinarith only [h, he, ht, hrw]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFold_normalized_strip_coercive
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFold_normalized_strip_mean_lower
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFold_strip_mean_lower
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFold_strip_coercive
