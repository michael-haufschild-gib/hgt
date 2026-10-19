import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalTranslatedHarmonicLimit

/-! Complete physical correlations of translated finite factorial patterns.
Absolute harmonic domination passes the exact native harmonic limit through the
full series, retaining the physical pattern mass on every dilation resonance. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

private def translatedLayer (S : Finset ℕ) (b : ℕ → ℝ) (n k : ℕ) (v : ℝ) : ℝ :=
  (factorialHarmonicLayer (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) k v).re

private def translatedPhase (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  (factorialPhaseCombination (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) v).re

private theorem translated_norm_sum (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) :
    (∑ q ∈ S.image (fun j => n+j), ‖(b (q-n) : ℂ)‖) = ∑ j ∈ S, |b j| := by
  classical
  rw [Finset.sum_image]
  · simp only [Nat.add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
  · intro i hi j hj hij
    exact Nat.add_left_cancel hij

private theorem translated_layer_bound (S : Finset ℕ) (b : ℕ → ℝ) (n k : ℕ) (v : ℝ) :
    |translatedLayer S b n k v| ≤ 2 * ∑ j ∈ S, |b j| := by
  have h := (Complex.abs_re_le_norm _).trans
    (norm_factorialHarmonicLayer_le (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) k v)
  rwa [translated_norm_sum] at h

private theorem translated_phase_bound (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) (v : ℝ) :
    |translatedPhase S b n v| ≤ 2 * ∑ j ∈ S, |b j| := by
  have h := (Complex.abs_re_le_norm _).trans
    (norm_factorialPhaseCombination_le (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) v)
  rwa [translated_norm_sum] at h

private theorem translated_layer_continuous (S : Finset ℕ) (b : ℕ → ℝ) (n k : ℕ) :
    Continuous (translatedLayer S b n k) :=
  Complex.continuous_re.comp (continuous_factorialHarmonicLayer _ _ _)

private theorem translated_phase_continuous (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) :
    Continuous (translatedPhase S b n) :=
  Complex.continuous_re.comp (continuous_factorialPhaseCombination _ _)

private theorem translated_layer_hasSum (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) (v : ℝ) :
    HasSum (fun k => dyadicHarmonicWeight k * translatedLayer S b n k v)
      (-(Real.pi ^ 2 / 2) * translatedPhase S b n v) := by
  have h := Complex.hasSum_re (factorialPhaseCombination_hasSum
    (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) v)
  simpa only [translatedLayer, translatedPhase, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, zero_mul,
    sub_zero] using h

private theorem translated_weight_integrable :
    IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
  integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one

private theorem translated_integrable {f : ℝ → ℝ} {B : ℝ}
    (hf : Continuous f) (hB : ∀ v, |f v| ≤ B) :
    IntegrableOn (fun v => v ^ (-2 : ℝ) * f v) (Ioi (1 : ℝ)) :=
  translated_weight_integrable.mul_bdd hf.aestronglyMeasurable
    (Eventually.of_forall fun v => by simpa only [Real.norm_eq_abs] using hB v)

private theorem translated_integral_bound {f : ℝ → ℝ} {B : ℝ}
    (hf : Continuous f) (hB : ∀ v, |f v| ≤ B) :
    |∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * f v| ≤ B := by
  have hi := translated_integrable hf hB
  have hmass : (∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ)) = 1 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one]
    norm_num
  calc |∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * f v|
      ≤ ∫ v in Ioi (1 : ℝ), ‖v ^ (-2 : ℝ) * f v‖ := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := volume.restrict (Ioi (1 : ℝ)))
            (fun v : ℝ => v ^ (-2 : ℝ) * f v))
    _ ≤ ∫ v in Ioi (1 : ℝ), B * v ^ (-2 : ℝ) := by
      refine setIntegral_mono_on hi.norm (translated_weight_integrable.const_mul B)
        measurableSet_Ioi fun v hv => ?_
      have hw : 0 ≤ v ^ (-2 : ℝ) := Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hv)) _
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hw, Real.norm_eq_abs]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hB v) hw
    _ = B := by rw [integral_const_mul, hmass, mul_one]

private theorem translated_layer_product_bound (S : Finset ℕ) (b : ℕ → ℝ)
    (n k l r : ℕ) (v : ℝ) :
    |translatedLayer S b n k v * translatedLayer S b n l ((r : ℝ) * v)| ≤
      4 * (∑ j ∈ S, |b j|) ^ 2 := by
  rw [abs_mul]
  exact (mul_le_mul (translated_layer_bound S b n k v) (translated_layer_bound S b n l _)
    (abs_nonneg _) (by positivity)).trans_eq (by ring)

private def translatedLayerCorr (S : Finset ℕ) (b : ℕ → ℝ) (n k l r : ℕ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * translatedLayer S b n k v *
    translatedLayer S b n l ((r : ℝ) * v)

private theorem translated_layer_corr_bound (S : Finset ℕ) (b : ℕ → ℝ) (n k l r : ℕ) :
    |translatedLayerCorr S b n k l r| ≤ 4 * (∑ j ∈ S, |b j|) ^ 2 := by
  have hc : Continuous (fun v : ℝ => translatedLayer S b n k v *
      translatedLayer S b n l ((r : ℝ) * v)) :=
    (translated_layer_continuous S b n k).mul
      ((translated_layer_continuous S b n l).comp (continuous_const.mul continuous_id))
  have h := translated_integral_bound hc (translated_layer_product_bound S b n k l r)
  simpa only [translatedLayerCorr, mul_assoc] using h

private theorem translated_pair_summable (S : Finset ℕ) (b : ℕ → ℝ) :
    Summable (fun p : ℕ × ℕ => (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) *
      (4 * (∑ j ∈ S, |b j|) ^ 2)) :=
  (summable_abs_dyadicHarmonicWeight.mul_of_nonneg summable_abs_dyadicHarmonicWeight
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)).mul_right _

private theorem translated_pair_bound (S : Finset ℕ) (b : ℕ → ℝ)
    (n r : ℕ) (p : ℕ × ℕ) (v : ℝ) :
    |(dyadicHarmonicWeight p.1 * translatedLayer S b n p.1 v) *
      (dyadicHarmonicWeight p.2 * translatedLayer S b n p.2 ((r : ℝ) * v))| ≤
      (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) *
        (4 * (∑ j ∈ S, |b j|) ^ 2) := by
  calc _ = (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) *
      |translatedLayer S b n p.1 v * translatedLayer S b n p.2 ((r : ℝ) * v)| := by
        simp only [abs_mul]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (translated_layer_product_bound S b n p.1 p.2 r v)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The complete physical correlation of an actual translated finite factorial pattern. -/
def factorialCriticalTranslatedCorrelation (S : Finset ℕ) (b : ℕ → ℝ) (n r : ℕ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) *
    (factorialPhaseCombination (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) v).re *
    (factorialPhaseCombination (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) ((r : ℝ)*v)).re

/-- These full-pattern physical correlations are genuine Lebesgue integrals. -/
theorem integrable_factorialCriticalTranslatedCorrelation
    (S : Finset ℕ) (b : ℕ → ℝ) (n r : ℕ) :
    IntegrableOn (fun v => v ^ (-2 : ℝ) *
      (factorialPhaseCombination (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) v).re *
      (factorialPhaseCombination (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) ((r : ℝ)*v)).re)
      (Ioi (1 : ℝ)) := by
  have hc : Continuous (fun v : ℝ => translatedPhase S b n v *
      translatedPhase S b n ((r : ℝ) * v)) :=
    (translated_phase_continuous S b n).mul
      ((translated_phase_continuous S b n).comp (continuous_const.mul continuous_id))
  have hb (v : ℝ) : |translatedPhase S b n v * translatedPhase S b n ((r : ℝ)*v)| ≤
      4 * (∑ j ∈ S, |b j|) ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul (translated_phase_bound S b n v) (translated_phase_bound S b n _)
      (abs_nonneg _) (by positivity)).trans_eq (by ring)
  simpa only [translatedPhase, mul_assoc] using translated_integrable hc hb

private theorem translated_correlation_hasSum (S : Finset ℕ) (b : ℕ → ℝ) (n r : ℕ) :
    HasSum (fun p : ℕ × ℕ => dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
      translatedLayerCorr S b n p.1 p.2 r)
      ((Real.pi ^ 4 / 4) * factorialCriticalTranslatedCorrelation S b n r) := by
  let F (p : ℕ × ℕ) (v : ℝ) := v ^ (-2 : ℝ) *
    ((dyadicHarmonicWeight p.1 * translatedLayer S b n p.1 v) *
      (dyadicHarmonicWeight p.2 * translatedLayer S b n p.2 ((r : ℝ) * v)))
  let B (p : ℕ × ℕ) := (|dyadicHarmonicWeight p.1| * |dyadicHarmonicWeight p.2|) *
    (4 * (∑ j ∈ S, |b j|) ^ 2)
  let f (v : ℝ) := v ^ (-2 : ℝ) *
    ((-(Real.pi ^ 2 / 2) * translatedPhase S b n v) *
      (-(Real.pi ^ 2 / 2) * translatedPhase S b n ((r : ℝ) * v)))
  have hs (v : ℝ) : Summable (fun p : ℕ × ℕ =>
      (dyadicHarmonicWeight p.1 * translatedLayer S b n p.1 v) *
        (dyadicHarmonicWeight p.2 * translatedLayer S b n p.2 ((r : ℝ) * v))) :=
    (translated_pair_summable S b).of_norm_bounded (fun p => by
      rw [Real.norm_eq_abs]
      exact translated_pair_bound S b n r p v)
  have h := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (1 : ℝ))) (F := F) (f := f)
    (fun p v => B p * v ^ (-2 : ℝ))
    (fun p => translated_weight_integrable.aestronglyMeasurable.mul
      (((translated_layer_continuous S b n p.1).const_mul _).mul
        (((translated_layer_continuous S b n p.2).comp
          (continuous_const.mul continuous_id)).const_mul _)).aestronglyMeasurable)
    (by
      intro p
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hw : 0 ≤ v ^ (-2 : ℝ) := Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hv)) _
      dsimp only [F, B]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hw, Real.norm_eq_abs]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (translated_pair_bound S b n r p v) hw)
    (Eventually.of_forall fun v => (translated_pair_summable S b).mul_right (v ^ (-2 : ℝ)))
    (by
      have hi := translated_weight_integrable.const_mul (∑' p, B p)
      simpa only [tsum_mul_right] using hi)
    (Eventually.of_forall fun v =>
      ((translated_layer_hasSum S b n v).mul (translated_layer_hasSum S b n ((r : ℝ) * v))
        (hs v)).mul_left (v ^ (-2 : ℝ)))
  have hfun : HasSum (fun p : ℕ × ℕ => dyadicHarmonicWeight p.1 * dyadicHarmonicWeight p.2 *
      translatedLayerCorr S b n p.1 p.2 r) (∫ v in Ioi (1 : ℝ), f v) := by
    refine h.congr_fun (fun p => ?_)
    unfold translatedLayerCorr
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp only [F]
    ring
  have hval : (∫ v in Ioi (1 : ℝ), f v) =
      (Real.pi ^ 4 / 4) * factorialCriticalTranslatedCorrelation S b n r := by
    unfold factorialCriticalTranslatedCorrelation
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp only [f, translatedPhase]
    ring
  rwa [hval] at hfun

private theorem translated_weighted_layer_tendsto (S : Finset ℕ) (b : ℕ → ℝ)
    (k l r : ℕ) (hr : 0 < r) :
    Tendsto (fun n => dyadicHarmonicWeight k * dyadicHarmonicWeight l *
      translatedLayerCorr S b n k l r) atTop
      (𝓝 (if k=r*l then dyadicHarmonicWeight k * dyadicHarmonicWeight l *
        factorialCriticalPatternHarmonicMass S b k else 0)) := by
  have h := (factorialCriticalTranslatedHarmonicCorrelation_tendsto S b k l r hr).const_mul
    (dyadicHarmonicWeight k * dyadicHarmonicWeight l)
  simpa only [translatedLayerCorr, translatedLayer, mul_ite, mul_zero] using h

private theorem translated_weighted_layer_bound (S : Finset ℕ) (b : ℕ → ℝ) (n k l r : ℕ) :
    ‖dyadicHarmonicWeight k * dyadicHarmonicWeight l * translatedLayerCorr S b n k l r‖ ≤
      (|dyadicHarmonicWeight k| * |dyadicHarmonicWeight l|) * (4 * (∑ j ∈ S, |b j|) ^ 2) := by
  simp only [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (translated_layer_corr_bound S b n k l r)
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Every dilation resonance, with the actual pattern's slow phase retained. -/
def factorialCriticalTranslatedCorrelationLimit (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) : ℝ :=
  (4 / Real.pi ^ 4) * ∑' l : ℕ, dyadicHarmonicWeight (r*l) * dyadicHarmonicWeight l *
    factorialCriticalPatternHarmonicMass S b (r*l)

/-- The complete translated actual-source correlation has the exact resonant limit. -/
theorem factorialCriticalTranslatedCorrelation_tendsto
    (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) (hr : 0 < r) :
    Tendsto (fun n => factorialCriticalTranslatedCorrelation S b n r) atTop
      (𝓝 (factorialCriticalTranslatedCorrelationLimit S b r)) := by
  let g (p : ℕ × ℕ) := if p.1=r*p.2 then dyadicHarmonicWeight p.1 *
    dyadicHarmonicWeight p.2 * factorialCriticalPatternHarmonicMass S b p.1 else 0
  have hpair (p : ℕ × ℕ) := translated_weighted_layer_tendsto S b p.1 p.2 r hr
  have hg : Summable g := (translated_pair_summable S b).of_norm_bounded fun p =>
    le_of_tendsto (hpair p).norm
      (Eventually.of_forall fun n => translated_weighted_layer_bound S b n p.1 p.2 r)
  have h := tendsto_tsum_of_dominated_convergence (translated_pair_summable S b) hpair
    (Eventually.of_forall fun n p => translated_weighted_layer_bound S b n p.1 p.2 r)
  have hsum : (∑' p, g p) = ∑' l : ℕ,
      dyadicHarmonicWeight (r*l) * dyadicHarmonicWeight l *
        factorialCriticalPatternHarmonicMass S b (r*l) := by
    rw [← (Equiv.prodComm ℕ ℕ).tsum_eq g]
    change (∑' p : ℕ × ℕ, g p.swap) = _
    rw [hg.prod_symm.tsum_prod]
    apply tsum_congr
    intro l
    dsimp only [g, Prod.swap]
    rw [tsum_eq_single (r*l)]
    · simp only [ite_true]
    · intro k hk
      simp only [if_neg hk]
  change Tendsto _ atTop (𝓝 (∑' p, g p)) at h
  rw [hsum] at h
  have hscaled := h.const_mul (4 / Real.pi ^ 4)
  apply hscaled.congr
  intro n
  rw [(translated_correlation_hasSum S b n r).tsum_eq]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end GaloisForLFunctions.ArithmeticPositivityTheory
