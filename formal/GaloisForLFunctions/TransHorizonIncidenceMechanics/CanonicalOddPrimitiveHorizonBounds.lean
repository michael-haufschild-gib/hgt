import GaloisForLFunctions.TransHorizonIncidenceMechanics.CollectiveLowPrimeChebyshevTransportAndSinhAbsorption

/-!
# Complete horizon bounds for canonical odd primitive theta cutoffs

Translate the same theta cutoff before taking normalized odd differences. Paired
shifts cancel both polar moments exactly and converge to a nonzero signed-radical
family. Full edge and translated-source moments pay every cutoff error, giving an
unconditional inverse-square bound for the absolute original Markov energy.

The estimate retains every prime, the original cosh subtraction, and the reflected
collar compensation. It gives neither a finite-horizon sign nor density in the
entire primitive sector.
-/

open MeasureTheory Set Filter Topology
open scoped Real InnerProductSpace
open RHTower RHTower.CHMDPolar RHTower.CHMDDoobGraph RHTower.CHMDClosedJump
open RHTower.CHMDThetaTranslate RHTower.CHMDTranslation
namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
private theorem sourceGraph_norm_sq (p : SourceGraph) :
    ‖p‖ ^ 2 = ‖edgeMap p‖ ^ 2 + ‖sourceMap p‖ ^ 2 := by
  have h := sourceEnergy_add_two_mass p
  change ‖p.val.snd‖ ^ 2 - ‖p.val.fst‖ ^ 2 + 2 * ‖p.val.fst‖ ^ 2 = ‖p‖ ^ 2 at h
  change ‖p‖ ^ 2 = ‖p.val.snd‖ ^ 2 + ‖p.val.fst‖ ^ 2
  linarith

theorem abs_sourcePair_le_graph_norm (p q : SourceGraph) :
    |sourcePair p q| ≤ ‖p‖ * ‖q‖ := by
  have h := (abs_sub _ _).trans (add_le_add
    (abs_real_inner_le_norm (edgeMap p) (edgeMap q))
    (abs_real_inner_le_norm (sourceMap p) (sourceMap q)))
  change |sourcePair p q| ≤ ‖edgeMap p‖ * ‖edgeMap q‖ +
    ‖sourceMap p‖ * ‖sourceMap q‖ at h
  apply h.trans
  have hp := sourceGraph_norm_sq p
  have hq := sourceGraph_norm_sq q
  have hs := sq_nonneg (‖edgeMap p‖ * ‖sourceMap q‖ - ‖sourceMap p‖ * ‖edgeMap q‖)
  have ht : (‖edgeMap p‖ * ‖edgeMap q‖ + ‖sourceMap p‖ * ‖sourceMap q‖) ^ 2 ≤
      (‖p‖ * ‖q‖) ^ 2 := by rw [mul_pow, hp, hq]; nlinarith
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp ht

theorem abs_sourceEnergy_sub_le_graph_error (p q : SourceGraph) :
    |sourceEnergy p - sourceEnergy q| ≤ ‖p - q‖ * (2 * ‖q‖ + ‖p - q‖) := by
  have hsub (u v w : SourceGraph) : sourcePair u (v - w) =
      sourcePair u v - sourcePair u w := by
    rw [sourcePair_symm, sourcePair_sub_left, sourcePair_symm v u, sourcePair_symm w u]
  have he : sourceEnergy p - sourceEnergy q =
      2 * sourcePair (p - q) q + sourceEnergy (p - q) := by
    simp only [← sourcePair_self, sourcePair_sub_left, hsub, sourcePair_symm q p]
    ring
  rw [he]
  calc |2 * sourcePair (p - q) q + sourceEnergy (p - q)|
      ≤ |2 * sourcePair (p - q) q| + |sourceEnergy (p - q)| := abs_add_le _ _
    _ ≤ 2 * (‖p - q‖ * ‖q‖) + ‖p - q‖ * ‖p - q‖ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← sourcePair_self]
      exact add_le_add (mul_le_mul_of_nonneg_left (abs_sourcePair_le_graph_norm _ _) (by norm_num))
        (abs_sourcePair_le_graph_norm _ _)
    _ = _ := by ring

def fullCutoffEdgeBudget (n : ℕ) : ℝ :=
  ((cutoffLipschitz : ℝ) * cutoffScale n) ^ 2 * ∫ e : ℝ × ℝ, e.1 ^ 2 ∂edgeMeasure

theorem fullCutoffEdgeBudget_nonneg (n : ℕ) : 0 ≤ fullCutoffEdgeBudget n :=
  mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)

theorem cutoff_difference_le_scaled (n : ℕ) (x y : ℝ) :
    |cutoff n x - cutoff n y| ≤ (cutoffLipschitz : ℝ) * cutoffScale n * |x - y| := by
  have h := exists_baseCutoff_lipschitz.choose_spec.norm_sub_le
    (cutoffScale n * x) (cutoffScale n * y)
  change _ ≤ (cutoffLipschitz : ℝ) * ‖cutoffScale n * x - cutoffScale n * y‖ at h
  rw [← mul_sub, norm_mul, Real.norm_of_nonneg (cutoffScale_pos n).le, Real.norm_eq_abs] at h
  simpa only [cutoff, Real.norm_eq_abs, mul_assoc] using h

theorem cutoff_edge_norm_sq_le_budget (n : ℕ) :
    ‖(cutoffLift n).val.snd‖ ^ 2 ≤ fullCutoffEdgeBudget n := by
  change ‖(compact_memLp_difference (cutoff_contDiff n) (cutoff_hasCompactSupport n)).toLp _‖ ^ 2 ≤ _
  rw [norm_toLp_sq, fullCutoffEdgeBudget, ← integral_const_mul]
  apply integral_mono
    (compact_memLp_difference (cutoff_contDiff n) (cutoff_hasCompactSupport n)).integrable_sq
    (memLp_displacement.integrable_sq.const_mul _)
  intro e
  have h := cutoff_difference_le_scaled n (left e) (right e)
  have ht : |left e - right e| = |e.1| := by simp [left, right]
  rw [ht] at h
  simpa only [difference, mul_pow, sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg
      (mul_nonneg cutoffLipschitz.coe_nonneg (cutoffScale_pos n).le) (abs_nonneg _))).mpr h

theorem cutoff_error_energy_le_budget (n : ℕ) :
    sourceEnergy (cutoffLift n - constantLift 1) ≤ fullCutoffEdgeBudget n := by
  have h := cutoff_edge_norm_sq_le_budget n
  change ‖(cutoffLift n).val.snd - (constantLift 1).val.snd‖ ^ 2 -
    ‖(cutoffLift n - constantLift 1).val.fst‖ ^ 2 ≤ _
  rw [constantLift_edge, sub_zero]
  linarith [sq_nonneg ‖(cutoffLift n - constantLift 1).val.fst‖]

def translatedCutoffMassError (a : ℝ) (n : ℕ) : ℝ :=
  ∫ x, (ratio a x * (cutoff n (x - a) - 1)) ^ 2 ∂massMeasure

theorem translatedCutoffMassError_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ translatedCutoffMassError a n := integral_nonneg fun _ => sq_nonneg _

theorem translatedCutoffMassError_eq_volume (a : ℝ) (n : ℕ) :
    translatedCutoffMassError a n = ∫ x, riemannKernelReal x * Real.cosh (x / 2) *
      (ratio a x * (cutoff n (x - a) - 1)) ^ 2 := by
  exact integral_weighted volume continuous_massDensity.measurable
    (Eventually.of_forall fun x => (massDensity_pos x).le) _

theorem translatedCutoffMassError_eq_norm (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|))
    (n : ℕ) : ‖(approx a n - lift a ha).val.fst‖ ^ 2 = translatedCutoffMassError a n := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (approx a n).val.fst (lift a ha).val.fst,
    testLift_source (CHMDTranslation.translate (CHMDThetaTranslate.cutSource n) a) _ _, lift_source_ae a ha] with x hsub hn hl
  change (approx a n).val.fst x = _ at hn
  change ((approx a n).val.fst - (lift a ha).val.fst) x *
    ((approx a n).val.fst - (lift a ha).val.fst) x = _
  rw [hsub, Pi.sub_apply, hn, hl, approx_source_function]
  ring

theorem translatedCutoff_error_energy (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|))
    (n : ℕ) : sourceEnergy (approx a n - lift a ha) =
      sourceEnergy (cutoffLift n - constantLift 1) := by
  have hl := continuous_sourceEnergy.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := approx a n)).sub (approx_tendsto a ha))
  have hr := continuous_sourceEnergy.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := cutoffLift n)).sub cutoffLift_tendsto_constant)
  exact tendsto_nhds_unique hl (by
    simpa only [Function.comp_def, approx_difference_energy] using hr)

theorem translatedCutoff_graph_error_le (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|))
    (n : ℕ) : ‖approx a n - lift a ha‖ ^ 2 ≤
      fullCutoffEdgeBudget n + 2 * translatedCutoffMassError a n := by
  have h := sourceEnergy_add_two_mass (approx a n - lift a ha)
  rw [translatedCutoff_error_energy a ha n, translatedCutoffMassError_eq_norm a ha n] at h
  linarith [cutoff_error_energy_le_budget n]

theorem fullCutoffEdgeBudget_tendsto : Tendsto fullCutoffEdgeBudget atTop (𝓝 0) := by
  change Tendsto (fun n => ((cutoffLipschitz : ℝ) * cutoffScale n) ^ 2 *
    ∫ e : ℝ × ℝ, e.1 ^ 2 ∂edgeMeasure) atTop (𝓝 0)
  have hs : Tendsto cutoffScale atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  simpa [fullCutoffEdgeBudget] using ((hs.const_mul (cutoffLipschitz : ℝ)).pow 2).mul_const
    (∫ e : ℝ × ℝ, e.1 ^ 2 ∂edgeMeasure)

theorem translatedCutoffMassError_tendsto (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    Tendsto (translatedCutoffMassError a) atTop (𝓝 0) := by
  have h := sourceMap.continuous.continuousAt.tendsto.comp
    ((approx_tendsto a ha).sub (tendsto_const_nhds (x := lift a ha)))
  have ht := h.norm.pow 2
  simp only [sub_self, map_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at ht
  change Tendsto (fun n => ‖(approx a n - lift a ha).val.fst‖ ^ 2) atTop (𝓝 0) at ht
  simpa only [translatedCutoffMassError_eq_norm] using ht

def canonicalOddCutoff (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (CHMDTranslation.translate (CHMDThetaTranslate.cutSource n) a x - CHMDTranslation.translate (CHMDThetaTranslate.cutSource n) (-a) x) / (2 * Real.sinh (a / 2))

def canonicalOddCutoffGraph (a : ℝ) (n : ℕ) : SourceGraph :=
  (2 * Real.sinh (a / 2))⁻¹ • (approx a n - approx (-a) n)

def canonicalOddCutoffBudget (a : ℝ) (n : ℕ) : ℝ :=
  4 * ((2 * Real.sinh (a / 2))⁻¹) ^ 2 *
    (fullCutoffEdgeBudget n + translatedCutoffMassError a n + translatedCutoffMassError (-a) n)

theorem canonicalOddCutoffBudget_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ canonicalOddCutoffBudget a n := by
  unfold canonicalOddCutoffBudget
  have hj := fullCutoffEdgeBudget_nonneg n
  have hp := translatedCutoffMassError_nonneg a n
  have hm := translatedCutoffMassError_nonneg (-a) n
  positivity

theorem canonicalOddCutoff_graph_error_le (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|))
    (n : ℕ) : ‖canonicalOddCutoffGraph a n - oddPolarVectorAt a ha‖ ^ 2 ≤
      canonicalOddCutoffBudget a n := by
  have hp := translatedCutoff_graph_error_le a ha n
  have hm := translatedCutoff_graph_error_le (-a) (neg_admissible ha) n
  have he : canonicalOddCutoffGraph a n - oddPolarVectorAt a ha =
      (2 * Real.sinh (a / 2))⁻¹ •
        ((approx a n - lift a ha) - (approx (-a) n - lift (-a) (neg_admissible ha))) := by
    unfold canonicalOddCutoffGraph oddPolarVectorAt
    module
  rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have htri := norm_sub_le (approx a n - lift a ha) (approx (-a) n - lift (-a) (neg_admissible ha))
  have hs : ‖(approx a n - lift a ha) - (approx (-a) n - lift (-a) (neg_admissible ha))‖ ^ 2 ≤
      2 * (‖approx a n - lift a ha‖ ^ 2 + ‖approx (-a) n - lift (-a) (neg_admissible ha)‖ ^ 2) := by
    nlinarith [norm_nonneg ((approx a n - lift a ha) - (approx (-a) n - lift (-a) (neg_admissible ha))),
      norm_nonneg (approx a n - lift a ha), norm_nonneg (approx (-a) n - lift (-a) (neg_admissible ha)),
      sq_nonneg (‖approx a n - lift a ha‖ - ‖approx (-a) n - lift (-a) (neg_admissible ha)‖)]
  have ht : ‖(approx a n - lift a ha) - (approx (-a) n - lift (-a) (neg_admissible ha))‖ ^ 2 ≤
      4 * (fullCutoffEdgeBudget n + translatedCutoffMassError a n +
        translatedCutoffMassError (-a) n) := hs.trans (by linarith)
  have h := mul_le_mul_of_nonneg_left ht
    (sq_nonneg ((2 * Real.sinh (a / 2))⁻¹))
  unfold canonicalOddCutoffBudget
  nlinarith [h]

theorem canonicalOddCutoffBudget_tendsto (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    Tendsto (canonicalOddCutoffBudget a) atTop (𝓝 0) := by
  change Tendsto (fun n => 4 * ((2 * Real.sinh (a / 2))⁻¹) ^ 2 *
    (fullCutoffEdgeBudget n + translatedCutoffMassError a n + translatedCutoffMassError (-a) n))
    atTop (𝓝 0)
  simpa only [canonicalOddCutoffBudget, add_zero, mul_zero] using
    ((fullCutoffEdgeBudget_tendsto.add (translatedCutoffMassError_tendsto a ha)).add
      (translatedCutoffMassError_tendsto (-a) (neg_admissible ha))).const_mul
        (4 * ((2 * Real.sinh (a / 2))⁻¹) ^ 2)

theorem canonicalOddCutoff_complete_energy_error {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (n : ℕ) :
    |sourceEnergy (canonicalOddCutoffGraph a n) - 1 / 2| ≤
      Real.sqrt (canonicalOddCutoffBudget a n) *
        (2 * ‖oddPolarVectorAt a ha‖ + Real.sqrt (canonicalOddCutoffBudget a n)) := by
  have h := abs_sourceEnergy_sub_le_graph_error (canonicalOddCutoffGraph a n) (oddPolarVectorAt a ha)
  rw [sourceEnergy_oddPolarVectorAt hane ha] at h
  have hb := canonicalOddCutoff_graph_error_le a ha n
  have hs := Real.sq_sqrt (canonicalOddCutoffBudget_nonneg a n)
  have hn : ‖canonicalOddCutoffGraph a n - oddPolarVectorAt a ha‖ ≤
      Real.sqrt (canonicalOddCutoffBudget a n) := by
    nlinarith [Real.sqrt_nonneg (canonicalOddCutoffBudget a n),
      norm_nonneg (canonicalOddCutoffGraph a n - oddPolarVectorAt a ha)]
  exact h.trans (mul_le_mul hn (by linarith) (by positivity) (Real.sqrt_nonneg _))

theorem canonicalOddCutoff_contDiff (a : ℝ) (n : ℕ) :
    ContDiff ℝ 2 (canonicalOddCutoff a n) :=
  ((contDiff_translate (cutSource_contDiff n) a).sub
    (contDiff_translate (cutSource_contDiff n) (-a))).div_const _

theorem canonicalOddCutoff_compact (a : ℝ) (n : ℕ) :
    HasCompactSupport (canonicalOddCutoff a n) := by
  have h := (compact_translate (cutSource_compact n) a).sub
    (compact_translate (cutSource_compact n) (-a))
  have hc : HasCompactSupport (fun x =>
      (CHMDTranslation.translate (CHMDThetaTranslate.cutSource n) a x - CHMDTranslation.translate (CHMDThetaTranslate.cutSource n) (-a) x) *
        (2 * Real.sinh (a / 2))⁻¹) := h.mul_right
  change HasCompactSupport (fun x =>
    (CHMDTranslation.translate (CHMDThetaTranslate.cutSource n) a x -
      CHMDTranslation.translate (CHMDThetaTranslate.cutSource n) (-a) x) / (2 * Real.sinh (a / 2)))
  simpa only [div_eq_mul_inv] using hc

private theorem cutoff_even (n : ℕ) (x : ℝ) : cutoff n (-x) = cutoff n x := by
  simp only [cutoff, mul_neg, baseCutoff.neg]

private theorem cutSource_even (n : ℕ) (x : ℝ) : CHMDThetaTranslate.cutSource n (-x) = CHMDThetaTranslate.cutSource n x := by
  simp only [CHMDThetaTranslate.cutSource, phiDoobTest, WeilExcess.riemannKernelReal_neg, cutoff_even]

theorem canonicalOddCutoff_odd (a : ℝ) (n : ℕ) (x : ℝ) :
    canonicalOddCutoff a n (-x) = -canonicalOddCutoff a n x := by
  unfold canonicalOddCutoff CHMDTranslation.translate
  rw [show -x - a = -(x + a) by ring, show -x - -a = -(x - a) by ring,
    cutSource_even, cutSource_even, sub_neg_eq_add]
  ring

theorem canonicalOddCutoff_mean_zero (a : ℝ) (n : ℕ) :
    (∫ x, canonicalOddCutoff a n x) = 0 :=
  integral_eq_zero_of_odd (canonicalOddCutoff_odd a n)

theorem cutoff_eq_one_on_inner (n : ℕ) {x : ℝ} (hx : |x| ≤ (n : ℝ) + 1) :
    cutoff n x = 1 := by
  apply baseCutoff.one_of_mem_closedBall
  have hi : cutoffScale n * ((n : ℝ) + 1) = 1 := by
    unfold cutoffScale
    exact inv_mul_cancel₀ (by positivity)
  have h := mul_le_mul_of_nonneg_left hx (cutoffScale_pos n).le
  rw [hi] at h
  simpa only [Metric.mem_closedBall, dist_zero_right, baseCutoff,
    Real.norm_eq_abs, abs_mul, abs_of_pos (cutoffScale_pos n)] using h

theorem cutoff_eq_zero_on_outer (n : ℕ) {x : ℝ} (hx : 2 * ((n : ℝ) + 1) ≤ |x|) :
    cutoff n x = 0 := by
  apply baseCutoff.zero_of_le_dist
  have hi : cutoffScale n * ((n : ℝ) + 1) = 1 := by
    unfold cutoffScale
    exact inv_mul_cancel₀ (by positivity)
  have h := mul_le_mul_of_nonneg_left hx (cutoffScale_pos n).le
  have ht : 2 ≤ cutoffScale n * |x| := by nlinarith [hi]
  simpa only [dist_zero_right, baseCutoff, Real.norm_eq_abs, abs_mul,
    abs_of_pos (cutoffScale_pos n)] using ht

theorem canonicalOddCutoff_eq_profile_on_inner (a : ℝ) (n : ℕ) {x : ℝ}
    (hx : |x| + |a| ≤ (n : ℝ) + 1) : canonicalOddCutoff a n x = oddProfile a x := by
  have hm := cutoff_eq_one_on_inner n ((abs_sub x a).trans hx)
  have hp := cutoff_eq_one_on_inner n ((abs_add_le x a).trans hx)
  simp only [canonicalOddCutoff, CHMDTranslation.translate, CHMDThetaTranslate.cutSource, phiDoobTest, sub_neg_eq_add,
    hm, hp, mul_one, oddProfile]

theorem canonicalOddCutoff_zero_on_outer (a : ℝ) (n : ℕ) {x : ℝ}
    (hx : 2 * ((n : ℝ) + 1) + |a| ≤ |x|) : canonicalOddCutoff a n x = 0 := by
  have hm : 2 * ((n : ℝ) + 1) ≤ |x - a| := by
    have h := abs_add_le (x - a) a
    rw [sub_add_cancel] at h
    linarith
  have hp : 2 * ((n : ℝ) + 1) ≤ |x + a| := by
    have h := abs_sub (x + a) a
    rw [add_sub_cancel_right] at h
    linarith
  simp only [canonicalOddCutoff, CHMDTranslation.translate, CHMDThetaTranslate.cutSource, phiDoobTest, sub_neg_eq_add,
    cutoff_eq_zero_on_outer n hm, cutoff_eq_zero_on_outer n hp, mul_zero, sub_self, zero_div]

theorem translatedCutoffResidual_zero_on_inner (a : ℝ) (n : ℕ) {x : ℝ}
    (hx : |x - a| ≤ (n : ℝ) + 1) : ratio a x * (cutoff n (x - a) - 1) = 0 := by
  rw [cutoff_eq_one_on_inner n hx, sub_self, mul_zero]

theorem canonicalOddCutoffGraph_eq_testLift (a : ℝ) (n : ℕ) :
    canonicalOddCutoffGraph a n = testLift (canonicalOddCutoff a n)
      (canonicalOddCutoff_contDiff a n) (canonicalOddCutoff_compact a n) := by
  apply source_projection_injective
  apply Lp.ext
  let A := (approx a n).val.fst
  let B := (approx (-a) n).val.fst
  let c := (2 * Real.sinh (a / 2))⁻¹
  filter_upwards [Lp.coeFn_smul c (A - B), Lp.coeFn_sub A B,
    testLift_source (CHMDTranslation.translate (CHMDThetaTranslate.cutSource n) a) _ _,
    testLift_source (CHMDTranslation.translate (CHMDThetaTranslate.cutSource n) (-a)) _ _,
    testLift_source (canonicalOddCutoff a n) _ _] with x hsm hsub hp hm ht
  change (c • (A - B)) x = _
  rw [hsm, Pi.smul_apply, hsub, Pi.sub_apply, ht]
  change c * (A x - B x) = _
  change A x = _ at hp
  change B x = _ at hm
  rw [hp, hm]
  unfold c phiDoobInv canonicalOddCutoff
  ring

theorem canonicalOddCutoffGraph_tendsto (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    Tendsto (canonicalOddCutoffGraph a) atTop (𝓝 (oddPolarVectorAt a ha)) :=
  ((approx_tendsto a ha).sub (approx_tendsto (-a) (neg_admissible ha))).const_smul _

theorem canonicalOddCutoff_energy_eq (a : ℝ) (n : ℕ) :
    sourceEnergy (canonicalOddCutoffGraph a n) =
      markovEnergy (fun x => (canonicalOddCutoff a n x : ℂ)) := by
  rw [canonicalOddCutoffGraph_eq_testLift, testLift_energy]

theorem canonicalOddCutoff_eventually_positive {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    ∀ᶠ n in atTop, (1 / 4 : ℝ) < markovEnergy (fun x => (canonicalOddCutoff a n x : ℂ)) := by
  have h := continuous_sourceEnergy.continuousAt.tendsto.comp
    (canonicalOddCutoffGraph_tendsto a ha)
  rw [sourceEnergy_oddPolarVectorAt hane ha] at h
  simpa only [Function.comp_def, canonicalOddCutoff_energy_eq] using
    h.eventually_const_lt (by norm_num : (1 / 4 : ℝ) < 1 / 2)

theorem canonicalOddCutoff_markov_error {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (n : ℕ) :
    |markovEnergy (fun x => (canonicalOddCutoff a n x : ℂ)) - 1 / 2| ≤
      Real.sqrt (canonicalOddCutoffBudget a n) *
        (2 * ‖oddPolarVectorAt a ha‖ + Real.sqrt (canonicalOddCutoffBudget a n)) := by
  rw [← canonicalOddCutoff_energy_eq]
  exact canonicalOddCutoff_complete_energy_error hane ha n

theorem canonicalOddCutoff_cosh_moment (a : ℝ) (n : ℕ) :
    coshHalfMoment (canonicalOddCutoff a n) = 0 := by
  unfold coshHalfMoment
  apply integral_eq_zero_of_odd
  intro x
  rw [canonicalOddCutoff_odd, neg_div, Real.cosh_neg, neg_mul]

theorem canonicalOddCutoff_sinh_moment {a : ℝ} (ha : a ≠ 0) (n : ℕ) :
    sinhHalfMoment (canonicalOddCutoff a n) = coshHalfMoment (CHMDThetaTranslate.cutSource n) := by
  let c := (2 * Real.sinh (a / 2))⁻¹
  have he : canonicalOddCutoff a n = fun x =>
      c * CHMDTranslation.translate (CHMDThetaTranslate.cutSource n) a x + (-c) * CHMDTranslation.translate (CHMDThetaTranslate.cutSource n) (-a) x := by
    funext x
    unfold canonicalOddCutoff c
    ring
  rw [he, sinhHalfMoment_linear_comb
    (contDiff_translate (cutSource_contDiff n) a).continuous (compact_translate (cutSource_compact n) a)
    (contDiff_translate (cutSource_contDiff n) (-a)).continuous
      (compact_translate (cutSource_compact n) (-a)),
    sinhHalfMoment_translate (cutSource_contDiff n).continuous (cutSource_compact n),
    sinhHalfMoment_translate (cutSource_contDiff n).continuous (cutSource_compact n),
    neg_div, Real.sinh_neg, Real.cosh_neg]
  have hs : Real.sinh (a / 2) ≠ 0 := by
    rw [ne_eq, Real.sinh_eq_zero]
    exact div_ne_zero ha (by norm_num)
  unfold c
  field_simp [hs]
  ring

def canonicalPrimitiveCutoff (a b : ℝ) (n : ℕ) : ℝ → ℝ :=
  canonicalOddCutoff a n - canonicalOddCutoff b n

theorem canonicalPrimitiveCutoff_contDiff (a b : ℝ) (n : ℕ) :
    ContDiff ℝ 2 (canonicalPrimitiveCutoff a b n) :=
  (canonicalOddCutoff_contDiff a n).sub (canonicalOddCutoff_contDiff b n)

theorem canonicalPrimitiveCutoff_compact (a b : ℝ) (n : ℕ) :
    HasCompactSupport (canonicalPrimitiveCutoff a b n) :=
  (canonicalOddCutoff_compact a n).sub (canonicalOddCutoff_compact b n)

theorem canonicalPrimitiveCutoff_odd (a b : ℝ) (n : ℕ) (x : ℝ) :
    canonicalPrimitiveCutoff a b n (-x) = -canonicalPrimitiveCutoff a b n x := by
  simp only [canonicalPrimitiveCutoff, Pi.sub_apply, canonicalOddCutoff_odd]
  ring

/-- The same unshifted cutoff gives exact cancellation of both polar moments. -/
theorem canonicalPrimitiveCutoff_moments {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    coshHalfMoment (canonicalPrimitiveCutoff a b n) = 0 ∧
    sinhHalfMoment (canonicalPrimitiveCutoff a b n) = 0 := by
  have he : canonicalPrimitiveCutoff a b n = fun x =>
      1 * canonicalOddCutoff a n x + (-1) * canonicalOddCutoff b n x := by
    funext x
    simp only [canonicalPrimitiveCutoff, Pi.sub_apply]
    ring
  rw [he, coshHalfMoment_linear_comb (canonicalOddCutoff_contDiff a n).continuous
    (canonicalOddCutoff_compact a n) (canonicalOddCutoff_contDiff b n).continuous
    (canonicalOddCutoff_compact b n),
    sinhHalfMoment_linear_comb (canonicalOddCutoff_contDiff a n).continuous
    (canonicalOddCutoff_compact a n) (canonicalOddCutoff_contDiff b n).continuous
    (canonicalOddCutoff_compact b n), canonicalOddCutoff_cosh_moment,
    canonicalOddCutoff_cosh_moment, canonicalOddCutoff_sinh_moment ha,
    canonicalOddCutoff_sinh_moment hb]
  constructor <;> ring

private theorem canonicalPrimitiveCutoff_energy (a b : ℝ) (n : ℕ) :
    sourceEnergy (canonicalOddCutoffGraph a n - canonicalOddCutoffGraph b n) =
      markovEnergy (fun x => (canonicalPrimitiveCutoff a b n x : ℂ)) := by
  rw [canonicalOddCutoffGraph_eq_testLift, canonicalOddCutoffGraph_eq_testLift,
    ← testLift_sub, testLift_energy]
  rfl

private theorem abs_sourceEnergy_le_graph_norm_sq (p : SourceGraph) :
    |sourceEnergy p| ≤ ‖p‖ ^ 2 := by
  rw [← sourcePair_self]
  simpa only [pow_two] using abs_sourcePair_le_graph_norm p p

private theorem sourceEnergy_sub_radical (p q : SourceGraph)
    (hq : ∀ r, sourcePair q r = 0) : sourceEnergy (p - q) = sourceEnergy p := by
  rw [← sourcePair_self, sourcePair_sub_left, hq, sub_zero, sourcePair_symm,
    sourcePair_sub_left, hq, sub_zero, sourcePair_self]

/-- Signed-radical cancellation removes the square-root error. All arithmetic edges
and the original mass subtraction remain in this finite-horizon estimate. -/
theorem canonicalPrimitiveCutoff_complete_energy_bound {a b : ℝ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (hb : 1 < 2 * Real.exp (-2 * |b|)) (n : ℕ) :
    |markovEnergy (fun x => (canonicalPrimitiveCutoff a b n x : ℂ))| ≤
      2 * (canonicalOddCutoffBudget a n + canonicalOddCutoffBudget b n) := by
  let p := canonicalOddCutoffGraph a n - canonicalOddCutoffGraph b n
  let q := oddCritical a b ha hb
  have hrad : ∀ r, sourcePair q r = 0 := oddCritical_mem_signedRadical ha0 hb0 ha hb
  have he : p - q = (canonicalOddCutoffGraph a n - oddPolarVectorAt a ha) -
      (canonicalOddCutoffGraph b n - oddPolarVectorAt b hb) := by
    unfold p q oddCritical
    abel
  rw [← canonicalPrimitiveCutoff_energy]
  change |sourceEnergy p| ≤ _
  rw [← sourceEnergy_sub_radical p q hrad]
  apply (abs_sourceEnergy_le_graph_norm_sq (p - q)).trans
  rw [he]
  have ht := norm_sub_le (canonicalOddCutoffGraph a n - oddPolarVectorAt a ha)
    (canonicalOddCutoffGraph b n - oddPolarVectorAt b hb)
  have hs : ‖(canonicalOddCutoffGraph a n - oddPolarVectorAt a ha) -
      (canonicalOddCutoffGraph b n - oddPolarVectorAt b hb)‖ ^ 2 ≤
      2 * (‖canonicalOddCutoffGraph a n - oddPolarVectorAt a ha‖ ^ 2 +
        ‖canonicalOddCutoffGraph b n - oddPolarVectorAt b hb‖ ^ 2) := by
    nlinarith [norm_nonneg ((canonicalOddCutoffGraph a n - oddPolarVectorAt a ha) -
      (canonicalOddCutoffGraph b n - oddPolarVectorAt b hb)),
      norm_nonneg (canonicalOddCutoffGraph a n - oddPolarVectorAt a ha),
      norm_nonneg (canonicalOddCutoffGraph b n - oddPolarVectorAt b hb),
      sq_nonneg (‖canonicalOddCutoffGraph a n - oddPolarVectorAt a ha‖ -
        ‖canonicalOddCutoffGraph b n - oddPolarVectorAt b hb‖)]
  exact hs.trans (mul_le_mul_of_nonneg_left (add_le_add
    (canonicalOddCutoff_graph_error_le a ha n) (canonicalOddCutoff_graph_error_le b hb n))
      (by norm_num))

theorem canonicalPrimitiveCutoff_energy_tendsto {a b : ℝ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (hb : 1 < 2 * Real.exp (-2 * |b|)) :
    Tendsto (fun n => markovEnergy (fun x => (canonicalPrimitiveCutoff a b n x : ℂ)))
      atTop (𝓝 0) := by
  have h := continuous_sourceEnergy.continuousAt.tendsto.comp
    ((canonicalOddCutoffGraph_tendsto a ha).sub (canonicalOddCutoffGraph_tendsto b hb))
  change Tendsto (fun n => sourceEnergy (canonicalOddCutoffGraph a n - canonicalOddCutoffGraph b n))
    atTop (𝓝 (sourceEnergy (oddCritical a b ha hb))) at h
  simpa only [canonicalPrimitiveCutoff_energy, oddCritical_sourceEnergy ha0 hb0 ha hb] using h

/-- The admitted critical sequence gives genuinely nonzero finite-horizon graph tests. -/
theorem canonicalPrimitiveCutoff_eventually_nonzero (k : ℕ) :
    ∀ᶠ n in atTop,
      canonicalOddCutoffGraph (shifts (k + 1)) n - canonicalOddCutoffGraph (shifts 0) n ≠ 0 := by
  have h := (canonicalOddCutoffGraph_tendsto (shifts (k + 1)) (shifts_admissible (k + 1))).sub
    (canonicalOddCutoffGraph_tendsto (shifts 0) (shifts_admissible 0))
  change Tendsto _ atTop (𝓝 (oddCriticalSequence k)) at h
  exact h.eventually_ne (LinearIndependent.ne_zero k oddCriticalSequence_linearIndependent)

/-- Each primitive test keeps the full compensated chain expression, including cosh mass. -/
theorem canonicalPrimitiveCutoff_complete_chain_identity (a b : ℝ) (n : ℕ) :
    let v := phiDoobInv (canonicalPrimitiveCutoff a b n)
    markovEnergy (fun x => (canonicalPrimitiveCutoff a b n x : ℂ)) =
      phiDoobArchJumpEnergy v + RHTower.CHMDPrimeCuts.sameSide v +
        RHTower.CHMDPrimeCuts.sameSide (fun x => v (-x)) +
        (∑' q : RHTower.CHMDPrimeChainSource.ChainIndex,
          RHTower.CHMDPrimeChainSource.chainIntegral v q) - phiDoobCoshMass (fun x => v x ^ 2) := by
  have h := RHTower.CHMDPrimeChainSource.doob_source_eq_chain_variances_sub_cosh
    (contDiff_phiDoobInv (canonicalPrimitiveCutoff_contDiff a b n))
    (hasCompactSupport_phiDoobInv (canonicalPrimitiveCutoff_compact a b n))
  simpa only [phiDoobTest_phiDoobInv] using h

/-- The translated source moment pays the moving cutoff error in the original mass. -/
def translatedSourceMoment (a : ℝ) : ℝ :=
  ∫ x, ((x - a) * ratio a x) ^ 2 ∂massMeasure

theorem translatedSourceMoment_nonneg (a : ℝ) : 0 ≤ translatedSourceMoment a :=
  integral_nonneg fun _ => sq_nonneg _

private theorem shifted_square_le_exp (a x : ℝ) :
    (x - a) ^ 2 ≤ (1 + |a|) ^ 2 * Real.exp (2 * |x|) := by
  have h1 := Real.add_one_le_exp |x|
  have h2 : 1 ≤ Real.exp |x| := Real.one_le_exp_iff.mpr (abs_nonneg x)
  have ht : |x - a| ≤ (1 + |a|) * Real.exp |x| := by
    nlinarith [abs_sub x a, mul_nonneg (abs_nonneg a) (sub_nonneg.mpr h2)]
  have hs := (sq_le_sq₀ (abs_nonneg (x - a)) (by positivity)).mpr ht
  have he : Real.exp |x| ^ 2 = Real.exp (2 * |x|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [sq_abs, mul_pow, he] using hs

/-- The strict theta-translation admission also admits the first spatial moment. -/
theorem memLp_translatedSourceMoment (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    MemLp (fun x => (x - a) * ratio a x) 2 massMeasure := by
  let c := Real.pi * (2 * Real.exp (-2 * |a|) - 1)
  let B := HedenmalmThetaSource.thetaEnvelopeUpper ^ 2 /
    HedenmalmThetaSource.thetaEnvelopeLower * Real.exp (9 * |a|)
  have hc : 0 < c := mul_pos Real.pi_pos (by linarith)
  have hcont : Continuous (fun x => (x - a) * ratio a x) :=
    (continuous_id.sub continuous_const).mul (continuous_ratio a)
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable, massMeasure,
    integrable_weighted_iff volume continuous_massDensity.measurable
      (Eventually.of_forall fun x => (massDensity_pos x).le)]
  apply ((cusp_integrable 7 c hc).const_mul (B * (1 + |a|) ^ 2)).mono'
    (continuous_massDensity.mul (hcont.pow 2)).aestronglyMeasurable
  have hz : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
  filter_upwards [hz] with x hx
  change ‖massDensity x * ((x - a) * ratio a x) ^ 2‖ ≤
    B * (1 + |a|) ^ 2 * Real.exp (7 * |x| - c * Real.exp (2 * |x|))
  rw [Real.norm_of_nonneg (mul_nonneg (massDensity_pos x).le (sq_nonneg _))]
  have hb : massDensity x * ratio a x ^ 2 ≤ B * Real.exp (5 * |x| - c * Real.exp (2 * |x|)) :=
    ratio_mass_bound a x hx
  calc massDensity x * ((x - a) * ratio a x) ^ 2
      = (x - a) ^ 2 * (massDensity x * ratio a x ^ 2) := by ring
    _ ≤ ((1 + |a|) ^ 2 * Real.exp (2 * |x|)) *
        (B * Real.exp (5 * |x| - c * Real.exp (2 * |x|))) :=
      mul_le_mul (shifted_square_le_exp a x) hb
        (mul_nonneg (massDensity_pos x).le (sq_nonneg _)) (by positivity)
    _ = B * (1 + |a|) ^ 2 * Real.exp (7 * |x| - c * Real.exp (2 * |x|)) := by
      rw [show 7 * |x| - c * Real.exp (2 * |x|) =
        2 * |x| + (5 * |x| - c * Real.exp (2 * |x|)) by ring, Real.exp_add]
      ring

private theorem memLp_translatedCutoffResidual (a : ℝ)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (n : ℕ) :
    MemLp (fun x => ratio a x * (cutoff n (x - a) - 1)) 2 massMeasure := by
  have hc := compact_memLp_mass
    (contDiff_phiDoobInv (contDiff_translate (cutSource_contDiff n) a)).continuous
    (hasCompactSupport_phiDoobInv (compact_translate (cutSource_compact n) a))
  apply (hc.sub (memLp_ratio ha)).ae_eq
  exact Eventually.of_forall fun x => by
    dsimp only [Pi.sub_apply]
    rw [approx_source_function]
    ring

/-- Every omitted translated mass term is paid by a finite source moment at inverse-square rate. -/
theorem translatedCutoffMassError_le_moment (a : ℝ)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (n : ℕ) :
    translatedCutoffMassError a n ≤
      ((cutoffLipschitz : ℝ) * cutoffScale n) ^ 2 * translatedSourceMoment a := by
  unfold translatedCutoffMassError translatedSourceMoment
  rw [← integral_const_mul]
  apply integral_mono (memLp_translatedCutoffResidual a ha n).integrable_sq
    ((memLp_translatedSourceMoment a ha).integrable_sq.const_mul _)
  intro x
  have hb := cutoff_difference_le_scaled n (x - a) 0
  have hz : cutoff n 0 = 1 := cutoff_eq_one_on_inner n (x := 0)
    (by simpa only [abs_zero] using (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity))
  rw [hz, sub_zero] at hb
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg
    (mul_nonneg cutoffLipschitz.coe_nonneg (cutoffScale_pos n).le) (abs_nonneg _))).mpr hb
  rw [mul_pow, sq_abs, sq_abs] at hs
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (ratio a x))
  calc (ratio a x * (cutoff n (x - a) - 1)) ^ 2
      = ratio a x ^ 2 * (cutoff n (x - a) - 1) ^ 2 := by ring
    _ ≤ ratio a x ^ 2 * (((cutoffLipschitz : ℝ) * cutoffScale n) ^ 2 * (x - a) ^ 2) := hm
    _ = _ := by ring

/-- Finite coefficient involving the full edge moment and both literal shifted source moments. -/
def canonicalOddCutoffRate (a : ℝ) : ℝ :=
  4 * ((2 * Real.sinh (a / 2))⁻¹) ^ 2 * (cutoffLipschitz : ℝ) ^ 2 *
    ((∫ e : ℝ × ℝ, e.1 ^ 2 ∂edgeMeasure) + translatedSourceMoment a + translatedSourceMoment (-a))

theorem canonicalOddCutoffRate_nonneg (a : ℝ) : 0 ≤ canonicalOddCutoffRate a := by
  have hp := translatedSourceMoment_nonneg a
  have hm := translatedSourceMoment_nonneg (-a)
  have he : 0 ≤ ∫ e : ℝ × ℝ, e.1 ^ 2 ∂edgeMeasure := integral_nonneg fun _ => sq_nonneg _
  unfold canonicalOddCutoffRate
  positivity

theorem canonicalOddCutoffBudget_le_rate (a : ℝ)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (n : ℕ) :
    canonicalOddCutoffBudget a n ≤ canonicalOddCutoffRate a * cutoffScale n ^ 2 := by
  have hp := translatedCutoffMassError_le_moment a ha n
  have hm := translatedCutoffMassError_le_moment (-a) (neg_admissible ha) n
  have ht : fullCutoffEdgeBudget n + translatedCutoffMassError a n + translatedCutoffMassError (-a) n ≤
      ((cutoffLipschitz : ℝ) * cutoffScale n) ^ 2 *
        ((∫ e : ℝ × ℝ, e.1 ^ 2 ∂edgeMeasure) + translatedSourceMoment a + translatedSourceMoment (-a)) := by
    unfold fullCutoffEdgeBudget
    nlinarith [hp, hm]
  have h := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ 4 * ((2 * Real.sinh (a / 2))⁻¹) ^ 2 by positivity)
  calc canonicalOddCutoffBudget a n ≤
      4 * ((2 * Real.sinh (a / 2))⁻¹) ^ 2 * (((cutoffLipschitz : ℝ) * cutoffScale n) ^ 2 *
        ((∫ e : ℝ × ℝ, e.1 ^ 2 ∂edgeMeasure) + translatedSourceMoment a + translatedSourceMoment (-a))) := h
    _ = _ := by unfold canonicalOddCutoffRate; ring

/-- The complete original primitive energy has a paid inverse-square horizon bound. -/
theorem canonicalPrimitiveCutoff_inverse_square_bound {a b : ℝ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (hb : 1 < 2 * Real.exp (-2 * |b|)) (n : ℕ) :
    |markovEnergy (fun x => (canonicalPrimitiveCutoff a b n x : ℂ))| ≤
      2 * (canonicalOddCutoffRate a + canonicalOddCutoffRate b) / ((n : ℝ) + 1) ^ 2 := by
  calc |markovEnergy (fun x => (canonicalPrimitiveCutoff a b n x : ℂ))|
      ≤ 2 * (canonicalOddCutoffBudget a n + canonicalOddCutoffBudget b n) :=
        canonicalPrimitiveCutoff_complete_energy_bound ha0 hb0 ha hb n
    _ ≤ 2 * (canonicalOddCutoffRate a * cutoffScale n ^ 2 +
        canonicalOddCutoffRate b * cutoffScale n ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add (canonicalOddCutoffBudget_le_rate a ha n)
        (canonicalOddCutoffBudget_le_rate b hb n)) (by norm_num)
    _ = _ := by simp only [cutoffScale, div_eq_mul_inv, inv_pow]; ring

/-- An explicit admitted sequence: no source-admission or moment hypothesis is supplied. -/
theorem canonicalCriticalCutoff_source_class (k n : ℕ) :
    let f := canonicalPrimitiveCutoff (shifts (k + 1)) (shifts 0) n
    ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ (∀ x, f (-x) = -f x) ∧
      coshHalfMoment f = 0 ∧ sinhHalfMoment f = 0 := by
  exact ⟨canonicalPrimitiveCutoff_contDiff _ _ n, canonicalPrimitiveCutoff_compact _ _ n,
    canonicalPrimitiveCutoff_odd _ _ n,
    canonicalPrimitiveCutoff_moments (shifts_pos (k + 1)).ne' (shifts_pos 0).ne' n⟩

/-- Unconditional complete energy bound for the explicit, eventually nonzero primitive sequence. -/
theorem canonicalCriticalCutoff_inverse_square_bound (k n : ℕ) :
    |markovEnergy (fun x =>
      (canonicalPrimitiveCutoff (shifts (k + 1)) (shifts 0) n x : ℂ))| ≤
      2 * (canonicalOddCutoffRate (shifts (k + 1)) + canonicalOddCutoffRate (shifts 0)) /
        ((n : ℝ) + 1) ^ 2 :=
  canonicalPrimitiveCutoff_inverse_square_bound (shifts_pos (k + 1)).ne' (shifts_pos 0).ne'
    (shifts_admissible (k + 1)) (shifts_admissible 0) n

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
