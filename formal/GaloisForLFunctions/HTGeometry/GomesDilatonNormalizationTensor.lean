import GaloisForLFunctions.HTGeometry.GomesPolynomialChargeNormalization

/-!
# When normalization commutes with tensor reweighting

The tensor construction of arXiv:2509.25276v7 section 5.2 meets the observation-kernel
question of arXiv:2607.24901v1 section 4. Normalizing an infinite initial measure erases
information that a later density factor could have made integrable. We classify this
failure exactly and exhibit it in both existing Gaussian and quartic charge families.
-/

noncomputable section
open Polynomial MeasureTheory
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- Reweight the already normalized observation by a second polynomial density. -/
def gomesDilatonNormalizedReweight (H K : ℝ[X]) : Measure ℝ :=
  (gomesDilatonMassNormalized H).withDensity (fun x => ENNReal.ofReal (dilatonWeight K x))

/-- Normalize again after the second density has been applied. -/
def gomesDilatonRenormalizedReweight (H K : ℝ[X]) : Measure ℝ :=
  (gomesDilatonNormalizedReweight H K Set.univ)⁻¹ • gomesDilatonNormalizedReweight H K

/-- The complete reweighted measure retains the inverse initial mass as an exact scalar. -/
theorem gomesDilatonNormalizedReweight_formula (H K : ℝ[X]) :
    gomesDilatonNormalizedReweight H K =
      (gomesDilatonMeasure H Set.univ)⁻¹ • gomesDilatonMeasure (H + K) := by
  rw [gomesDilatonNormalizedReweight, gomesDilatonMassNormalized,
    withDensity_smul_measure, gomesDilatonMeasure_tensor]

/-- Normalization cancels every positive finite scale of an unrestricted raw measure. -/
theorem gomesDilatonPositiveScale_normalize (H : ℝ[X]) (s : Set.Ioi (0 : ℝ)) :
    ((ENNReal.ofReal (s : ℝ) • gomesDilatonMeasure H) Set.univ)⁻¹ •
      (ENNReal.ofReal (s : ℝ) • gomesDilatonMeasure H) = gomesDilatonMassNormalized H := by
  have he : gomesDilatonMeasure (H + C (Real.log (s : ℝ))) =
      ENNReal.ofReal (s : ℝ) • gomesDilatonMeasure H := by
    rw [gomesDilatonMeasure_constant, Real.exp_log s.property]
  rw [← he]
  exact gomesDilatonMassNormalized_constant H (Real.log (s : ℝ))

/-- Exact order-of-operations law: an infinite initial mass creates irreversible zero collapse. -/
theorem gomesDilatonRenormalizedReweight_formula (H K : ℝ[X]) :
    gomesDilatonRenormalizedReweight H K =
      if gomesDilatonMeasure H Set.univ = ∞ then 0 else gomesDilatonMassNormalized (H + K) := by
  classical
  by_cases ht : gomesDilatonMeasure H Set.univ = ∞
  · rw [if_pos ht, gomesDilatonRenormalizedReweight, gomesDilatonNormalizedReweight_formula]
    simp only [ht, ENNReal.inv_top, zero_smul, smul_zero]
  · rw [if_neg ht]
    let r := (gomesDilatonMeasure H Set.univ)⁻¹
    have hr0 : r ≠ 0 := ENNReal.inv_ne_zero.mpr ht
    have hrt : r ≠ ∞ := ENNReal.inv_ne_top.mpr (gomesDilatonMeasure_mass_ne_zero H)
    let s : Set.Ioi (0 : ℝ) := ⟨r.toReal, ENNReal.toReal_pos hr0 hrt⟩
    have he : gomesDilatonNormalizedReweight H K =
        ENNReal.ofReal (s : ℝ) • gomesDilatonMeasure (H + K) := by
      rw [gomesDilatonNormalizedReweight_formula]
      simp only [s, ENNReal.ofReal_toReal hrt, r]
    rw [gomesDilatonRenormalizedReweight, he]
    exact gomesDilatonPositiveScale_normalize (H + K) s

/-- The two orders agree exactly for finite initial mass or when the final result also collapses. -/
theorem gomesDilatonRenormalizedReweight_commutes_iff (H K : ℝ[X]) :
    gomesDilatonRenormalizedReweight H K = gomesDilatonMassNormalized (H + K) ↔
      IsFiniteMeasure (gomesDilatonMeasure H) ∨ gomesDilatonMeasure (H + K) Set.univ = ∞ := by
  rw [gomesDilatonRenormalizedReweight_formula, isFiniteMeasure_iff, lt_top_iff_ne_top]
  by_cases ht : gomesDilatonMeasure H Set.univ = ∞
  · rw [if_pos ht]
    simp only [ht, ne_eq, not_true_eq_false, false_or]
    exact eq_comm.trans (gomesDilatonMassNormalized_zero_iff (H + K))
  · rw [if_neg ht]
    simp only [ne_eq, ht, not_false_eq_true, true_or]

/-- A valid probability law survives both stages exactly when both required masses are finite. -/
theorem gomesDilatonRenormalizedReweight_probability_iff (H K : ℝ[X]) :
    IsProbabilityMeasure (gomesDilatonRenormalizedReweight H K) ↔
      IsFiniteMeasure (gomesDilatonMeasure H) ∧ IsFiniteMeasure (gomesDilatonMeasure (H + K)) := by
  rw [gomesDilatonRenormalizedReweight_formula]
  by_cases ht : gomesDilatonMeasure H Set.univ = ∞
  · rw [if_pos ht]
    have hn : ¬ IsFiniteMeasure (gomesDilatonMeasure H) := not_isFiniteMeasure_iff.mpr ht
    simp only [hn, false_and, iff_false]
    intro hp
    have hm : (0 : Measure ℝ) Set.univ = 1 := @measure_univ _ _ _ hp
    exact zero_ne_one hm
  · rw [if_neg ht, gomesDilatonMassNormalized_probability_iff]
    have hf : IsFiniteMeasure (gomesDilatonMeasure H) :=
      (isFiniteMeasure_iff _).mpr (lt_top_iff_ne_top.mpr ht)
    simp only [hf, true_and]

/-- Exact Gaussian integer-charge boundary for normalization before tensor addition. -/
theorem gomesGaussianRenormalizedReweight_probability_iff (b : ℝ) (n m : ℤ) :
    IsProbabilityMeasure (gomesDilatonRenormalizedReweight
      (gomesGaussianTensorLogWeight b n) (gomesGaussianTensorLogWeight b m)) ↔
        0 < (n : ℝ) * b ∧ 0 < ((n + m : ℤ) : ℝ) * b := by
  rw [gomesDilatonRenormalizedReweight_probability_iff,
    ← gomesGaussianTensorLogWeight_add, gomesDilatonMeasure_gaussian,
    gomesDilatonMeasure_gaussian, gomesGaussianChargeMeasure_finite_iff,
    gomesGaussianChargeMeasure_finite_iff]

/-- Exact quartic integer-charge boundary for the same two-stage operation. -/
theorem gomesQuarticRenormalizedReweight_probability_iff (b : ℝ) (n m : ℤ) :
    IsProbabilityMeasure (gomesDilatonRenormalizedReweight
      (gomesQuarticTensorLogWeight b n) (gomesQuarticTensorLogWeight b m)) ↔
        0 < (n : ℝ) * b ∧ 0 < ((n + m : ℤ) : ℝ) * b := by
  have ha : gomesQuarticTensorLogWeight b (n + m) =
      gomesQuarticTensorLogWeight b n + gomesQuarticTensorLogWeight b m := by
    apply Polynomial.funext
    intro x
    simp only [gomesQuarticTensorLogWeight, gomesQuarticLogWeight_eval,
      eval_add, Int.cast_add]
    ring
  rw [gomesDilatonRenormalizedReweight_probability_iff, ← ha,
    gomesDilatonMeasure_quartic, gomesDilatonMeasure_quartic,
    gomesQuarticChargeMeasure_finite_iff, gomesQuarticChargeMeasure_finite_iff]

/-- Premature normalization of neutral volume destroys every subsequent positive Gaussian law. -/
theorem gomesGaussianNeutralNormalization_failure (b : ℝ) (n : GomesGaussianFiniteCharge b) :
    gomesDilatonRenormalizedReweight 0 (gomesGaussianTensorLogWeight b n.val) ≠
      gomesGaussianNormalizedCharge b n.val := by
  have hzero : gomesDilatonMeasure 0 Set.univ = ∞ := by
    have he : (0 : ℝ[X]) = gomesGaussianTensorLogWeight b 0 := by
      simp [gomesGaussianTensorLogWeight, gomesGaussianLogWeight]
    rw [he, gomesDilatonMeasure_gaussian, gomesGaussianChargeMeasure_zero, Real.volume_univ]
  rw [gomesDilatonRenormalizedReweight_formula, if_pos hzero]
  intro h
  exact (not_le_of_gt n.property) ((gomesGaussianNormalizedCharge_zero_iff b n.val).mp h.symm)

/-- The same premature-neutral-normalization failure holds for every positive quartic charge. -/
theorem gomesQuarticNeutralNormalization_failure (b : ℝ) (n : GomesQuarticFiniteCharge b) :
    gomesDilatonRenormalizedReweight 0 (gomesQuarticTensorLogWeight b n.val) ≠
      gomesQuarticNormalizedCharge b n.val := by
  have hzero : gomesDilatonMeasure 0 Set.univ = ∞ := by
    have he : (0 : ℝ[X]) = gomesQuarticTensorLogWeight b 0 := by
      simp [gomesQuarticTensorLogWeight, gomesQuarticLogWeight]
    rw [he, gomesDilatonMeasure_quartic, gomesQuarticChargeMeasure_zero, Real.volume_univ]
  rw [gomesDilatonRenormalizedReweight_formula, if_pos hzero]
  intro h
  exact (not_le_of_gt n.property) ((gomesQuarticNormalizedCharge_zero_iff b n.val).mp h.symm)

/-- Total normalization sends the polynomial tensor unit to the zero measure. -/
theorem gomesDilatonMassNormalized_zero_profile : gomesDilatonMassNormalized 0 = 0 := by
  rw [gomesDilatonMassNormalized_zero_iff]
  have he : gomesDilatonMeasure 0 = volume := by
    simp only [gomesDilatonMeasure, dilatonWeight, eval_zero, Real.exp_zero, ENNReal.ofReal_one]
    exact withDensity_one
  rw [he, Real.volume_univ]

/-- Gaussian witnesses show that equality of normalized observations is not stable under tensoring. -/
theorem gomesGaussianNormalized_tensor_noncongruence (b : ℝ) (n : GomesGaussianFiniteCharge b) :
    gomesDilatonMassNormalized 0 =
      gomesDilatonMassNormalized (-gomesGaussianTensorLogWeight b n.val) ∧
    gomesDilatonMassNormalized (0 + gomesGaussianTensorLogWeight b n.val) ≠
      gomesDilatonMassNormalized
        (-gomesGaussianTensorLogWeight b n.val + gomesGaussianTensorLogWeight b n.val) := by
  have he : gomesGaussianTensorLogWeight b (-n.val) =
      -gomesGaussianTensorLogWeight b n.val := by
    simp only [gomesGaussianTensorLogWeight, Int.cast_neg, neg_mul, gomesGaussianLogWeight_neg]
  have hz : gomesDilatonMassNormalized (-gomesGaussianTensorLogWeight b n.val) = 0 := by
    rw [← he]
    exact (gomesGaussianNormalizedCharge_zero_iff b (-n.val)).mpr (by
      simp only [Int.cast_neg, neg_mul]
      linarith [n.property])
  refine ⟨gomesDilatonMassNormalized_zero_profile.trans hz.symm, ?_⟩
  rw [zero_add, neg_add_cancel, gomesDilatonMassNormalized_zero_profile]
  exact fun h => (not_le_of_gt n.property) ((gomesGaussianNormalizedCharge_zero_iff b n.val).mp h)

/-- Quartic witnesses exhibit the same failure of a tensor operation on normalized observations. -/
theorem gomesQuarticNormalized_tensor_noncongruence (b : ℝ) (n : GomesQuarticFiniteCharge b) :
    gomesDilatonMassNormalized 0 =
      gomesDilatonMassNormalized (-gomesQuarticTensorLogWeight b n.val) ∧
    gomesDilatonMassNormalized (0 + gomesQuarticTensorLogWeight b n.val) ≠
      gomesDilatonMassNormalized
        (-gomesQuarticTensorLogWeight b n.val + gomesQuarticTensorLogWeight b n.val) := by
  have he : gomesQuarticTensorLogWeight b (-n.val) =
      -gomesQuarticTensorLogWeight b n.val := by
    simp only [gomesQuarticTensorLogWeight, Int.cast_neg, neg_mul, gomesQuarticLogWeight_neg]
  have hz : gomesDilatonMassNormalized (-gomesQuarticTensorLogWeight b n.val) = 0 := by
    rw [← he]
    exact (gomesQuarticNormalizedCharge_zero_iff b (-n.val)).mpr (by
      simp only [Int.cast_neg, neg_mul]
      linarith [n.property])
  refine ⟨gomesDilatonMassNormalized_zero_profile.trans hz.symm, ?_⟩
  rw [zero_add, neg_add_cancel, gomesDilatonMassNormalized_zero_profile]
  exact fun h => (not_le_of_gt n.property) ((gomesQuarticNormalizedCharge_zero_iff b n.val).mp h)

/-- No binary operation on normalized measures can recover every polynomial tensor product. -/
theorem gomesDilatonMassNormalized_no_tensor_lift :
    ¬ ∃ T : Measure ℝ → Measure ℝ → Measure ℝ, ∀ H K : ℝ[X],
      T (gomesDilatonMassNormalized H) (gomesDilatonMassNormalized K) =
        gomesDilatonMassNormalized (H + K) := by
  rintro ⟨T, hT⟩
  let n : GomesGaussianFiniteCharge 1 := ⟨1, by
    simp only [Int.cast_one, one_mul]
    exact zero_lt_one⟩
  obtain ⟨he, hn⟩ := gomesGaussianNormalized_tensor_noncongruence 1 n
  apply hn
  calc
    _ = T (gomesDilatonMassNormalized 0)
        (gomesDilatonMassNormalized (gomesGaussianTensorLogWeight 1 n.val)) := (hT _ _).symm
    _ = T (gomesDilatonMassNormalized (-gomesGaussianTensorLogWeight 1 n.val))
        (gomesDilatonMassNormalized (gomesGaussianTensorLogWeight 1 n.val)) := by rw [he]
    _ = _ := hT _ _

end GaloisForLFunctions.HTGeometry
