import GaloisForLFunctions.RHTower.ThetaTranslationDensityRatio
import GaloisForLFunctions.RHTower.ThetaWeightedHistoryProperness
import GaloisForLFunctions.RHTower.L2MellinUnitary
import GaloisForLFunctions.HTGeometry.LpContinuousMultiplierNorm

/-!
# Sharp translation operators on the literal theta weighted scale

Positive density unitaries conjugate actual translation with its continuous
multiplier. Interval indicators force the ratio bound; the two cusp tails
then give the strict exponent threshold, including failure at equality.
The squared operator norm is the literal density-ratio essential supremum.
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace RHTower
open HedenmalmThetaSource

private theorem densityRoot_pos (q x : ℝ) :
    0 < Real.sqrt (thetaCuspFullSource x ^ (-q)) :=
  Real.sqrt_pos.mpr (Real.rpow_pos_of_pos (thetaCuspFullSource_pos_all x) _)

private theorem densityRoot_ne_zero (q x : ℝ) :
    (Real.sqrt (thetaCuspFullSource x ^ (-q)) : ℂ) ≠ 0 := by
  exact_mod_cast (densityRoot_pos q x).ne'

/-- The inverse density unitary preserves the literal reciprocal-root representative. -/
theorem thetaPowerDensityUnitary_symm_coe (q : ℝ)
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ((thetaPowerDensityUnitary q).symm g : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.sqrt (thetaCuspFullSource x ^ (-q)) : ℂ)⁻¹ * g x := by
  have h := thetaPowerDensityUnitary_coe q ((thetaPowerDensityUnitary q).symm g)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  filter_upwards [h] with x hx
  rw [hx, ← mul_assoc, inv_mul_cancel₀ (densityRoot_ne_zero q x), one_mul]

theorem thetaLebesgueTranslation_coe (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (MellinL2.additiveTranslationUnitary a f : ℝ → ℂ) =ᵐ[volume]
      fun x => f (x+a) := by
  exact Lp.coeFn_compMeasurePreserving f (MellinL2.realTranslation_measurePreserving a)

/-- The actual conjugated symbol at the output coordinate. -/
def thetaTranslationMultiplier (q q' a x : ℝ) : ℂ :=
  (Real.sqrt (thetaCuspFullSource x ^ (-q')) /
    Real.sqrt (thetaCuspFullSource (x+a) ^ (-q)) : ℝ)

theorem continuous_thetaTranslationMultiplier (q q' a : ℝ) :
    Continuous (thetaTranslationMultiplier q q' a) := by
  have hk := contDiff_thetaCuspFullSource.continuous
  apply Complex.continuous_ofReal.comp
  exact (Real.continuous_sqrt.comp (hk.rpow_const
    fun x => Or.inl (thetaCuspFullSource_pos_all x).ne')).div
    (Real.continuous_sqrt.comp ((hk.comp (continuous_id.add continuous_const)).rpow_const
      fun x => Or.inl (thetaCuspFullSource_pos_all (x+a)).ne'))
    (fun x => (densityRoot_pos q (x+a)).ne')

theorem norm_thetaTranslationMultiplier (q q' a x : ℝ) :
    ‖thetaTranslationMultiplier q q' a x‖ =
      Real.sqrt (thetaTranslationDensityRatio q q' a (x+a)) := by
  rw [thetaTranslationMultiplier, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (densityRoot_pos q' x) (densityRoot_pos q (x+a)))]
  simp only [thetaTranslationDensityRatio, add_sub_cancel_right]
  exact (Real.sqrt_div (Real.rpow_pos_of_pos (thetaCuspFullSource_pos_all x) (-q')).le _).symm

theorem norm_thetaTranslationMultiplier_sq (q q' a x : ℝ) :
    ‖thetaTranslationMultiplier q q' a x‖ ^ 2 =
      thetaTranslationDensityRatio q q' a (x+a) := by
  rw [norm_thetaTranslationMultiplier,
    Real.sq_sqrt (thetaTranslationDensityRatio_pos q q' a (x+a)).le]

theorem thetaTranslationMultiplier_bounded (q q' a : ℝ)
    (hb : BddAbove (range (thetaTranslationDensityRatio q q' a))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖thetaTranslationMultiplier q q' a x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun x => ?_⟩
  rw [norm_thetaTranslationMultiplier]
  exact Real.sqrt_le_sqrt (hC ⟨x+a, rfl⟩)

/-- Every input is sent to its literal translate, modulo the equivalent theta null sets. -/
def IsThetaWeightedTranslation (q q' a : ℝ)
    (T : Lp ℂ 2 (thetaPowerWeightedMeasure q) →L[ℂ]
      Lp ℂ 2 (thetaPowerWeightedMeasure q')) : Prop :=
  ∀ f, (T f : ℝ → ℂ) =ᵐ[volume] fun x => f (x+a)

/-- The ordinary Lebesgue operator obtained from the literal weighted translation. -/
def thetaTranslationConjugate (q q' a : ℝ)
    (T : Lp ℂ 2 (thetaPowerWeightedMeasure q) →L[ℂ]
      Lp ℂ 2 (thetaPowerWeightedMeasure q')) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (((thetaPowerDensityUnitary q').toContinuousLinearEquiv.toContinuousLinearMap.comp T).comp
    (thetaPowerDensityUnitary q).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (MellinL2.additiveTranslationUnitary (-a)).toContinuousLinearEquiv.toContinuousLinearMap

theorem norm_thetaTranslationConjugate (q q' a : ℝ)
    (T : Lp ℂ 2 (thetaPowerWeightedMeasure q) →L[ℂ]
      Lp ℂ 2 (thetaPowerWeightedMeasure q')) :
    ‖thetaTranslationConjugate q q' a T‖ = ‖T‖ := by
  unfold thetaTranslationConjugate
  rw [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp]

theorem thetaTranslationConjugate_coe (q q' a : ℝ)
    (T : Lp ℂ 2 (thetaPowerWeightedMeasure q) →L[ℂ]
      Lp ℂ 2 (thetaPowerWeightedMeasure q')) (hT : IsThetaWeightedTranslation q q' a T)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (thetaTranslationConjugate q q' a T f : ℝ → ℂ) =ᵐ[volume]
      fun x => thetaTranslationMultiplier q q' a x * f x := by
  let g := MellinL2.additiveTranslationUnitary (-a) f
  let h := (thetaPowerDensityUnitary q).symm g
  have hu := thetaPowerDensityUnitary_symm_coe q g
  have ht := thetaLebesgueTranslation_coe (-a) f
  have hs := (MellinL2.realTranslation_measurePreserving a).quasiMeasurePreserving.tendsto_ae
  change (thetaPowerDensityUnitary q' (T h) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [thetaPowerDensityUnitary_coe q' (T h), hT h,
    hu.comp_tendsto hs, ht.comp_tendsto hs] with x h1 h2 h3 h4
  dsimp only [Function.comp_apply] at h3 h4
  change h (x+a) = (Real.sqrt (thetaCuspFullSource (x+a) ^ (-q)) : ℂ)⁻¹ * g (x+a) at h3
  change g (x+a) = f ((x+a) + -a) at h4
  rw [h1, h2, h3, h4]
  simp only [add_neg_cancel_right]
  unfold thetaTranslationMultiplier
  push_cast
  ring

/-- Every bounded literal translation forces a bound on the actual density ratio. -/
theorem thetaTranslationDensityRatio_bddAbove_of_operator (q q' a : ℝ)
    (T : Lp ℂ 2 (thetaPowerWeightedMeasure q) →L[ℂ]
      Lp ℂ 2 (thetaPowerWeightedMeasure q')) (hT : IsThetaWeightedTranslation q q' a T) :
    BddAbove (range (thetaTranslationDensityRatio q q' a)) := by
  refine ⟨‖T‖ ^ 2, ?_⟩
  rintro _ ⟨y, rfl⟩
  have h := norm_symbol_le_of_ae_mul_continuous
    (continuous_thetaTranslationMultiplier q q' a) (thetaTranslationConjugate_coe q q' a T hT)
    (y-a)
  rw [norm_thetaTranslationConjugate] at h
  have hsq : ‖thetaTranslationMultiplier q q' a (y-a)‖ ^ 2 ≤ ‖T‖ ^ 2 := by
    nlinarith [norm_nonneg (thetaTranslationMultiplier q q' a (y-a)), norm_nonneg T]
  simpa only [norm_thetaTranslationMultiplier_sq, sub_add_cancel] using hsq

/-- The bounded literal translation, constructed from the actual ratio bound. -/
def thetaWeightedTranslation (q q' a : ℝ)
    (hb : BddAbove (range (thetaTranslationDensityRatio q q' a))) :
    Lp ℂ 2 (thetaPowerWeightedMeasure q) →L[ℂ] Lp ℂ 2 (thetaPowerWeightedMeasure q') :=
  let hC := thetaTranslationMultiplier_bounded q q' a hb
  let M := lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (continuous_thetaTranslationMultiplier q q' a).measurable hC.choose_spec.1 hC.choose_spec.2
  ((thetaPowerDensityUnitary q').symm.toContinuousLinearEquiv.toContinuousLinearMap.comp M).comp
    ((MellinL2.additiveTranslationUnitary a).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (thetaPowerDensityUnitary q).toContinuousLinearEquiv.toContinuousLinearMap)

theorem thetaWeightedTranslation_coe (q q' a : ℝ)
    (hb : BddAbove (range (thetaTranslationDensityRatio q q' a))) :
    IsThetaWeightedTranslation q q' a (thetaWeightedTranslation q q' a hb) := by
  intro f
  let hC := thetaTranslationMultiplier_bounded q q' a hb
  let M := lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (continuous_thetaTranslationMultiplier q q' a).measurable hC.choose_spec.1 hC.choose_spec.2
  let g := MellinL2.additiveTranslationUnitary a (thetaPowerDensityUnitary q f)
  have hm : (M g : ℝ → ℂ) =ᵐ[volume]
      fun x => thetaTranslationMultiplier q q' a x * g x :=
    lpBoundedMulCLM_coeFn _ _ _ g
  have hs := (MellinL2.realTranslation_measurePreserving a).quasiMeasurePreserving.tendsto_ae
  change ((thetaPowerDensityUnitary q').symm (M g) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [thetaPowerDensityUnitary_symm_coe q' (M g), hm,
    thetaLebesgueTranslation_coe a (thetaPowerDensityUnitary q f),
    (thetaPowerDensityUnitary_coe q f).comp_tendsto hs] with x h1 h2 h3 h4
  dsimp only [Function.comp_apply] at h4
  change thetaPowerDensityUnitary q f (x+a) =
    (Real.sqrt (thetaCuspFullSource (x+a) ^ (-q)) : ℂ) * f (x+a) at h4
  rw [h1, h2]
  change _ * (thetaTranslationMultiplier q q' a x *
    MellinL2.additiveTranslationUnitary a (thetaPowerDensityUnitary q f) x) = _
  rw [h3, h4]
  unfold thetaTranslationMultiplier
  push_cast
  field_simp [densityRoot_ne_zero q' x, densityRoot_ne_zero q (x+a)]

theorem exists_thetaWeightedTranslation_iff_bddAbove (q q' a : ℝ) :
    (∃ T, IsThetaWeightedTranslation q q' a T) ↔
      BddAbove (range (thetaTranslationDensityRatio q q' a)) := by
  constructor
  · rintro ⟨T, hT⟩
    exact thetaTranslationDensityRatio_bddAbove_of_operator q q' a T hT
  · intro hb
    exact ⟨thetaWeightedTranslation q q' a hb, thetaWeightedTranslation_coe q q' a hb⟩

/-- Exact operator-existence classification for every shift. -/
theorem exists_thetaWeightedTranslation_iff (q q' a : ℝ) (hq' : 0 < q') :
    (∃ T, IsThetaWeightedTranslation q q' a T) ↔
      (a = 0 ∧ q' ≤ q) ∨ (a ≠ 0 ∧ q' < q * Real.exp (-2 * |a|)) := by
  rw [exists_thetaWeightedTranslation_iff_bddAbove,
    thetaTranslationDensityRatio_bddAbove_iff q q' a hq']

theorem exists_thetaWeightedTranslation_iff_of_ne_zero (q q' a : ℝ)
    (hq' : 0 < q') (ha : a ≠ 0) :
    (∃ T, IsThetaWeightedTranslation q q' a T) ↔ q' < q * Real.exp (-2 * |a|) := by
  rw [exists_thetaWeightedTranslation_iff_bddAbove,
    thetaTranslationDensityRatio_bddAbove_iff_of_ne_zero q q' a hq' ha]

theorem exists_thetaWeightedTranslation_zero_iff (q q' : ℝ) :
    (∃ T, IsThetaWeightedTranslation q q' 0 T) ↔ q' ≤ q := by
  rw [exists_thetaWeightedTranslation_iff_bddAbove,
    thetaTranslationDensityRatio_bddAbove_zero_iff]

/-- The squared norm equals the literal density-ratio essential supremum. -/
theorem thetaWeightedTranslation_norm_sq_essSup (q q' a : ℝ)
    (T : Lp ℂ 2 (thetaPowerWeightedMeasure q) →L[ℂ]
      Lp ℂ 2 (thetaPowerWeightedMeasure q')) (hT : IsThetaWeightedTranslation q q' a T) :
    ENNReal.ofReal (‖T‖ ^ 2) =
      essSup (fun y => ENNReal.ofReal (thetaTranslationDensityRatio q q' a y)) volume := by
  have h := ofReal_norm_sq_eq_essSup_of_ae_mul_continuous
    (continuous_thetaTranslationMultiplier q q' a) (thetaTranslationConjugate_coe q q' a T hT)
  rw [norm_thetaTranslationConjugate] at h
  have hfun : (fun x => ENNReal.ofReal (‖thetaTranslationMultiplier q q' a x‖ ^ 2)) =
      (fun x => ENNReal.ofReal (thetaTranslationDensityRatio q q' a (x+a))) := by
    funext x
    rw [norm_thetaTranslationMultiplier_sq]
  rw [hfun, continuous_essSup_ofReal_eq_iSup
    (f := fun x => thetaTranslationDensityRatio q q' a (x+a))
    ((continuous_thetaTranslationDensityRatio q q' a).comp
      (continuous_id.add continuous_const))] at h
  rw [continuous_essSup_ofReal_eq_iSup (continuous_thetaTranslationDensityRatio q q' a)]
  refine h.trans ?_
  apply le_antisymm
  · exact iSup_le fun x => le_iSup (fun y =>
      ENNReal.ofReal (thetaTranslationDensityRatio q q' a y)) (x+a)
  · apply iSup_le
    intro y
    simpa only [sub_add_cancel] using le_iSup (fun x =>
      ENNReal.ofReal (thetaTranslationDensityRatio q q' a (x+a))) (y-a)

/-- The same exact norm law as a real-valued equality. -/
theorem thetaWeightedTranslation_norm_sq (q q' a : ℝ)
    (T : Lp ℂ 2 (thetaPowerWeightedMeasure q) →L[ℂ]
      Lp ℂ 2 (thetaPowerWeightedMeasure q')) (hT : IsThetaWeightedTranslation q q' a T) :
    ‖T‖ ^ 2 =
      (essSup (fun y => ENNReal.ofReal (thetaTranslationDensityRatio q q' a y)) volume).toReal := by
  have h := congrArg ENNReal.toReal (thetaWeightedTranslation_norm_sq_essSup q q' a T hT)
  simpa only [ENNReal.toReal_ofReal (sq_nonneg ‖T‖)] using h

theorem IsThetaWeightedTranslation_iff_weighted_ae (q q' a : ℝ)
    (T : Lp ℂ 2 (thetaPowerWeightedMeasure q) →L[ℂ]
      Lp ℂ 2 (thetaPowerWeightedMeasure q')) :
    IsThetaWeightedTranslation q q' a T ↔
      ∀ f, (T f : ℝ → ℂ) =ᵐ[thetaPowerWeightedMeasure q'] fun x => f (x+a) := by
  simp only [IsThetaWeightedTranslation, thetaPowerWeightedMeasure_ae_eq]

/-- The representative law determines the bounded operator uniquely. -/
theorem thetaWeightedTranslation_unique (q q' a : ℝ)
    (T S : Lp ℂ 2 (thetaPowerWeightedMeasure q) →L[ℂ]
      Lp ℂ 2 (thetaPowerWeightedMeasure q'))
    (hT : IsThetaWeightedTranslation q q' a T) (hS : IsThetaWeightedTranslation q q' a S) :
    T = S := by
  ext f
  exact (thetaPowerWeightedMeasure_ae_eq q').mpr ((hT f).trans (hS f).symm)

theorem not_exists_thetaWeightedTranslation_of_le (q q' a : ℝ)
    (hq' : 0 < q') (ha : a ≠ 0) (hb : q * Real.exp (-2 * |a|) ≤ q') :
    ¬ ∃ T, IsThetaWeightedTranslation q q' a T := by
  intro h
  have hs := (exists_thetaWeightedTranslation_iff_of_ne_zero q q' a hq' ha).mp h
  linarith

/-- The dangerous-tail equality is excluded. -/
theorem not_exists_thetaWeightedTranslation_boundary (q a : ℝ) (hq : 0 < q) (ha : a ≠ 0) :
    ¬ ∃ T, IsThetaWeightedTranslation q (q * Real.exp (-2 * |a|)) a T := by
  apply not_exists_thetaWeightedTranslation_of_le
  · positivity
  · exact ha
  · exact le_rfl

/-- No nonzero translation is bounded on a fixed positive-weight carrier. -/
theorem not_exists_thetaWeightedTranslation_fixed (q a : ℝ) (hq : 0 < q) (ha : a ≠ 0) :
    ¬ ∃ T, IsThetaWeightedTranslation q q a T := by
  intro h
  have hs := (exists_thetaWeightedTranslation_iff_of_ne_zero q q a hq ha).mp h
  have he : Real.exp (-2 * |a|) < 1 := Real.exp_lt_one_iff.mpr (by
    have := abs_pos.mpr ha
    linarith)
  nlinarith

theorem thetaTranslation_log_weightFactor (p : ℝ) (hp : 1 < p) :
    Real.exp (-2 * |Real.log p|) = (p ^ 2)⁻¹ := by
  rw [abs_of_pos (Real.log_pos hp), show -2 * Real.log p = -(2 * Real.log p) by ring,
    Real.exp_neg]
  have h : Real.exp (2 * Real.log p) = p ^ 2 := by
    simpa [Real.exp_log (by linarith : 0 < p)] using Real.exp_nat_mul (Real.log p) 2
  rw [h]

theorem exists_thetaWeightedTranslation_log_iff (q q' p : ℝ) (hq' : 0 < q') (hp : 1 < p) :
    (∃ T, IsThetaWeightedTranslation q q' (Real.log p) T) ↔ q' < q / p ^ 2 := by
  rw [exists_thetaWeightedTranslation_iff_of_ne_zero q q' (Real.log p) hq'
    (Real.log_pos hp).ne', thetaTranslation_log_weightFactor p hp, div_eq_mul_inv]

/-- Every prime translation loses the exact squared-prime factor with strict slack. -/
theorem exists_thetaWeightedTranslation_prime_iff (q q' : ℝ) (p : ℕ)
    (hq' : 0 < q') (hp : p.Prime) :
    (∃ T, IsThetaWeightedTranslation q q' (Real.log p) T) ↔ q' < q / (p : ℝ) ^ 2 :=
  exists_thetaWeightedTranslation_log_iff q q' p hq' (by exact_mod_cast hp.one_lt)

end RHTower
