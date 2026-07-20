import GaloisForLFunctions.RHTower.UniversalPhaseCoherenceEntropy
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Universal phase-coherence target measure

This file supplies the analytic core of the lower half of the universal
coherence-entropy law.  The first theorem is the sharp linear chord floor on
the standard fundamental interval.  Integrating its Gaussian majorant gives
an explicit inverse-square-root bound for the one-circle exponential moment.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- On the standard fundamental interval, the unit-circle chord from `1`
dominates four times the additive coordinate. -/
theorem four_mul_abs_le_norm_fourier_one_sub_one
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    4 * |x| ≤ ‖fourier 1 (x : UnitAddCircle) - 1‖ := by
  have hxabs : |Real.pi * x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    have habs : |x| ≤ 1 / 2 := (abs_le).2 hx
    nlinarith [Real.pi_pos]
  have hjordan := Real.mul_abs_le_abs_sin hxabs
  have hsin : 2 * |x| ≤ |Real.sin (Real.pi * x)| := by
    calc
      2 * |x| = 2 / Real.pi * |Real.pi * x| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        field_simp [Real.pi_ne_zero]
      _ ≤ |Real.sin (Real.pi * x)| := hjordan
  rw [fourier_coe_apply]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) * (x : ℂ) / (1 : ℝ) =
        Complex.I * (((2 * Real.pi * x : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith

/-- The Laplace transform of the squared chord distance from `1` under
normalized Haar measure on the additive unit circle. -/
def circleChordExponentialMoment (lam : ℝ) : ℝ :=
  ∫ z : UnitAddCircle, Real.exp (-lam * ‖fourier 1 z - 1‖ ^ 2)

/-- **One-circle Gaussian domination.**  The chord Laplace transform is at
most the full-line Gaussian integral with coefficient `16 * lam`. -/
theorem circleChordExponentialMoment_le_gaussian
    {lam : ℝ} (hlam : 0 < lam) :
    circleChordExponentialMoment lam ≤
      Real.sqrt (Real.pi / (16 * lam)) := by
  let f : ℝ → ℝ := fun x ↦
    Real.exp (-lam * ‖fourier 1 (x : UnitAddCircle) - 1‖ ^ 2)
  let g : ℝ → ℝ := fun x ↦ Real.exp (-(16 * lam) * x ^ 2)
  have hfcont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hgint : Integrable g := by
    dsimp only [g]
    exact integrable_exp_neg_mul_sq (by positivity)
  have hfint : IntegrableOn f (Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
    apply IntegrableOn.mono_set
      (ContinuousOn.integrableOn_compact isCompact_Icc hfcont.continuousOn)
    exact Ioc_subset_Icc_self
  have hgset : IntegrableOn g (Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    hgint.integrableOn
  have hfg : ∀ x ∈ Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), f x ≤ g x := by
    intro x hx
    have hchord := four_mul_abs_le_norm_fourier_one_sub_one
      (show x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) from
        Ioc_subset_Icc_self hx)
    have hsq : 16 * x ^ 2 ≤ ‖fourier 1 (x : UnitAddCircle) - 1‖ ^ 2 := by
      have hsquare := (sq_le_sq₀
        (mul_nonneg (by norm_num) (abs_nonneg x)) (norm_nonneg _)).2 hchord
      nlinarith [sq_abs x]
    dsimp only [f, g]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [circleChordExponentialMoment, ← UnitAddCircle.integral_preimage
    (-(1 / 2 : ℝ))]
  have hhalf : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [hhalf]
  change (∫ x in Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), f x) ≤ _
  have hset :
      ∫ x in Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), f x ≤
        ∫ x in Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), g x := by
    exact integral_mono_ae hfint hgset
      (ae_restrict_iff' measurableSet_Ioc |>.2 <|
        ae_of_all _ fun x hx ↦ hfg x hx)
  calc
    ∫ x in Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), f x ≤
        ∫ x in Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ), g x := hset
    _ ≤ ∫ x : ℝ, g x := by
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun _x ↦ (Real.exp_pos _).le) hgint
    _ = Real.sqrt (Real.pi / (16 * lam)) := by
      simpa only [g] using integral_gaussian (16 * lam)

/-- The pivot-coordinate shear which retains the pivot coordinate and replaces
every other coordinate by its difference from the pivot. -/
noncomputable def pivotDifferenceEquiv {d : Type*} [Fintype d] (k : d) :
    (d → UnitAddCircle) ≃+ (d → UnitAddCircle) := by
  classical
  exact
    { toFun := fun x j ↦ if j = k then x k else x j - x k
      invFun := fun y j ↦ if j = k then y k else y j + y k
      left_inv := fun x ↦ by
        funext j
        by_cases hj : j = k
        · subst j
          simp
        · simp [hj]
      right_inv := fun y ↦ by
        funext j
        by_cases hj : j = k
        · subst j
          simp
        · simp [hj]
      map_add' := fun x y ↦ by
        funext j
        by_cases hj : j = k
        · subst j
          simp
        · simp only [hj, ↓reduceIte, Pi.add_apply]
          abel }

theorem continuous_pivotDifferenceEquiv
    {d : Type*} [Fintype d] (k : d) :
    Continuous (pivotDifferenceEquiv k :
      (d → UnitAddCircle) → (d → UnitAddCircle)) := by
  classical
  change Continuous (fun x : d → UnitAddCircle ↦
    fun j ↦ if j = k then x k else x j - x k)
  apply continuous_pi
  intro j
  by_cases hj : j = k
  · subst j
    simp only [if_pos]
    exact continuous_apply k
  · simp only [hj, ↓reduceIte]
    fun_prop

theorem continuous_pivotDifferenceEquiv_symm
    {d : Type*} [Fintype d] (k : d) :
    Continuous ((pivotDifferenceEquiv k).symm :
      (d → UnitAddCircle) → (d → UnitAddCircle)) := by
  classical
  change Continuous (fun y : d → UnitAddCircle ↦
    fun j ↦ if j = k then y k else y j + y k)
  apply continuous_pi
  intro j
  by_cases hj : j = k
  · subst j
    simp only [if_pos]
    exact continuous_apply k
  · simp only [hj, ↓reduceIte]
    fun_prop

def measurablePivotDifferenceEquiv {d : Type*} [Fintype d] (k : d) :
    (d → UnitAddCircle) ≃ᵐ (d → UnitAddCircle) where
  toEquiv := pivotDifferenceEquiv k
  measurable_toFun := (continuous_pivotDifferenceEquiv k).measurable
  measurable_invFun := (continuous_pivotDifferenceEquiv_symm k).measurable

/-- The pivot shear preserves normalized Haar measure exactly. -/
theorem measurePreserving_pivotDifferenceEquiv
    {d : Type*} [Fintype d] (k : d) :
    MeasurePreserving (pivotDifferenceEquiv k :
      (d → UnitAddCircle) → (d → UnitAddCircle)) := by
  exact (pivotDifferenceEquiv k).toAddMonoidHom.measurePreserving
    (continuous_pivotDifferenceEquiv k) (pivotDifferenceEquiv k).surjective rfl

theorem norm_pivot_fourier_sub_one
    {d : Type*} [Fintype d] (k j : d) (hj : j ≠ k)
    (x : d → UnitAddCircle) :
    ‖fourier 1 ((pivotDifferenceEquiv k x) j) - 1‖ =
      ‖fourier 1 (x j) - fourier 1 (x k)‖ := by
  classical
  rw [show (pivotDifferenceEquiv k x) j = x j - x k by
    simp [pivotDifferenceEquiv, hj]]
  simp only [fourier_one]
  have hsub : x j - x k = x j + (-x k) := sub_eq_add_neg _ _
  rw [hsub, AddCircle.toCircle_add, AddCircle.toCircle_neg]
  change
    ‖(AddCircle.toCircle (x j) : ℂ) * (AddCircle.toCircle (x k) : ℂ)⁻¹ - 1‖ =
      ‖(AddCircle.toCircle (x j) - AddCircle.toCircle (x k) : ℂ)‖
  have hk : ‖(AddCircle.toCircle (x k) : ℂ)⁻¹‖ = 1 := by
    rw [norm_inv, Circle.norm_coe, inv_one]
  calc
    ‖(AddCircle.toCircle (x j) : ℂ) * (AddCircle.toCircle (x k) : ℂ)⁻¹ - 1‖ =
        ‖((AddCircle.toCircle (x j) : ℂ) - AddCircle.toCircle (x k)) *
          (AddCircle.toCircle (x k) : ℂ)⁻¹‖ := by
            congr 1
            have hk0 : (AddCircle.toCircle (x k) : ℂ) ≠ 0 := by
              exact Circle.coe_ne_zero _
            field_simp
    _ = ‖(AddCircle.toCircle (x j) : ℂ) - AddCircle.toCircle (x k)‖ := by
      rw [norm_mul, hk, mul_one]

/-- Total squared phase distance from a chosen pivot. -/
def torusPivotPhaseEnergy {d : Type*} [Fintype d]
    (k : d) (x : d → UnitAddCircle) : ℝ :=
  ∑ j, ‖fourier 1 (x j) - fourier 1 (x k)‖ ^ 2

theorem continuous_torusPivotPhaseEnergy
    {d : Type*} [Fintype d] (k : d) :
    Continuous (torusPivotPhaseEnergy k) := by
  change Continuous (fun x : d → UnitAddCircle ↦
    ∑ j, ‖fourier 1 (x j) - fourier 1 (x k)‖ ^ 2)
  fun_prop

/-- The independent-coordinate form of pivot energy after the pivot shear. -/
noncomputable def torusIndependentPivotPhaseEnergy
    {d : Type*} [Fintype d] (k : d) (y : d → UnitAddCircle) : ℝ := by
  classical
  exact ∑ j, if j = k then 0 else ‖fourier 1 (y j) - 1‖ ^ 2

theorem torusIndependentPivotPhaseEnergy_pivotDifferenceEquiv
    {d : Type*} [Fintype d] (k : d) (x : d → UnitAddCircle) :
    torusIndependentPivotPhaseEnergy k (pivotDifferenceEquiv k x) =
      torusPivotPhaseEnergy k x := by
  classical
  rw [torusIndependentPivotPhaseEnergy, torusPivotPhaseEnergy]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjk : j = k
  · subst j
    simp
  · simp only [hjk, ↓reduceIte]
    rw [norm_pivot_fourier_sub_one k j hjk x]

/-- Exact product factorization of the sheared pivot-energy Laplace
transform.  One coordinate is free, hence the exponent `card d - 1`. -/
theorem integral_exp_neg_torusIndependentPivotPhaseEnergy
    {d : Type*} [Fintype d] [Nonempty d] (k : d) (lam : ℝ) :
    (∫ y : d → UnitAddCircle,
      Real.exp (-lam * torusIndependentPivotPhaseEnergy k y)) =
        circleChordExponentialMoment lam ^ (Fintype.card d - 1) := by
  classical
  have hfactor (y : d → UnitAddCircle) :
      Real.exp (-lam * torusIndependentPivotPhaseEnergy k y) =
        ∏ j, if j = k then 1 else
          Real.exp (-lam * ‖fourier 1 (y j) - 1‖ ^ 2) := by
    rw [torusIndependentPivotPhaseEnergy]
    calc
      Real.exp (-lam * ∑ j, if j = k then 0 else
          ‖fourier 1 (y j) - 1‖ ^ 2) =
          Real.exp (∑ j, -lam * (if j = k then 0 else
            ‖fourier 1 (y j) - 1‖ ^ 2)) := by
              congr 1
              rw [← Finset.mul_sum]
      _ = ∏ j, Real.exp (-lam * (if j = k then 0 else
            ‖fourier 1 (y j) - 1‖ ^ 2)) := Real.exp_sum _ _
      _ = ∏ j, if j = k then 1 else
          Real.exp (-lam * ‖fourier 1 (y j) - 1‖ ^ 2) := by
            apply Finset.prod_congr rfl
            intro j hj
            by_cases hjk : j = k <;> simp [hjk]
  rw [integral_congr_ae (ae_of_all _ hfactor)]
  change (∫ y : d → UnitAddCircle,
    ∏ j, (fun z : UnitAddCircle ↦ if j = k then 1 else
      Real.exp (-lam * ‖fourier 1 z - 1‖ ^ 2)) (y j)) = _
  have hprod := integral_fintype_prod_volume_eq_prod
    (fun j : d ↦ fun z : UnitAddCircle ↦ if j = k then 1 else
      Real.exp (-lam * ‖fourier 1 z - 1‖ ^ 2))
  rw [hprod]
  have hcoordinate (j : d) :
      (∫ z : UnitAddCircle,
        if j = k then 1 else Real.exp (-lam * ‖fourier 1 z - 1‖ ^ 2)) =
        if j = k then 1 else circleChordExponentialMoment lam := by
    by_cases hjk : j = k
    · subst j
      simp only [if_pos]
      rw [integral_const]
      rw [measureReal_def, UnitAddCircle.measure_univ]
      norm_num
    · simp [hjk, circleChordExponentialMoment]
  simp_rw [hcoordinate]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
  simp only [if_pos, mul_one]
  have hprodErase :
      (∏ j ∈ Finset.univ.erase k,
        if j = k then 1 else circleChordExponentialMoment lam) =
        ∏ _j ∈ Finset.univ.erase k, circleChordExponentialMoment lam := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj)]
  rw [hprodErase, Finset.prod_const]
  congr 1
  rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ]

/-- The unsheared pivot energy has the same exact product Laplace transform. -/
theorem integral_exp_neg_torusPivotPhaseEnergy
    {d : Type*} [Fintype d] [Nonempty d] (k : d) (lam : ℝ) :
    (∫ x : d → UnitAddCircle,
      Real.exp (-lam * torusPivotPhaseEnergy k x)) =
        circleChordExponentialMoment lam ^ (Fintype.card d - 1) := by
  have hmp := measurePreserving_pivotDifferenceEquiv k
  have hmp' : MeasurePreserving (measurablePivotDifferenceEquiv k) := hmp
  have hchange := hmp'.integral_comp'
    (fun y : d → UnitAddCircle ↦
      Real.exp (-lam * torusIndependentPivotPhaseEnergy k y))
  change (∫ x : d → UnitAddCircle,
    Real.exp (-lam * torusIndependentPivotPhaseEnergy k
      (pivotDifferenceEquiv k x))) = _ at hchange
  have hidentify :
      (∫ x : d → UnitAddCircle,
        Real.exp (-lam * torusIndependentPivotPhaseEnergy k
          (pivotDifferenceEquiv k x))) =
        ∫ x : d → UnitAddCircle,
          Real.exp (-lam * torusPivotPhaseEnergy k x) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ congrArg (fun u : ℝ ↦ Real.exp (-lam * u))
      (torusIndependentPivotPhaseEnergy_pivotDifferenceEquiv k x)
  calc
    (∫ x : d → UnitAddCircle,
      Real.exp (-lam * torusPivotPhaseEnergy k x)) =
        ∫ x : d → UnitAddCircle,
          Real.exp (-lam * torusIndependentPivotPhaseEnergy k
            (pivotDifferenceEquiv k x)) := hidentify.symm
    _ = ∫ y : d → UnitAddCircle,
      Real.exp (-lam * torusIndependentPivotPhaseEnergy k y) := hchange
    _ = circleChordExponentialMoment lam ^ (Fintype.card d - 1) :=
      integral_exp_neg_torusIndependentPivotPhaseEnergy k lam

def torusPivotEnergyTarget {d : Type*} [Fintype d]
    (k : d) (η : ℝ) : Set (d → UnitAddCircle) :=
  {x | torusPivotPhaseEnergy k x ≤ 4 * η * (Fintype.card d : ℝ)}

/-- Chernoff bound for one pivot-energy target. -/
theorem measureReal_torusPivotEnergyTarget_le
    {d : Type*} [Fintype d] [Nonempty d]
    (k : d) {η lam : ℝ} (hlam : 0 < lam) :
    volume.real (torusPivotEnergyTarget k η) ≤
      Real.exp (lam * (4 * η * (Fintype.card d : ℝ))) *
        circleChordExponentialMoment lam ^ (Fintype.card d - 1) := by
  let D : ℝ := Fintype.card d
  let f : (d → UnitAddCircle) → ℝ := fun x ↦
    Real.exp (-lam * torusPivotPhaseEnergy k x)
  let eps : ℝ := Real.exp (-lam * (4 * η * D))
  have hfcont : Continuous f := by
    dsimp only [f]
    exact Real.continuous_exp.comp
      (continuous_const.mul (continuous_torusPivotPhaseEnergy k))
  have hfint : Integrable f := by
    rw [← integrableOn_univ]
    exact ContinuousOn.integrableOn_compact isCompact_univ hfcont.continuousOn
  have hfnonneg : ∀ᵐ _x ∂(volume : Measure (d → UnitAddCircle)), 0 ≤ f _x :=
    Filter.Eventually.of_forall fun _x ↦ (Real.exp_pos _).le
  have hsubset : torusPivotEnergyTarget k η ⊆ {x | eps ≤ f x} := by
    intro x hx
    rw [torusPivotEnergyTarget, Set.mem_setOf_eq] at hx
    rw [Set.mem_setOf_eq]
    dsimp only [eps, f, D]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hfnonneg hfint eps
  have hmono : volume.real (torusPivotEnergyTarget k η) ≤
      volume.real {x | eps ≤ f x} := measureReal_mono hsubset
  have hmul : eps * volume.real (torusPivotEnergyTarget k η) ≤
      ∫ x, f x :=
    (mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le).trans hmarkov
  have hmul' : volume.real (torusPivotEnergyTarget k η) * eps ≤
      ∫ x, f x := by
    rw [mul_comm]
    exact hmul
  have hdiv : volume.real (torusPivotEnergyTarget k η) ≤
      (∫ x, f x) / eps := (le_div_iff₀ (Real.exp_pos _)).2 hmul'
  calc
    volume.real (torusPivotEnergyTarget k η) ≤
        (∫ x, f x) / eps := hdiv
    _ = Real.exp (lam * (4 * η * D)) *
        circleChordExponentialMoment lam ^ (Fintype.card d - 1) := by
      rw [show (∫ x, f x) =
          circleChordExponentialMoment lam ^ (Fintype.card d - 1) by
        simpa only [f] using integral_exp_neg_torusPivotPhaseEnergy k lam]
      dsimp only [eps]
      rw [show -lam * (4 * η * D) = -(lam * (4 * η * D)) by ring,
        Real.exp_neg, div_eq_mul_inv, inv_inv, mul_comm]
    _ = Real.exp (lam * (4 * η * (Fintype.card d : ℝ))) *
        circleChordExponentialMoment lam ^ (Fintype.card d - 1) := by rfl

/-- The normalized Haar target of phase packets with coherence at least
`1 - η`. -/
def torusCoherenceTarget {d : Type*} [Fintype d] [Nonempty d]
    (η : ℝ) : Set (d → UnitAddCircle) :=
  {x | 1 - η ≤ ‖equalPhaseAmplitude (fun j ↦ fourier 1 (x j))‖}

theorem continuous_torusCoherenceAmplitude
    {d : Type*} [Fintype d] [Nonempty d] :
    Continuous (fun x : d → UnitAddCircle ↦
      ‖equalPhaseAmplitude (fun j ↦ fourier 1 (x j))‖) := by
  unfold equalPhaseAmplitude GaloisForLFunctions.HilbertMetric.hilbertCentroid
  fun_prop

theorem measurableSet_torusCoherenceTarget
    {d : Type*} [Fintype d] [Nonempty d] (η : ℝ) :
    MeasurableSet (torusCoherenceTarget (d := d) η) := by
  rw [torusCoherenceTarget]
  exact measurableSet_le measurable_const
    (continuous_torusCoherenceAmplitude (d := d)).measurable

/-- The finite phase torus carries normalized Haar probability. -/
theorem measureReal_torus_univ
    {d : Type*} [Fintype d] :
    volume.real (Set.univ : Set (d → UnitAddCircle)) = 1 := by
  rw [measureReal_def]
  rw [show (volume : Measure (d → UnitAddCircle)) =
      Measure.pi (fun _ : d ↦ (volume : Measure UnitAddCircle)) by rfl]
  rw [Measure.pi_univ]
  simp only [UnitAddCircle.measure_univ, Finset.prod_const_one, ENNReal.toReal_one]

theorem torusCoherenceTarget_subset_iUnion_pivotEnergyTarget
    {d : Type*} [Fintype d] [Nonempty d]
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    torusCoherenceTarget (d := d) η ⊆
      ⋃ k, torusPivotEnergyTarget k η := by
  intro x hx
  rw [torusCoherenceTarget, Set.mem_setOf_eq] at hx
  have hphase : ∀ j, ‖fourier 1 (x j)‖ = 1 := by
    intro j
    rw [fourier_apply, Circle.norm_coe]
  obtain ⟨k, hk⟩ := exists_phasePivot_sum_norm_sub_sq_le
    (fun j ↦ fourier 1 (x j)) hphase hη0 hη1 hx
  rw [Set.mem_iUnion]
  refine ⟨k, ?_⟩
  rw [torusPivotEnergyTarget, Set.mem_setOf_eq, torusPivotPhaseEnergy]
  exact hk

/-- **Finite coherence-target entropy bound.**  The Haar volume of the
`1 - η` target is bounded by one pivot union and `card d - 1` independent
one-circle chord moments. -/
theorem measureReal_torusCoherenceTarget_le
    {d : Type*} [Fintype d] [Nonempty d]
    {η lam : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hlam : 0 < lam) :
    volume.real (torusCoherenceTarget (d := d) η) ≤
      (Fintype.card d : ℝ) *
        Real.exp (lam * (4 * η * (Fintype.card d : ℝ))) *
          circleChordExponentialMoment lam ^ (Fintype.card d - 1) := by
  let B : ℝ := Real.exp (lam * (4 * η * (Fintype.card d : ℝ))) *
    circleChordExponentialMoment lam ^ (Fintype.card d - 1)
  calc
    volume.real (torusCoherenceTarget (d := d) η) ≤
        volume.real (⋃ k, torusPivotEnergyTarget k η) :=
      measureReal_mono
        (torusCoherenceTarget_subset_iUnion_pivotEnergyTarget hη0 hη1)
    _ ≤ ∑ k : d, volume.real (torusPivotEnergyTarget k η) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : d, B := by
      apply Finset.sum_le_sum
      intro k hk
      exact measureReal_torusPivotEnergyTarget_le k hlam
    _ = (Fintype.card d : ℝ) * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card d : ℝ) *
        Real.exp (lam * (4 * η * (Fintype.card d : ℝ))) *
          circleChordExponentialMoment lam ^ (Fintype.card d - 1) := by
      dsimp only [B]
      ring

theorem circleChordExponentialMoment_nonneg (lam : ℝ) :
    0 ≤ circleChordExponentialMoment lam := by
  rw [circleChordExponentialMoment]
  exact integral_nonneg fun _z ↦ (Real.exp_pos _).le

/-- Gaussian form of the finite coherence-target entropy bound. -/
theorem measureReal_torusCoherenceTarget_le_gaussian
    {d : Type*} [Fintype d] [Nonempty d]
    {η lam : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hlam : 0 < lam) :
    volume.real (torusCoherenceTarget (d := d) η) ≤
      (Fintype.card d : ℝ) *
        Real.exp (lam * (4 * η * (Fintype.card d : ℝ))) *
          Real.sqrt (Real.pi / (16 * lam)) ^ (Fintype.card d - 1) := by
  have htarget := measureReal_torusCoherenceTarget_le
    (d := d) (η := η) (lam := lam) hη0 hη1 hlam
  have hmoment := circleChordExponentialMoment_le_gaussian hlam
  have hpow :
      circleChordExponentialMoment lam ^ (Fintype.card d - 1) ≤
        Real.sqrt (Real.pi / (16 * lam)) ^ (Fintype.card d - 1) :=
    pow_le_pow_left₀ (circleChordExponentialMoment_nonneg lam) hmoment _
  calc
    volume.real (torusCoherenceTarget (d := d) η) ≤
        (Fintype.card d : ℝ) *
          Real.exp (lam * (4 * η * (Fintype.card d : ℝ))) *
            circleChordExponentialMoment lam ^ (Fintype.card d - 1) := htarget
    _ ≤ (Fintype.card d : ℝ) *
        Real.exp (lam * (4 * η * (Fintype.card d : ℝ))) *
          Real.sqrt (Real.pi / (16 * lam)) ^ (Fintype.card d - 1) := by
      exact mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)

/-- **Optimized target-volume law.**  At the Chernoff scale
`lam = 1/(8η)`, a `1-η` coherent target in dimension `d` has Haar volume
at most `d exp(d/2) (sqrt(πη/2))^(d-1)`. -/
theorem measureReal_torusCoherenceTarget_le_optimized
    {d : Type*} [Fintype d] [Nonempty d]
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    volume.real (torusCoherenceTarget (d := d) η) ≤
      (Fintype.card d : ℝ) * Real.exp ((Fintype.card d : ℝ) / 2) *
        Real.sqrt (Real.pi * η / 2) ^ (Fintype.card d - 1) := by
  have hlam : 0 < 1 / (8 * η) := by positivity
  have htarget := measureReal_torusCoherenceTarget_le_gaussian
    (d := d) hη0.le hη1 hlam
  have hexponent :
      (1 / (8 * η)) * (4 * η * (Fintype.card d : ℝ)) =
        (Fintype.card d : ℝ) / 2 := by
    field_simp [hη0.ne']
    ring
  have hgaussian :
      Real.pi / (16 * (1 / (8 * η))) = Real.pi * η / 2 := by
    field_simp [hη0.ne']
    ring
  rw [hexponent, hgaussian] at htarget
  exact htarget

end RHTower
