import Mathlib

/-!
# Gaussian determinant tube upper bound

The standard Gaussian density is globally bounded by its value at the origin.  In finite
dimensions this gives domination by peak density times Lebesgue measure.  Pulling a coordinate
box back through an invertible square linear observer then costs exactly the reciprocal absolute
determinant.  The resulting theorem is uniform in the box centre and makes the singular branch
explicit instead of hiding it in an invertibility premise.

After quotienting a rectangular observer by its kernel, the determinant in this module is the
pseudodeterminant of the active observer.  Thus this is the reusable probability/change-of-
variables layer needed by return-excised observer-Jacobian arguments.  It does not assert the
model-specific lower tail for that active determinant.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Peak of the one-dimensional standard Gaussian density. -/
def gaussianDensityPeak : ℝ := (Real.sqrt (2 * Real.pi))⁻¹

theorem gaussianDensityPeak_pos : 0 < gaussianDensityPeak := by
  unfold gaussianDensityPeak
  positivity

/-- The standard Gaussian density is globally bounded by its value at the origin. -/
theorem gaussianPDF_le_densityPeak (x : ℝ) :
    gaussianPDF 0 1 x ≤ ENNReal.ofReal gaussianDensityPeak := by
  rw [gaussianPDF, gaussianDensityPeak, gaussianPDFReal]
  apply ENNReal.ofReal_le_ofReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x] : -x ^ 2 / 2 ≤ 0))
    (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi)))

/-- One-dimensional standard Gaussian measure is dominated globally by peak density times
Lebesgue measure. -/
theorem gaussianReal_le_densityPeak_smul_volume :
    gaussianReal 0 1 ≤
      ENNReal.ofReal gaussianDensityPeak • (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num), ← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall gaussianPDF_le_densityPeak)

/-- Peak density as an extended nonnegative real. -/
def gaussianDensityPeakENN : ℝ≥0∞ := ENNReal.ofReal gaussianDensityPeak

/-- In every finite dimension, product standard Gaussian measure is globally dominated by
`gaussianDensityPeak ^ dimension` times Lebesgue measure. -/
theorem pi_gaussian_le_densityPeak_pow_smul_volume
    (ι : Type) [Fintype ι] :
    Measure.pi (fun _ : ι => gaussianReal 0 1) ≤
      gaussianDensityPeakENN ^ Fintype.card ι •
        (volume : Measure (ι → ℝ)) := by
  classical
  let P : ∀ (α : Type) [Fintype α], Prop := fun α _ =>
    Measure.pi (fun _ : α => gaussianReal 0 1) ≤
      gaussianDensityPeakENN ^ Fintype.card α •
        (volume : Measure (α → ℝ))
  apply Fintype.induction_empty_option (P := P)
  · intro α β _ e h
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let E := MeasurableEquiv.piCongrLeft (fun _ : β => ℝ) e
    have hm := Measure.map_mono h E.measurable
    rw [Measure.pi_map_piCongrLeft e
      (fun _ : β => gaussianReal 0 1)] at hm
    have hEvol : Measure.map E (volume : Measure (α → ℝ)) =
        (volume : Measure (β → ℝ)) :=
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : β => ℝ) e).map_eq
    rw [Measure.map_smul, hEvol] at hm
    simpa [Fintype.card_congr e] using hm
  · change Measure.pi (fun _ : PEmpty => gaussianReal 0 1) ≤
      gaussianDensityPeakENN ^ Fintype.card PEmpty •
        (volume : Measure (PEmpty → ℝ))
    rw [Measure.pi_of_empty
        (fun _ : PEmpty => gaussianReal 0 1) isEmptyElim,
      MeasureTheory.Measure.volume_pi_eq_dirac
        (α := fun _ : PEmpty => ℝ) isEmptyElim]
    simp
  · intro α _ h
    let G : Measure (α → ℝ) := Measure.pi fun _ : α => gaussianReal 0 1
    let V : Measure (α → ℝ) := volume
    let e := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option α => ℝ)).symm
    have hp := Measure.prod_mono h gaussianReal_le_densityPeak_smul_volume
    have hm := Measure.map_mono hp e.measurable
    rw [Measure.pi_map_piOptionEquivProd
      (fun _ : Option α => gaussianReal 0 1)] at hm
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      Measure.map_smul] at hm
    have hvmap : (V.prod (volume : Measure ℝ)).map e =
        (volume : Measure (Option α → ℝ)) := by
      simpa [V, ← volume_pi] using
        (Measure.pi_map_piOptionEquivProd
          (fun _ : Option α => (volume : Measure ℝ)))
    rw [hvmap] at hm
    simpa [P, G, V, Fintype.card_option, pow_succ, mul_comm,
      gaussianDensityPeakENN] using hm

/-- Pullback of a coordinate box through a square real linear observer. -/
def gaussianLinearBoxTube {m : ℕ}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (center : Fin m → ℝ) (radius : ℝ) : Set (Fin m → ℝ) :=
  A ⁻¹' (Set.univ.pi fun i =>
    Set.Icc (center i - radius) (center i + radius))

/-- Invertible active-observer branch.  Gaussian tube mass is bounded by peak density, reciprocal
absolute determinant, and exact box volume. -/
theorem measure_gaussianLinearBoxTube_le_of_det_ne_zero
    {m : ℕ} (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (hA : LinearMap.det A ≠ 0) (center : Fin m → ℝ) (radius : ℝ) :
    (Measure.pi fun _ : Fin m => gaussianReal 0 1)
        (gaussianLinearBoxTube A center radius) ≤
      gaussianDensityPeakENN ^ m *
        ENNReal.ofReal |(LinearMap.det A)⁻¹| *
          ENNReal.ofReal (2 * radius) ^ m := by
  have hdom := pi_gaussian_le_densityPeak_pow_smul_volume (Fin m)
  have hpre := Measure.le_iff'.mp hdom
    (gaussianLinearBoxTube A center radius)
  rw [Measure.smul_apply, smul_eq_mul] at hpre
  rw [gaussianLinearBoxTube,
    MeasureTheory.Measure.addHaar_preimage_linearMap
      (volume : Measure (Fin m → ℝ)) hA] at hpre
  have hvol : (volume : Measure (Fin m → ℝ))
      (Set.univ.pi fun i =>
        Set.Icc (center i - radius) (center i + radius)) =
      ENNReal.ofReal (2 * radius) ^ m := by
    rw [volume_pi_pi]
    simp only [Real.volume_Icc]
    simp_rw [show ∀ i : Fin m,
      center i + radius - (center i - radius) = 2 * radius by
        intro i
        ring]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hvol] at hpre
  simpa [gaussianLinearBoxTube, Fintype.card_fin, mul_assoc] using hpre

/-- Absolute determinant of the active square observer.  When this square map is obtained by
quotienting a rectangular observer by its kernel, this is its pseudodeterminant. -/
def activeObserverPseudodeterminant {m : ℕ}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) : ℝ :=
  |LinearMap.det A|

/-- Total Gaussian tube budget, including the singular active-observer branch. -/
def gaussianLinearBoxTubeBudget {m : ℕ}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (radius : ℝ) : ℝ≥0∞ :=
  if activeObserverPseudodeterminant A = 0 then 1
  else gaussianDensityPeakENN ^ m *
    ENNReal.ofReal |(LinearMap.det A)⁻¹| *
      ENNReal.ofReal (2 * radius) ^ m

/-- **Unconditional Gaussian active-observer law.**  Invertible active quotients pay the exact
reciprocal pseudodeterminant.  Singular quotients are exposed by the sharp probability cap `1`;
there is no hidden nonsingularity hypothesis. -/
theorem measure_gaussianLinearBoxTube_le
    {m : ℕ} (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (center : Fin m → ℝ) (radius : ℝ) :
    (Measure.pi fun _ : Fin m => gaussianReal 0 1)
        (gaussianLinearBoxTube A center radius) ≤
      gaussianLinearBoxTubeBudget A radius := by
  by_cases hA : LinearMap.det A = 0
  · rw [gaussianLinearBoxTubeBudget, activeObserverPseudodeterminant,
      if_pos (abs_eq_zero.mpr hA)]
    calc
      (Measure.pi fun _ : Fin m => gaussianReal 0 1)
          (gaussianLinearBoxTube A center radius) ≤
          (Measure.pi fun _ : Fin m => gaussianReal 0 1) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  · rw [gaussianLinearBoxTubeBudget, activeObserverPseudodeterminant,
      if_neg (abs_ne_zero.mpr hA)]
    exact measure_gaussianLinearBoxTube_le_of_det_ne_zero
      A hA center radius

/-- Affine observer tube after splitting Gaussian coefficients into inactive and active blocks.
The inactive block may shift the centre arbitrarily through `B`; the active square block is `A`. -/
def gaussianConditionedLinearBoxTube {m : ℕ} {ι : Type*}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (B : (ι → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (center : Fin m → ℝ) (radius : ℝ) :
    Set ((ι → ℝ) × (Fin m → ℝ)) :=
  {p | A p.2 + B p.1 ∈
    Set.univ.pi fun i =>
      Set.Icc (center i - radius) (center i + radius)}

theorem measurableSet_gaussianConditionedLinearBoxTube {m : ℕ} {ι : Type*} [Fintype ι]
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (B : (ι → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (center : Fin m → ℝ) (radius : ℝ) :
    MeasurableSet (gaussianConditionedLinearBoxTube A B center radius) := by
  apply (MeasurableSet.univ_pi fun i => measurableSet_Icc).preimage
  exact ((A.continuous_of_finiteDimensional.measurable.comp measurable_snd).add
    (B.continuous_of_finiteDimensional.measurable.comp measurable_fst))

/-- Conditioning on inactive coefficients only translates the active Gaussian box. -/
theorem section_gaussianConditionedLinearBoxTube {m : ℕ} {ι : Type*} [Fintype ι]
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (B : (ι → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (center : Fin m → ℝ) (radius : ℝ) (y : ι → ℝ) :
    Prod.mk y ⁻¹' gaussianConditionedLinearBoxTube A B center radius =
      gaussianLinearBoxTube A (center - B y) radius := by
  ext x
  simp only [gaussianConditionedLinearBoxTube, mem_setOf_eq, mem_preimage,
    gaussianLinearBoxTube, Set.mem_pi, Set.mem_univ, forall_true_left,
    Pi.sub_apply, Pi.add_apply]
  constructor <;> intro h i
  · have hi := h i
    constructor <;> linarith [hi.1, hi.2]
  · have hi := h i
    constructor <;> linarith [hi.1, hi.2]

/-- **Inactive-drift survival law.**  The active-minor determinant bound survives integration over
every inactive Gaussian coefficient.  No union factor and no bound on the inactive drift appear. -/
theorem measure_gaussianConditionedLinearBoxTube_le {m : ℕ} {ι : Type*} [Fintype ι]
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (B : (ι → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (center : Fin m → ℝ) (radius : ℝ) :
    ((Measure.pi fun _ : ι => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin m => gaussianReal 0 1))
        (gaussianConditionedLinearBoxTube A B center radius) ≤
      gaussianLinearBoxTubeBudget A radius := by
  rw [Measure.prod_apply
    (measurableSet_gaussianConditionedLinearBoxTube A B center radius)]
  calc
    (∫⁻ y, (Measure.pi fun _ : Fin m => gaussianReal 0 1)
      (Prod.mk y ⁻¹' gaussianConditionedLinearBoxTube A B center radius)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤
        ∫⁻ _y, gaussianLinearBoxTubeBudget A radius
          ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
      apply lintegral_mono
      intro y
      change (Measure.pi fun _ : Fin m => gaussianReal 0 1)
        (Prod.mk y ⁻¹' gaussianConditionedLinearBoxTube A B center radius) ≤ _
      rw [section_gaussianConditionedLinearBoxTube]
      exact measure_gaussianLinearBoxTube_le A (center - B y) radius
    _ = gaussianLinearBoxTubeBudget A radius := by simp

/-- Sup-norm tube for the same conditioned affine observer. -/
def gaussianConditionedObserverNormTube {m : ℕ} {ι : Type*}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (B : (ι → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (center : Fin m → ℝ) (radius : ℝ) :
    Set ((ι → ℝ) × (Fin m → ℝ)) :=
  {p | ‖A p.2 + B p.1 - center‖ ≤ radius}

theorem gaussianConditionedObserverNormTube_subset_box {m : ℕ} {ι : Type*}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (B : (ι → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (center : Fin m → ℝ) (radius : ℝ) :
    gaussianConditionedObserverNormTube A B center radius ⊆
      gaussianConditionedLinearBoxTube A B center radius := by
  intro p hp i _
  have hcoord : ‖(A p.2 + B p.1 - center) i‖ ≤
      ‖A p.2 + B p.1 - center‖ := norm_le_pi_norm _ i
  have hi : |(A p.2 + B p.1) i - center i| ≤ radius := by
    rw [← Real.norm_eq_abs]
    exact hcoord.trans hp
  change center i - radius ≤ (A p.2 + B p.1) i ∧
    (A p.2 + B p.1) i ≤ center i + radius
  have habs := abs_le.mp hi
  constructor <;> linarith [habs.1, habs.2]

/-- Approximate observer tubes inherit the inactive-drift determinant budget. -/
theorem measure_gaussianConditionedObserverNormTube_le {m : ℕ} {ι : Type*} [Fintype ι]
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (B : (ι → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (center : Fin m → ℝ) (radius : ℝ) :
    ((Measure.pi fun _ : ι => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin m => gaussianReal 0 1))
        (gaussianConditionedObserverNormTube A B center radius) ≤
      gaussianLinearBoxTubeBudget A radius :=
  (measure_mono (gaussianConditionedObserverNormTube_subset_box
    A B center radius)).trans
      (measure_gaussianConditionedLinearBoxTube_le A B center radius)

end GaloisForLFunctions.HTGeometry
