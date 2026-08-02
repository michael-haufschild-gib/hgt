import GaloisForLFunctions.RHTower.BurnolSoninEvaluationAperture
import GaloisForLFunctions.RHTower.SoninEvenCarrier

/-!
# The cosine transform on the even carrier and its aperture bound

Burnol's Sonine space sits inside `L²(0,∞)`, which is the even carrier of `L²(ℝ)` after the
half-line identification `f ↦ f|_{(0,∞)}`.  This module realizes that identification, computes its
exact norm factor `1/sqrt 2`, and builds the cosine transform as the ambient Fourier unitary
restricted to the even carrier.

The cosine transform is a genuine unitary involution of the even carrier: `F` preserves evenness in
both directions, and `F² = reflection` is the identity there.  Transporting the ambient off-axis
aperture estimate through the half-line identification gives the same aperture exponent
`A^(1/2 - Re w)` for even carriers with constant aperture head.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ## The `L²` norm of an ambient vector -/

theorem norm_sq_lp_eq_integral_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ a, ‖f a‖ ^ 2 ∂μ := by
  have h := norm_sq_toLp_eq_integral_norm_sq (Lp.memLp f)
  rwa [Lp.toLp_coeFn f (Lp.memLp f)] at h

/-! ## The half-line restriction of an even carrier -/

theorem memLp_restrict_Ioi (f : SoninL2) :
    MemLp (f : ℝ → ℂ) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (Lp.memLp f).restrict _

/-- The half-line vector of an ambient `L²(ℝ)` carrier. -/
def soninHalfLine (f : SoninL2) : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (memLp_restrict_Ioi f).toLp _

theorem coeFn_soninHalfLine (f : SoninL2) :
    (soninHalfLine f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] (f : ℝ → ℂ) :=
  (memLp_restrict_Ioi f).coeFn_toLp

/-- An even carrier is almost everywhere invariant under reflection. -/
theorem coeFn_even_ae {f : SoninL2} (hf : f ∈ evenSubspace) :
    (f : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => f (-x) := by
  have h := l2Reflection_ae f
  rwa [(mem_evenSubspace_iff f).mp hf] at h

/-- **Equal half-line masses.**  An even carrier splits its `L²` mass evenly between the two
half-lines. -/
theorem integral_Iio_norm_sq_eq_integral_Ioi {f : SoninL2} (hf : f ∈ evenSubspace) :
    (∫ x in Iio (0 : ℝ), ‖f x‖ ^ 2) = ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 := by
  have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' (Ioi (0 : ℝ)) = Iio 0 := by
    ext x
    simp
  have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    measurableEmbedding_neg (fun y : ℝ => ‖f y‖ ^ 2) (Ioi (0 : ℝ))
  rw [hpre] at hmp
  rw [← hmp]
  refine setIntegral_congr_ae measurableSet_Iio ?_
  filter_upwards [coeFn_even_ae hf] with x hx
  intro _
  rw [hx]

theorem norm_sq_soninHalfLine {f : SoninL2} (hf : f ∈ evenSubspace) :
    ‖soninHalfLine f‖ ^ 2 * 2 = ‖f‖ ^ 2 := by
  have hint : Integrable (fun x : ℝ => ‖f x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hsplit := integral_add_compl (measurableSet_Iio (a := (0 : ℝ))) hint
  rw [compl_Iio, integral_Ici_eq_integral_Ioi,
    integral_Iio_norm_sq_eq_integral_Ioi hf] at hsplit
  have hhalf : ‖soninHalfLine f‖ ^ 2 = ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 :=
    norm_sq_toLp_eq_integral_norm_sq (memLp_restrict_Ioi f)
  rw [hhalf, ← norm_sq_lp_eq_integral_norm_sq f] at *
  linarith [hsplit]

/-- **Exact half-line norm factor.**  Restricting an even carrier to the positive ray divides its
norm by `sqrt 2`. -/
theorem norm_soninHalfLine {f : SoninL2} (hf : f ∈ evenSubspace) :
    ‖soninHalfLine f‖ = ‖f‖ / Real.sqrt 2 := by
  have hsq := norm_sq_soninHalfLine hf
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hkey : ‖soninHalfLine f‖ ^ 2 = (‖f‖ / Real.sqrt 2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hnn1 : 0 ≤ ‖soninHalfLine f‖ := norm_nonneg _
  have hnn2 : 0 ≤ ‖f‖ / Real.sqrt 2 := by positivity
  have := Real.sqrt_le_sqrt hkey.le
  have hrev := Real.sqrt_le_sqrt hkey.ge
  rw [Real.sqrt_sq hnn1, Real.sqrt_sq hnn2] at this hrev
  linarith

/-! ## The cosine transform on the even carrier -/

theorem fourierUnitary_mem_evenSubspace_self {f : SoninL2} (hf : f ∈ evenSubspace) :
    fourierUnitary f ∈ evenSubspace := by
  rw [mem_evenSubspace_iff, ← fourierUnitary_l2Reflection,
    (mem_evenSubspace_iff f).mp hf]

theorem fourierUnitary_symm_mem_evenSubspace {f : SoninL2} (hf : f ∈ evenSubspace) :
    fourierUnitary.symm f ∈ evenSubspace := by
  have hkey := fourierUnitary_l2Reflection (fourierUnitary.symm f)
  rw [LinearIsometryEquiv.apply_symm_apply, (mem_evenSubspace_iff f).mp hf] at hkey
  rw [mem_evenSubspace_iff]
  have := congrArg fourierUnitary.symm hkey
  rwa [LinearIsometryEquiv.symm_apply_apply] at this

/-- **The Burnol cosine transform.**  The ambient Fourier unitary restricts to a unitary of the
even carrier. -/
def soninCosineUnitary : evenSubspace ≃ₗᵢ[ℂ] evenSubspace where
  toFun f := ⟨fourierUnitary (f : SoninL2), fourierUnitary_mem_evenSubspace_self f.2⟩
  invFun f := ⟨fourierUnitary.symm (f : SoninL2), fourierUnitary_symm_mem_evenSubspace f.2⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add fourierUnitary _ _
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul fourierUnitary c _
  left_inv f := by
    apply Subtype.ext
    exact LinearIsometryEquiv.symm_apply_apply fourierUnitary _
  right_inv f := by
    apply Subtype.ext
    exact LinearIsometryEquiv.apply_symm_apply fourierUnitary _
  norm_map' f := fourierUnitary.norm_map _

@[simp] theorem coe_soninCosineUnitary (f : evenSubspace) :
    (soninCosineUnitary f : SoninL2) = fourierUnitary (f : SoninL2) := rfl

/-- **The cosine transform is an involution.**  On the even carrier the ambient Fourier square is
the reflection, which acts trivially. -/
theorem soninCosineUnitary_involutive (f : evenSubspace) :
    soninCosineUnitary (soninCosineUnitary f) = f := by
  apply Subtype.ext
  have h := l2_fourier_fourier (f : SoninL2)
  rw [show l2Reflection (f : SoninL2) = (f : SoninL2) from
    (mem_evenSubspace_iff _).mp f.2] at h
  exact h

@[simp] theorem soninCosineUnitary_symm_eq :
    soninCosineUnitary.symm = soninCosineUnitary := by
  refine LinearIsometryEquiv.ext fun f => ?_
  have h := soninCosineUnitary_involutive f
  have hs := congrArg soninCosineUnitary.symm h
  rw [LinearIsometryEquiv.symm_apply_apply] at hs
  exact hs.symm

/-! ## The aperture bound on the even carrier -/

/-- **Aperture bound for even carriers.**  The completed Mellin evaluator of an even `L²(ℝ)` vector
with constant aperture head `A` obeys the same aperture exponent, with the half-line norm factor
made explicit. -/
theorem norm_soninMellinEvaluation_le_aperture_even
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {A : ℝ} (hA : 0 < A)
    {f : SoninL2} (hfe : f ∈ evenSubspace)
    (hhead : SoninHeadConstant A (f : ℝ → ℂ)) :
    ‖soninMellinEvaluation w (f : ℝ → ℂ)‖ ≤
      soninApertureConstant w * A ^ (1 / 2 - w.re) * (‖f‖ / Real.sqrt 2) := by
  have h := norm_soninMellinEvaluation_le_soninApertureConstant hlo hhi hA
    (memLp_restrict_Ioi f) hhead
  rwa [show (memLp_restrict_Ioi f).toLp (f : ℝ → ℂ) = soninHalfLine f from rfl,
    norm_soninHalfLine hfe] at h


/-! ## The extended Sonine space at a fixed aperture -/

theorem soninHeadConstant_of_ae {a : ℝ} {f g : ℝ → ℂ}
    (hf : SoninHeadConstant a f) (hfg : f =ᵐ[volume.restrict (Ioo (0 : ℝ) a)] g) :
    SoninHeadConstant a g := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, ?_⟩
  filter_upwards [hc, hfg] with t h1 h2
  rw [← h2, h1]

/-- Vectors of the even carrier with constant aperture head. -/
def soninHeadConstantSubmodule (a : ℝ) : Submodule ℂ evenSubspace where
  carrier := {f | SoninHeadConstant a ((f : SoninL2) : ℝ → ℂ)}
  zero_mem' := by
    refine ⟨0, ?_⟩
    have h : (((0 : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume] 0 := by
      simpa using Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))
    exact ae_restrict_of_ae h
  add_mem' := by
    rintro f g ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, ?_⟩
    have hadd : (((f + g : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
        ((f : SoninL2) : ℝ → ℂ) + ((g : SoninL2) : ℝ → ℂ) := by
      simpa using Lp.coeFn_add ((f : SoninL2)) ((g : SoninL2))
    filter_upwards [hc, hd, ae_restrict_of_ae hadd] with t h1 h2 h3
    rw [h3, Pi.add_apply, h1, h2]
  smul_mem' := by
    rintro r f ⟨c, hc⟩
    refine ⟨r * c, ?_⟩
    have hsmul : (((r • f : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
        r • ((f : SoninL2) : ℝ → ℂ) := by
      simpa using Lp.coeFn_smul r ((f : SoninL2))
    filter_upwards [hc, ae_restrict_of_ae hsmul] with t h1 h2
    rw [h2, Pi.smul_apply, smul_eq_mul, h1]

@[simp] theorem mem_soninHeadConstantSubmodule {a : ℝ} {f : evenSubspace} :
    f ∈ soninHeadConstantSubmodule a ↔ SoninHeadConstant a ((f : SoninL2) : ℝ → ℂ) :=
  Iff.rfl

/-- **Burnol's extended cosine-Sonine space.**  Both the vector and its cosine transform have
constant aperture head `a`. -/
def soninExtendedSpace (a : ℝ) : Submodule ℂ evenSubspace :=
  soninHeadConstantSubmodule a ⊓
    (soninHeadConstantSubmodule a).comap soninCosineUnitary.toLinearEquiv.toLinearMap

theorem mem_soninExtendedSpace {a : ℝ} {f : evenSubspace} :
    f ∈ soninExtendedSpace a ↔
      SoninHeadConstant a ((f : SoninL2) : ℝ → ℂ) ∧
        SoninHeadConstant a (((soninCosineUnitary f : evenSubspace) : SoninL2) : ℝ → ℂ) :=
  Iff.rfl

/-- **The Sonine space is cosine invariant.**  This is the symmetry that lets the off-axis estimate
be transferred across the critical line. -/
theorem soninCosineUnitary_mem_soninExtendedSpace {a : ℝ} {f : evenSubspace}
    (hf : f ∈ soninExtendedSpace a) : soninCosineUnitary f ∈ soninExtendedSpace a := by
  obtain ⟨h1, h2⟩ := hf
  refine ⟨h2, ?_⟩
  have hinv : soninCosineUnitary.toLinearEquiv.toLinearMap (soninCosineUnitary f) = f :=
    soninCosineUnitary_involutive f
  show soninCosineUnitary.toLinearEquiv.toLinearMap (soninCosineUnitary f) ∈
    soninHeadConstantSubmodule a
  rw [hinv]
  exact h1

/-- **Aperture bound on the cosine side.**  For a vector of the extended Sonine space the completed
Mellin evaluator of its cosine transform obeys the same aperture exponent, with the same constant
and the same norm. -/
theorem norm_soninMellinEvaluation_cosine_le_aperture
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {A : ℝ} (hA : 0 < A)
    {f : evenSubspace} (hf : f ∈ soninExtendedSpace A) :
    ‖soninMellinEvaluation w
        (((soninCosineUnitary f : evenSubspace) : SoninL2) : ℝ → ℂ)‖ ≤
      soninApertureConstant w * A ^ (1 / 2 - w.re) * (‖f‖ / Real.sqrt 2) := by
  have hmem : ((soninCosineUnitary f : evenSubspace) : SoninL2) ∈ evenSubspace :=
    (soninCosineUnitary f).2
  have h := norm_soninMellinEvaluation_le_aperture_even hlo hhi hA hmem hf.2
  have hnorm : ‖((soninCosineUnitary f : evenSubspace) : SoninL2)‖ = ‖(f : SoninL2)‖ := by
    rw [coe_soninCosineUnitary]
    exact fourierUnitary.norm_map _
  rw [hnorm] at h
  have hfnorm : ‖(f : SoninL2)‖ = ‖f‖ := rfl
  rwa [hfnorm] at h

end RHTower
