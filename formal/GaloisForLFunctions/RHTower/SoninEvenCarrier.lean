import GaloisForLFunctions.RHTower.SoninL2Model
import GaloisForLFunctions.RHTower.L2FourierReflection
import GaloisForLFunctions.RHTower.SoninEulerCornerConcrete
import GaloisForLFunctions.RHTower.SoninProjectionCorrection
import GaloisForLFunctions.RHTower.CutoffCochain
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

noncomputable section

open MeasureTheory Set
open Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace

namespace RHTower

/-- The symmetric central interval used by the fixed Sonin cutoff. -/
def centralInterval (a : ℝ) : Set ℝ := Set.Icc (-a) a

theorem measurableSet_centralInterval (a : ℝ) : MeasurableSet (centralInterval a) :=
  measurableSet_Icc

theorem neg_mem_centralInterval_iff (a x : ℝ) :
    -x ∈ centralInterval a ↔ x ∈ centralInterval a := by
  simp only [centralInterval, Set.mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-! ### The even Hilbert carrier -/

theorem l2Reflection_ae (f : SoninL2) :
    l2Reflection f =ᵐ[volume] fun x : ℝ => f (-x) :=
  MeasureTheory.Lp.coeFn_compMeasurePreserving f
    (Measure.measurePreserving_neg (volume : Measure ℝ))

@[simp] theorem l2Reflection_involutive (f : SoninL2) :
    l2Reflection (l2Reflection f) = f := by
  apply Lp.ext
  have hinner := (l2Reflection_ae f).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (l2Reflection f), hinner] with x hout hin
  rw [hout]
  simpa [Function.comp_apply] using hin

theorem l2Reflection_symmetric : l2Reflection.toLinearMap.IsSymmetric := by
  intro f g
  calc
    inner ℂ (l2Reflection f) g =
        inner ℂ (l2Reflection (l2Reflection f)) (l2Reflection g) :=
      (l2ReflectionIsometry.inner_map_map (l2Reflection f) g).symm
    _ = inner ℂ f (l2Reflection g) := by rw [l2Reflection_involutive]

def evenProjection : SoninL2 →L[ℂ] SoninL2 :=
  (2 : ℂ)⁻¹ • ((1 : SoninL2 →L[ℂ] SoninL2) + l2Reflection)

@[simp] theorem evenProjection_apply (f : SoninL2) :
    evenProjection f = (2 : ℂ)⁻¹ • (f + l2Reflection f) := rfl

@[simp] theorem l2Reflection_evenProjection (f : SoninL2) :
    l2Reflection (evenProjection f) = evenProjection f := by
  simp [evenProjection_apply, map_add, map_smul, add_comm]

theorem evenProjection_idempotent : IsIdempotentElem evenProjection := by
  rw [isIdempotentElem_iff]
  apply ContinuousLinearMap.ext
  intro f
  change evenProjection (evenProjection f) = evenProjection f
  rw [evenProjection_apply (evenProjection f), l2Reflection_evenProjection]
  module

theorem evenProjection_symmetric : evenProjection.toLinearMap.IsSymmetric := by
  apply (LinearMap.IsSymmetric.one.add l2Reflection_symmetric).smul
  change star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹
  rw [star_inv₀, star_ofNat]

theorem evenProjection_isStarProjection : IsStarProjection evenProjection := by
  rw [ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]
  exact ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap evenProjection_idempotent,
    evenProjection_symmetric⟩

def evenSubspace : Submodule ℂ SoninL2 := LinearMap.range evenProjection.toLinearMap

instance evenSubspace_completeSpace : CompleteSpace evenSubspace := by
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    evenProjection_idempotent).completeSpace_coe

instance evenSubspace_hasOrthogonalProjection : evenSubspace.HasOrthogonalProjection :=
  (ContinuousLinearMap.IsStarProjection.isSymmetricProjection
    evenProjection_isStarProjection).hasOrthogonalProjection_range

theorem evenProjection_eq_starProjection :
    evenProjection = evenSubspace.starProjection :=
  (isStarProjection_iff_eq_starProjection_range.mp evenProjection_isStarProjection).2

theorem mem_evenSubspace_iff (f : SoninL2) :
    f ∈ evenSubspace ↔ l2Reflection f = f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact l2Reflection_evenProjection g
  · intro hf
    refine ⟨f, ?_⟩
    change evenProjection f = f
    rw [evenProjection_apply, hf]
    module

theorem fourierUnitary_l2Reflection (f : SoninL2) :
    fourierUnitary (l2Reflection f) = l2Reflection (fourierUnitary f) := by
  simpa [fourierUnitary, SoninL2, FourierRealL2] using l2_fourier_reflection f

/-- Reflection commutes with the symmetric physical cutoff. -/
theorem l2Reflection_indicatorCutoff_central (a : ℝ) (f : SoninL2) :
    l2Reflection (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f) =
      indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        (l2Reflection f) := by
  apply Lp.ext
  have hcut_neg :=
    (indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a) f).comp_tendsto
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [
    l2Reflection_ae
      (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f),
    hcut_neg,
    indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a) (l2Reflection f),
    l2Reflection_ae f
  ] with x href hcut hright hf
  have hcut' :
      indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f (-x) =
        (centralInterval a).indicator (fun y => f y) (-x) := by
    simpa [Function.comp_apply] using hcut
  rw [href, hcut', hright]
  by_cases hx : x ∈ centralInterval a
  · rw [Set.indicator_of_mem hx,
      Set.indicator_of_mem ((neg_mem_centralInterval_iff a x).2 hx), hf]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (mt (neg_mem_centralInterval_iff a x).1 hx)]

/-- Reflection commutes with the symmetric Fourier cutoff. -/
theorem l2Reflection_fourierCutoff_central (a : ℝ) (f : SoninL2) :
    l2Reflection (fourierCutoff (centralInterval a) (measurableSet_centralInterval a) f) =
      fourierCutoff (centralInterval a) (measurableSet_centralInterval a)
        (l2Reflection f) := by
  apply fourierUnitary.injective
  rw [fourierUnitary_l2Reflection]
  simp only [fourierCutoff_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [l2Reflection_indicatorCutoff_central, fourierUnitary_l2Reflection]

theorem indicatorCutoff_central_mapsTo_evenSubspace (a : ℝ) :
    Set.MapsTo (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a))
      evenSubspace evenSubspace := by
  intro f hf
  apply (mem_evenSubspace_iff _).mpr
  rw [l2Reflection_indicatorCutoff_central, (mem_evenSubspace_iff f).mp hf]

theorem fourierCutoff_central_mapsTo_evenSubspace (a : ℝ) :
    Set.MapsTo (fourierCutoff (centralInterval a) (measurableSet_centralInterval a))
      evenSubspace evenSubspace := by
  intro f hf
  apply (mem_evenSubspace_iff _).mpr
  rw [l2Reflection_fourierCutoff_central, (mem_evenSubspace_iff f).mp hf]

def evenIndicatorCutoff (a : ℝ) : evenSubspace →L[ℂ] evenSubspace :=
  (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)).restrict
    (indicatorCutoff_central_mapsTo_evenSubspace a)

@[simp] theorem coe_evenIndicatorCutoff_apply (a : ℝ) (f : evenSubspace) :
    ((evenIndicatorCutoff a f : evenSubspace) : SoninL2) =
      indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f := rfl

def evenFourierCutoff (a : ℝ) : evenSubspace →L[ℂ] evenSubspace :=
  (fourierCutoff (centralInterval a) (measurableSet_centralInterval a)).restrict
    (fourierCutoff_central_mapsTo_evenSubspace a)

@[simp] theorem coe_evenFourierCutoff_apply (a : ℝ) (f : evenSubspace) :
    ((evenFourierCutoff a f : evenSubspace) : SoninL2) =
      fourierCutoff (centralInterval a) (measurableSet_centralInterval a) f := rfl

/-- Normalized dilation commutes with reflection. -/
theorem l2Reflection_dilation (a : ℝ) (ha : 0 < a) (f : SoninL2) :
    l2Reflection (dilation a ha f) = dilation a ha (l2Reflection f) := by
  apply Lp.ext
  have hdil_neg := (dilation_ae a ha f).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  have href_scaled := (l2Reflection_ae f).comp_tendsto
    (realMul_quasiMeasurePreserving a ha.ne').tendsto_ae
  filter_upwards [l2Reflection_ae (dilation a ha f), hdil_neg,
    dilation_ae a ha (l2Reflection f), href_scaled] with x href hdil hright hscaled
  have hdil' : dilation a ha f (-x) =
      (Real.sqrt a : ℂ) * f (a * (-x)) := by
    simpa [Function.comp_apply] using hdil
  have hscaled' : l2Reflection f (a * x) = f (-(a * x)) := by
    simpa [Function.comp_apply] using hscaled
  rw [href, hdil', hright, hscaled']
  congr 2
  ring

theorem dilation_mapsTo_evenSubspace (a : ℝ) (ha : 0 < a) :
    Set.MapsTo (dilation a ha) evenSubspace evenSubspace := by
  intro f hf
  apply (mem_evenSubspace_iff _).mpr
  rw [l2Reflection_dilation, (mem_evenSubspace_iff f).mp hf]

/-- Normalized dilation as a unitary on the even Hilbert space. -/
def evenDilationUnitary (a : ℝ) (ha : 0 < a) :
    evenSubspace ≃ₗᵢ[ℂ] evenSubspace where
  toFun f := ⟨dilation a ha f, dilation_mapsTo_evenSubspace a ha f.property⟩
  invFun f :=
    ⟨dilation a⁻¹ (inv_pos.mpr ha) f,
      dilation_mapsTo_evenSubspace a⁻¹ (inv_pos.mpr ha) f.property⟩
  left_inv f := by
    apply Subtype.ext
    exact dilation_inv_dilation a ha f
  right_inv f := by
    apply Subtype.ext
    exact dilation_dilation_inv a ha f
  map_add' f g := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul _ _ _
  norm_map' f := by
    exact (dilation a ha).norm_map f

@[simp] theorem coe_evenDilationUnitary_apply
    (a : ℝ) (ha : 0 < a) (f : evenSubspace) :
    (((evenDilationUnitary a ha f : evenSubspace) : SoninL2)) = dilation a ha f := rfl

@[simp] theorem evenDilationUnitary_symm_apply
    (a : ℝ) (ha : 0 < a) (f : evenSubspace) :
    (evenDilationUnitary a ha).symm f =
      ⟨dilation a⁻¹ (inv_pos.mpr ha) f,
        dilation_mapsTo_evenSubspace a⁻¹ (inv_pos.mpr ha) f.property⟩ := rfl

theorem l2Reflection_dilationSum (p : ℝ) (hp : 1 < p) (f : SoninL2) :
    l2Reflection (dilationSum p hp f) = dilationSum p hp (l2Reflection f) := by
  rw [dilationSum_apply, map_add, l2Reflection_dilation, l2Reflection_dilation,
    dilationSum_apply]

theorem dilationSum_mapsTo_evenSubspace (p : ℝ) (hp : 1 < p) :
    Set.MapsTo (dilationSum p hp) evenSubspace evenSubspace := by
  intro f hf
  apply (mem_evenSubspace_iff _).mpr
  rw [l2Reflection_dilationSum, (mem_evenSubspace_iff f).mp hf]

def evenDilationSum (p : ℝ) (hp : 1 < p) : evenSubspace →L[ℂ] evenSubspace :=
  (dilationSum p hp).restrict (dilationSum_mapsTo_evenSubspace p hp)

@[simp] theorem coe_evenDilationSum_apply
    (p : ℝ) (hp : 1 < p) (f : evenSubspace) :
    ((evenDilationSum p hp f : evenSubspace) : SoninL2) = dilationSum p hp f := rfl

/-! ### The central Sonin carrier and its even restriction -/

theorem l2Reflection_mem_centralPhysicalKernel (a : ℝ) {f : SoninL2}
    (hf : f ∈ (centralPhysicalForbidden a)ᗮ) :
    l2Reflection f ∈ (centralPhysicalForbidden a)ᗮ := by
  apply (Submodule.starProjection_apply_eq_zero_iff
    (K := centralPhysicalForbidden a)).mp
  change (physicalForbidden (centralInterval a)
    (measurableSet_centralInterval a)).starProjection (l2Reflection f) = 0
  rw [← indicatorCutoff_eq_physicalForbidden_starProjection]
  rw [← l2Reflection_indicatorCutoff_central]
  have hzero : indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f = 0 := by
    rw [indicatorCutoff_eq_physicalForbidden_starProjection]
    exact (Submodule.starProjection_apply_eq_zero_iff
      (K := centralPhysicalForbidden a)).mpr hf
  rw [hzero, map_zero]

theorem l2Reflection_mem_centralFourierKernel (a : ℝ) {f : SoninL2}
    (hf : f ∈ (centralFourierForbidden a)ᗮ) :
    l2Reflection f ∈ (centralFourierForbidden a)ᗮ := by
  apply (Submodule.starProjection_apply_eq_zero_iff
    (K := centralFourierForbidden a)).mp
  change (fourierForbidden (centralInterval a)
    (measurableSet_centralInterval a)).starProjection (l2Reflection f) = 0
  rw [← fourierCutoff_eq_fourierForbidden_starProjection]
  rw [← l2Reflection_fourierCutoff_central]
  have hzero : fourierCutoff (centralInterval a) (measurableSet_centralInterval a) f = 0 := by
    rw [fourierCutoff_eq_fourierForbidden_starProjection]
    exact (Submodule.starProjection_apply_eq_zero_iff
      (K := centralFourierForbidden a)).mpr hf
  rw [hzero, map_zero]

theorem l2Reflection_mem_centralSoninCarrier (a : ℝ) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) : l2Reflection f ∈ centralSoninCarrier a := by
  exact ⟨l2Reflection_mem_centralPhysicalKernel a hf.1,
    l2Reflection_mem_centralFourierKernel a hf.2⟩

theorem l2Reflection_mem_centralSoninCarrier_orthogonal (a : ℝ) {f : SoninL2}
    (hf : f ∈ (centralSoninCarrier a)ᗮ) :
    l2Reflection f ∈ (centralSoninCarrier a)ᗮ := by
  rw [Submodule.mem_orthogonal'] at hf ⊢
  intro g hg
  exact (l2Reflection_symmetric f g).trans
    (hf (l2Reflection g) (l2Reflection_mem_centralSoninCarrier a hg))

/-- The actual common-kernel projection commutes with reflection. -/
theorem l2Reflection_centralSoninProjection (a : ℝ) (f : SoninL2) :
    l2Reflection (centralSoninProjection a f) =
      centralSoninProjection a (l2Reflection f) := by
  symm
  apply (centralSoninCarrier a).eq_starProjection_of_mem_orthogonal
  · exact l2Reflection_mem_centralSoninCarrier a
      ((centralSoninCarrier a).starProjection_apply_mem f)
  · simpa only [map_sub] using! l2Reflection_mem_centralSoninCarrier_orthogonal a
      ((centralSoninCarrier a).sub_starProjection_mem_orthogonal f)

theorem centralSoninProjection_mapsTo_evenSubspace (a : ℝ) :
    Set.MapsTo (centralSoninProjection a) evenSubspace evenSubspace := by
  intro f hf
  apply (mem_evenSubspace_iff _).mpr
  rw [l2Reflection_centralSoninProjection, (mem_evenSubspace_iff f).mp hf]

/-- The Sonin carrier internal to `L²(ℝ)^ev`. -/
def evenCentralSoninCarrier (a : ℝ) : Submodule ℂ evenSubspace :=
  (centralSoninCarrier a).comap evenSubspace.subtype

theorem evenCentralSoninCarrier_isClosed (a : ℝ) :
    IsClosed (evenCentralSoninCarrier a : Set evenSubspace) :=
  (centralSoninCarrier_isClosed a).preimage continuous_subtype_val

instance evenCentralSoninCarrier_completeSpace (a : ℝ) :
    CompleteSpace (evenCentralSoninCarrier a) :=
  (evenCentralSoninCarrier_isClosed a).completeSpace_coe

instance evenCentralSoninCarrier_hasOrthogonalProjection (a : ℝ) :
    (evenCentralSoninCarrier a).HasOrthogonalProjection := by infer_instance

/-- The common-kernel projection restricted to the even Hilbert carrier. -/
def evenCentralSoninProjection (a : ℝ) : evenSubspace →L[ℂ] evenSubspace :=
  (centralSoninProjection a).restrict (centralSoninProjection_mapsTo_evenSubspace a)

@[simp] theorem coe_evenCentralSoninProjection_apply (a : ℝ) (f : evenSubspace) :
    ((evenCentralSoninProjection a f : evenSubspace) : SoninL2) =
      centralSoninProjection a f := rfl

/-- The restriction of the ambient common-kernel projection is exactly the orthogonal projection
onto the even Sonin carrier. -/
theorem evenCentralSoninProjection_eq_starProjection (a : ℝ) :
    evenCentralSoninProjection a = (evenCentralSoninCarrier a).starProjection := by
  apply ContinuousLinearMap.ext
  intro f
  symm
  apply (evenCentralSoninCarrier a).eq_starProjection_of_mem_orthogonal
  · change centralSoninProjection a (f : SoninL2) ∈ centralSoninCarrier a
    exact (centralSoninCarrier a).starProjection_apply_mem f
  · have hamb :
        (f : SoninL2) - centralSoninProjection a f ∈ (centralSoninCarrier a)ᗮ :=
      (centralSoninCarrier a).sub_starProjection_mem_orthogonal f
    rw [Submodule.mem_orthogonal'] at hamb ⊢
    intro w hw
    exact hamb (w : SoninL2) hw

/-! ### Restriction of the dilation corner to the even carrier -/

theorem centralSoninDilationCorner_mapsTo_evenSubspace
    (a p : ℝ) (hp : 1 < p) :
    Set.MapsTo
      (crossBoundary (centralSoninProjection a) (dilationSum p hp) : SoninL2 →L[ℂ] SoninL2)
      evenSubspace evenSubspace := by
  intro f hf
  have hQf : centralSoninProjection a f ∈ evenSubspace :=
    centralSoninProjection_mapsTo_evenSubspace a hf
  have hWQf : dilationSum p hp (centralSoninProjection a f) ∈ evenSubspace :=
    dilationSum_mapsTo_evenSubspace p hp hQf
  have hQWQf :
      centralSoninProjection a (dilationSum p hp (centralSoninProjection a f)) ∈ evenSubspace :=
    centralSoninProjection_mapsTo_evenSubspace a hWQf
  simpa [crossBoundary] using evenSubspace.sub_mem hWQf hQWQf

/-- The fixed-cutoff one-prime dilation corner acting on `L²(ℝ)^ev`. -/
def evenCentralSoninDilationCorner (a p : ℝ) (hp : 1 < p) :
    evenSubspace →L[ℂ] evenSubspace :=
  (crossBoundary (centralSoninProjection a) (dilationSum p hp) :
      SoninL2 →L[ℂ] SoninL2).restrict
    (centralSoninDilationCorner_mapsTo_evenSubspace a p hp)

@[simp] theorem coe_evenCentralSoninDilationCorner_apply
    (a p : ℝ) (hp : 1 < p) (f : evenSubspace) :
    ((evenCentralSoninDilationCorner a p hp f : evenSubspace) : SoninL2) =
      (crossBoundary (centralSoninProjection a) (dilationSum p hp) :
        SoninL2 →L[ℂ] SoninL2) f := rfl

@[simp] theorem norm_evenCentralSoninDilationCorner_apply
    (a p : ℝ) (hp : 1 < p) (f : evenSubspace) :
    ‖evenCentralSoninDilationCorner a p hp f‖ =
      ‖(crossBoundary (centralSoninProjection a) (dilationSum p hp) :
        SoninL2 →L[ℂ] SoninL2) f‖ := rfl

theorem l2Reflection_evenShellVector
    (a b : ℝ) (hab : a < b) (n : ℕ) :
    l2Reflection (evenShellVector a b hab n) = evenShellVector a b hab n := by
  apply Lp.ext
  let s := evenShellCell a b n
  let hs := measurableSet_evenShellCell a b n
  let hfin := evenShellCell_measure_ne_top hab n
  have hneg := (normalizedIndicator_ae s hs hfin).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (evenShellVector a b hab n), hneg,
    normalizedIndicator_ae s hs hfin] with x href hnegx hx
  rw [href]
  change normalizedIndicator s hs hfin (-x) = normalizedIndicator s hs hfin x
  have hnegx' : normalizedIndicator s hs hfin (-x) =
      ((Real.sqrt (volume.real s))⁻¹ : ℂ) *
        s.indicator (fun _ => (1 : ℂ)) (-x) := by
    simpa [Function.comp_apply] using hnegx
  rw [hnegx', hx]
  have hmem : -x ∈ s ↔ x ∈ s := by simp [s, evenShellCell]
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem (hmem.mpr hxs)]
  · rw [Set.indicator_of_notMem hxs,
      Set.indicator_of_notMem (mt hmem.mp hxs)]

theorem evenShellVector_mem_evenSubspace
    (a b : ℝ) (hab : a < b) (n : ℕ) :
    evenShellVector a b hab n ∈ evenSubspace :=
  (mem_evenSubspace_iff _).mpr (l2Reflection_evenShellVector a b hab n)

/-- Symmetric shell indicators, regarded as vectors in the even carrier. -/
def evenShellVectorEven (a b : ℝ) (hab : a < b) (n : ℕ) : evenSubspace :=
  ⟨evenShellVector a b hab n, evenShellVector_mem_evenSubspace a b hab n⟩

@[simp] theorem coe_evenShellVectorEven
    (a b : ℝ) (hab : a < b) (n : ℕ) :
    ((evenShellVectorEven a b hab n : evenSubspace) : SoninL2) =
      evenShellVector a b hab n := rfl

theorem evenShellVectorEven_orthonormal (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Orthonormal ℂ (evenShellVectorEven a b hab) := by
  exact (evenShellVector_orthonormal a b ha hab).codRestrict evenSubspace
    (evenShellVector_mem_evenSubspace a b hab)

/-- The even Sonin carrier is concretely nontrivial, witnessed by a normalized shell vector. -/
theorem evenSubspace_nontrivial : Nontrivial evenSubspace := by
  let x : evenSubspace := evenShellVectorEven 1 2 (by norm_num) 0
  have hxnorm : ‖x‖ = 1 := by
    exact (evenShellVectorEven_orthonormal 1 2 (by norm_num) (by norm_num)).norm_eq_one 0
  have hx : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxnorm
    norm_num at hxnorm
  exact ⟨x, 0, hx⟩

/-- The even Sonin carrier is infinite-dimensional, witnessed by its infinite orthonormal shell
family. -/
theorem evenSubspace_not_finiteDimensional : ¬ FiniteDimensional ℂ evenSubspace := by
  intro hfd
  letI : FiniteDimensional ℂ evenSubspace := hfd
  exact Module.Finite.not_linearIndependent_of_infinite
    (evenShellVectorEven 1 2 (by norm_num))
    (evenShellVectorEven_orthonormal 1 2 (by norm_num) (by norm_num)).linearIndependent

/-- The ambiently restricted dilation corner is the intrinsic lower corner of the restricted
Sonin projection and restricted dilation sum. -/
theorem evenCentralSoninDilationCorner_eq_crossBoundary
    (a p : ℝ) (hp : 1 < p) :
    evenCentralSoninDilationCorner a p hp =
      (crossBoundary (evenCentralSoninProjection a) (evenDilationSum p hp) :
        evenSubspace →L[ℂ] evenSubspace) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  rfl

/-- **Even-carrier Sonin corner theorem.** The one-prime dilation corner is noncompact already on
`L²(ℝ)^ev`; its certificate is the corrected symmetric shell sequence internal to that carrier. -/
theorem evenCentralSoninDilationCorner_not_isCompactOperator
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ¬ IsCompactOperator (evenCentralSoninDilationCorner a p hp) := by
  let Q : evenSubspace →L[ℂ] evenSubspace := evenCentralSoninProjection a
  let W : evenSubspace →L[ℂ] evenSubspace := evenDilationSum p hp
  let A : evenSubspace →L[ℂ] evenSubspace := evenIndicatorCutoff a
  let g : ℕ → evenSubspace :=
    evenShellVectorEven a (p * a) (by nlinarith)
  let e : ℕ → evenSubspace := fun n => Q (g n)
  have hg : Orthonormal ℂ g := by
    simpa [g] using evenShellVectorEven_orthonormal a (p * a) ha (by nlinarith)
  have he_approx : Tendsto (fun n => ‖e n - g n‖) atTop (𝓝 0) := by
    simpa [e, g, Q] using
      centralSoninProjection_evenShellVector_tendsto a p ha hp
  have he_weak : ∀ ℓ : evenSubspace →L[ℂ] ℂ,
      Tendsto (fun n => ℓ (e n)) atTop (𝓝 0) :=
    weakly_tendsto_zero_of_norm_sub_tendsto_zero
      (Orthonormal.weakly_tendsto_zero hg) he_approx
  have he_bound : ∀ n, ‖e n‖ ≤ 1 := by
    intro n
    calc
      ‖e n‖ ≤ ‖g n‖ := by
        change ‖evenCentralSoninProjection a (g n)‖ ≤ ‖g n‖
        rw [evenCentralSoninProjection_eq_starProjection]
        exact (evenCentralSoninCarrier a).norm_starProjection_apply_le (g n)
      _ = 1 := hg.norm_eq_one n
  have hQe : ∀ n, Q (e n) = e n := by
    intro n
    change evenCentralSoninProjection a (evenCentralSoninProjection a (g n)) =
      evenCentralSoninProjection a (g n)
    rw [evenCentralSoninProjection_eq_starProjection]
    apply (evenCentralSoninCarrier a).starProjection_eq_self_iff.mpr
    exact (evenCentralSoninCarrier a).starProjection_apply_mem (g n)
  have hAQ : ∀ x, A (Q x) = 0 := by
    intro x
    apply Subtype.ext
    change indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        (centralSoninProjection a (x : SoninL2)) = 0
    rw [indicatorCutoff_eq_physicalForbidden_starProjection]
    apply (Submodule.starProjection_apply_eq_zero_iff
      (K := physicalForbidden (centralInterval a)
        (measurableSet_centralInterval a))).mpr
    change centralSoninProjection a (x : SoninL2) ∈
      (centralPhysicalForbidden a)ᗮ
    exact ((centralSoninCarrier a).starProjection_apply_mem (x : SoninL2)).1
  have hA_contract : ∀ x, ‖A x‖ ≤ ‖x‖ := by
    intro x
    change ‖indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        (x : SoninL2)‖ ≤ ‖(x : SoninL2)‖
    rw [indicatorCutoff_eq_physicalForbidden_starProjection]
    exact (physicalForbidden (centralInterval a)
      (measurableSet_centralInterval a)).norm_starProjection_apply_le (x : SoninL2)
  have hcross : Tendsto (fun n => ‖A (W (e n))‖) atTop (𝓝 1) := by
    change Tendsto (fun n =>
      ‖indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        (dilationSum p hp
          (centralSoninProjection a
            (evenShellVector a (p * a) (by nlinarith) n)))‖) atTop (𝓝 1)
    rw [indicatorCutoff_eq_physicalForbidden_starProjection]
    simpa [centralPhysicalForbidden, centralInterval] using
      centralPhysicalProjection_dilationSum_correctedShell_tendsto a p ha hp
  have hcross_lower : ∀ᶠ n in atTop, (1 / 2 : ℝ) ≤ ‖A (W (e n))‖ := by
    have hlt : ∀ᶠ n in atTop, (1 / 2 : ℝ) < ‖A (W (e n))‖ := by
      exact (tendsto_order.1 hcross).1 (1 / 2) (by norm_num)
    exact hlt.mono fun _ hn => hn.le
  rw [evenCentralSoninDilationCorner_eq_crossBoundary]
  exact crossBoundary_not_isCompactOperator_of_eventual_shell_sequence
    Q W A e 1 (1 / 2) he_bound he_weak (by norm_num) hQe hAQ hA_contract hcross_lower

/-! ### The positive Euler corner on the even carrier -/

theorem centralPositiveEulerCorner_mapsTo_evenSubspace
    (a p : ℝ) (hp : 1 < p) :
    Set.MapsTo
      (crossBoundary (centralSoninProjection a) (positiveEulerDilationOperator p hp) :
        SoninL2 →L[ℂ] SoninL2)
      evenSubspace evenSubspace := by
  intro f hf
  rw [centralPositiveEulerCorner_eq_smul]
  exact evenSubspace.smul_mem _
    (centralSoninDilationCorner_mapsTo_evenSubspace a p hp hf)

/-- The fixed-cutoff positive one-prime Euler corner acting on `L²(ℝ)^ev`. -/
def evenCentralPositiveEulerCorner (a p : ℝ) (hp : 1 < p) :
    evenSubspace →L[ℂ] evenSubspace :=
  (crossBoundary (centralSoninProjection a) (positiveEulerDilationOperator p hp) :
      SoninL2 →L[ℂ] SoninL2).restrict
    (centralPositiveEulerCorner_mapsTo_evenSubspace a p hp)

@[simp] theorem coe_evenCentralPositiveEulerCorner_apply
    (a p : ℝ) (hp : 1 < p) (f : evenSubspace) :
    ((evenCentralPositiveEulerCorner a p hp f : evenSubspace) : SoninL2) =
      (crossBoundary (centralSoninProjection a) (positiveEulerDilationOperator p hp) :
        SoninL2 →L[ℂ] SoninL2) f := rfl

/-- The metric constant cannot cross the restricted Sonin projection: the positive Euler corner is
exactly the nonzero Euler coefficient times the restricted dilation corner. -/
theorem evenCentralPositiveEulerCorner_eq_smul
    (a p : ℝ) (hp : 1 < p) :
    evenCentralPositiveEulerCorner a p hp =
      (-((Real.sqrt p : ℂ)⁻¹)) • evenCentralSoninDilationCorner a p hp := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  have h := DFunLike.congr_fun (centralPositiveEulerCorner_eq_smul a p hp)
    (f : SoninL2)
  exact h

/-- The positive one-prime Euler corner is noncompact already after restriction to the actual even
Sonin carrier. -/
theorem evenCentralPositiveEulerCorner_not_isCompactOperator
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ¬ IsCompactOperator (evenCentralPositiveEulerCorner a p hp) := by
  rw [evenCentralPositiveEulerCorner_eq_smul]
  intro hcompact
  let b : ℂ := -((Real.sqrt p : ℂ)⁻¹)
  let T : evenSubspace →L[ℂ] evenSubspace :=
    evenCentralSoninDilationCorner a p hp
  have hb : b ≠ 0 := by
    dsimp [b]
    simp [Real.sqrt_ne_zero'.mpr (zero_lt_one.trans hp)]
  have hcompact' : IsCompactOperator (b • T) := by
    simpa [b, T] using hcompact
  have hunscaled : IsCompactOperator (b⁻¹ • (b • T)) := hcompact'.smul b⁻¹
  have heq : b⁻¹ • (b • T) = T := by
    rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
  apply evenCentralSoninDilationCorner_not_isCompactOperator a p ha hp
  change IsCompactOperator T
  rw [← heq]
  exact hunscaled

/-- Prime-indexed specialization of the even positive Euler corner theorem. -/
theorem evenCentralPrimePositiveEulerCorner_not_isCompactOperator
    (a : ℝ) (p : ℕ) (ha : 0 < a) (hp : p.Prime) :
    ¬ IsCompactOperator
      (evenCentralPositiveEulerCorner a (p : ℝ) (by exact_mod_cast hp.one_lt)) :=
  evenCentralPositiveEulerCorner_not_isCompactOperator a (p : ℝ) ha (by
    exact_mod_cast hp.one_lt)

end RHTower
