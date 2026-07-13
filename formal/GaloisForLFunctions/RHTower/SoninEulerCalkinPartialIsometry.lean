import GaloisForLFunctions.RHTower.SoninProjectionCalkin

noncomputable section

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

theorem mem_centralInterval_mul_iff
    (a r x : ℝ) (hr : 0 < r) :
    x ∈ centralInterval a ↔ r * x ∈ centralInterval (r * a) := by
  simp only [centralInterval, mem_Icc]
  constructor <;> intro h
  · constructor <;> nlinarith
  · constructor <;> nlinarith

theorem indicatorCutoff_dilation
    (a r : ℝ) (hr : 0 < r) (f : SoninL2) :
    indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        (dilation r hr f) =
      dilation r hr
        (indicatorCutoff (centralInterval (r * a))
          (measurableSet_centralInterval (r * a)) f) := by
  apply Lp.ext
  have hinner :=
    (indicatorCutoff_ae (centralInterval (r * a))
      (measurableSet_centralInterval (r * a)) f).comp_tendsto
      (realMul_quasiMeasurePreserving r hr.ne').tendsto_ae
  filter_upwards [
    indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a)
      (dilation r hr f),
    dilation_ae r hr f,
    dilation_ae r hr
      (indicatorCutoff (centralInterval (r * a))
        (measurableSet_centralInterval (r * a)) f),
    hinner
  ] with x hleft hdil hright hcut
  rw [hleft, hright]
  have hcut' :
      indicatorCutoff (centralInterval (r * a))
          (measurableSet_centralInterval (r * a)) f (r * x) =
        (centralInterval (r * a)).indicator (fun y => f y) (r * x) := by
    simpa only [Function.comp_apply] using hcut
  rw [hcut']
  by_cases hx : x ∈ centralInterval a
  · have hrx : r * x ∈ centralInterval (r * a) :=
      (mem_centralInterval_mul_iff a r x hr).mp hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hrx, hdil]
  · have hrx : r * x ∉ centralInterval (r * a) := by
      exact mt (mem_centralInterval_mul_iff a r x hr).mpr hx
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hrx]
    simp

theorem indicatorCutoff_mul_dilationCLM
    (a r : ℝ) (hr : 0 < r) :
    indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) *
        dilationCLM r hr =
      dilationCLM r hr *
        indicatorCutoff (centralInterval (r * a))
          (measurableSet_centralInterval (r * a)) := by
  apply ContinuousLinearMap.ext
  intro f
  exact indicatorCutoff_dilation a r hr f

theorem fourier_normalized_dilation
    (f : ℝ → Complex) (r : ℝ) (hr : 0 < r) (xi : ℝ) :
    FourierTransform.fourier (fun x ↦ (Real.sqrt r : Complex) * f (r * x)) xi =
      (Real.sqrt r⁻¹ : Complex) *
        FourierTransform.fourier f (r⁻¹ * xi) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  simp only [Real.inner_apply]
  let k : ℝ → Complex := fun y ↦
    Complex.exp (((-2 * Real.pi * ((r⁻¹ * y) * xi) : ℝ) : Complex) * Complex.I) *
      ((Real.sqrt r : Complex) * f y)
  have hleft :
      (∫ x : ℝ, Complex.exp (((-2 * Real.pi * (x * xi) : ℝ) : Complex) * Complex.I) •
          ((Real.sqrt r : Complex) * f (r * x))) =
        ∫ x : ℝ, k (r * x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [k]
    congr 2
    push_cast
    field_simp [hr.ne']
  rw [hleft, Measure.integral_comp_mul_left]
  have habs : |r⁻¹| = r⁻¹ := abs_of_pos (inv_pos.mpr hr)
  rw [habs]
  simp only [smul_eq_mul]
  have hsqrt : r⁻¹ * Real.sqrt r = Real.sqrt r⁻¹ := by
    rw [Real.sqrt_inv]
    field_simp [Real.sqrt_ne_zero'.mpr hr]
    exact Real.sq_sqrt hr.le
  rw [Complex.real_smul]
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  dsimp [k]
  have hexp :
      Complex.exp (((-2 * Real.pi * (r⁻¹ * y * xi) : ℝ) : Complex) * Complex.I) =
        Complex.exp (((-2 * Real.pi * (y * (r⁻¹ * xi)) : ℝ) : Complex) * Complex.I) := by
    congr 2
    push_cast
    ring
  rw [hexp]
  have hcoef : ((r⁻¹ : ℝ) : Complex) * (Real.sqrt r : Complex) =
      (Real.sqrt r⁻¹ : Complex) := by
    exact_mod_cast hsqrt
  calc
    ((r⁻¹ : ℝ) : Complex) *
        (Complex.exp (((-2 * Real.pi * (y * (r⁻¹ * xi)) : ℝ) : Complex) * Complex.I) *
          ((Real.sqrt r : Complex) * f y)) =
      (((r⁻¹ : ℝ) : Complex) * (Real.sqrt r : Complex)) *
        (Complex.exp (((-2 * Real.pi * (y * (r⁻¹ * xi)) : ℝ) : Complex) * Complex.I) *
          f y) := by ring
    _ = _ := by rw [hcoef]

theorem fourierUnitary_dilation
    (r : ℝ) (hr : 0 < r) (f : SoninL2) :
    fourierUnitary (dilation r hr f) =
      dilation r⁻¹ (inv_pos.mpr hr) (fourierUnitary f) := by
  let p : SoninL2 → Prop := fun f ↦
    fourierUnitary (dilation r hr f) =
      dilation r⁻¹ (inv_pos.mpr hr) (fourierUnitary f)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact fourierUnitary.continuous.comp (dilation r hr).continuous
    · exact (dilation r⁻¹ (inv_pos.mpr hr)).continuous.comp fourierUnitary.continuous
  · intro g
    change fourierUnitary (dilation r hr (g.toLp 2)) =
      dilation r⁻¹ (inv_pos.mpr hr) (fourierUnitary (g.toLp 2))
    let g2 : SoninL2 := g.toLp 2
    let d2 : SoninL2 := dilation r hr g2
    have hg2ae : (g2 : ℝ → Complex) =ᵐ[volume] (g : ℝ → Complex) := by
      simpa [g2] using g.coeFn_toLp 2 volume
    have hgscaled : Integrable (fun x : ℝ => (Real.sqrt r : Complex) * g (r * x)) :=
      (g.integrable.comp_mul_left' hr.ne').const_mul (Real.sqrt r : Complex)
    have hd2ae : (d2 : ℝ → Complex) =ᵐ[volume]
        fun x : ℝ => (Real.sqrt r : Complex) * g (r * x) := by
      have hgcomp := hg2ae.comp_tendsto
        (realMul_quasiMeasurePreserving r hr.ne').tendsto_ae
      filter_upwards [dilation_ae r hr g2, hgcomp] with x hd hg
      rw [hd]
      have hg' : g2 (r * x) = g (r * x) := by
        simpa only [Function.comp_apply] using hg
      rw [hg']
    have hd2Int : Integrable (d2 : ℝ → Complex) := hgscaled.congr hd2ae.symm
    have hg2Int : Integrable (g2 : ℝ → Complex) := g.integrable.congr hg2ae.symm
    let d1 : Lp Complex 1 (volume : Measure ℝ) :=
      (memLp_one_iff_integrable.mpr hd2Int).toLp d2
    let g1 : Lp Complex 1 (volume : Measure ℝ) :=
      (memLp_one_iff_integrable.mpr hg2Int).toLp g2
    have hd1ae : (d1 : ℝ → Complex) =ᵐ[volume]
        fun x : ℝ => (Real.sqrt r : Complex) * g (r * x) := by
      exact (MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hd2Int)).trans hd2ae
    have hg1ae : (g1 : ℝ → Complex) =ᵐ[volume] (g : ℝ → Complex) := by
      exact (MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hg2Int)).trans hg2ae
    have hFd := l2_fourier_coeFn_eq_l1_fourier_of_integrable d2 hd2Int
    have hFg := l2_fourier_coeFn_eq_l1_fourier_of_integrable g2 hg2Int
    have hFgcomp := hFg.comp_tendsto
      (realMul_quasiMeasurePreserving r⁻¹ (inv_ne_zero hr.ne')).tendsto_ae
    have hright := dilation_ae r⁻¹ (inv_pos.mpr hr) (fourierUnitary g2)
    apply Lp.ext
    filter_upwards [hFd, hFgcomp, hright] with xi hFdx hFgx hrightx
    change (FourierTransform.fourier d2 : SoninL2) xi =
      dilation r⁻¹ (inv_pos.mpr hr) (fourierUnitary g2) xi
    rw [hFdx, hrightx]
    have hFgx' : fourierUnitary g2 (r⁻¹ * xi) =
        Real.Lp.fourierTransform g1 (r⁻¹ * xi) := by
      simpa only [Function.comp_apply] using hFgx
    rw [hFgx']
    simp only [Real.Lp.fourierTransform_apply]
    rw [Real.fourier_congr_ae hd1ae xi,
      Real.fourier_congr_ae hg1ae (r⁻¹ * xi)]
    exact fourier_normalized_dilation g r hr xi

theorem fourierCutoff_dilation
    (a r : ℝ) (hr : 0 < r) (f : SoninL2) :
    fourierCutoff (centralInterval a) (measurableSet_centralInterval a)
        (dilation r hr f) =
      dilation r hr
        (fourierCutoff (centralInterval (r⁻¹ * a))
          (measurableSet_centralInterval (r⁻¹ * a)) f) := by
  apply fourierUnitary.injective
  simp only [fourierCutoff_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [fourierUnitary_dilation]
  rw [indicatorCutoff_dilation a r⁻¹ (inv_pos.mpr hr)]
  rw [fourierUnitary_dilation]
  congr 1
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem fourierCutoff_mul_dilationCLM
    (a r : ℝ) (hr : 0 < r) :
    fourierCutoff (centralInterval a) (measurableSet_centralInterval a) *
        dilationCLM r hr =
      dilationCLM r hr *
        fourierCutoff (centralInterval (r⁻¹ * a))
          (measurableSet_centralInterval (r⁻¹ * a)) := by
  apply ContinuousLinearMap.ext
  intro f
  exact fourierCutoff_dilation a r hr f

def CompactOperatorEq {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]
    (S T : E →L[Complex] E) : Prop :=
  IsCompactOperator (S - T)

infix:50 " =ₖ " => CompactOperatorEq

namespace CompactOperatorEq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]

theorem refl (S : E →L[Complex] E) : S =ₖ S := by
  rw [CompactOperatorEq, sub_self]
  exact isCompactOperator_zero

theorem symm {S T : E →L[Complex] E} (h : S =ₖ T) : T =ₖ S := by
  rw [CompactOperatorEq] at h ⊢
  have heq : T - S = -(S - T) := by abel
  rw [heq]
  exact h.neg

theorem trans {S T U : E →L[Complex] E} (hST : S =ₖ T) (hTU : T =ₖ U) :
    S =ₖ U := by
  rw [CompactOperatorEq] at hST hTU ⊢
  have heq : S - U = (S - T) + (T - U) := by abel
  rw [heq]
  exact hST.add hTU

theorem add {S₁ S₂ T₁ T₂ : E →L[Complex] E}
    (h₁ : S₁ =ₖ T₁) (h₂ : S₂ =ₖ T₂) : S₁ + S₂ =ₖ T₁ + T₂ := by
  rw [CompactOperatorEq] at h₁ h₂ ⊢
  have heq : (S₁ + S₂) - (T₁ + T₂) = (S₁ - T₁) + (S₂ - T₂) := by abel
  rw [heq]
  exact h₁.add h₂

theorem sub {S₁ S₂ T₁ T₂ : E →L[Complex] E}
    (h₁ : S₁ =ₖ T₁) (h₂ : S₂ =ₖ T₂) : S₁ - S₂ =ₖ T₁ - T₂ := by
  rw [CompactOperatorEq] at h₁ h₂ ⊢
  have heq : (S₁ - S₂) - (T₁ - T₂) = (S₁ - T₁) - (S₂ - T₂) := by abel
  rw [heq]
  exact h₁.sub h₂

theorem left_mul (L : E →L[Complex] E) {S T : E →L[Complex] E}
    (h : S =ₖ T) : L * S =ₖ L * T := by
  rw [CompactOperatorEq] at h ⊢
  have heq : L * S - L * T = L * (S - T) := by noncomm_ring
  rw [heq]
  exact h.clm_comp L

theorem right_mul {S T : E →L[Complex] E} (h : S =ₖ T)
    (R : E →L[Complex] E) : S * R =ₖ T * R := by
  rw [CompactOperatorEq] at h ⊢
  have heq : S * R - T * R = (S - T) * R := by noncomm_ring
  rw [heq]
  exact h.comp_clm R

theorem mul {S₁ S₂ T₁ T₂ : E →L[Complex] E}
    (h₁ : S₁ =ₖ T₁) (h₂ : S₂ =ₖ T₂) : S₁ * S₂ =ₖ T₁ * T₂ := by
  exact (right_mul h₁ S₂).trans (left_mul T₁ h₂)

theorem of_eq {S T : E →L[Complex] E} (h : S = T) : S =ₖ T := by
  subst T
  exact refl S

theorem sub_sandwich
    (E₀ F X : E →L[Complex] E)
    (hFX : IsCompactOperator (F * X))
    (hXF : IsCompactOperator (X * F)) :
    (E₀ - F) * X * (E₀ - F) =ₖ E₀ * X * E₀ := by
  rw [CompactOperatorEq]
  have hFXE : IsCompactOperator (F * X * E₀) := hFX.comp_clm E₀
  have hEXF : IsCompactOperator (E₀ * (X * F)) := hXF.clm_comp E₀
  have hFXF : IsCompactOperator (F * X * F) := hFX.comp_clm F
  have hsum := (hFXE.neg.add hEXF.neg).add hFXF
  have heq :
      (E₀ - F) * X * (E₀ - F) - E₀ * X * E₀ =
        -(F * X * E₀) + -(E₀ * (X * F)) + F * X * F := by
    noncomm_ring
  rw [heq]
  exact hsum

end CompactOperatorEq

def evenDilationCLM (r : ℝ) (hr : 0 < r) : evenSubspace →L[Complex] evenSubspace :=
  (evenDilationUnitary r hr : evenSubspace →L[Complex] evenSubspace)

@[simp] theorem coe_evenDilationCLM_apply
    (r : ℝ) (hr : 0 < r) (f : evenSubspace) :
    ((evenDilationCLM r hr f : evenSubspace) : SoninL2) = dilation r hr f := rfl

theorem adjoint_evenDilationCLM (r : ℝ) (hr : 0 < r) :
    (evenDilationCLM r hr)† = evenDilationCLM r⁻¹ (inv_pos.mpr hr) := by
  rw [evenDilationCLM, LinearIsometryEquiv.adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro f
  rfl

theorem evenIndicatorCutoff_mul_evenDilationCLM
    (a r : ℝ) (hr : 0 < r) :
    evenIndicatorCutoff a * evenDilationCLM r hr =
      evenDilationCLM r hr * evenIndicatorCutoff (r * a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact DFunLike.congr_fun (indicatorCutoff_mul_dilationCLM a r hr) (f : SoninL2)

theorem evenFourierCutoff_mul_evenDilationCLM
    (a r : ℝ) (hr : 0 < r) :
    evenFourierCutoff a * evenDilationCLM r hr =
      evenDilationCLM r hr * evenFourierCutoff (r⁻¹ * a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact DFunLike.congr_fun (fourierCutoff_mul_dilationCLM a r hr) (f : SoninL2)

theorem evenDilationCLM_mul
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    evenDilationCLM r hr * evenDilationCLM s hs =
      evenDilationCLM (r * s) (mul_pos hr hs) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact dilation_comp_apply r s hr hs f

theorem evenCentralSoninProjection_compactEq_complement
    (a : ℝ) (ha : 0 < a) :
    evenCentralSoninProjection a =ₖ
      1 - evenIndicatorCutoff a - evenFourierCutoff a :=
  isCompactOperator_evenCentralSoninProjection_sub_complement a ha

theorem isCompactOperator_fourierCutoff_indicatorCutoff_central
    (s t : ℝ) (hs : 0 < s) :
    IsCompactOperator
      (fourierCutoff (centralInterval s) (measurableSet_centralInterval s) *
        indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)) := by
  have hcompact := isCompactOperator_cutoffFourierCutoff (-s) s (-t) t (by linarith)
  have hpull := hcompact.clm_comp
    fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap
  simpa [fourierCutoff, cutoffFourierCutoff, Function.comp_def] using hpull

theorem isCompactOperator_indicatorCutoff_fourierCutoff_central
    (s t : ℝ) (hs : 0 < s) :
    IsCompactOperator
      (indicatorCutoff (centralInterval s) (measurableSet_centralInterval s) *
        fourierCutoff (centralInterval t) (measurableSet_centralInterval t)) := by
  let Aₛ : SoninL2 →L[Complex] SoninL2 :=
    indicatorCutoff (centralInterval s) (measurableSet_centralInterval s)
  let F : SoninL2 →L[Complex] SoninL2 :=
    fourierUnitary.toLinearIsometry.toContinuousLinearMap
  let J : SoninL2 →L[Complex] SoninL2 := l2Reflection
  let K : SoninL2 →L[Complex] SoninL2 := cutoffFourierCutoff (-s) s (-t) t
  have hK : IsCompactOperator K := by
    simpa [K] using isCompactOperator_cutoffFourierCutoff (-s) s (-t) t (by linarith)
  have hEq :
      indicatorCutoff (centralInterval s) (measurableSet_centralInterval s) *
          fourierCutoff (centralInterval t) (measurableSet_centralInterval t) =
        J * K * F := by
    apply ContinuousLinearMap.ext
    intro f
    change Aₛ (fourierUnitary.symm
      (indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)
        (fourierUnitary f))) = J (K (F f))
    rw [fourierUnitary_symm_eq_reflection_fourier]
    change indicatorCutoff (centralInterval s) (measurableSet_centralInterval s)
        (l2Reflection (fourierUnitary
          (indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)
            (fourierUnitary f)))) = J (K (F f))
    rw [← l2Reflection_indicatorCutoff_central]
    dsimp [J, K, F, cutoffFourierCutoff]
    rfl
  rw [hEq]
  exact (hK.comp_clm F).clm_comp J

theorem isCompactOperator_evenIndicatorFourierBlock
    (s t : ℝ) (hs : 0 < s) :
    IsCompactOperator (evenIndicatorCutoff s * evenFourierCutoff t) := by
  let T : SoninL2 →L[Complex] SoninL2 :=
    indicatorCutoff (centralInterval s) (measurableSet_centralInterval s) *
      fourierCutoff (centralInterval t) (measurableSet_centralInterval t)
  have hT : IsCompactOperator T := by
    simpa [T] using isCompactOperator_indicatorCutoff_fourierCutoff_central s t hs
  have hmap : Set.MapsTo T evenSubspace evenSubspace := by
    intro f hf
    exact indicatorCutoff_central_mapsTo_evenSubspace s
      (fourierCutoff_central_mapsTo_evenSubspace t hf)
  have hrestrict : IsCompactOperator (T.restrict hmap) :=
    (hT.comp_clm evenSubspace.subtypeL).codRestrict
      (fun f ↦ hmap f.property)
      (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace evenSubspace)).isClosed
  have heq : T.restrict hmap = evenIndicatorCutoff s * evenFourierCutoff t := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    rfl
  rw [← heq]
  exact hrestrict

theorem isCompactOperator_evenFourierIndicatorBlock
    (s t : ℝ) (hs : 0 < s) :
    IsCompactOperator (evenFourierCutoff s * evenIndicatorCutoff t) := by
  let T : SoninL2 →L[Complex] SoninL2 :=
    fourierCutoff (centralInterval s) (measurableSet_centralInterval s) *
      indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)
  have hT : IsCompactOperator T := by
    simpa [T] using isCompactOperator_fourierCutoff_indicatorCutoff_central s t hs
  have hmap : Set.MapsTo T evenSubspace evenSubspace := by
    intro f hf
    exact fourierCutoff_central_mapsTo_evenSubspace s
      (indicatorCutoff_central_mapsTo_evenSubspace t hf)
  have hrestrict : IsCompactOperator (T.restrict hmap) :=
    (hT.comp_clm evenSubspace.subtypeL).codRestrict
      (fun f ↦ hmap f.property)
      (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace evenSubspace)).isClosed
  have heq : T.restrict hmap = evenFourierCutoff s * evenIndicatorCutoff t := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    rfl
  rw [← heq]
  exact hrestrict

theorem indicatorCutoff_central_mul_of_le
    (s t : ℝ) (hst : s ≤ t) :
    indicatorCutoff (centralInterval s) (measurableSet_centralInterval s) *
        indicatorCutoff (centralInterval t) (measurableSet_centralInterval t) =
      indicatorCutoff (centralInterval s) (measurableSet_centralInterval s) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [
    indicatorCutoff_ae (centralInterval s) (measurableSet_centralInterval s)
      (indicatorCutoff (centralInterval t) (measurableSet_centralInterval t) f),
    indicatorCutoff_ae (centralInterval t) (measurableSet_centralInterval t) f,
    indicatorCutoff_ae (centralInterval s) (measurableSet_centralInterval s) f
  ] with x houter hinner htarget
  rw [ContinuousLinearMap.mul_apply, houter, htarget]
  by_cases hxs : x ∈ centralInterval s
  · have hxt : x ∈ centralInterval t := by
      rw [centralInterval] at hxs ⊢
      constructor <;> linarith [hxs.1, hxs.2]
    rw [Set.indicator_of_mem hxs, hinner, Set.indicator_of_mem hxt,
      Set.indicator_of_mem hxs]
  · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs]

theorem fourierCutoff_central_mul_of_le
    (s t : ℝ) (hst : s ≤ t) :
    fourierCutoff (centralInterval s) (measurableSet_centralInterval s) *
        fourierCutoff (centralInterval t) (measurableSet_centralInterval t) =
      fourierCutoff (centralInterval s) (measurableSet_centralInterval s) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fourierUnitary.injective
  simp only [ContinuousLinearMap.mul_apply, fourierCutoff_apply,
    LinearIsometryEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (indicatorCutoff_central_mul_of_le s t hst) (fourierUnitary f)

theorem evenIndicatorCutoff_mul_of_le
    (s t : ℝ) (hst : s ≤ t) :
    evenIndicatorCutoff s * evenIndicatorCutoff t = evenIndicatorCutoff s := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact DFunLike.congr_fun (indicatorCutoff_central_mul_of_le s t hst) (f : SoninL2)

theorem evenFourierCutoff_mul_of_le
    (s t : ℝ) (hst : s ≤ t) :
    evenFourierCutoff s * evenFourierCutoff t = evenFourierCutoff s := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact DFunLike.congr_fun (fourierCutoff_central_mul_of_le s t hst) (f : SoninL2)

/-! ### Aperture covariance of the Sonin carrier -/

/-- A normalized dilation by a scale `r ≥ 1` sends the Sonin carrier at aperture `a`
into the carrier at the enlarged aperture level `r⁻¹ a`.  The physical gap is transported
exactly; the Fourier gap becomes larger, so cutoff nesting supplies the second constraint. -/
theorem dilation_mem_centralSoninCarrier_inv_mul
    {a r : ℝ} (ha : 0 ≤ a) (hr : 1 ≤ r)
    {f : SoninL2} (hf : f ∈ centralSoninCarrier a) :
    dilation r (lt_of_lt_of_le zero_lt_one hr) f ∈
      centralSoninCarrier (r⁻¹ * a) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  constructor
  · change dilation r hr0 f ∈
      (physicalForbidden (centralInterval (r⁻¹ * a))
        (measurableSet_centralInterval (r⁻¹ * a)))ᗮ
    apply (Submodule.starProjection_apply_eq_zero_iff
      (K := physicalForbidden (centralInterval (r⁻¹ * a))
        (measurableSet_centralInterval (r⁻¹ * a)))).mp
    rw [← indicatorCutoff_eq_physicalForbidden_starProjection]
    rw [indicatorCutoff_dilation]
    have hcut : indicatorCutoff (centralInterval a)
        (measurableSet_centralInterval a) f = 0 := by
      rw [indicatorCutoff_eq_physicalForbidden_starProjection]
      exact (Submodule.starProjection_apply_eq_zero_iff
        (K := centralPhysicalForbidden a)).mpr hf.1
    have hscale : r * (r⁻¹ * a) = a := by
      field_simp [hr0.ne']
    rw [hscale, hcut, map_zero]
  · change dilation r hr0 f ∈
      (fourierForbidden (centralInterval (r⁻¹ * a))
        (measurableSet_centralInterval (r⁻¹ * a)))ᗮ
    apply (Submodule.starProjection_apply_eq_zero_iff
      (K := fourierForbidden (centralInterval (r⁻¹ * a))
        (measurableSet_centralInterval (r⁻¹ * a)))).mp
    rw [← fourierCutoff_eq_fourierForbidden_starProjection]
    rw [fourierCutoff_dilation]
    have hcutA : fourierCutoff (centralInterval a)
        (measurableSet_centralInterval a) f = 0 := by
      rw [fourierCutoff_eq_fourierForbidden_starProjection]
      exact (Submodule.starProjection_apply_eq_zero_iff
        (K := centralFourierForbidden a)).mpr hf.2
    have hinv : r⁻¹ ≤ 1 := (inv_le_one₀ hr0).2 hr
    have hinv0 : 0 ≤ r⁻¹ := (inv_pos.mpr hr0).le
    have hsq : r⁻¹ * r⁻¹ ≤ 1 := by
      calc
        r⁻¹ * r⁻¹ ≤ 1 * r⁻¹ := mul_le_mul_of_nonneg_right hinv hinv0
        _ ≤ 1 := by simpa using hinv
    have hsmall : r⁻¹ * (r⁻¹ * a) ≤ a := by
      calc
        r⁻¹ * (r⁻¹ * a) = (r⁻¹ * r⁻¹) * a := by ring
        _ ≤ 1 * a := mul_le_mul_of_nonneg_right hsq ha
        _ = a := one_mul a
    have hnest := fourierCutoff_central_mul_of_le
      (r⁻¹ * (r⁻¹ * a)) a hsmall
    have hsmallzero : fourierCutoff
        (centralInterval (r⁻¹ * (r⁻¹ * a)))
        (measurableSet_centralInterval (r⁻¹ * (r⁻¹ * a))) f = 0 := by
      calc
        fourierCutoff
            (centralInterval (r⁻¹ * (r⁻¹ * a)))
            (measurableSet_centralInterval (r⁻¹ * (r⁻¹ * a))) f =
            (fourierCutoff
              (centralInterval (r⁻¹ * (r⁻¹ * a)))
              (measurableSet_centralInterval (r⁻¹ * (r⁻¹ * a))) *
              fourierCutoff (centralInterval a)
                (measurableSet_centralInterval a)) f := by rw [hnest]
        _ = 0 := by rw [ContinuousLinearMap.mul_apply, hcutA, map_zero]
    simpa using congrArg (dilation r hr0) hsmallzero

/-- The inverse normalized dilation by `r ≥ 1` obeys the same aperture loss.  This is the
Fourier-reflected half of `dilation_mem_centralSoninCarrier_inv_mul`. -/
theorem inverseDilation_mem_centralSoninCarrier_inv_mul
    {a r : ℝ} (ha : 0 ≤ a) (hr : 1 ≤ r)
    {f : SoninL2} (hf : f ∈ centralSoninCarrier a) :
    dilation r⁻¹ (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hr)) f ∈
      centralSoninCarrier (r⁻¹ * a) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hri0 : 0 < r⁻¹ := inv_pos.mpr hr0
  have hinv : r⁻¹ ≤ 1 := (inv_le_one₀ hr0).2 hr
  have hinv0 : 0 ≤ r⁻¹ := hri0.le
  have hsq : r⁻¹ * r⁻¹ ≤ 1 := by
    calc
      r⁻¹ * r⁻¹ ≤ 1 * r⁻¹ := mul_le_mul_of_nonneg_right hinv hinv0
      _ ≤ 1 := by simpa using hinv
  have hsmall : r⁻¹ * (r⁻¹ * a) ≤ a := by
    calc
      r⁻¹ * (r⁻¹ * a) = (r⁻¹ * r⁻¹) * a := by ring
      _ ≤ 1 * a := mul_le_mul_of_nonneg_right hsq ha
      _ = a := one_mul a
  constructor
  · change dilation r⁻¹ hri0 f ∈
      (physicalForbidden (centralInterval (r⁻¹ * a))
        (measurableSet_centralInterval (r⁻¹ * a)))ᗮ
    apply (Submodule.starProjection_apply_eq_zero_iff
      (K := physicalForbidden (centralInterval (r⁻¹ * a))
        (measurableSet_centralInterval (r⁻¹ * a)))).mp
    rw [← indicatorCutoff_eq_physicalForbidden_starProjection]
    rw [indicatorCutoff_dilation]
    have hcutA : indicatorCutoff (centralInterval a)
        (measurableSet_centralInterval a) f = 0 := by
      rw [indicatorCutoff_eq_physicalForbidden_starProjection]
      exact (Submodule.starProjection_apply_eq_zero_iff
        (K := centralPhysicalForbidden a)).mpr hf.1
    have hnest := indicatorCutoff_central_mul_of_le
      (r⁻¹ * (r⁻¹ * a)) a hsmall
    have hsmallzero : indicatorCutoff
        (centralInterval (r⁻¹ * (r⁻¹ * a)))
        (measurableSet_centralInterval (r⁻¹ * (r⁻¹ * a))) f = 0 := by
      calc
        indicatorCutoff
            (centralInterval (r⁻¹ * (r⁻¹ * a)))
            (measurableSet_centralInterval (r⁻¹ * (r⁻¹ * a))) f =
            (indicatorCutoff
              (centralInterval (r⁻¹ * (r⁻¹ * a)))
              (measurableSet_centralInterval (r⁻¹ * (r⁻¹ * a))) *
              indicatorCutoff (centralInterval a)
                (measurableSet_centralInterval a)) f := by rw [hnest]
        _ = 0 := by rw [ContinuousLinearMap.mul_apply, hcutA, map_zero]
    simpa only [inv_inv, map_zero] using
      congrArg (dilation r⁻¹ hri0) hsmallzero
  · change dilation r⁻¹ hri0 f ∈
      (fourierForbidden (centralInterval (r⁻¹ * a))
        (measurableSet_centralInterval (r⁻¹ * a)))ᗮ
    apply (Submodule.starProjection_apply_eq_zero_iff
      (K := fourierForbidden (centralInterval (r⁻¹ * a))
        (measurableSet_centralInterval (r⁻¹ * a)))).mp
    rw [← fourierCutoff_eq_fourierForbidden_starProjection]
    rw [fourierCutoff_dilation]
    have hcut : fourierCutoff (centralInterval a)
        (measurableSet_centralInterval a) f = 0 := by
      rw [fourierCutoff_eq_fourierForbidden_starProjection]
      exact (Submodule.starProjection_apply_eq_zero_iff
        (K := centralFourierForbidden a)).mpr hf.2
    have hscale : (r⁻¹)⁻¹ * (r⁻¹ * a) = a := by
      field_simp [hr0.ne']
    rw [hscale, hcut, map_zero]

/-- The symmetric prime-dilation generator `U_p + U_p⁻¹` therefore preserves the inductive
Sonin aperture tower, losing at most the factor `p` in the aperture. -/
theorem dilationSum_mem_centralSoninCarrier_inv_mul
    {a p : ℝ} (ha : 0 ≤ a) (hp : 1 < p)
    {f : SoninL2} (hf : f ∈ centralSoninCarrier a) :
    dilationSum p hp f ∈ centralSoninCarrier (p⁻¹ * a) := by
  rw [dilationSum_apply]
  exact (centralSoninCarrier (p⁻¹ * a)).add_mem
    (dilation_mem_centralSoninCarrier_inv_mul ha hp.le hf)
    (inverseDilation_mem_centralSoninCarrier_inv_mul ha hp.le hf)

theorem evenDilationSum_eq
    (p : ℝ) (hp : 1 < p) :
    evenDilationSum p hp =
      evenDilationCLM p (zero_lt_one.trans hp) +
        evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  simp only [ContinuousLinearMap.add_apply, coe_evenDilationSum_apply,
    dilationSum_apply, coe_evenDilationCLM_apply, Submodule.coe_add]

theorem adjoint_evenDilationSum
    (p : ℝ) (hp : 1 < p) :
    (evenDilationSum p hp)† = evenDilationSum p hp := by
  have hstar : ContinuousLinearMap.adjoint
      (evenDilationCLM p (zero_lt_one.trans hp)) =
        evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) :=
    adjoint_evenDilationCLM p (zero_lt_one.trans hp)
  have hEq : evenDilationSum p hp =
      evenDilationCLM p (zero_lt_one.trans hp) +
        ContinuousLinearMap.adjoint
          (evenDilationCLM p (zero_lt_one.trans hp)) := by
    rw [evenDilationSum_eq, hstar]
  change star (evenDilationSum p hp) = evenDilationSum p hp
  rw [hEq]
  exact (IsSelfAdjoint.add_star_self
    (evenDilationCLM p (zero_lt_one.trans hp))).star_eq

theorem adjoint_evenCentralSoninProjection (a : ℝ) :
    (evenCentralSoninProjection a)† = evenCentralSoninProjection a := by
  rw [evenCentralSoninProjection_eq_starProjection]
  exact (isStarProjection_starProjection (U := evenCentralSoninCarrier a)).2.star_eq

theorem evenCentralSoninDilationCorner_eq_mul
    (a p : ℝ) (hp : 1 < p) :
    evenCentralSoninDilationCorner a p hp =
      (1 - evenCentralSoninProjection a) * evenDilationSum p hp *
        evenCentralSoninProjection a := by
  rw [evenCentralSoninDilationCorner_eq_crossBoundary]
  rfl

theorem evenCentralSoninQuadraticCorner_eq_mul
    (a p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    evenCentralSoninQuadraticCorner a p q hp hq =
      evenCentralSoninProjection a * evenDilationSum p hp *
        (1 - evenCentralSoninProjection a) * evenDilationSum q hq *
          evenCentralSoninProjection a := by
  rw [evenCentralSoninQuadraticCorner,
    evenCentralSoninDilationCorner_eq_mul,
    evenCentralSoninDilationCorner_eq_mul]
  change ((1 - evenCentralSoninProjection a) * evenDilationSum p hp *
      evenCentralSoninProjection a)† *
        ((1 - evenCentralSoninProjection a) * evenDilationSum q hq *
          evenCentralSoninProjection a) = _
  have hAdj :
      ((1 - evenCentralSoninProjection a) * evenDilationSum p hp *
        evenCentralSoninProjection a)† =
      evenCentralSoninProjection a ∘L
        (evenDilationSum p hp ∘L (1 - evenCentralSoninProjection a)) := by
    change ContinuousLinearMap.adjoint
        (((1 - evenCentralSoninProjection a) ∘L evenDilationSum p hp) ∘L
          evenCentralSoninProjection a) = _
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      adjoint_evenCentralSoninProjection, adjoint_evenDilationSum,
      ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint_one,
      adjoint_evenCentralSoninProjection]
  rw [hAdj]
  have hQ : evenCentralSoninProjection a * evenCentralSoninProjection a =
      evenCentralSoninProjection a := by
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier a).isIdempotentElem_starProjection
  have hE : (1 - evenCentralSoninProjection a) *
      (1 - evenCentralSoninProjection a) = 1 - evenCentralSoninProjection a := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hQ]
    abel
  let Q := evenCentralSoninProjection a
  let E := 1 - Q
  let Dp := evenDilationSum p hp
  let Dq := evenDilationSum q hq
  change (Q * Dp * E) * (E * Dq * Q) = Q * Dp * E * Dq * Q
  have hE' : E * E = E := by
    dsimp only [E, Q]
    exact hE
  calc
    (Q * Dp * E) * (E * Dq * Q) = Q * Dp * (E * E) * Dq * Q := by
      noncomm_ring
    _ = Q * Dp * E * Dq * Q := by rw [hE']

theorem adjoint_evenIndicatorCutoff (a : ℝ) :
    (evenIndicatorCutoff a)† = evenIndicatorCutoff a := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner Complex
      (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        (f : SoninL2)) (g : SoninL2) =
    inner Complex (f : SoninL2)
      (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        (g : SoninL2))
  exact indicatorCutoff_symmetric (centralInterval a)
    (measurableSet_centralInterval a) f g

theorem adjoint_evenFourierCutoff (a : ℝ) :
    (evenFourierCutoff a)† = evenFourierCutoff a := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner Complex
      (fourierCutoff (centralInterval a) (measurableSet_centralInterval a)
        (f : SoninL2)) (g : SoninL2) =
    inner Complex (f : SoninL2)
      (fourierCutoff (centralInterval a) (measurableSet_centralInterval a)
        (g : SoninL2))
  exact fourierCutoff_symmetric (centralInterval a)
    (measurableSet_centralInterval a) f g

theorem evenIndicatorCutoff_mul_evenCentralSoninProjection (a : ℝ) :
    evenIndicatorCutoff a * evenCentralSoninProjection a = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  change indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (centralSoninProjection a (f : SoninL2)) = 0
  rw [indicatorCutoff_eq_physicalForbidden_starProjection]
  apply (Submodule.starProjection_apply_eq_zero_iff
    (K := centralPhysicalForbidden a)).mpr
  change centralSoninProjection a (f : SoninL2) ∈
    (centralPhysicalForbidden a).orthogonal
  exact ((centralSoninCarrier a).starProjection_apply_mem (f : SoninL2)).1

theorem evenFourierCutoff_mul_evenCentralSoninProjection (a : ℝ) :
    evenFourierCutoff a * evenCentralSoninProjection a = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  change fourierCutoff (centralInterval a) (measurableSet_centralInterval a)
      (centralSoninProjection a (f : SoninL2)) = 0
  rw [fourierCutoff_eq_fourierForbidden_starProjection]
  apply (Submodule.starProjection_apply_eq_zero_iff
    (K := centralFourierForbidden a)).mpr
  change centralSoninProjection a (f : SoninL2) ∈
    (centralFourierForbidden a).orthogonal
  exact ((centralSoninCarrier a).starProjection_apply_mem (f : SoninL2)).2

theorem evenCentralSoninProjection_mul_evenIndicatorCutoff (a : ℝ) :
    evenCentralSoninProjection a * evenIndicatorCutoff a = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint
    (evenIndicatorCutoff_mul_evenCentralSoninProjection a)
  change ContinuousLinearMap.adjoint
      (evenIndicatorCutoff a ∘L evenCentralSoninProjection a) =
    ContinuousLinearMap.adjoint 0 at h
  rw [ContinuousLinearMap.adjoint_comp, adjoint_evenIndicatorCutoff,
    adjoint_evenCentralSoninProjection, ContinuousLinearMap.adjoint.map_zero] at h
  simpa using h

theorem evenCentralSoninProjection_mul_evenFourierCutoff (a : ℝ) :
    evenCentralSoninProjection a * evenFourierCutoff a = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint
    (evenFourierCutoff_mul_evenCentralSoninProjection a)
  change ContinuousLinearMap.adjoint
      (evenFourierCutoff a ∘L evenCentralSoninProjection a) =
    ContinuousLinearMap.adjoint 0 at h
  rw [ContinuousLinearMap.adjoint_comp, adjoint_evenFourierCutoff,
    adjoint_evenCentralSoninProjection, ContinuousLinearMap.adjoint.map_zero] at h
  simpa using h

theorem evenIndicatorCutoff_mul_inverseDilation_mul_soninProjection
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    evenIndicatorCutoff a *
        evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) *
      evenCentralSoninProjection a = 0 := by
  have hcov := evenIndicatorCutoff_mul_evenDilationCLM
    a p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp))
  rw [hcov]
  have hsmall : evenIndicatorCutoff (p⁻¹ * a) * evenCentralSoninProjection a = 0 := by
    rw [← evenIndicatorCutoff_mul_of_le (p⁻¹ * a) a]
    · simp [mul_assoc, evenIndicatorCutoff_mul_evenCentralSoninProjection]
    · have hp0 := zero_lt_one.trans hp
      nlinarith [inv_lt_one_of_one_lt₀ hp]
  simp only [mul_assoc, hsmall, mul_zero]

theorem evenFourierCutoff_mul_dilation_mul_soninProjection
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    evenFourierCutoff a * evenDilationCLM p (zero_lt_one.trans hp) *
      evenCentralSoninProjection a = 0 := by
  have hcov := evenFourierCutoff_mul_evenDilationCLM
    a p (zero_lt_one.trans hp)
  rw [hcov]
  have hsmall : evenFourierCutoff (p⁻¹ * a) * evenCentralSoninProjection a = 0 := by
    rw [← evenFourierCutoff_mul_of_le (p⁻¹ * a) a]
    · simp [mul_assoc, evenFourierCutoff_mul_evenCentralSoninProjection]
    · have hp0 := zero_lt_one.trans hp
      nlinarith [inv_lt_one_of_one_lt₀ hp]
  simp only [mul_assoc, hsmall, mul_zero]

theorem evenSoninProjection_mul_dilation_mul_indicatorCutoff
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    evenCentralSoninProjection a * evenDilationCLM p (zero_lt_one.trans hp) *
      evenIndicatorCutoff a = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint
    (evenIndicatorCutoff_mul_inverseDilation_mul_soninProjection a p ha hp)
  change ContinuousLinearMap.adjoint
      ((evenIndicatorCutoff a ∘L
        evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp))) ∘L
          evenCentralSoninProjection a) = ContinuousLinearMap.adjoint 0 at h
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_evenCentralSoninProjection, adjoint_evenDilationCLM,
    adjoint_evenIndicatorCutoff, ContinuousLinearMap.adjoint.map_zero] at h
  simpa only [inv_inv] using h

theorem evenSoninProjection_mul_inverseDilation_mul_fourierCutoff
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    evenCentralSoninProjection a *
        evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) *
      evenFourierCutoff a = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint
    (evenFourierCutoff_mul_dilation_mul_soninProjection a p ha hp)
  change ContinuousLinearMap.adjoint
      ((evenFourierCutoff a ∘L evenDilationCLM p (zero_lt_one.trans hp)) ∘L
        evenCentralSoninProjection a) = ContinuousLinearMap.adjoint 0 at h
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_evenCentralSoninProjection, adjoint_evenDilationCLM,
    adjoint_evenFourierCutoff, ContinuousLinearMap.adjoint.map_zero] at h
  exact h

/-- The compact-quotient model of the ordered mixed Sonin Gram entry. -/
def evenSoninMixedCalkinModel
    (a p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    evenSubspace →L[Complex] evenSubspace :=
  evenCentralSoninProjection a *
    (evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) *
        evenIndicatorCutoff a * evenDilationCLM q (zero_lt_one.trans hq) +
      evenDilationCLM p (zero_lt_one.trans hp) * evenFourierCutoff a *
        evenDilationCLM q⁻¹ (inv_pos.mpr (zero_lt_one.trans hq))) *
    evenCentralSoninProjection a

theorem evenCentralSoninQuadraticCorner_compactEq_mixedModel
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    evenCentralSoninQuadraticCorner a p q hp hq =ₖ
      evenSoninMixedCalkinModel a p q hp hq := by
  let Q := evenCentralSoninProjection a
  let A := evenIndicatorCutoff a
  let R := evenFourierCutoff a
  let Dp := evenDilationSum p hp
  let Dq := evenDilationSum q hq
  have hQ : Q =ₖ 1 - A - R := by
    simpa [Q, A, R] using evenCentralSoninProjection_compactEq_complement a ha
  have hE : 1 - Q =ₖ A + R := by
    have h := CompactOperatorEq.sub (CompactOperatorEq.refl (1 : evenSubspace →L[Complex] evenSubspace)) hQ
    exact h.trans (CompactOperatorEq.of_eq (by noncomm_ring))
  have hreplace : Q * Dp * (1 - Q) * Dq * Q =ₖ
      Q * Dp * (A + R) * Dq * Q := by
    have h := CompactOperatorEq.left_mul (Q * Dp) hE
    have h' := CompactOperatorEq.right_mul h (Dq * Q)
    simpa only [mul_assoc] using h'
  rw [evenCentralSoninQuadraticCorner_eq_mul]
  refine hreplace.trans (CompactOperatorEq.of_eq ?_)
  dsimp [evenSoninMixedCalkinModel, Q, A, R, Dp, Dq]
  rw [evenDilationSum_eq, evenDilationSum_eq]
  have h₁ := evenSoninProjection_mul_dilation_mul_indicatorCutoff a p ha hp
  have h₂ := evenSoninProjection_mul_inverseDilation_mul_fourierCutoff a p ha hp
  have h₃ := evenIndicatorCutoff_mul_inverseDilation_mul_soninProjection a q ha hq
  have h₄ := evenFourierCutoff_mul_dilation_mul_soninProjection a q ha hq
  noncomm_ring [h₁, h₂, h₃, h₄]

theorem physicalMixedBranch_eq_shellTranslation
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    (1 - evenIndicatorCutoff a) *
        evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) *
        evenIndicatorCutoff a * evenDilationCLM q (zero_lt_one.trans hq) *
        (1 - evenIndicatorCutoff a) =
      (evenIndicatorCutoff (p * a) - evenIndicatorCutoff a) *
        evenDilationCLM (p⁻¹ * q)
          (mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hq)) *
        (1 - evenIndicatorCutoff a) := by
  let A := evenIndicatorCutoff a
  let Ap := evenIndicatorCutoff (p * a)
  let Upi := evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp))
  let Uq := evenDilationCLM q (zero_lt_one.trans hq)
  let Ur := evenDilationCLM (p⁻¹ * q)
    (mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hq))
  have hmove : Upi * A = Ap * Upi := by
    have h := evenIndicatorCutoff_mul_evenDilationCLM
      (p * a) p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp))
    have hscale : p⁻¹ * (p * a) = a := by field_simp
    rw [hscale] at h
    exact h.symm
  have hcomp : Upi * Uq = Ur := by
    exact evenDilationCLM_mul p⁻¹ q
      (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hq)
  have hnest : A * Ap = A := by
    apply evenIndicatorCutoff_mul_of_le
    nlinarith [ha, hp]
  have hEA : (1 - A) * Ap = Ap - A := by
    rw [sub_mul, one_mul, hnest]
  change (1 - A) * Upi * A * Uq * (1 - A) =
    (Ap - A) * Ur * (1 - A)
  calc
    (1 - A) * Upi * A * Uq * (1 - A) =
        (1 - A) * (Upi * A) * (Uq * (1 - A)) := by noncomm_ring
    _ = (1 - A) * (Ap * Upi) * (Uq * (1 - A)) := by rw [hmove]
    _ = ((1 - A) * Ap) * (Upi * Uq) * (1 - A) := by noncomm_ring
    _ = (Ap - A) * Ur * (1 - A) := by rw [hEA, hcomp]

theorem fourierMixedBranch_eq_shellTranslation
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    (1 - evenFourierCutoff a) * evenDilationCLM p (zero_lt_one.trans hp) *
        evenFourierCutoff a *
        evenDilationCLM q⁻¹ (inv_pos.mpr (zero_lt_one.trans hq)) *
        (1 - evenFourierCutoff a) =
      (evenFourierCutoff (p * a) - evenFourierCutoff a) *
        evenDilationCLM (p * q⁻¹)
          (mul_pos (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hq))) *
        (1 - evenFourierCutoff a) := by
  let R := evenFourierCutoff a
  let Rp := evenFourierCutoff (p * a)
  let Up := evenDilationCLM p (zero_lt_one.trans hp)
  let Uqi := evenDilationCLM q⁻¹ (inv_pos.mpr (zero_lt_one.trans hq))
  let Ur := evenDilationCLM (p * q⁻¹)
    (mul_pos (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hq))
  )
  have hmove : Up * R = Rp * Up := by
    have h := evenFourierCutoff_mul_evenDilationCLM
      (p * a) p (zero_lt_one.trans hp)
    have hscale : p⁻¹ * (p * a) = a := by field_simp
    rw [hscale] at h
    exact h.symm
  have hcomp : Up * Uqi = Ur := by
    exact evenDilationCLM_mul p q⁻¹
      (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hq))
  have hnest : R * Rp = R := by
    apply evenFourierCutoff_mul_of_le
    nlinarith [ha, hp]
  have hER : (1 - R) * Rp = Rp - R := by
    rw [sub_mul, one_mul, hnest]
  change (1 - R) * Up * R * Uqi * (1 - R) =
    (Rp - R) * Ur * (1 - R)
  calc
    (1 - R) * Up * R * Uqi * (1 - R) =
        (1 - R) * (Up * R) * (Uqi * (1 - R)) := by noncomm_ring
    _ = (1 - R) * (Rp * Up) * (Uqi * (1 - R)) := by rw [hmove]
    _ = ((1 - R) * Rp) * (Up * Uqi) * (1 - R) := by noncomm_ring
    _ = (Rp - R) * Ur * (1 - R) := by rw [hER, hcomp]

def evenPhysicalMixedShellTranslation
    (a p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    evenSubspace →L[Complex] evenSubspace :=
  (evenIndicatorCutoff (p * a) - evenIndicatorCutoff a) *
    evenDilationCLM (p⁻¹ * q)
      (mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hq)) *
    (1 - evenIndicatorCutoff a)

def evenFourierMixedShellTranslation
    (a p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    evenSubspace →L[Complex] evenSubspace :=
  (evenFourierCutoff (p * a) - evenFourierCutoff a) *
    evenDilationCLM (p * q⁻¹)
      (mul_pos (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hq))) *
    (1 - evenFourierCutoff a)

def evenSoninMixedShellTranslation
    (a p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    evenSubspace →L[Complex] evenSubspace :=
  evenPhysicalMixedShellTranslation a p q hp hq +
    evenFourierMixedShellTranslation a p q hp hq

theorem physicalMixedBranch_compactEq_shellTranslation
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    evenCentralSoninProjection a *
        (evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) *
          evenIndicatorCutoff a * evenDilationCLM q (zero_lt_one.trans hq)) *
        evenCentralSoninProjection a =ₖ
      evenPhysicalMixedShellTranslation a p q hp hq := by
  let Q := evenCentralSoninProjection a
  let A := evenIndicatorCutoff a
  let R := evenFourierCutoff a
  let Upi := evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp))
  let Uq := evenDilationCLM q (zero_lt_one.trans hq)
  let X := Upi * A * Uq
  let Eₐ := 1 - A
  let E := Eₐ - R
  have hQ : Q =ₖ E := by
    have h := evenCentralSoninProjection_compactEq_complement a ha
    exact h.trans (CompactOperatorEq.of_eq (by dsimp [E, Eₐ, A, R]))
  have hRX : IsCompactOperator (R * X) := by
    have hmove := evenFourierCutoff_mul_evenDilationCLM
      a p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp))
    have hscale : (p⁻¹)⁻¹ * a = p * a := by rw [inv_inv]
    rw [hscale] at hmove
    have hb := isCompactOperator_evenFourierIndicatorBlock (p * a) a (mul_pos (zero_lt_one.trans hp) ha)
    have hc := (hb.comp_clm Uq).clm_comp Upi
    have heq : R * X = Upi * (evenFourierCutoff (p * a) * A) * Uq := by
      change R * (Upi * A * Uq) =
        Upi * (evenFourierCutoff (p * a) * A) * Uq
      calc
        R * (Upi * A * Uq) = (R * Upi) * A * Uq := by noncomm_ring
        _ = (Upi * evenFourierCutoff (p * a)) * A * Uq := by rw [hmove]
        _ = Upi * (evenFourierCutoff (p * a) * A) * Uq := by noncomm_ring
    rw [heq]
    exact hc
  have hXR : IsCompactOperator (X * R) := by
    have hmove := evenFourierCutoff_mul_evenDilationCLM
      (q * a) q (zero_lt_one.trans hq)
    have hscale : q⁻¹ * (q * a) = a := by field_simp
    rw [hscale] at hmove
    have hb := isCompactOperator_evenIndicatorFourierBlock a (q * a) ha
    have hc := (hb.comp_clm Uq).clm_comp Upi
    have heq : X * R = Upi * (A * evenFourierCutoff (q * a)) * Uq := by
      change (Upi * A * Uq) * R =
        Upi * (A * evenFourierCutoff (q * a)) * Uq
      calc
        (Upi * A * Uq) * R = Upi * A * (Uq * R) := by noncomm_ring
        _ = Upi * A * (evenFourierCutoff (q * a) * Uq) := by rw [hmove.symm]
        _ = Upi * (A * evenFourierCutoff (q * a)) * Uq := by noncomm_ring
    rw [heq]
    exact hc
  have houter : Q * X * Q =ₖ E * X * E := by
    exact (CompactOperatorEq.mul
      (CompactOperatorEq.mul hQ (CompactOperatorEq.refl X)) hQ)
  have hremove : E * X * E =ₖ Eₐ * X * Eₐ := by
    exact CompactOperatorEq.sub_sandwich Eₐ R X hRX hXR
  refine houter.trans (hremove.trans (CompactOperatorEq.of_eq ?_))
  dsimp [Eₐ, X, Upi, Uq, A, evenPhysicalMixedShellTranslation]
  exact physicalMixedBranch_eq_shellTranslation a p q ha hp hq

theorem fourierMixedBranch_compactEq_shellTranslation
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    evenCentralSoninProjection a *
        (evenDilationCLM p (zero_lt_one.trans hp) * evenFourierCutoff a *
          evenDilationCLM q⁻¹ (inv_pos.mpr (zero_lt_one.trans hq))) *
        evenCentralSoninProjection a =ₖ
      evenFourierMixedShellTranslation a p q hp hq := by
  let Q := evenCentralSoninProjection a
  let A := evenIndicatorCutoff a
  let R := evenFourierCutoff a
  let Up := evenDilationCLM p (zero_lt_one.trans hp)
  let Uqi := evenDilationCLM q⁻¹ (inv_pos.mpr (zero_lt_one.trans hq))
  let X := Up * R * Uqi
  let Eᵣ := 1 - R
  let E := Eᵣ - A
  have hQ : Q =ₖ E := by
    have h := evenCentralSoninProjection_compactEq_complement a ha
    exact h.trans (CompactOperatorEq.of_eq (by dsimp [E, Eᵣ, A, R]; abel))
  have hAX : IsCompactOperator (A * X) := by
    have hmove := evenIndicatorCutoff_mul_evenDilationCLM
      a p (zero_lt_one.trans hp)
    have hb := isCompactOperator_evenIndicatorFourierBlock (p * a) a (mul_pos (zero_lt_one.trans hp) ha)
    have hc := (hb.comp_clm Uqi).clm_comp Up
    have heq : A * X = Up * (evenIndicatorCutoff (p * a) * R) * Uqi := by
      change A * (Up * R * Uqi) =
        Up * (evenIndicatorCutoff (p * a) * R) * Uqi
      calc
        A * (Up * R * Uqi) = (A * Up) * R * Uqi := by noncomm_ring
        _ = (Up * evenIndicatorCutoff (p * a)) * R * Uqi := by rw [hmove]
        _ = Up * (evenIndicatorCutoff (p * a) * R) * Uqi := by noncomm_ring
    rw [heq]
    exact hc
  have hXA : IsCompactOperator (X * A) := by
    have hmove := evenIndicatorCutoff_mul_evenDilationCLM
      (q * a) q⁻¹ (inv_pos.mpr (zero_lt_one.trans hq))
    have hscale : q⁻¹ * (q * a) = a := by field_simp
    rw [hscale] at hmove
    have hb := isCompactOperator_evenFourierIndicatorBlock a (q * a) ha
    have hc := (hb.comp_clm Uqi).clm_comp Up
    have heq : X * A = Up * (R * evenIndicatorCutoff (q * a)) * Uqi := by
      change (Up * R * Uqi) * A =
        Up * (R * evenIndicatorCutoff (q * a)) * Uqi
      calc
        (Up * R * Uqi) * A = Up * R * (Uqi * A) := by noncomm_ring
        _ = Up * R * (evenIndicatorCutoff (q * a) * Uqi) := by rw [hmove.symm]
        _ = Up * (R * evenIndicatorCutoff (q * a)) * Uqi := by noncomm_ring
    rw [heq]
    exact hc
  have houter : Q * X * Q =ₖ E * X * E := by
    exact (CompactOperatorEq.mul
      (CompactOperatorEq.mul hQ (CompactOperatorEq.refl X)) hQ)
  have hremove : E * X * E =ₖ Eᵣ * X * Eᵣ := by
    exact CompactOperatorEq.sub_sandwich Eᵣ A X hAX hXA
  refine houter.trans (hremove.trans (CompactOperatorEq.of_eq ?_))
  dsimp [Eᵣ, X, Up, Uqi, R, evenFourierMixedShellTranslation]
  exact fourierMixedBranch_eq_shellTranslation a p q ha hp hq

theorem evenSoninMixedCalkinModel_compactEq_shellTranslation
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    evenSoninMixedCalkinModel a p q hp hq =ₖ
      evenSoninMixedShellTranslation a p q hp hq := by
  have hpbranch := physicalMixedBranch_compactEq_shellTranslation a p q ha hp hq
  have hfbranch := fourierMixedBranch_compactEq_shellTranslation a p q ha hp hq
  dsimp [evenSoninMixedCalkinModel, evenSoninMixedShellTranslation]
  have hsum := CompactOperatorEq.add hpbranch hfbranch
  simpa only [mul_add, add_mul, mul_assoc] using hsum

theorem evenCentralSoninQuadraticCorner_compactEq_shellTranslation
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    evenCentralSoninQuadraticCorner a p q hp hq =ₖ
      evenSoninMixedShellTranslation a p q hp hq :=
  (evenCentralSoninQuadraticCorner_compactEq_mixedModel a p q ha hp hq).trans
    (evenSoninMixedCalkinModel_compactEq_shellTranslation a p q ha hp hq)

theorem evenDilationCLM_mul_evenIndicatorCutoff
    (a r : ℝ) (hr : 0 < r) :
    evenDilationCLM r hr * evenIndicatorCutoff a =
      evenIndicatorCutoff (r⁻¹ * a) * evenDilationCLM r hr := by
  have h := evenIndicatorCutoff_mul_evenDilationCLM
    (r⁻¹ * a) r hr
  have hscale : r * (r⁻¹ * a) = a := by field_simp
  rw [hscale] at h
  exact h.symm

theorem evenDilationCLM_mul_evenFourierCutoff
    (a r : ℝ) (hr : 0 < r) :
    evenDilationCLM r hr * evenFourierCutoff a =
      evenFourierCutoff (r * a) * evenDilationCLM r hr := by
  have h := evenFourierCutoff_mul_evenDilationCLM (r * a) r hr
  have hscale : r⁻¹ * (r * a) = a := by field_simp
  rw [hscale] at h
  exact h.symm

theorem evenDilationCLM_one :
    evenDilationCLM 1 zero_lt_one = (1 : evenSubspace →L[Complex] evenSubspace) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [dilation_ae 1 zero_lt_one (f : SoninL2)] with x hx
  simpa using hx

theorem evenIndicatorCutoff_mul_of_le_rev
    (s t : ℝ) (hst : s ≤ t) :
    evenIndicatorCutoff t * evenIndicatorCutoff s = evenIndicatorCutoff s := by
  have h := congrArg ContinuousLinearMap.adjoint
    (evenIndicatorCutoff_mul_of_le s t hst)
  change ContinuousLinearMap.adjoint
      (evenIndicatorCutoff s ∘L evenIndicatorCutoff t) =
    ContinuousLinearMap.adjoint (evenIndicatorCutoff s) at h
  rw [ContinuousLinearMap.adjoint_comp, adjoint_evenIndicatorCutoff,
    adjoint_evenIndicatorCutoff] at h
  exact h

theorem evenFourierCutoff_mul_of_le_rev
    (s t : ℝ) (hst : s ≤ t) :
    evenFourierCutoff t * evenFourierCutoff s = evenFourierCutoff s := by
  have h := congrArg ContinuousLinearMap.adjoint
    (evenFourierCutoff_mul_of_le s t hst)
  change ContinuousLinearMap.adjoint
      (evenFourierCutoff s ∘L evenFourierCutoff t) =
    ContinuousLinearMap.adjoint (evenFourierCutoff s) at h
  rw [ContinuousLinearMap.adjoint_comp, adjoint_evenFourierCutoff,
    adjoint_evenFourierCutoff] at h
  exact h

theorem physicalShellTranslation_mul_of_le
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hpq : p ≤ q) :
    evenPhysicalMixedShellTranslation a q p hq hp *
        evenPhysicalMixedShellTranslation a p q hp hq =
      evenIndicatorCutoff (q * a) -
        evenIndicatorCutoff ((q * p⁻¹) * a) := by
  let A := evenIndicatorCutoff a
  let Ap := evenIndicatorCutoff (p * a)
  let Aq := evenIndicatorCutoff (q * a)
  let Al := evenIndicatorCutoff ((q * p⁻¹) * a)
  let Us := evenDilationCLM (q⁻¹ * p)
    (mul_pos (inv_pos.mpr (zero_lt_one.trans hq)) (zero_lt_one.trans hp))
  let Ur := evenDilationCLM (p⁻¹ * q)
    (mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hq))
  let E := 1 - A
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hratio : 1 ≤ q * p⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hp0).2 (by simpa using hpq)
  have hinv : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have haAp : a ≤ p * a := by nlinarith
  have haAq : a ≤ q * a := by nlinarith
  have haAl : a ≤ (q * p⁻¹) * a := by nlinarith
  have hAlAq : (q * p⁻¹) * a ≤ q * a := by
    have : q * p⁻¹ ≤ q := by nlinarith
    nlinarith
  have hEAp : E * (Ap - A) = Ap - A := by
    have hAAp : A * Ap = A := evenIndicatorCutoff_mul_of_le a (p * a) haAp
    have hAA : A * A = A := evenIndicatorCutoff_mul_of_le a a le_rfl
    dsimp [E]
    rw [sub_mul, one_mul, mul_sub, hAAp, hAA]
    abel
  have hmove : Us * (Ap - A) = (Aq - Al) * Us := by
    have hpMove := evenDilationCLM_mul_evenIndicatorCutoff
      (p * a) (q⁻¹ * p)
        (mul_pos (inv_pos.mpr hq0) hp0)
    have haMove := evenDilationCLM_mul_evenIndicatorCutoff
      a (q⁻¹ * p) (mul_pos (inv_pos.mpr hq0) hp0)
    have hscaleP : (q⁻¹ * p)⁻¹ * (p * a) = q * a := by field_simp
    have hscaleA : (q⁻¹ * p)⁻¹ * a = (q * p⁻¹) * a := by field_simp
    rw [hscaleP] at hpMove
    rw [hscaleA] at haMove
    change Us * Ap = Aq * Us at hpMove
    change Us * A = Al * Us at haMove
    rw [mul_sub, hpMove, haMove, sub_mul]
  have hshell : (Aq - A) * (Aq - Al) = Aq - Al := by
    have hAqAq : Aq * Aq = Aq := evenIndicatorCutoff_mul_of_le (q * a) (q * a) le_rfl
    have hAqAl : Aq * Al = Al := evenIndicatorCutoff_mul_of_le_rev
      ((q * p⁻¹) * a) (q * a) hAlAq
    have hAAq : A * Aq = A := evenIndicatorCutoff_mul_of_le a (q * a) haAq
    have hAAl : A * Al = A := evenIndicatorCutoff_mul_of_le a ((q * p⁻¹) * a) haAl
    rw [sub_mul, mul_sub, hAqAq, hAqAl, mul_sub, hAAq, hAAl]
    abel
  have hU : Us * Ur = (1 : evenSubspace →L[Complex] evenSubspace) := by
    have hs : 0 < q⁻¹ * p := mul_pos (inv_pos.mpr hq0) hp0
    have hscale : p⁻¹ * q = (q⁻¹ * p)⁻¹ := by field_simp
    have hUr : Ur = evenDilationCLM (q⁻¹ * p)⁻¹ (inv_pos.mpr hs) := by
      dsimp [Ur]
      congr 1
    rw [hUr]
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    exact dilation_dilation_inv (q⁻¹ * p) hs (f : SoninL2)
  have hshellE : (Aq - Al) * E = Aq - Al := by
    have hAqA : Aq * A = A := evenIndicatorCutoff_mul_of_le_rev a (q * a) haAq
    have hAlA : Al * A = A := evenIndicatorCutoff_mul_of_le_rev a ((q * p⁻¹) * a) haAl
    have hsubA : (Aq - Al) * A = 0 := by
      rw [sub_mul, hAqA, hAlA, sub_self]
    change (Aq - Al) * (1 - A) = Aq - Al
    rw [mul_sub, hsubA, sub_zero, mul_one]
  change ((Aq - A) * Us * E) * ((Ap - A) * Ur * E) = Aq - Al
  calc
    ((Aq - A) * Us * E) * ((Ap - A) * Ur * E) =
        (Aq - A) * Us * (E * (Ap - A)) * Ur * E := by noncomm_ring
    _ = (Aq - A) * (Us * (Ap - A)) * Ur * E := by rw [hEAp]; noncomm_ring
    _ = ((Aq - A) * (Aq - Al)) * (Us * Ur) * E := by rw [hmove]; noncomm_ring
    _ = Aq - Al := by
      rw [hshell, hU]
      simpa only [mul_one] using hshellE

theorem fourierShellTranslation_mul_of_le
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hpq : p ≤ q) :
    evenFourierMixedShellTranslation a q p hq hp *
        evenFourierMixedShellTranslation a p q hp hq =
      evenFourierCutoff (q * a) -
        evenFourierCutoff ((q * p⁻¹) * a) := by
  let R := evenFourierCutoff a
  let Rp := evenFourierCutoff (p * a)
  let Rq := evenFourierCutoff (q * a)
  let Rl := evenFourierCutoff ((q * p⁻¹) * a)
  let Us := evenDilationCLM (q * p⁻¹)
    (mul_pos (zero_lt_one.trans hq) (inv_pos.mpr (zero_lt_one.trans hp)))
  let Ur := evenDilationCLM (p * q⁻¹)
    (mul_pos (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hq)))
  let E := 1 - R
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hratio : 1 ≤ q * p⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hp0).2 (by simpa using hpq)
  have hinv : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have haRp : a ≤ p * a := by nlinarith
  have haRq : a ≤ q * a := by nlinarith
  have haRl : a ≤ (q * p⁻¹) * a := by nlinarith
  have hRlRq : (q * p⁻¹) * a ≤ q * a := by
    have : q * p⁻¹ ≤ q := by nlinarith
    nlinarith
  have hERp : E * (Rp - R) = Rp - R := by
    have hRRp : R * Rp = R := evenFourierCutoff_mul_of_le a (p * a) haRp
    have hRR : R * R = R := evenFourierCutoff_mul_of_le a a le_rfl
    dsimp [E]
    rw [sub_mul, one_mul, mul_sub, hRRp, hRR]
    abel
  have hmove : Us * (Rp - R) = (Rq - Rl) * Us := by
    have hpMove := evenDilationCLM_mul_evenFourierCutoff
      (p * a) (q * p⁻¹)
        (mul_pos hq0 (inv_pos.mpr hp0))
    have haMove := evenDilationCLM_mul_evenFourierCutoff
      a (q * p⁻¹) (mul_pos hq0 (inv_pos.mpr hp0))
    have hscaleP : (q * p⁻¹) * (p * a) = q * a := by field_simp
    have hscaleA : (q * p⁻¹) * a = (q * p⁻¹) * a := rfl
    rw [hscaleP] at hpMove
    rw [hscaleA] at haMove
    change Us * Rp = Rq * Us at hpMove
    change Us * R = Rl * Us at haMove
    rw [mul_sub, hpMove, haMove, sub_mul]
  have hshell : (Rq - R) * (Rq - Rl) = Rq - Rl := by
    have hRqRq : Rq * Rq = Rq := evenFourierCutoff_mul_of_le (q * a) (q * a) le_rfl
    have hRqRl : Rq * Rl = Rl := evenFourierCutoff_mul_of_le_rev
      ((q * p⁻¹) * a) (q * a) hRlRq
    have hRRq : R * Rq = R := evenFourierCutoff_mul_of_le a (q * a) haRq
    have hRRl : R * Rl = R := evenFourierCutoff_mul_of_le a ((q * p⁻¹) * a) haRl
    rw [sub_mul, mul_sub, hRqRq, hRqRl, mul_sub, hRRq, hRRl]
    abel
  have hU : Us * Ur = (1 : evenSubspace →L[Complex] evenSubspace) := by
    have hs : 0 < q * p⁻¹ := mul_pos hq0 (inv_pos.mpr hp0)
    have hscale : p * q⁻¹ = (q * p⁻¹)⁻¹ := by field_simp
    have hUr : Ur = evenDilationCLM (q * p⁻¹)⁻¹ (inv_pos.mpr hs) := by
      dsimp [Ur]
      congr 1
    rw [hUr]
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    exact dilation_dilation_inv (q * p⁻¹) hs (f : SoninL2)
  have hshellE : (Rq - Rl) * E = Rq - Rl := by
    have hRqR : Rq * R = R := evenFourierCutoff_mul_of_le_rev a (q * a) haRq
    have hRlR : Rl * R = R := evenFourierCutoff_mul_of_le_rev a ((q * p⁻¹) * a) haRl
    have hsubR : (Rq - Rl) * R = 0 := by
      rw [sub_mul, hRqR, hRlR, sub_self]
    change (Rq - Rl) * (1 - R) = Rq - Rl
    rw [mul_sub, hsubR, sub_zero, mul_one]
  change ((Rq - R) * Us * E) * ((Rp - R) * Ur * E) = Rq - Rl
  calc
    ((Rq - R) * Us * E) * ((Rp - R) * Ur * E) =
        (Rq - R) * Us * (E * (Rp - R)) * Ur * E := by noncomm_ring
    _ = (Rq - R) * (Us * (Rp - R)) * Ur * E := by rw [hERp]; noncomm_ring
    _ = ((Rq - R) * (Rq - Rl)) * (Us * Ur) * E := by rw [hmove]; noncomm_ring
    _ = Rq - Rl := by
      rw [hshell, hU]
      simpa only [mul_one] using hshellE

theorem physicalShellTranslation_mul_rev_of_le
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hpq : p ≤ q) :
    evenPhysicalMixedShellTranslation a p q hp hq *
        evenPhysicalMixedShellTranslation a q p hq hp =
      evenIndicatorCutoff (p * a) - evenIndicatorCutoff a := by
  let A := evenIndicatorCutoff a
  let Ap := evenIndicatorCutoff (p * a)
  let Aq := evenIndicatorCutoff (q * a)
  let Ab := evenIndicatorCutoff ((p * q⁻¹) * a)
  let Ur := evenDilationCLM (p⁻¹ * q)
    (mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hq))
  let Us := evenDilationCLM (q⁻¹ * p)
    (mul_pos (inv_pos.mpr (zero_lt_one.trans hq)) (zero_lt_one.trans hp))
  let E := 1 - A
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hsmall : p * q⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hq0).2 hpq
  have haAp : a ≤ p * a := by nlinarith
  have haAq : a ≤ q * a := by nlinarith
  have hAbA : (p * q⁻¹) * a ≤ a := by nlinarith
  have hAbAp : (p * q⁻¹) * a ≤ p * a := by
    have hqi : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
    nlinarith
  have hEAq : E * (Aq - A) = Aq - A := by
    have hAAq : A * Aq = A := evenIndicatorCutoff_mul_of_le a (q * a) haAq
    have hAA : A * A = A := evenIndicatorCutoff_mul_of_le a a le_rfl
    dsimp [E]
    rw [sub_mul, one_mul, mul_sub, hAAq, hAA]
    abel
  have hmove : Ur * (Aq - A) = (Ap - Ab) * Ur := by
    have hqMove := evenDilationCLM_mul_evenIndicatorCutoff
      (q * a) (p⁻¹ * q) (mul_pos (inv_pos.mpr hp0) hq0)
    have haMove := evenDilationCLM_mul_evenIndicatorCutoff
      a (p⁻¹ * q) (mul_pos (inv_pos.mpr hp0) hq0)
    have hscaleQ : (p⁻¹ * q)⁻¹ * (q * a) = p * a := by field_simp
    have hscaleA : (p⁻¹ * q)⁻¹ * a = (p * q⁻¹) * a := by field_simp
    rw [hscaleQ] at hqMove
    rw [hscaleA] at haMove
    change Ur * Aq = Ap * Ur at hqMove
    change Ur * A = Ab * Ur at haMove
    rw [mul_sub, hqMove, haMove, sub_mul]
  have hshell : (Ap - A) * (Ap - Ab) = Ap - A := by
    have hApAp : Ap * Ap = Ap := evenIndicatorCutoff_mul_of_le (p * a) (p * a) le_rfl
    have hApAb : Ap * Ab = Ab := evenIndicatorCutoff_mul_of_le_rev
      ((p * q⁻¹) * a) (p * a) hAbAp
    have hAAp : A * Ap = A := evenIndicatorCutoff_mul_of_le a (p * a) haAp
    have hAAb : A * Ab = Ab := evenIndicatorCutoff_mul_of_le_rev
      ((p * q⁻¹) * a) a hAbA
    rw [sub_mul, mul_sub, hApAp, hApAb, mul_sub, hAAp, hAAb]
    abel
  have hU : Ur * Us = (1 : evenSubspace →L[Complex] evenSubspace) := by
    have hr : 0 < p⁻¹ * q := mul_pos (inv_pos.mpr hp0) hq0
    have hscale : q⁻¹ * p = (p⁻¹ * q)⁻¹ := by field_simp
    have hUs : Us = evenDilationCLM (p⁻¹ * q)⁻¹ (inv_pos.mpr hr) := by
      dsimp [Us]
      congr 1
    rw [hUs]
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    exact dilation_dilation_inv (p⁻¹ * q) hr (f : SoninL2)
  have hshellE : (Ap - A) * E = Ap - A := by
    have hApA : Ap * A = A := evenIndicatorCutoff_mul_of_le_rev a (p * a) haAp
    have hAA : A * A = A := evenIndicatorCutoff_mul_of_le a a le_rfl
    have hsubA : (Ap - A) * A = 0 := by
      rw [sub_mul, hApA, hAA, sub_self]
    change (Ap - A) * (1 - A) = Ap - A
    rw [mul_sub, hsubA, sub_zero, mul_one]
  change ((Ap - A) * Ur * E) * ((Aq - A) * Us * E) = Ap - A
  calc
    ((Ap - A) * Ur * E) * ((Aq - A) * Us * E) =
        (Ap - A) * Ur * (E * (Aq - A)) * Us * E := by noncomm_ring
    _ = (Ap - A) * (Ur * (Aq - A)) * Us * E := by rw [hEAq]; noncomm_ring
    _ = ((Ap - A) * (Ap - Ab)) * (Ur * Us) * E := by rw [hmove]; noncomm_ring
    _ = Ap - A := by
      rw [hshell, hU]
      simpa only [mul_one] using hshellE

theorem fourierShellTranslation_mul_rev_of_le
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hpq : p ≤ q) :
    evenFourierMixedShellTranslation a p q hp hq *
        evenFourierMixedShellTranslation a q p hq hp =
      evenFourierCutoff (p * a) - evenFourierCutoff a := by
  let R := evenFourierCutoff a
  let Rp := evenFourierCutoff (p * a)
  let Rq := evenFourierCutoff (q * a)
  let Rb := evenFourierCutoff ((p * q⁻¹) * a)
  let Ur := evenDilationCLM (p * q⁻¹)
    (mul_pos (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hq)))
  let Us := evenDilationCLM (q * p⁻¹)
    (mul_pos (zero_lt_one.trans hq) (inv_pos.mpr (zero_lt_one.trans hp)))
  let E := 1 - R
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hsmall : p * q⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hq0).2 hpq
  have haRp : a ≤ p * a := by nlinarith
  have haRq : a ≤ q * a := by nlinarith
  have hRbR : (p * q⁻¹) * a ≤ a := by nlinarith
  have hRbRp : (p * q⁻¹) * a ≤ p * a := by
    have hqi : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
    nlinarith
  have hERq : E * (Rq - R) = Rq - R := by
    have hRRq : R * Rq = R := evenFourierCutoff_mul_of_le a (q * a) haRq
    have hRR : R * R = R := evenFourierCutoff_mul_of_le a a le_rfl
    dsimp [E]
    rw [sub_mul, one_mul, mul_sub, hRRq, hRR]
    abel
  have hmove : Ur * (Rq - R) = (Rp - Rb) * Ur := by
    have hqMove := evenDilationCLM_mul_evenFourierCutoff
      (q * a) (p * q⁻¹) (mul_pos hp0 (inv_pos.mpr hq0))
    have haMove := evenDilationCLM_mul_evenFourierCutoff
      a (p * q⁻¹) (mul_pos hp0 (inv_pos.mpr hq0))
    have hscaleQ : (p * q⁻¹) * (q * a) = p * a := by field_simp
    have hscaleA : (p * q⁻¹) * a = (p * q⁻¹) * a := rfl
    rw [hscaleQ] at hqMove
    rw [hscaleA] at haMove
    change Ur * Rq = Rp * Ur at hqMove
    change Ur * R = Rb * Ur at haMove
    rw [mul_sub, hqMove, haMove, sub_mul]
  have hshell : (Rp - R) * (Rp - Rb) = Rp - R := by
    have hRpRp : Rp * Rp = Rp := evenFourierCutoff_mul_of_le (p * a) (p * a) le_rfl
    have hRpRb : Rp * Rb = Rb := evenFourierCutoff_mul_of_le_rev
      ((p * q⁻¹) * a) (p * a) hRbRp
    have hRRp : R * Rp = R := evenFourierCutoff_mul_of_le a (p * a) haRp
    have hRRb : R * Rb = Rb := evenFourierCutoff_mul_of_le_rev
      ((p * q⁻¹) * a) a hRbR
    rw [sub_mul, mul_sub, hRpRp, hRpRb, mul_sub, hRRp, hRRb]
    abel
  have hU : Ur * Us = (1 : evenSubspace →L[Complex] evenSubspace) := by
    have hr : 0 < p * q⁻¹ := mul_pos hp0 (inv_pos.mpr hq0)
    have hscale : q * p⁻¹ = (p * q⁻¹)⁻¹ := by field_simp
    have hUs : Us = evenDilationCLM (p * q⁻¹)⁻¹ (inv_pos.mpr hr) := by
      dsimp [Us]
      congr 1
    rw [hUs]
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    exact dilation_dilation_inv (p * q⁻¹) hr (f : SoninL2)
  have hshellE : (Rp - R) * E = Rp - R := by
    have hRpR : Rp * R = R := evenFourierCutoff_mul_of_le_rev a (p * a) haRp
    have hRR : R * R = R := evenFourierCutoff_mul_of_le a a le_rfl
    have hsubR : (Rp - R) * R = 0 := by
      rw [sub_mul, hRpR, hRR, sub_self]
    change (Rp - R) * (1 - R) = Rp - R
    rw [mul_sub, hsubR, sub_zero, mul_one]
  change ((Rp - R) * Ur * E) * ((Rq - R) * Us * E) = Rp - R
  calc
    ((Rp - R) * Ur * E) * ((Rq - R) * Us * E) =
        (Rp - R) * Ur * (E * (Rq - R)) * Us * E := by noncomm_ring
    _ = (Rp - R) * (Ur * (Rq - R)) * Us * E := by rw [hERq]; noncomm_ring
    _ = ((Rp - R) * (Rp - Rb)) * (Ur * Us) * E := by rw [hmove]; noncomm_ring
    _ = Rp - R := by
      rw [hshell, hU]
      simpa only [mul_one] using hshellE

theorem isCompactOperator_evenIndicatorDiff_mul_evenFourierDiff
    (s t u v : ℝ) (hs : 0 < s) (ht : 0 < t) :
    IsCompactOperator
      ((evenIndicatorCutoff s - evenIndicatorCutoff t) *
        (evenFourierCutoff u - evenFourierCutoff v)) := by
  have hsu := isCompactOperator_evenIndicatorFourierBlock s u hs
  have hsv := isCompactOperator_evenIndicatorFourierBlock s v hs
  have htu := isCompactOperator_evenIndicatorFourierBlock t u ht
  have htv := isCompactOperator_evenIndicatorFourierBlock t v ht
  have h : IsCompactOperator
      (evenIndicatorCutoff s * evenFourierCutoff u -
        evenIndicatorCutoff s * evenFourierCutoff v -
        (evenIndicatorCutoff t * evenFourierCutoff u -
          evenIndicatorCutoff t * evenFourierCutoff v)) := by
    exact (hsu.sub hsv).sub (htu.sub htv)
  have heq :
      (evenIndicatorCutoff s - evenIndicatorCutoff t) *
          (evenFourierCutoff u - evenFourierCutoff v) =
        evenIndicatorCutoff s * evenFourierCutoff u -
          evenIndicatorCutoff s * evenFourierCutoff v -
          (evenIndicatorCutoff t * evenFourierCutoff u -
            evenIndicatorCutoff t * evenFourierCutoff v) := by
    simp only [sub_mul, mul_sub]
    abel
  rw [heq]
  exact h

theorem isCompactOperator_evenFourierDiff_mul_evenIndicatorDiff
    (s t u v : ℝ) (hs : 0 < s) (ht : 0 < t) :
    IsCompactOperator
      ((evenFourierCutoff s - evenFourierCutoff t) *
        (evenIndicatorCutoff u - evenIndicatorCutoff v)) := by
  have hsu := isCompactOperator_evenFourierIndicatorBlock s u hs
  have hsv := isCompactOperator_evenFourierIndicatorBlock s v hs
  have htu := isCompactOperator_evenFourierIndicatorBlock t u ht
  have htv := isCompactOperator_evenFourierIndicatorBlock t v ht
  have h : IsCompactOperator
      (evenFourierCutoff s * evenIndicatorCutoff u -
        evenFourierCutoff s * evenIndicatorCutoff v -
        (evenFourierCutoff t * evenIndicatorCutoff u -
          evenFourierCutoff t * evenIndicatorCutoff v)) := by
    exact (hsu.sub hsv).sub (htu.sub htv)
  have heq :
      (evenFourierCutoff s - evenFourierCutoff t) *
          (evenIndicatorCutoff u - evenIndicatorCutoff v) =
        evenFourierCutoff s * evenIndicatorCutoff u -
          evenFourierCutoff s * evenIndicatorCutoff v -
          (evenFourierCutoff t * evenIndicatorCutoff u -
            evenFourierCutoff t * evenIndicatorCutoff v) := by
    simp only [sub_mul, mul_sub]
    abel
  rw [heq]
  exact h

theorem isCompactOperator_physicalShellTranslation_mul_fourierShellTranslation
    (a p q r s : ℝ) (ha : 0 < a)
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hs : 1 < s) :
    IsCompactOperator
      (evenPhysicalMixedShellTranslation a p q hp hq *
        evenFourierMixedShellTranslation a r s hr hs) := by
  let A := evenIndicatorCutoff a
  let Ap := evenIndicatorCutoff (p * a)
  let Rr := evenFourierCutoff (r * a)
  let R := evenFourierCutoff a
  let x := p⁻¹ * q
  have hx : 0 < x := mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hq)
  let Ac := evenIndicatorCutoff (x⁻¹ * a)
  let Rxr := evenFourierCutoff (x * (r * a))
  let Rx := evenFourierCutoff (x * a)
  let Ux := evenDilationCLM x hx
  let Vy := evenDilationCLM (r * s⁻¹)
    (mul_pos (zero_lt_one.trans hr) (inv_pos.mpr (zero_lt_one.trans hs)))
  let Eₐ := 1 - A
  let Eᵣ := 1 - R
  have hmoveA : Ux * Eₐ = (1 - Ac) * Ux := by
    have h := evenDilationCLM_mul_evenIndicatorCutoff a x hx
    change Ux * A = Ac * Ux at h
    dsimp [Eₐ]
    rw [mul_sub, mul_one, h, sub_mul, one_mul]
  have hmoveR : Ux * (Rr - R) = (Rxr - Rx) * Ux := by
    have hrMove := evenDilationCLM_mul_evenFourierCutoff (r * a) x hx
    have haMove := evenDilationCLM_mul_evenFourierCutoff a x hx
    change Ux * Rr = Rxr * Ux at hrMove
    change Ux * R = Rx * Ux at haMove
    rw [mul_sub, hrMove, haMove, sub_mul]
  have hdirect : IsCompactOperator ((Ap - A) * (Rxr - Rx)) := by
    exact isCompactOperator_evenIndicatorDiff_mul_evenFourierDiff
      (p * a) a (x * (r * a)) (x * a)
        (mul_pos (zero_lt_one.trans hp) ha) ha
  have hAcDiff : IsCompactOperator (Ac * (Rxr - Rx)) := by
    have hAcPos : 0 < x⁻¹ * a := mul_pos (inv_pos.mpr hx) ha
    have h₁ := isCompactOperator_evenIndicatorFourierBlock
      (x⁻¹ * a) (x * (r * a)) hAcPos
    have h₀ := isCompactOperator_evenIndicatorFourierBlock
      (x⁻¹ * a) (x * a) hAcPos
    have h : IsCompactOperator (Ac * Rxr - Ac * Rx) := by
      exact h₁.sub h₀
    have heq : Ac * (Rxr - Rx) = Ac * Rxr - Ac * Rx := by
      rw [mul_sub]
    rw [heq]
    exact h
  have hmiddle : IsCompactOperator
      (((Ap - A) * (Ac * (Rxr - Rx)) : evenSubspace →L[Complex] evenSubspace)) := by
    exact hAcDiff.clm_comp (Ap - A)
  have hB : IsCompactOperator
      (((Ap - A) * (1 - Ac) * (Rxr - Rx) : evenSubspace →L[Complex] evenSubspace)) := by
    have h : IsCompactOperator
        ((Ap - A) * (Rxr - Rx) - (Ap - A) * (Ac * (Rxr - Rx))) := by
      exact hdirect.sub hmiddle
    have heq : (Ap - A) * (1 - Ac) * (Rxr - Rx) =
        (Ap - A) * (Rxr - Rx) - (Ap - A) * (Ac * (Rxr - Rx)) := by
      have hleft : (Ap - A) * (1 - Ac) = (Ap - A) - (Ap - A) * Ac := by
        rw [mul_sub, mul_one]
      rw [hleft, sub_mul, mul_assoc]
    rw [heq]
    exact h
  have heq :
      evenPhysicalMixedShellTranslation a p q hp hq *
          evenFourierMixedShellTranslation a r s hr hs =
        ((Ap - A) * (1 - Ac) * (Rxr - Rx)) * (Ux * Vy * Eᵣ) := by
    dsimp [evenPhysicalMixedShellTranslation,
      evenFourierMixedShellTranslation, A, Ap, Rr, R, Ux, Vy, Eₐ, Eᵣ]
    change ((Ap - A) * Ux * Eₐ) * ((Rr - R) * Vy * Eᵣ) =
      ((Ap - A) * (1 - Ac) * (Rxr - Rx)) * (Ux * Vy * Eᵣ)
    calc
      ((Ap - A) * Ux * Eₐ) * ((Rr - R) * Vy * Eᵣ) =
          (Ap - A) * (Ux * Eₐ) * (Rr - R) * Vy * Eᵣ := by
            simp only [mul_assoc]
      _ = (Ap - A) * ((1 - Ac) * Ux) * (Rr - R) * Vy * Eᵣ := by
            rw [hmoveA]
      _ = (Ap - A) * (1 - Ac) * (Ux * (Rr - R)) * Vy * Eᵣ := by
            simp only [mul_assoc]
      _ = (Ap - A) * (1 - Ac) * ((Rxr - Rx) * Ux) * Vy * Eᵣ := by
            rw [hmoveR]
      _ = ((Ap - A) * (1 - Ac) * (Rxr - Rx)) * (Ux * Vy * Eᵣ) := by
            simp only [mul_assoc]
  rw [heq]
  exact hB.comp_clm (Ux * Vy * Eᵣ)

theorem isCompactOperator_fourierShellTranslation_mul_physicalShellTranslation
    (a p q r s : ℝ) (ha : 0 < a)
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hs : 1 < s) :
    IsCompactOperator
      (evenFourierMixedShellTranslation a p q hp hq *
        evenPhysicalMixedShellTranslation a r s hr hs) := by
  let R := evenFourierCutoff a
  let Rp := evenFourierCutoff (p * a)
  let Ar := evenIndicatorCutoff (r * a)
  let A := evenIndicatorCutoff a
  let x := p * q⁻¹
  have hx : 0 < x := mul_pos (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hq))
  let Rc := evenFourierCutoff (x * a)
  let Axr := evenIndicatorCutoff (x⁻¹ * (r * a))
  let Ax := evenIndicatorCutoff (x⁻¹ * a)
  let Ux := evenDilationCLM x hx
  let Vy := evenDilationCLM (r⁻¹ * s)
    (mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) (zero_lt_one.trans hs))
  let Eᵣ := 1 - R
  let Eₐ := 1 - A
  have hmoveR : Ux * Eᵣ = (1 - Rc) * Ux := by
    have h := evenDilationCLM_mul_evenFourierCutoff a x hx
    change Ux * R = Rc * Ux at h
    dsimp [Eᵣ]
    rw [mul_sub, mul_one, h, sub_mul, one_mul]
  have hmoveA : Ux * (Ar - A) = (Axr - Ax) * Ux := by
    have hrMove := evenDilationCLM_mul_evenIndicatorCutoff (r * a) x hx
    have haMove := evenDilationCLM_mul_evenIndicatorCutoff a x hx
    change Ux * Ar = Axr * Ux at hrMove
    change Ux * A = Ax * Ux at haMove
    rw [mul_sub, hrMove, haMove, sub_mul]
  have hdirect : IsCompactOperator ((Rp - R) * (Axr - Ax)) := by
    exact isCompactOperator_evenFourierDiff_mul_evenIndicatorDiff
      (p * a) a (x⁻¹ * (r * a)) (x⁻¹ * a)
        (mul_pos (zero_lt_one.trans hp) ha) ha
  have hRcDiff : IsCompactOperator (Rc * (Axr - Ax)) := by
    have hRcPos : 0 < x * a := mul_pos hx ha
    have h₁ := isCompactOperator_evenFourierIndicatorBlock
      (x * a) (x⁻¹ * (r * a)) hRcPos
    have h₀ := isCompactOperator_evenFourierIndicatorBlock
      (x * a) (x⁻¹ * a) hRcPos
    have h : IsCompactOperator (Rc * Axr - Rc * Ax) := by
      exact h₁.sub h₀
    have heq : Rc * (Axr - Ax) = Rc * Axr - Rc * Ax := by
      rw [mul_sub]
    rw [heq]
    exact h
  have hmiddle : IsCompactOperator
      (((Rp - R) * (Rc * (Axr - Ax)) : evenSubspace →L[Complex] evenSubspace)) := by
    exact hRcDiff.clm_comp (Rp - R)
  have hB : IsCompactOperator
      (((Rp - R) * (1 - Rc) * (Axr - Ax) : evenSubspace →L[Complex] evenSubspace)) := by
    have h : IsCompactOperator
        ((Rp - R) * (Axr - Ax) - (Rp - R) * (Rc * (Axr - Ax))) := by
      exact hdirect.sub hmiddle
    have heq : (Rp - R) * (1 - Rc) * (Axr - Ax) =
        (Rp - R) * (Axr - Ax) - (Rp - R) * (Rc * (Axr - Ax)) := by
      have hleft : (Rp - R) * (1 - Rc) = (Rp - R) - (Rp - R) * Rc := by
        rw [mul_sub, mul_one]
      rw [hleft, sub_mul, mul_assoc]
    rw [heq]
    exact h
  have heq :
      evenFourierMixedShellTranslation a p q hp hq *
          evenPhysicalMixedShellTranslation a r s hr hs =
        ((Rp - R) * (1 - Rc) * (Axr - Ax)) * (Ux * Vy * Eₐ) := by
    dsimp [evenFourierMixedShellTranslation,
      evenPhysicalMixedShellTranslation, R, Rp, Ar, A, Ux, Vy, Eᵣ, Eₐ]
    change ((Rp - R) * Ux * Eᵣ) * ((Ar - A) * Vy * Eₐ) =
      ((Rp - R) * (1 - Rc) * (Axr - Ax)) * (Ux * Vy * Eₐ)
    calc
      ((Rp - R) * Ux * Eᵣ) * ((Ar - A) * Vy * Eₐ) =
          (Rp - R) * (Ux * Eᵣ) * (Ar - A) * Vy * Eₐ := by
            simp only [mul_assoc]
      _ = (Rp - R) * ((1 - Rc) * Ux) * (Ar - A) * Vy * Eₐ := by
            rw [hmoveR]
      _ = (Rp - R) * (1 - Rc) * (Ux * (Ar - A)) * Vy * Eₐ := by
            simp only [mul_assoc]
      _ = (Rp - R) * (1 - Rc) * ((Axr - Ax) * Ux) * Vy * Eₐ := by
            rw [hmoveA]
      _ = ((Rp - R) * (1 - Rc) * (Axr - Ax)) * (Ux * Vy * Eₐ) := by
            simp only [mul_assoc]
  rw [heq]
  exact hB.comp_clm (Ux * Vy * Eₐ)

def evenTwoPolarizationShell (s t : ℝ) :
    evenSubspace →L[Complex] evenSubspace :=
  (evenIndicatorCutoff t - evenIndicatorCutoff s) +
    (evenFourierCutoff t - evenFourierCutoff s)

theorem compactOperatorEq_zero_of_isCompact
    {T : evenSubspace →L[Complex] evenSubspace}
    (hT : IsCompactOperator T) : T =ₖ 0 := by
  rw [CompactOperatorEq, sub_zero]
  exact hT

theorem evenSoninMixedShellTranslation_adjointProduct_compactEq_shell_of_le
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hpq : p ≤ q) :
    evenSoninMixedShellTranslation a q p hq hp *
        evenSoninMixedShellTranslation a p q hp hq =ₖ
      evenTwoPolarizationShell ((q * p⁻¹) * a) (q * a) := by
  let Pqp := evenPhysicalMixedShellTranslation a q p hq hp
  let Ppq := evenPhysicalMixedShellTranslation a p q hp hq
  let Fqp := evenFourierMixedShellTranslation a q p hq hp
  let Fpq := evenFourierMixedShellTranslation a p q hp hq
  let AS := evenIndicatorCutoff (q * a) - evenIndicatorCutoff ((q * p⁻¹) * a)
  let RS := evenFourierCutoff (q * a) - evenFourierCutoff ((q * p⁻¹) * a)
  have hPP : Pqp * Ppq =ₖ AS := CompactOperatorEq.of_eq
    (physicalShellTranslation_mul_of_le a p q ha hp hq hpq)
  have hPF : Pqp * Fpq =ₖ 0 := compactOperatorEq_zero_of_isCompact
    (isCompactOperator_physicalShellTranslation_mul_fourierShellTranslation
      a q p p q ha hq hp hp hq)
  have hFP : Fqp * Ppq =ₖ 0 := compactOperatorEq_zero_of_isCompact
    (isCompactOperator_fourierShellTranslation_mul_physicalShellTranslation
      a q p p q ha hq hp hp hq)
  have hFF : Fqp * Fpq =ₖ RS := CompactOperatorEq.of_eq
    (fourierShellTranslation_mul_of_le a p q ha hp hq hpq)
  have hsum := CompactOperatorEq.add
    (CompactOperatorEq.add hPP hPF) (CompactOperatorEq.add hFP hFF)
  dsimp [evenSoninMixedShellTranslation, evenTwoPolarizationShell,
    Pqp, Ppq, Fqp, Fpq, AS, RS]
  simpa only [mul_add, add_mul, add_zero, zero_add, add_assoc,
    add_left_comm, add_comm] using hsum

theorem evenSoninMixedShellTranslation_product_compactEq_shell_of_le
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hpq : p ≤ q) :
    evenSoninMixedShellTranslation a p q hp hq *
        evenSoninMixedShellTranslation a q p hq hp =ₖ
      evenTwoPolarizationShell a (p * a) := by
  let Ppq := evenPhysicalMixedShellTranslation a p q hp hq
  let Pqp := evenPhysicalMixedShellTranslation a q p hq hp
  let Fpq := evenFourierMixedShellTranslation a p q hp hq
  let Fqp := evenFourierMixedShellTranslation a q p hq hp
  let AS := evenIndicatorCutoff (p * a) - evenIndicatorCutoff a
  let RS := evenFourierCutoff (p * a) - evenFourierCutoff a
  have hPP : Ppq * Pqp =ₖ AS := CompactOperatorEq.of_eq
    (physicalShellTranslation_mul_rev_of_le a p q ha hp hq hpq)
  have hPF : Ppq * Fqp =ₖ 0 := compactOperatorEq_zero_of_isCompact
    (isCompactOperator_physicalShellTranslation_mul_fourierShellTranslation
      a p q q p ha hp hq hq hp)
  have hFP : Fpq * Pqp =ₖ 0 := compactOperatorEq_zero_of_isCompact
    (isCompactOperator_fourierShellTranslation_mul_physicalShellTranslation
      a p q q p ha hp hq hq hp)
  have hFF : Fpq * Fqp =ₖ RS := CompactOperatorEq.of_eq
    (fourierShellTranslation_mul_rev_of_le a p q ha hp hq hpq)
  have hsum := CompactOperatorEq.add
    (CompactOperatorEq.add hPP hPF) (CompactOperatorEq.add hFP hFF)
  dsimp [evenSoninMixedShellTranslation, evenTwoPolarizationShell,
    Ppq, Pqp, Fpq, Fqp, AS, RS]
  simpa only [mul_add, add_mul, add_zero, zero_add, add_assoc,
    add_left_comm, add_comm] using hsum

theorem adjoint_mul_clm
    (S T : evenSubspace →L[Complex] evenSubspace) :
    (S * T)† = T† * S† := by
  change ContinuousLinearMap.adjoint (S ∘L T) =
    ContinuousLinearMap.adjoint T ∘L ContinuousLinearMap.adjoint S
  exact ContinuousLinearMap.adjoint_comp S T

theorem adjoint_sub_clm
    (S T : evenSubspace →L[Complex] evenSubspace) :
    (S - T)† = S† - T† := by
  let adj : (evenSubspace →L[Complex] evenSubspace) ≃ₗᵢ⋆[Complex]
      (evenSubspace →L[Complex] evenSubspace) := ContinuousLinearMap.adjoint
  change adj (S - T) = adj S - adj T
  exact adj.map_sub S T

theorem adjoint_evenCentralSoninQuadraticCorner
    (a p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    (evenCentralSoninQuadraticCorner a p q hp hq)† =
      evenCentralSoninQuadraticCorner a q p hq hp := by
  rw [evenCentralSoninQuadraticCorner_eq_mul,
    evenCentralSoninQuadraticCorner_eq_mul]
  simp only [adjoint_mul_clm, adjoint_sub_clm, ContinuousLinearMap.adjoint_one,
    adjoint_evenCentralSoninProjection, adjoint_evenDilationSum,
    mul_assoc]

theorem evenCentralSoninQuadraticCorner_adjoint_mul_compactEq_shell_of_le
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hpq : p ≤ q) :
    (evenCentralSoninQuadraticCorner a p q hp hq)† *
        evenCentralSoninQuadraticCorner a p q hp hq =ₖ
      evenTwoPolarizationShell ((q * p⁻¹) * a) (q * a) := by
  rw [adjoint_evenCentralSoninQuadraticCorner]
  exact (CompactOperatorEq.mul
      (evenCentralSoninQuadraticCorner_compactEq_shellTranslation a q p ha hq hp)
      (evenCentralSoninQuadraticCorner_compactEq_shellTranslation a p q ha hp hq)).trans
    (evenSoninMixedShellTranslation_adjointProduct_compactEq_shell_of_le
      a p q ha hp hq hpq)

theorem evenCentralSoninQuadraticCorner_mul_adjoint_compactEq_shell_of_le
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hpq : p ≤ q) :
    evenCentralSoninQuadraticCorner a p q hp hq *
        (evenCentralSoninQuadraticCorner a p q hp hq)† =ₖ
      evenTwoPolarizationShell a (p * a) := by
  rw [adjoint_evenCentralSoninQuadraticCorner]
  exact (CompactOperatorEq.mul
      (evenCentralSoninQuadraticCorner_compactEq_shellTranslation a p q ha hp hq)
      (evenCentralSoninQuadraticCorner_compactEq_shellTranslation a q p ha hq hp)).trans
    (evenSoninMixedShellTranslation_product_compactEq_shell_of_le
      a p q ha hp hq hpq)

theorem evenCentralSoninQuadraticCorner_adjoint_mul_compactEq_shell
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    (evenCentralSoninQuadraticCorner a p q hp hq)† *
        evenCentralSoninQuadraticCorner a p q hp hq =ₖ
      evenTwoPolarizationShell ((q * (min p q)⁻¹) * a) (q * a) := by
  by_cases hpq : p ≤ q
  · simpa [min_eq_left hpq] using
      evenCentralSoninQuadraticCorner_adjoint_mul_compactEq_shell_of_le
        a p q ha hp hq hpq
  · have hqp : q ≤ p := le_of_not_ge hpq
    have h := evenCentralSoninQuadraticCorner_mul_adjoint_compactEq_shell_of_le
      a q p ha hq hp hqp
    rw [adjoint_evenCentralSoninQuadraticCorner] at h
    rw [adjoint_evenCentralSoninQuadraticCorner]
    simpa [min_eq_right hqp, (ne_of_gt (zero_lt_one.trans hq))] using h

theorem evenCentralSoninQuadraticCorner_mul_adjoint_compactEq_shell
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    evenCentralSoninQuadraticCorner a p q hp hq *
        (evenCentralSoninQuadraticCorner a p q hp hq)† =ₖ
      evenTwoPolarizationShell ((p * (min p q)⁻¹) * a) (p * a) := by
  by_cases hpq : p ≤ q
  · have h := evenCentralSoninQuadraticCorner_mul_adjoint_compactEq_shell_of_le
      a p q ha hp hq hpq
    simpa [min_eq_left hpq, (ne_of_gt (zero_lt_one.trans hp))] using h
  · have hqp : q ≤ p := le_of_not_ge hpq
    have h := evenCentralSoninQuadraticCorner_adjoint_mul_compactEq_shell_of_le
      a q p ha hq hp hqp
    rw [adjoint_evenCentralSoninQuadraticCorner] at h
    rw [adjoint_evenCentralSoninQuadraticCorner]
    simpa [min_eq_right hqp] using h

theorem evenIndicatorShell_mul_self
    (s t : ℝ) (hst : s ≤ t) :
    (evenIndicatorCutoff t - evenIndicatorCutoff s) *
        (evenIndicatorCutoff t - evenIndicatorCutoff s) =
      evenIndicatorCutoff t - evenIndicatorCutoff s := by
  have htt := evenIndicatorCutoff_mul_of_le t t le_rfl
  have hts := evenIndicatorCutoff_mul_of_le_rev s t hst
  have hst' := evenIndicatorCutoff_mul_of_le s t hst
  have hss := evenIndicatorCutoff_mul_of_le s s le_rfl
  rw [sub_mul, mul_sub, htt, hts, mul_sub, hst', hss]
  abel

theorem evenFourierShell_mul_self
    (s t : ℝ) (hst : s ≤ t) :
    (evenFourierCutoff t - evenFourierCutoff s) *
        (evenFourierCutoff t - evenFourierCutoff s) =
      evenFourierCutoff t - evenFourierCutoff s := by
  have htt := evenFourierCutoff_mul_of_le t t le_rfl
  have hts := evenFourierCutoff_mul_of_le_rev s t hst
  have hst' := evenFourierCutoff_mul_of_le s t hst
  have hss := evenFourierCutoff_mul_of_le s s le_rfl
  rw [sub_mul, mul_sub, htt, hts, mul_sub, hst', hss]
  abel

theorem adjoint_add_clm
    (S T : evenSubspace →L[Complex] evenSubspace) :
    (S + T)† = S† + T† := by
  let adj : (evenSubspace →L[Complex] evenSubspace) ≃ₗᵢ⋆[Complex]
      (evenSubspace →L[Complex] evenSubspace) := ContinuousLinearMap.adjoint
  change adj (S + T) = adj S + adj T
  exact adj.map_add S T

theorem adjoint_evenTwoPolarizationShell (s t : ℝ) :
    (evenTwoPolarizationShell s t)† = evenTwoPolarizationShell s t := by
  dsimp [evenTwoPolarizationShell]
  simp only [adjoint_add_clm, adjoint_sub_clm,
    adjoint_evenIndicatorCutoff, adjoint_evenFourierCutoff]

theorem evenTwoPolarizationShell_mul_compactEq_self
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    evenTwoPolarizationShell s t * evenTwoPolarizationShell s t =ₖ
      evenTwoPolarizationShell s t := by
  have ht : 0 < t := hs.trans_le hst
  let AS := evenIndicatorCutoff t - evenIndicatorCutoff s
  let RS := evenFourierCutoff t - evenFourierCutoff s
  have hAA : AS * AS =ₖ AS := CompactOperatorEq.of_eq
    (evenIndicatorShell_mul_self s t hst)
  have hAR : AS * RS =ₖ 0 := compactOperatorEq_zero_of_isCompact
    (isCompactOperator_evenIndicatorDiff_mul_evenFourierDiff t s t s ht hs)
  have hRA : RS * AS =ₖ 0 := compactOperatorEq_zero_of_isCompact
    (isCompactOperator_evenFourierDiff_mul_evenIndicatorDiff t s t s ht hs)
  have hRR : RS * RS =ₖ RS := CompactOperatorEq.of_eq
    (evenFourierShell_mul_self s t hst)
  have hsum := CompactOperatorEq.add
    (CompactOperatorEq.add hAA hRA) (CompactOperatorEq.add hAR hRR)
  dsimp [evenTwoPolarizationShell, AS, RS]
  simpa only [mul_add, add_mul, add_zero, zero_add, add_assoc] using hsum

theorem evenTwoPolarizationShell_isCalkinProjection
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    (evenTwoPolarizationShell s t)† = evenTwoPolarizationShell s t ∧
      evenTwoPolarizationShell s t * evenTwoPolarizationShell s t =ₖ
        evenTwoPolarizationShell s t :=
  ⟨adjoint_evenTwoPolarizationShell s t,
    evenTwoPolarizationShell_mul_compactEq_self s t hs hst⟩

def IsCalkinPartialIsometry
    (T : evenSubspace →L[Complex] evenSubspace) : Prop :=
  (T† * T) * (T† * T) =ₖ T† * T ∧
    (T * T†) * (T * T†) =ₖ T * T†

theorem compactEq_idempotent_of_compactEq
    {P S : evenSubspace →L[Complex] evenSubspace}
    (hPS : P =ₖ S) (hS : S * S =ₖ S) : P * P =ₖ P :=
  (CompactOperatorEq.mul hPS hPS).trans (hS.trans hPS.symm)

theorem evenCentralSoninQuadraticCorner_isCalkinPartialIsometry
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    IsCalkinPartialIsometry
      (evenCentralSoninQuadraticCorner a p q hp hq) := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  by_cases hpq : p ≤ q
  · have hI :=
      evenCentralSoninQuadraticCorner_adjoint_mul_compactEq_shell_of_le
        a p q ha hp hq hpq
    have hF :=
      evenCentralSoninQuadraticCorner_mul_adjoint_compactEq_shell_of_le
        a p q ha hp hq hpq
    have hsI : 0 < (q * p⁻¹) * a :=
      mul_pos (mul_pos hq0 (inv_pos.mpr hp0)) ha
    have hstI : (q * p⁻¹) * a ≤ q * a := by
      have hpinv : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
      have hscale : q * p⁻¹ ≤ q := by nlinarith
      nlinarith
    have hSI := evenTwoPolarizationShell_mul_compactEq_self
      ((q * p⁻¹) * a) (q * a) hsI hstI
    have hstF : a ≤ p * a := by nlinarith
    have hSF := evenTwoPolarizationShell_mul_compactEq_self
      a (p * a) ha hstF
    exact ⟨compactEq_idempotent_of_compactEq hI hSI,
      compactEq_idempotent_of_compactEq hF hSF⟩
  · have hqp : q ≤ p := le_of_not_ge hpq
    have hI :
        (evenCentralSoninQuadraticCorner a p q hp hq)† *
            evenCentralSoninQuadraticCorner a p q hp hq =ₖ
          evenTwoPolarizationShell a (q * a) := by
      rw [adjoint_evenCentralSoninQuadraticCorner]
      have h := evenCentralSoninQuadraticCorner_mul_adjoint_compactEq_shell_of_le
        a q p ha hq hp hqp
      rw [adjoint_evenCentralSoninQuadraticCorner] at h
      exact h
    have hF :
        evenCentralSoninQuadraticCorner a p q hp hq *
            (evenCentralSoninQuadraticCorner a p q hp hq)† =ₖ
          evenTwoPolarizationShell ((p * q⁻¹) * a) (p * a) := by
      rw [adjoint_evenCentralSoninQuadraticCorner]
      have h := evenCentralSoninQuadraticCorner_adjoint_mul_compactEq_shell_of_le
        a q p ha hq hp hqp
      rw [adjoint_evenCentralSoninQuadraticCorner] at h
      exact h
    have hstI : a ≤ q * a := by nlinarith
    have hSI := evenTwoPolarizationShell_mul_compactEq_self
      a (q * a) ha hstI
    have hsF : 0 < (p * q⁻¹) * a :=
      mul_pos (mul_pos hp0 (inv_pos.mpr hq0)) ha
    have hstF : (p * q⁻¹) * a ≤ p * a := by
      have hqinv : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
      have hscale : p * q⁻¹ ≤ p := by nlinarith
      nlinarith
    have hSF := evenTwoPolarizationShell_mul_compactEq_self
      ((p * q⁻¹) * a) (p * a) hsF hstF
    exact ⟨compactEq_idempotent_of_compactEq hI hSI,
      compactEq_idempotent_of_compactEq hF hSF⟩

end RHTower
