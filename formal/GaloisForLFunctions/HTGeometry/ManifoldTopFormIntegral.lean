import Mathlib
import DifferentialGeometry.Topology.Manifold.Orientation
import DifferentialGeometry.Tensor.Exterior.Basic
import GaloisForLFunctions.HTGeometry.TopFormDeterminantScaling

/-!
# The integral of a top-degree form over an oriented manifold

Let `M` be a smooth manifold modelled on a finite-dimensional real space `E` without boundary, with
an orientation `o` (`ManifoldOrientation I M n`, `n = dim E`).  Fix on the model space a reference
orientation `e`, an evaluation frame `b` and a Haar measure `μ`.

* In the chart centred at `p` a top form `α` has value `formChartValue p α z` (an alternating map on
  `E`), and the orientation reads as `chartSign o e p z = ±1`.  The **chart density** is
  `y ↦ sign · α(b)` at `z = φ_p⁻¹ y`, and the **chart integral** is its integral over the chart
  target.
* Under a change of chart with tangent coordinate change `C`, the value transforms by
  `α_q(b) = det C · α_p(b)` and the sign by `|det C| sign_p = det C sign_q`
  (`abs_det_mul_chartSign_chartChange`); with the change-of-variables formula this gives
  **chart independence** (`chartIntegral_chartChange`) for forms supported in the overlap.
* The **integral** `topFormIntegral` sums the chart integrals of `ρ_p • α` over a smooth partition
  of unity subordinate to the chart domains.  It is linear, and by chart independence it equals
  the chart integral of any chart whose domain contains a closed set outside of which `α`
  vanishes (`topFormIntegral_eq_chartIntegral`, **locality**).
-/

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace GaloisForLFunctions.HTGeometry

theorem orientation_map_trans {R V W X : Type*} [CommRing R] [PartialOrder R]
    [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup X] [Module R X] {ι : Type*} (f : V ≃ₗ[R] W) (g : W ≃ₗ[R] X)
    (o : Orientation R V ι) :
    Orientation.map ι (f.trans g) o = Orientation.map ι g (Orientation.map ι f o) := by
  induction o using Module.Ray.ind with
  | h v hv =>
    rw [Orientation.map_apply, Orientation.map_apply, Orientation.map_apply]
    congr 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The value of a `k`-form at `z`, read in the chart centred at `p`. -/
noncomputable def formChartValue {k : ℕ} (p : M) (α : DifferentialGeometry.DifferentialForm I M k)
    (z : M) : E [⋀^Fin k]→L[ℝ] ℝ :=
  (trivializationAt (E [⋀^Fin k]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin k) E (TangentSpace I) ℝ (Bundle.Trivial M ℝ)) p
      ⟨z, α z⟩).2

theorem formChartValue_eq {k : ℕ} (p : M) (α : DifferentialGeometry.DifferentialForm I M k)
    (z : M) :
    formChartValue p α z =
      (α z).compContinuousLinearMap ((trivializationAt E (TangentSpace I) p).symmL ℝ z) :=
  DifferentialGeometry.continuousAlternatingMap_trivializationAt_apply (m := k) (x₀ := p) (x := z)
    (L := α z)

/-- Chart change of the inverse tangent trivialization. -/
theorem symmL_eq_symmL_comp_tangentCoordChange {p q z : M}
    (hp : z ∈ (extChartAt I p).source) (hq : z ∈ (extChartAt I q).source) :
    (trivializationAt E (TangentSpace I) q).symmL ℝ z =
      (trivializationAt E (TangentSpace I) p).symmL ℝ z ∘L tangentCoordChange I q p z := by
  have hlin : (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ z ∘L
      (trivializationAt E (TangentSpace I) q).symmL ℝ z = tangentCoordChange I q p z := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (by simpa
      [extChartAt_source] using hp),
      TangentBundle.symmL_trivializationAt_eq_core (by simpa [extChartAt_source] using hq)]
    apply ContinuousLinearMap.ext
    intro v
    have hw : z ∈ (extChartAt I q).source ∩ (extChartAt I z).source ∩ (extChartAt I p).source :=
      ⟨⟨hq, by simp⟩, hp⟩
    change tangentCoordChange I z p z (tangentCoordChange I q z z v) = tangentCoordChange I q p z v
    exact tangentCoordChange_comp hw
  rw [← hlin]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  exact ((trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt
    (by simpa [extChartAt_source] using hp) _).symm

/-- **Chart change of form values**: the value in chart `q` is the value in chart `p` composed
with the tangent coordinate change. -/
theorem formChartValue_chartChange {k : ℕ} {p q z : M}
    (hp : z ∈ (extChartAt I p).source) (hq : z ∈ (extChartAt I q).source)
    (α : DifferentialGeometry.DifferentialForm I M k) :
    formChartValue q α z =
      (formChartValue p α z).compContinuousLinearMap (tangentCoordChange I q p z) := by
  rw [formChartValue_eq, formChartValue_eq, symmL_eq_symmL_comp_tangentCoordChange hp hq]
  rfl

/-- Chart change of the tangent trivialization itself. -/
theorem continuousLinearMapAt_chartChange {p q z : M}
    (hp : z ∈ (extChartAt I p).source) (hq : z ∈ (extChartAt I q).source) (v : TangentSpace I z) :
    (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ z v =
      tangentCoordChange I q p z
        ((trivializationAt E (TangentSpace I) q).continuousLinearMapAt ℝ z v) := by
  have h := congrArg (fun L : E →L[ℝ] E =>
    ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ z ∘L L)
      ((trivializationAt E (TangentSpace I) q).continuousLinearMapAt ℝ z v))
    (symmL_eq_symmL_comp_tangentCoordChange hp hq)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [(trivializationAt E (TangentSpace I) q).symmL_continuousLinearMapAt
      (by simpa [extChartAt_source] using hq),
    (trivializationAt E (TangentSpace I) p).continuousLinearMapAt_symmL
      (by simpa [extChartAt_source] using hp)] at h
  exact h

theorem mem_baseSet_of_mem_extChartAt_source {p z : M} (h : z ∈ (extChartAt I p).source) :
    z ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
  simpa [extChartAt_source] using h

variable {n : ℕ}

/-- The sign of an orientation of `M` at `z`, read in the chart centred at `p`, relative to a
reference orientation `e` of the model space (zero outside the chart). -/
noncomputable def chartSign [FiniteDimensional ℝ E]
    (o : DifferentialGeometry.ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n))
    (p z : M) : ℝ :=
  open Classical in
  if h : z ∈ (trivializationAt E (TangentSpace I) p).baseSet then
    orientationSign e (o.inChart p z h)
  else 0

/-- **Orientation chart change**: `|det C| · sign_p = det C · sign_q`, with `C` the tangent
coordinate change from chart `q` to chart `p`. -/
theorem abs_det_mul_chartSign_chartChange [FiniteDimensional ℝ E]
    (o : DifferentialGeometry.ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n))
    {p q z : M} (hp : z ∈ (extChartAt I p).source) (hq : z ∈ (extChartAt I q).source) :
    |LinearMap.det (tangentCoordChange I q p z : E →ₗ[ℝ] E)| * chartSign o e p z =
      LinearMap.det (tangentCoordChange I q p z : E →ₗ[ℝ] E) * chartSign o e q z := by
  have hp' := mem_baseSet_of_mem_extChartAt_source hp
  have hq' := mem_baseSet_of_mem_extChartAt_source hq
  let tp := DifferentialGeometry.tangentChartEquiv I M p z hp'
  let tq := DifferentialGeometry.tangentChartEquiv I M q z hq'
  let C : E ≃ₗ[ℝ] E := tq.symm.trans tp
  have htq : ∀ v, tq v = (trivializationAt E (TangentSpace I) q).continuousLinearMapAt ℝ z v :=
    fun v => by
      rw [(trivializationAt E (TangentSpace I) q).continuousLinearMapAt_apply_of_mem (R := ℝ) hq' v]
      rfl
  have htp : ∀ v, tp v = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ z v :=
    fun v => by
      rw [(trivializationAt E (TangentSpace I) p).continuousLinearMapAt_apply_of_mem (R := ℝ) hp' v]
      rfl
  have hC : (C : E →ₗ[ℝ] E) = (tangentCoordChange I q p z : E →ₗ[ℝ] E) := by
    apply LinearMap.ext
    intro w
    change tp (tq.symm w) = tangentCoordChange I q p z w
    have h := continuousLinearMapAt_chartChange hp hq (tq.symm w)
    rw [← htq, tq.apply_symm_apply, ← htp] at h
    exact h
  have htrans : tq.trans C = tp := by
    ext v
    simp [C]
  have hin : o.inChart p z hp' = Orientation.map (Fin n) C (o.inChart q z hq') := by
    change Orientation.map (Fin n) tp (o.orientation z) =
      Orientation.map (Fin n) C (Orientation.map (Fin n) tq (o.orientation z))
    rw [← orientation_map_trans, htrans]
  unfold chartSign
  rw [dif_pos hp', dif_pos hq', hin, ← hC]
  exact abs_det_mul_orientationSign_map o.dimension_eq e (o.inChart q z hq') C

/-- The chart sign is locally constant on the chart domain. -/
theorem chartSign_eventuallyEq [FiniteDimensional ℝ E]
    (o : DifferentialGeometry.ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n))
    {p x : M} (hx : x ∈ (extChartAt I p).source) :
    chartSign o e p =ᶠ[𝓝 x] fun _ => chartSign o e p x := by
  have hx' := mem_baseSet_of_mem_extChartAt_source hx
  obtain ⟨U, hUo, hxU, hUs, hU⟩ := o.locally_constant p x hx'
  filter_upwards [hUo.mem_nhds hxU] with y hy
  unfold chartSign
  rw [dif_pos (hUs hy), dif_pos hx']
  congr 1
  exact hU y hy

theorem continuousOn_chartSign [FiniteDimensional ℝ E]
    (o : DifferentialGeometry.ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n)) (p : M) :
    ContinuousOn (chartSign o e p) (extChartAt I p).source := fun _ hx =>
  ((continuousAt_const.congr (chartSign_eventuallyEq o e hx).symm)).continuousWithinAt

/-! ## Chart integrals -/

variable [MeasurableSpace E] [BorelSpace E]

/-- The chart density of a top form. -/
noncomputable def chartDensity [FiniteDimensional ℝ E]
    (o : DifferentialGeometry.ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n))
    (b : Fin n → E) (p : M) (α : DifferentialGeometry.DifferentialForm I M n) (y : E) : ℝ :=
  chartSign o e p ((extChartAt I p).symm y) * formChartValue p α ((extChartAt I p).symm y) b

/-- The integral of a top form over the domain of the chart centred at `p`, with orientation
sign relative to `e`, evaluation frame `b` and Haar measure `μ` on the model space. -/
noncomputable def chartIntegral [FiniteDimensional ℝ E] (μ : Measure E)
    (o : DifferentialGeometry.ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n))
    (b : Fin n → E) (p : M) (α : DifferentialGeometry.DifferentialForm I M n) : ℝ :=
  ∫ y in (extChartAt I p).target, chartDensity o e b p α y ∂μ

omit [MeasurableSpace E] [BorelSpace E] in
theorem formChartValue_eq_zero {k : ℕ} (p : M) (α : DifferentialGeometry.DifferentialForm I M k)
    {z : M} (hz : α z = 0) : formChartValue p α z = 0 := by
  rw [formChartValue_eq, hz]
  rfl

/-- **Chart independence**: two charts give the same integral of a top form supported in the
intersection of their domains. -/
theorem chartIntegral_chartChange [FiniteDimensional ℝ E] [I.Boundaryless] (μ : Measure E)
    [μ.IsAddHaarMeasure] (o : DifferentialGeometry.ManifoldOrientation I M n)
    (e : Orientation ℝ E (Fin n)) (b : Fin n → E) {p q : M}
    (α : DifferentialGeometry.DifferentialForm I M n)
    (hα : ∀ z, α z ≠ 0 → z ∈ (extChartAt I p).source ∩ (extChartAt I q).source) :
    chartIntegral μ o e b p α = chartIntegral μ o e b q α := by
  set φp := extChartAt I p
  set φq := extChartAt I q
  let W := φp.source ∩ φq.source
  let U := φq.target ∩ φq.symm ⁻¹' φp.source
  let V := φp.target ∩ φp.symm ⁻¹' φq.source
  let ψ : E → E := φp ∘ φq.symm
  let Fp : E → ℝ := fun y => chartSign o e p (φp.symm y) * formChartValue p α (φp.symm y) b
  let Fq : E → ℝ := fun y => chartSign o e q (φq.symm y) * formChartValue q α (φq.symm y) b
  have hUo : IsOpen U :=
    (continuousOn_extChartAt_symm q).isOpen_inter_preimage (isOpen_extChartAt_target q)
      (isOpen_extChartAt_source p)
  have hVo : IsOpen V :=
    (continuousOn_extChartAt_symm p).isOpen_inter_preimage (isOpen_extChartAt_target p)
      (isOpen_extChartAt_source q)
  -- restriction to the overlap
  have hp_restrict : chartIntegral μ o e b p α = ∫ y in V, Fp y ∂μ := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (f := Fp)
      (isOpen_extChartAt_target p).measurableSet inter_subset_left fun y hy => ?_
    have hz : α (φp.symm y) = 0 := by
      by_contra hne
      exact hy.2 ⟨hy.1, (hα _ hne).2⟩
    simp [Fp, formChartValue_eq_zero p α hz]
  have hq_restrict : chartIntegral μ o e b q α = ∫ y in U, Fq y ∂μ := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (f := Fq)
      (isOpen_extChartAt_target q).measurableSet inter_subset_left fun y hy => ?_
    have hz : α (φq.symm y) = 0 := by
      by_contra hne
      exact hy.2 ⟨hy.1, (hα _ hne).1⟩
    simp [Fq, formChartValue_eq_zero q α hz]
  -- the overlap images correspond under the transition map
  have himage : ψ '' U = V := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxt, hxs⟩, rfl⟩
      have hxq : φq.symm x ∈ φq.source := φq.map_target hxt
      refine ⟨φp.map_source hxs, ?_⟩
      change φp.symm (φp (φq.symm x)) ∈ φq.source
      rw [φp.left_inv hxs]
      exact hxq
    · rintro ⟨hyt, hys⟩
      have hyp : φp.symm y ∈ φp.source := φp.map_target hyt
      refine ⟨φq (φp.symm y), ⟨φq.map_source hys, ?_⟩, ?_⟩
      · change φq.symm (φq (φp.symm y)) ∈ φp.source
        rw [φq.left_inv hys]
        exact hyp
      · change φp (φq.symm (φq (φp.symm y))) = y
        rw [φq.left_inv hys, φp.right_inv hyt]
  have hderiv : ∀ y ∈ U, HasFDerivWithinAt ψ (tangentCoordChange I q p (φq.symm y)) U y := by
    intro y hy
    have hz : φq.symm y ∈ φq.source ∩ φp.source := ⟨φq.map_target hy.1, hy.2⟩
    have h := hasFDerivWithinAt_tangentCoordChange (I := I) hz
    rw [ModelWithCorners.Boundaryless.range_eq_univ, hasFDerivWithinAt_univ,
      φq.right_inv hy.1] at h
    exact h.hasFDerivWithinAt
  have hinj : InjOn ψ U := by
    intro x hx y hy hxy
    have h1 : φq.symm x = φq.symm y :=
      φp.injOn hx.2 hy.2 hxy
    rw [← φq.right_inv hx.1, ← φq.right_inv hy.1, h1]
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul μ hUo.measurableSet hderiv hinj Fp
  rw [himage] at hcov
  rw [hp_restrict, hq_restrict, hcov]
  refine setIntegral_congr_fun hUo.measurableSet fun y hy => ?_
  set z := φq.symm y with hzdef
  have hzq : z ∈ φq.source := φq.map_target hy.1
  have hzp : z ∈ φp.source := hy.2
  have hψ : φp.symm (ψ y) = z := φp.left_inv hzp
  have h1 := abs_det_mul_chartSign_chartChange o e hzp hzq
  have h2 : formChartValue q α z b =
      LinearMap.det (tangentCoordChange I q p z : E →ₗ[ℝ] E) * formChartValue p α z b := by
    rw [formChartValue_chartChange hzp hzq α,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    exact topForm_apply_comp_eq_det_mul o.dimension_eq _ _ b
  show |LinearMap.det (tangentCoordChange I q p z : E →ₗ[ℝ] E)| •
      (chartSign o e p (φp.symm (ψ y)) * formChartValue p α (φp.symm (ψ y)) b) =
    chartSign o e q z * formChartValue q α z b
  rw [hψ, h2, smul_eq_mul]
  linear_combination formChartValue p α z b * h1

/-! ## Integrability and linearity of chart integrals -/

omit [MeasurableSpace E] [BorelSpace E] in
theorem formChartValue_add {k : ℕ} (p : M) (α β : DifferentialGeometry.DifferentialForm I M k)
    (z : M) : formChartValue p (α + β) z = formChartValue p α z + formChartValue p β z := by
  rw [formChartValue_eq, formChartValue_eq, formChartValue_eq]
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuousOn_formChartValue {k : ℕ} (p : M)
    (α : DifferentialGeometry.DifferentialForm I M k) :
    ContinuousOn (fun y => formChartValue p α ((extChartAt I p).symm y))
      (extChartAt I p).target :=
  (DifferentialGeometry.DifferentialForm.localRep_contDiffOn α p).continuousOn

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuousOn_chartDensity [FiniteDimensional ℝ E]
    (o : DifferentialGeometry.ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n))
    (b : Fin n → E) (p : M) (α : DifferentialGeometry.DifferentialForm I M n) :
    ContinuousOn (chartDensity o e b p α) (extChartAt I p).target := by
  have h1 : ContinuousOn (fun y => chartSign o e p ((extChartAt I p).symm y))
      (extChartAt I p).target :=
    (continuousOn_chartSign o e p).comp (continuousOn_extChartAt_symm p)
      (fun y hy => (extChartAt I p).map_target hy)
  have h2 : ContinuousOn (fun y => formChartValue p α ((extChartAt I p).symm y) b)
      (extChartAt I p).target :=
    (ContinuousAlternatingMap.apply ℝ E ℝ b).continuous.comp_continuousOn
      (continuousOn_formChartValue p α)
  exact h1.mul h2

/-- A top form vanishing outside a compact subset of a chart domain has integrable chart
density. -/
theorem integrableOn_chartDensity [FiniteDimensional ℝ E] [I.Boundaryless] (μ : Measure E)
    [μ.IsAddHaarMeasure] (o : DifferentialGeometry.ManifoldOrientation I M n)
    (e : Orientation ℝ E (Fin n)) (b : Fin n → E) {p : M}
    (α : DifferentialGeometry.DifferentialForm I M n) {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ (extChartAt I p).source) (hα : ∀ z, α z ≠ 0 → z ∈ K) :
    IntegrableOn (chartDensity o e b p α) (extChartAt I p).target μ := by
  have hKc : IsCompact ((extChartAt I p) '' K) :=
    hK.image_of_continuousOn ((continuousOn_extChartAt p).mono hKs)
  have hKt : (extChartAt I p) '' K ⊆ (extChartAt I p).target := by
    rintro _ ⟨z, hz, rfl⟩
    exact (extChartAt I p).map_source (hKs hz)
  have hint : IntegrableOn (chartDensity o e b p α) ((extChartAt I p) '' K) μ :=
    ((continuousOn_chartDensity o e b p α).mono hKt).integrableOn_compact hKc
  refine hint.of_forall_sdiff_eq_zero (isOpen_extChartAt_target p).measurableSet
    fun y hy => ?_
  have hz : α ((extChartAt I p).symm y) = 0 := by
    by_contra hne
    exact hy.2 ⟨_, hα _ hne, (extChartAt I p).right_inv hy.1⟩
  unfold chartDensity
  rw [formChartValue_eq_zero p α hz]
  simp

/-- Chart integrals are additive on top forms vanishing outside compact subsets of the chart. -/
theorem chartIntegral_add [FiniteDimensional ℝ E] [I.Boundaryless] (μ : Measure E)
    [μ.IsAddHaarMeasure] (o : DifferentialGeometry.ManifoldOrientation I M n)
    (e : Orientation ℝ E (Fin n)) (b : Fin n → E) {p : M}
    (α β : DifferentialGeometry.DifferentialForm I M n) {K L : Set M} (hK : IsCompact K)
    (hKs : K ⊆ (extChartAt I p).source) (hα : ∀ z, α z ≠ 0 → z ∈ K) (hL : IsCompact L)
    (hLs : L ⊆ (extChartAt I p).source) (hβ : ∀ z, β z ≠ 0 → z ∈ L) :
    chartIntegral μ o e b p (α + β) = chartIntegral μ o e b p α + chartIntegral μ o e b p β := by
  have h := integral_add (integrableOn_chartDensity μ o e b α hK hKs hα)
    (integrableOn_chartDensity μ o e b β hL hLs hβ)
  unfold chartIntegral
  rw [← h]
  refine setIntegral_congr_fun (isOpen_extChartAt_target p).measurableSet fun y _ => ?_
  simp only [chartDensity, formChartValue_add, ContinuousAlternatingMap.add_apply]
  ring

/-! ## Smooth weights and the global integral -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- A `k`-form multiplied by a smooth function. -/
noncomputable def weightedForm {k : ℕ} (f : C^∞⟮I, M; ℝ⟯)
    (α : DifferentialGeometry.DifferentialForm I M k) :
    DifferentialGeometry.DifferentialForm I M k :=
  ⟨fun z => f z • α z, ContMDiff.smul_section f.contMDiff α.contMDiff_toFun⟩

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem weightedForm_apply {k : ℕ} (f : C^∞⟮I, M; ℝ⟯)
    (α : DifferentialGeometry.DifferentialForm I M k) (z : M) :
    weightedForm f α z = f z • α z := rfl

omit [MeasurableSpace E] [BorelSpace E] in
theorem formChartValue_weightedForm {k : ℕ} (p : M) (f : C^∞⟮I, M; ℝ⟯)
    (α : DifferentialGeometry.DifferentialForm I M k) (z : M) :
    formChartValue p (weightedForm f α) z = f z • formChartValue p α z := by
  rw [formChartValue_eq, formChartValue_eq]
  rfl

variable (I M) in
/-- A fixed smooth partition of unity subordinate to the chart domains. -/
noncomputable def chartPartition [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] :
    SmoothPartitionOfUnity M I M univ :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose

omit [MeasurableSpace E] [BorelSpace E] in
theorem chartPartition_isSubordinate [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] :
    (chartPartition I M).IsSubordinate (fun x : M => (chartAt H x).source) :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose_spec

/-- **The integral of a top form** over an oriented manifold: the sum over a chart partition of
unity of the chart integrals of the weighted pieces. -/
noncomputable def topFormIntegral [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (μ : Measure E) (o : DifferentialGeometry.ManifoldOrientation I M n)
    (e : Orientation ℝ E (Fin n)) (b : Fin n → E)
    (α : DifferentialGeometry.DifferentialForm I M n) : ℝ :=
  ∑ᶠ p : M, chartIntegral μ o e b p (weightedForm (chartPartition I M p) α)

omit [MeasurableSpace E] [BorelSpace E] in
theorem chartDensity_weightedForm [FiniteDimensional ℝ E]
    (o : DifferentialGeometry.ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n))
    (b : Fin n → E) (p : M) (f : C^∞⟮I, M; ℝ⟯)
    (α : DifferentialGeometry.DifferentialForm I M n) (y : E) :
    chartDensity o e b p (weightedForm f α) y =
      f ((extChartAt I p).symm y) * chartDensity o e b p α y := by
  unfold chartDensity
  rw [formChartValue_weightedForm, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

omit [MeasurableSpace E] [BorelSpace E] in
theorem finite_chartPartition_support [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] :
    {p : M | (Function.support (chartPartition I M p)).Nonempty}.Finite := by
  have h := (chartPartition I M).locallyFinite.finite_nonempty_inter_compact
    (isCompact_univ (X := M))
  simpa using h

/-- **Locality**: the integral of a top form vanishing outside a closed subset of one chart
domain is its chart integral there. -/
theorem topFormIntegral_eq_chartIntegral [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    [I.Boundaryless] (μ : Measure E) [μ.IsAddHaarMeasure]
    (o : DifferentialGeometry.ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n))
    (b : Fin n → E) (α : DifferentialGeometry.DifferentialForm I M n) {q : M} {K : Set M}
    (hK : IsClosed K) (hKs : K ⊆ (extChartAt I q).source) (hα : ∀ z, α z ≠ 0 → z ∈ K) :
    topFormIntegral μ o e b α = chartIntegral μ o e b q α := by
  set ρ := chartPartition I M
  have hfin := finite_chartPartition_support (I := I) (M := M)
  set S := hfin.toFinset
  have hKc : IsCompact K := hK.isCompact
  -- each weighted piece is supported in its own chart and in `K`
  have hpiece : ∀ p : M, ∀ z, weightedForm (ρ p) α z ≠ 0 →
      z ∈ (extChartAt I p).source ∩ (extChartAt I q).source := by
    intro p z hz
    have hρ : ρ p z ≠ 0 := by
      intro h0
      apply hz
      rw [weightedForm_apply, h0, zero_smul]
    have hαz : α z ≠ 0 := by
      intro h0
      apply hz
      rw [weightedForm_apply, h0, smul_zero]
    refine ⟨?_, hKs (hα z hαz)⟩
    rw [extChartAt_source]
    exact chartPartition_isSubordinate p (subset_tsupport _ hρ)
  have hsupp : (Function.support fun p =>
      chartIntegral μ o e b p (weightedForm (ρ p) α)) ⊆ S := by
    intro p hp
    refine hfin.mem_toFinset.mpr ?_
    by_contra hne
    apply hp
    have hzero : ∀ z, ρ p z = 0 := fun z => by
      by_contra h
      exact hne ⟨z, h⟩
    unfold chartIntegral
    refine setIntegral_eq_zero_of_forall_eq_zero fun y _ => ?_
    rw [chartDensity_weightedForm, hzero, zero_mul]
  unfold topFormIntegral
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hchange : ∀ p ∈ S, chartIntegral μ o e b p (weightedForm (ρ p) α) =
      ∫ y in (extChartAt I q).target,
        ρ p ((extChartAt I q).symm y) * chartDensity o e b q α y ∂μ := by
    intro p _
    rw [chartIntegral_chartChange μ o e b (weightedForm (ρ p) α) (hpiece p)]
    unfold chartIntegral
    refine setIntegral_congr_fun (isOpen_extChartAt_target q).measurableSet fun y _ => ?_
    rw [chartDensity_weightedForm]
  rw [Finset.sum_congr rfl hchange, ← integral_finsetSum]
  · unfold chartIntegral
    refine setIntegral_congr_fun (isOpen_extChartAt_target q).measurableSet fun y _ => ?_
    rw [← Finset.sum_mul]
    have hone : ∑ p ∈ S, ρ p ((extChartAt I q).symm y) = 1 := by
      rw [← ρ.sum_eq_one (mem_univ ((extChartAt I q).symm y))]
      refine (finsum_eq_sum_of_support_subset _ fun p hp => ?_).symm
      exact hfin.mem_toFinset.mpr ⟨_, hp⟩
    rw [hone, one_mul]
  · intro p _
    have h := integrableOn_chartDensity μ o e b (weightedForm (ρ p) α) hKc hKs
      (fun z hz => hα z (by
        intro h0
        apply hz
        rw [weightedForm_apply, h0, smul_zero]))
    refine h.congr_fun (fun y _ => ?_) (isOpen_extChartAt_target q).measurableSet
    rw [chartDensity_weightedForm]

/-! ## Linearity of the global integral -/

omit [MeasurableSpace E] [BorelSpace E] in
theorem weightedForm_ne_zero_mem {k : ℕ} [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] (α : DifferentialGeometry.DifferentialForm I M k) (p z : M)
    (hz : weightedForm (chartPartition I M p) α z ≠ 0) :
    z ∈ tsupport (chartPartition I M p) := by
  refine subset_tsupport _ fun h0 => hz ?_
  rw [weightedForm_apply, h0, zero_smul]

omit [MeasurableSpace E] [BorelSpace E] in
theorem tsupport_chartPartition_subset [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] (p : M) :
    tsupport (chartPartition I M p) ⊆ (extChartAt I p).source := by
  rw [extChartAt_source]
  exact chartPartition_isSubordinate p

omit [BorelSpace E] in
theorem chartIntegral_weighted_eq_zero [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    (μ : Measure E) (o : DifferentialGeometry.ManifoldOrientation I M n)
    (e : Orientation ℝ E (Fin n)) (b : Fin n → E)
    (α : DifferentialGeometry.DifferentialForm I M n) {p : M}
    (hp : p ∉ (finite_chartPartition_support (I := I) (M := M)).toFinset) :
    chartIntegral μ o e b p (weightedForm (chartPartition I M p) α) = 0 := by
  have hzero : ∀ z, chartPartition I M p z = 0 := fun z => by
    by_contra h
    exact hp ((finite_chartPartition_support (I := I) (M := M)).mem_toFinset.mpr ⟨z, h⟩)
  unfold chartIntegral
  refine setIntegral_eq_zero_of_forall_eq_zero fun y _ => ?_
  rw [chartDensity_weightedForm, hzero, zero_mul]

omit [BorelSpace E] in
/-- The integral as a finite sum over the charts carrying the partition. -/
theorem topFormIntegral_eq_sum [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    (μ : Measure E) (o : DifferentialGeometry.ManifoldOrientation I M n)
    (e : Orientation ℝ E (Fin n)) (b : Fin n → E)
    (α : DifferentialGeometry.DifferentialForm I M n) :
    topFormIntegral μ o e b α = ∑ p ∈ (finite_chartPartition_support (I := I) (M := M)).toFinset,
      chartIntegral μ o e b p (weightedForm (chartPartition I M p) α) := by
  unfold topFormIntegral
  refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
  by_contra hne
  exact hp (chartIntegral_weighted_eq_zero μ o e b α hne)

theorem topFormIntegral_add [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    [I.Boundaryless] (μ : Measure E) [μ.IsAddHaarMeasure]
    (o : DifferentialGeometry.ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n))
    (b : Fin n → E) (α β : DifferentialGeometry.DifferentialForm I M n) :
    topFormIntegral μ o e b (α + β) = topFormIntegral μ o e b α + topFormIntegral μ o e b β := by
  rw [topFormIntegral_eq_sum, topFormIntegral_eq_sum, topFormIntegral_eq_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hK : IsCompact (tsupport (chartPartition I M p)) := (isClosed_tsupport _).isCompact
  have hw : weightedForm (chartPartition I M p) (α + β) =
      weightedForm (chartPartition I M p) α + weightedForm (chartPartition I M p) β := by
    apply ContMDiffSection.ext
    intro z
    simp [smul_add]
  rw [hw]
  exact chartIntegral_add μ o e b _ _ hK (tsupport_chartPartition_subset p)
    (weightedForm_ne_zero_mem α p) hK (tsupport_chartPartition_subset p)
    (weightedForm_ne_zero_mem β p)

omit [MeasurableSpace E] [BorelSpace E] in
theorem chartDensity_smul [FiniteDimensional ℝ E]
    (o : DifferentialGeometry.ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n))
    (b : Fin n → E) (p : M) (c : ℝ) (α : DifferentialGeometry.DifferentialForm I M n) (y : E) :
    chartDensity o e b p (c • α) y = c * chartDensity o e b p α y := by
  unfold chartDensity
  rw [formChartValue_eq, formChartValue_eq]
  change chartSign o e p _ * (c • (α ((extChartAt I p).symm y)).compContinuousLinearMap _) b = _
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

omit [BorelSpace E] in
theorem chartIntegral_smul [FiniteDimensional ℝ E] (μ : Measure E)
    (o : DifferentialGeometry.ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n))
    (b : Fin n → E) (p : M) (c : ℝ) (α : DifferentialGeometry.DifferentialForm I M n) :
    chartIntegral μ o e b p (c • α) = c * chartIntegral μ o e b p α := by
  unfold chartIntegral
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => chartDensity_smul o e b p c α y)

omit [BorelSpace E] in
theorem topFormIntegral_smul [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    (μ : Measure E) (o : DifferentialGeometry.ManifoldOrientation I M n)
    (e : Orientation ℝ E (Fin n)) (b : Fin n → E) (c : ℝ)
    (α : DifferentialGeometry.DifferentialForm I M n) :
    topFormIntegral μ o e b (c • α) = c * topFormIntegral μ o e b α := by
  rw [topFormIntegral_eq_sum, topFormIntegral_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hw : weightedForm (chartPartition I M p) (c • α) =
      c • weightedForm (chartPartition I M p) α := by
    apply ContMDiffSection.ext
    intro z
    simp only [weightedForm_apply, DifferentialGeometry.DifferentialForm.smul_apply]
    exact smul_comm _ _ _
  rw [hw, chartIntegral_smul]

omit [BorelSpace E] in
theorem topFormIntegral_zero [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    (μ : Measure E) (o : DifferentialGeometry.ManifoldOrientation I M n)
    (e : Orientation ℝ E (Fin n)) (b : Fin n → E) :
    topFormIntegral μ o e b (0 : DifferentialGeometry.DifferentialForm I M n) = 0 := by
  have h := topFormIntegral_smul μ o e b 0 (0 : DifferentialGeometry.DifferentialForm I M n)
  rw [zero_smul, zero_mul] at h
  exact h

theorem topFormIntegral_sum {ι : Type*} [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    [I.Boundaryless] (μ : Measure E) [μ.IsAddHaarMeasure]
    (o : DifferentialGeometry.ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n))
    (b : Fin n → E) (s : Finset ι) (α : ι → DifferentialGeometry.DifferentialForm I M n) :
    topFormIntegral μ o e b (∑ i ∈ s, α i) = ∑ i ∈ s, topFormIntegral μ o e b (α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [topFormIntegral_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, topFormIntegral_add, ih]

end GaloisForLFunctions.HTGeometry
