import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.CauchyWindowRangeDensity
import GaloisForLFunctions.HTGeometry.OrthogonalClosureCriterion
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Closed Cauchy reflection across the strip

The equation between actual Cauchy averages defines a closed, densely defined reflection.
Swapping the parameters gives its inverse. Analytic uniqueness makes every nonempty source
interval a core for the linearized graph, including where no bounded total reflection exists.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate FourierTransform ENNReal
open GaloisForLFunctions RenormalizedIntersectionTheory

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering


local notation "H" => Lp ℂ 2 (volume : Measure ℝ)
local notation "H₂" => WithLp 2 (H × H)

private theorem cauchy_commute (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re) (f : H) :
    mayerCauchyHaarOperator s hs (mayerCauchyHaarOperator r hr f) =
      mayerCauchyHaarOperator r hr (mayerCauchyHaarOperator s hs f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change HTGeometry.fourierL2 ℝ (mayerCauchyHaarOperator s hs (mayerCauchyHaarOperator r hr f)) =
    HTGeometry.fourierL2 ℝ (mayerCauchyHaarOperator r hr (mayerCauchyHaarOperator s hs f))
  apply Lp.ext
  filter_upwards [fourier_mayerCauchyHaarOperator_coeFn s hs (mayerCauchyHaarOperator r hr f),
    fourier_mayerCauchyHaarOperator_coeFn r hr f,
    fourier_mayerCauchyHaarOperator_coeFn r hr (mayerCauchyHaarOperator s hs f),
    fourier_mayerCauchyHaarOperator_coeFn s hs f] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  ring

private theorem cauchy_adjoint_commute (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re) (f : H) :
    mayerCauchyHaarOperator s hs (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) f) =
      ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) (mayerCauchyHaarOperator s hs f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change HTGeometry.fourierL2 ℝ (mayerCauchyHaarOperator s hs
      (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) f)) =
    HTGeometry.fourierL2 ℝ (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr)
      (mayerCauchyHaarOperator s hs f))
  apply Lp.ext
  filter_upwards [fourier_mayerCauchyHaarOperator_coeFn s hs
      (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) f),
    fourier_adjoint_mayerCauchyHaarOperator_coeFn r hr f,
    fourier_adjoint_mayerCauchyHaarOperator_coeFn r hr (mayerCauchyHaarOperator s hs f),
    fourier_mayerCauchyHaarOperator_coeFn s hs f] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  ring

/-- The closed linear relation `A_s y=A_r†x` of the actual Cauchy averages. -/
def mayerCauchyQuotientGraph (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re) :
    Submodule ℂ H₂ where
  carrier := {p | mayerCauchyHaarOperator s hs p.snd =
    ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) p.fst}
  zero_mem' := by simp
  add_mem' hp hq := by
    simp only [mem_setOf_eq] at hp hq ⊢
    simp only [WithLp.add_fst, WithLp.add_snd, map_add, hp, hq]
  smul_mem' c p hp := by
    simp only [mem_setOf_eq] at hp ⊢
    simp only [WithLp.smul_fst, WithLp.smul_snd, map_smul, hp]

/-- A common source gives one vector in the quotient graph. -/
def mayerCauchyGraphSource (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re) : H →L[ℂ] H₂ :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    ((mayerCauchyHaarOperator s hs).prod (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr)))

@[simp] theorem mayerCauchyGraphSource_fst (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re) (f : H) :
    (mayerCauchyGraphSource s r hs hr f).fst = mayerCauchyHaarOperator s hs f := rfl

@[simp] theorem mayerCauchyGraphSource_snd (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re) (f : H) :
    (mayerCauchyGraphSource s r hs hr f).snd =
      ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) f := rfl

/-- The quotient graph is closed, even where its operator is unbounded. -/
theorem isClosed_mayerCauchyQuotientGraph (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re) :
    IsClosed (mayerCauchyQuotientGraph s r hs hr : Set H₂) :=
  isClosed_eq ((mayerCauchyHaarOperator s hs).continuous.comp (WithLp.sndL 2 ℂ H H).continuous)
    ((ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr)).continuous.comp
      (WithLp.fstL 2 ℂ H H).continuous)

/-- Injectivity of actual averaging rules out vertical fibers in the closed graph. -/
theorem mayerCauchyQuotientGraph_single_valued (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re)
    {p q : H₂} (hp : p ∈ mayerCauchyQuotientGraph s r hs hr)
    (hq : q ∈ mayerCauchyQuotientGraph s r hs hr) (hx : p.fst = q.fst) : p = q := by
  apply (WithLp.equiv 2 (H × H)).injective
  refine Prod.ext hx ?_
  apply injective_mayerCauchyHaarOperator s hs
  exact hp.trans ((congrArg (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr)) hx).trans hq.symm)

private theorem graphSource_mem (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re) (f : H) :
    mayerCauchyGraphSource s r hs hr f ∈ mayerCauchyQuotientGraph s r hs hr :=
  cauchy_adjoint_commute s r hs hr f

private theorem cauchy_adjoint_injective (s : ℂ) (hs : 0 < s.re) :
    Function.Injective (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs)) := by
  intro f g h
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  apply Lp.ext
  have he := congrArg (HTGeometry.fourierL2 ℝ) h
  filter_upwards [fourier_adjoint_mayerCauchyHaarOperator_coeFn s hs f,
    fourier_adjoint_mayerCauchyHaarOperator_coeFn s hs g] with ξ hf hg
  rw [he, hg] at hf
  exact (mul_left_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr
    (mayerCoreMellinFactor_ne_zero_of_re_pos s hs _)) hf).symm

private theorem graph_orthogonal_row_zero (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re)
    (p : H₂) (hp : p ∈ mayerCauchyQuotientGraph s r hs hr)
    (hrow : ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) p.fst +
      mayerCauchyHaarOperator r hr p.snd = 0) : p = 0 := by
  -- The graph equation turns source orthogonality into a positive sum of adjoint squares.
  have he := congrArg (mayerCauchyHaarOperator s hs) hrow
  rw [map_add, map_zero, cauchy_commute s r hs hr, hp] at he
  have hnorm : ‖ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) p.fst‖ ^ 2 +
      ‖ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) p.fst‖ ^ 2 = 0 := by
    have hi := congrArg (fun v => (inner ℂ v p.fst).re) he
    have h1 := ContinuousLinearMap.adjoint_inner_right (mayerCauchyHaarOperator s hs)
      (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) p.fst) p.fst
    have h2 := ContinuousLinearMap.adjoint_inner_right (mayerCauchyHaarOperator r hr)
      (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) p.fst) p.fst
    have hnorms (v : H) : (inner ℂ v v).re = ‖v‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
    rw [inner_add_left, inner_zero_left, ← h1, ← h2, Complex.add_re,
      hnorms, hnorms, Complex.zero_re] at hi
    exact hi
  have hz : ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) p.fst = 0 := by
    apply norm_eq_zero.mp
    nlinarith only [hnorm, sq_nonneg
      ‖ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) p.fst‖,
      norm_nonneg (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) p.fst)]
  have hx : p.fst = 0 := cauchy_adjoint_injective s hs (hz.trans (map_zero _).symm)
  have hy : p.snd = 0 := by
    apply injective_mayerCauchyHaarOperator s hs
    rw [hp, hx, map_zero, map_zero]
  apply (WithLp.equiv 2 (H × H)).injective
  exact Prod.ext hx hy

/-- Any positive-length source interval is a core for the full closed Cauchy quotient graph. -/
theorem mayerCauchy_window_graph_core (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re)
    (a b : ℝ) (hab : a < b) :
    (Submodule.span ℂ (mayerCauchyGraphSource s r hs hr ''
      {f : H | ∀ᵐ x ∂volume, x ∉ Ioo a b → f x = 0})).topologicalClosure =
      mayerCauchyQuotientGraph s r hs hr := by
  apply HTGeometry.submodule_topologicalClosure_eq_of_orthogonal_inf_eq_bot
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, _, rfl⟩
    exact graphSource_mem s r hs hr f
  · exact isClosed_mayerCauchyQuotientGraph s r hs hr
  · apply le_antisymm ?_ bot_le
    intro p hp
    change p = 0
    apply graph_orthogonal_row_zero s r hs hr p hp.2
    -- An analytic adjoint row that vanishes on one source interval vanishes everywhere.
    obtain ⟨F₁, hF₁, he₁⟩ := adjoint_mayerCauchyHaarOperator_analytic_representative s hs p.fst
    obtain ⟨F₂, hF₂, he₂⟩ := mayerCauchyHaarOperator_analytic_representative r hr p.snd
    refine cauchyStripAnalytic_zero_of_local_orthogonality _ ?_ hab ?_
    · refine ⟨F₁ + F₂, hF₁.add hF₂, ?_⟩
      filter_upwards [he₁, he₂, Lp.coeFn_add
        (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) p.fst)
        (mayerCauchyHaarOperator r hr p.snd)] with x h1 h2 hsum
      simp only [hsum, Pi.add_apply, h1, h2]
    · intro f hf
      have h := (Submodule.mem_orthogonal _ _).mp hp.1 _ (Submodule.subset_span ⟨f, hf, rfl⟩)
      change inner ℂ (mayerCauchyHaarOperator s hs f) p.fst +
        inner ℂ (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) f) p.snd = 0 at h
      rw [inner_add_right, ContinuousLinearMap.adjoint_inner_right,
        ← ContinuousLinearMap.adjoint_inner_left]
      exact h


private theorem fieldReflection_sub (f g : H) :
    mayerFieldReflection (f - g) = mayerFieldReflection f - mayerFieldReflection g := by
  have hn := mayerFieldReflection_smul (-1) g
  simp only [neg_smul, one_smul, map_neg, map_one] at hn
  rw [sub_eq_add_neg, mayerFieldReflection_add, hn, sub_eq_add_neg]

private theorem continuous_fieldReflection : Continuous (mayerFieldReflection : H → H) := by
  have hi : Isometry (mayerFieldReflection : H → H) := by
    apply Isometry.of_dist_eq
    intro f g
    rw [dist_eq_norm, ← fieldReflection_sub, norm_mayerFieldReflection, dist_eq_norm]
  exact hi.continuous

/-- The actual conjugate-linear reflection graph, without a boundedness restriction.
The second parameter is specialized to `s♯` for arithmetic reflection. -/
def mayerCauchyClosedReflectionGraph (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re) : Set (H × H) :=
  {p | mayerCauchyHaarOperator s hs (mayerFieldReflection p.2) =
    ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr) p.1}

/-- Actual Cauchy reflection has a closed graph throughout the parameter half-plane. -/
theorem isClosed_mayerCauchyClosedReflectionGraph (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re) :
    IsClosed (mayerCauchyClosedReflectionGraph s r hs hr) :=
  isClosed_eq ((mayerCauchyHaarOperator s hs).continuous.comp
    (continuous_fieldReflection.comp continuous_snd))
    ((ContinuousLinearMap.adjoint (mayerCauchyHaarOperator r hr)).continuous.comp continuous_fst)

/-- Each input in the closed reflection domain has exactly one output. -/
theorem mayerCauchyClosedReflectionGraph_single_valued (s r : ℂ)
    (hs : 0 < s.re) (hr : 0 < r.re) {x y z : H}
    (hy : (x, y) ∈ mayerCauchyClosedReflectionGraph s r hs hr)
    (hz : (x, z) ∈ mayerCauchyClosedReflectionGraph s r hs hr) : y = z := by
  have h := injective_mayerCauchyHaarOperator s hs (hy.trans hz.symm)
  have he := congrArg mayerFieldReflection h
  simpa only [mayerFieldReflection_involutive] using he

/-- The closed graph retains the original source identity on every Haar `L²` input. -/
theorem mayerCauchyClosedReflectionGraph_source (s r : ℂ)
    (hs : 0 < s.re) (hr : 0 < r.re) (f : H) :
    (mayerCauchyHaarOperator s hs f, mayerCauchyHaarOperator r hr (mayerFieldReflection f)) ∈
      mayerCauchyClosedReflectionGraph s r hs hr := by
  change mayerCauchyHaarOperator s hs
    (mayerFieldReflection (mayerCauchyHaarOperator r hr (mayerFieldReflection f))) = _
  rw [mayerFieldReflection_cauchy_adjoint]
  exact cauchy_adjoint_commute s r hs hr f

/-- The domain of the closed arithmetic reflection is dense in physical Haar `L²`. -/
theorem dense_mayerCauchyClosedReflectionGraph_domain (s r : ℂ)
    (hs : 0 < s.re) (hr : 0 < r.re) :
    Dense {x : H | ∃ y, (x, y) ∈ mayerCauchyClosedReflectionGraph s r hs hr} := by
  apply (denseRange_mayerCauchyHaarOperator s hs).mono
  rintro _ ⟨f, rfl⟩
  exact ⟨mayerCauchyHaarOperator r hr (mayerFieldReflection f),
    mayerCauchyClosedReflectionGraph_source s r hs hr f⟩

private theorem fieldReflection_adjoint (s : ℂ) (hs : 0 < s.re) (f : H) :
    mayerFieldReflection (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) f) =
      mayerCauchyHaarOperator s hs (mayerFieldReflection f) := by
  rw [← mayerFieldReflection_cauchy_adjoint, mayerFieldReflection_involutive]

/-- Swapping the parameters gives the inverse closed reflection, including the unbounded sector. -/
theorem mayerCauchyClosedReflectionGraph_inverse (s r : ℂ)
    (hs : 0 < s.re) (hr : 0 < r.re) (x y : H) :
    (x, y) ∈ mayerCauchyClosedReflectionGraph s r hs hr ↔
      (y, x) ∈ mayerCauchyClosedReflectionGraph r s hr hs := by
  constructor <;> intro h
  · have he := congrArg mayerFieldReflection h
    rw [mayerFieldReflection_cauchy_adjoint, fieldReflection_adjoint] at he
    exact he.symm
  · have he := congrArg mayerFieldReflection h
    rw [mayerFieldReflection_cauchy_adjoint, fieldReflection_adjoint] at he
    exact he.symm

/-- Addition and conjugate scaling preserve the closed reflection graph. -/
theorem mayerCauchyClosedReflectionGraph_conjugate_linear (s r : ℂ)
    (hs : 0 < s.re) (hr : 0 < r.re) {x y u v : H}
    (hxy : (x, y) ∈ mayerCauchyClosedReflectionGraph s r hs hr)
    (huv : (u, v) ∈ mayerCauchyClosedReflectionGraph s r hs hr) (c : ℂ) :
    (x + u, y + v) ∈ mayerCauchyClosedReflectionGraph s r hs hr ∧
      (c • x, conj c • y) ∈ mayerCauchyClosedReflectionGraph s r hs hr := by
  constructor
  · change mayerCauchyHaarOperator s hs (mayerFieldReflection (y + v)) = _
    rw [mayerFieldReflection_add, map_add, hxy, huv, map_add]
  · change mayerCauchyHaarOperator s hs (mayerFieldReflection (conj c • y)) = _
    rw [mayerFieldReflection_smul, starRingEnd_self_apply, map_smul, hxy, map_smul]

/-- Arithmetic parameter reflection exchanges the actual PM core columns in the closed graph. -/
theorem mayerCauchyClosedReflectionGraph_core (s : upperMayerResonances) :
    (mayerPeriodCoreLogColumn s, mayerPeriodCoreLogColumn (reflectUpperResonance s)) ∈
      mayerCauchyClosedReflectionGraph s.1 (reflectUpperResonance s).1
        s.2.2.1 (reflectUpperResonance s).2.2.1 := by
  have h := mayerCauchyClosedReflectionGraph_source s.1 (reflectUpperResonance s).1
    s.2.2.1 (reflectUpperResonance s).2.2.1 (mayerFieldLogColumn s)
  rw [mayerCauchyHaarOperator_column, mayerFieldReflection_column,
    mayerCauchyHaarOperator_column] at h
  exact h

/-- Any closed linear relation containing one interval of source pairs contains the canonical graph. -/
theorem mayerCauchy_window_graph_minimal (s r : ℂ) (hs : 0 < s.re) (hr : 0 < r.re)
    (a b : ℝ) (hab : a < b) (V : Submodule ℂ H₂) (hV : IsClosed (V : Set H₂))
    (hsource : ∀ f : H, (∀ᵐ x ∂volume, x ∉ Ioo a b → f x = 0) →
      mayerCauchyGraphSource s r hs hr f ∈ V) :
    mayerCauchyQuotientGraph s r hs hr ≤ V := by
  rw [← mayerCauchy_window_graph_core s r hs hr a b hab]
  refine Submodule.topologicalClosure_minimal _ ?_ hV
  apply Submodule.span_le.mpr
  rintro _ ⟨f, hf, rfl⟩
  exact hsource f hf

/-- A total selection from the closed reflection graph automatically satisfies actual source compatibility. -/
theorem mayerCauchyClosedReflectionGraph_selection_compatible (s r : ℂ)
    (hs : 0 < s.re) (hr : 0 < r.re) (R : H → H)
    (hR : ∀ x, (x, R x) ∈ mayerCauchyClosedReflectionGraph s r hs hr) :
    ∀ f, R (mayerCauchyHaarOperator s hs f) = mayerCauchyHaarOperator r hr (mayerFieldReflection f) := by
  intro f
  exact mayerCauchyClosedReflectionGraph_single_valued s r hs hr
    (hR _) (mayerCauchyClosedReflectionGraph_source s r hs hr f)

/-- Below the critical line the canonical closed reflection has no bounded conjugate-linear
realization on all Haar `L²`. -/
theorem mayerCauchyClosedReflectionGraph_no_bounded_total_selection
    (s : ℂ) (hs0 : 0 < s.re) (hs : s.re < 1 / 4) :
    ¬ ∃ R : H → H,
      (∀ f g, R (f + g) = R f + R g) ∧
      (∀ (c : ℂ) f, R (c • f) = conj c • R f) ∧
      (∃ C : ℝ, ∀ f, ‖R f‖ ≤ C * ‖f‖) ∧
      (∀ f, (f, R f) ∈ mayerCauchyClosedReflectionGraph s (riemannMayerReflect s) hs0
        (by simp [riemannMayerReflect]; linarith only [hs])) := by
  rintro ⟨R, hadd, hsmul, hbound, hgraph⟩
  have hs1 : s.re < 1 / 2 := by linarith only [hs]
  have hcomp := mayerCauchyClosedReflectionGraph_selection_compatible s (riemannMayerReflect s)
    hs0 (by simp [riemannMayerReflect]; linarith only [hs]) R hgraph
  have hge := (mayerCauchy_bounded_compatible_reflection_iff s hs0 hs1).mp
    ⟨R, hadd, hsmul, hbound, hcomp⟩
  exact (not_le_of_gt hs) hge

#print axioms mayerCauchy_window_graph_core
#print axioms isClosed_mayerCauchyClosedReflectionGraph
#print axioms mayerCauchyClosedReflectionGraph_single_valued
#print axioms mayerCauchyClosedReflectionGraph_source
#print axioms dense_mayerCauchyClosedReflectionGraph_domain
#print axioms mayerCauchyClosedReflectionGraph_inverse
#print axioms mayerCauchyClosedReflectionGraph_conjugate_linear
#print axioms mayerCauchyClosedReflectionGraph_core
#print axioms mayerCauchy_window_graph_minimal
#print axioms mayerCauchyClosedReflectionGraph_no_bounded_total_selection

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
