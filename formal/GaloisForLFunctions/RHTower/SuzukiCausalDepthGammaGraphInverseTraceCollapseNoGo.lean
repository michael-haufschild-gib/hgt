import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaExactKernel
import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaWeakRobinTraceNoGo
import GaloisForLFunctions.RHTower.TraceClassCyclicity
import GaloisForLFunctions.HTGeometry.OperatorTraceAdjoint
import GaloisForLFunctions.HTGeometry.OperatorAbsoluteValueBetween
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Canonical Gamma graph-inverse metric-trace collapse

For a bounded semimetric `T`, its canonical support inverse can be a genuinely unbounded closed
operator when `range T` is not closed.  This module extends the graph-inverse construction from
real to arbitrary `RCLike` Hilbert spaces and proves the exact metric cancellation

`T S_T(D) = 1/2 * (T D P_T + D† T)`

on the maximal incidence domain.  If `T` is self-adjoint and Schatten one over `ℂ`, the bounded
metric extension has trace

`Tr(T S_T(D)) = Re Tr(T D)`.

Thus neither the unbounded inverse nor its support projection amplifies the canonical metric trace.
For the actual causal-depth Gamma energy this graph correction is exactly the already-classified
bounded-observer correction.  A successful Ward producer must put linear growth and WOT blow-up in
the clock before inversion; the canonical graph inverse supplies none.
-/

noncomputable section

open Complex Filter ContinuousLinearMap
open scoped Topology

namespace RHTower

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Restriction of a bounded operator to the orthogonal complement of its kernel. -/
def rclikeSupportRestriction (T : E →L[𝕜] E) : E →ₗ.[𝕜] E :=
  T.toLinearMap.toPMap T.kerᗮ

/-- Canonical partially defined support inverse over a real or complex Hilbert space. -/
def rclikeClosedSupportInverse (T : E →L[𝕜] E) : E →ₗ.[𝕜] E :=
  (rclikeSupportRestriction T).inverse

omit [CompleteSpace E] in
theorem rclikeSupportRestriction_toFun_ker_eq_bot (T : E →L[𝕜] E) :
    LinearMap.ker (rclikeSupportRestriction T).toFun = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  rintro ⟨x, hxS⟩ hx
  apply Subtype.ext
  change x = 0
  have hxK : x ∈ T.ker := by
    change T x = 0
    exact hx
  have hxbot : x ∈ T.ker ⊓ T.kerᗮ := ⟨hxK, hxS⟩
  have : x ∈ (⊥ : Submodule 𝕜 E) := T.ker.orthogonal_disjoint.le_bot hxbot
  simpa using this

def rclikeSupportRestrictionGraphDefect (T : E →L[𝕜] E) : (E × E) →L[𝕜] E :=
  T.comp (ContinuousLinearMap.fst 𝕜 E E) - ContinuousLinearMap.snd 𝕜 E E

omit [CompleteSpace E] in
theorem rclikeSupportRestriction_graph_eq (T : E →L[𝕜] E) :
    (rclikeSupportRestriction T).graph =
      T.kerᗮ.comap (ContinuousLinearMap.fst 𝕜 E E).toLinearMap ⊓
        (rclikeSupportRestrictionGraphDefect T).ker := by
  ext p
  constructor
  · intro hp
    rw [LinearPMap.mem_graph_iff] at hp
    rcases hp with ⟨x, hxp, hxout⟩
    constructor
    · change p.1 ∈ T.kerᗮ
      rw [← hxp]
      exact x.property
    · change T p.1 - p.2 = 0
      rw [← hxp, ← hxout]
      simp [rclikeSupportRestriction]
  · rintro ⟨hpS, hpD⟩
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨p.1, hpS⟩, rfl, ?_⟩
    change T p.1 = p.2
    change T p.1 - p.2 = 0 at hpD
    exact sub_eq_zero.mp hpD

omit [CompleteSpace E] in
theorem rclikeSupportRestriction_isClosed (T : E →L[𝕜] E) :
    (rclikeSupportRestriction T).IsClosed := by
  rw [LinearPMap.IsClosed, rclikeSupportRestriction_graph_eq]
  apply IsClosed.inter
  · exact (Submodule.isClosed_orthogonal T.ker).preimage
      (ContinuousLinearMap.fst 𝕜 E E).continuous
  · exact (rclikeSupportRestrictionGraphDefect T).isClosed_ker

omit [CompleteSpace E] in
theorem rclikeClosedSupportInverse_isClosed (T : E →L[𝕜] E) :
    (rclikeClosedSupportInverse T).IsClosed := by
  exact (LinearPMap.inverse_closed_iff (rclikeSupportRestriction_toFun_ker_eq_bot T)).2
    (rclikeSupportRestriction_isClosed T)

theorem rclikeClosedSupportInverse_domain (T : E →L[𝕜] E) :
    (rclikeClosedSupportInverse T).domain = T.range := by
  rw [rclikeClosedSupportInverse, LinearPMap.inverse_domain]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    let S : Submodule 𝕜 E := T.kerᗮ
    letI : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
    letI : T.ker.HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace T.ker
    letI : CompleteSpace S := (Submodule.isClosed_orthogonal T.ker).completeSpace_coe
    letI : S.HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace S
    let sx : S := S.orthogonalProjectionOnto x
    refine ⟨sx, ?_⟩
    change T (S.starProjection x) = T x
    have hdiff : x - S.starProjection x ∈ T.ker := by
      have horth := Submodule.sub_starProjection_mem_orthogonal x (K := S)
      have hSK : Sᗮ = T.ker := by
        change T.kerᗮᗮ = T.ker
        exact Submodule.orthogonal_orthogonal T.ker
      simpa [hSK] using horth
    have hz : T (x - S.starProjection x) = 0 := hdiff
    rw [map_sub, sub_eq_zero] at hz
    exact hz.symm

omit [CompleteSpace E] in
theorem rclikeClosedSupportInverse_rightInverse
    (T : E →L[𝕜] E) (y : (rclikeClosedSupportInverse T).domain) :
    T (rclikeClosedSupportInverse T y) = y := by
  change T ((rclikeSupportRestriction T).inverse y) = y
  have hyrange : (y : E) ∈ LinearMap.range (rclikeSupportRestriction T).toFun := by
    rw [← LinearPMap.inverse_domain]
    exact y.property
  rcases hyrange with ⟨x, hx⟩
  have hinv : (rclikeSupportRestriction T).inverse y = x :=
    LinearPMap.inverse_apply_eq (rclikeSupportRestriction_toFun_ker_eq_bot T) hx
  rw [hinv]
  simpa [rclikeSupportRestriction] using! hx

/-- Orthogonal projection onto the kernel support. -/
def rclikeKernelSupportProjection (T : E →L[𝕜] E) : E →L[𝕜] E := by
  let K : Submodule 𝕜 E := T.ker
  let S : Submodule 𝕜 E := Kᗮ
  letI : CompleteSpace K := T.isClosed_ker.completeSpace_coe
  letI : K.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace K
  letI : CompleteSpace S := (Submodule.isClosed_orthogonal K).completeSpace_coe
  letI : S.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace S
  exact S.starProjection

theorem rclikeKernelSupportProjection_isSelfAdjoint (T : E →L[𝕜] E) :
    IsSelfAdjoint (rclikeKernelSupportProjection T) := by
  dsimp [rclikeKernelSupportProjection]
  exact isSelfAdjoint_starProjection T.kerᗮ

theorem rclikeKernelSupportProjection_apply_mem (T : E →L[𝕜] E) (x : E) :
    rclikeKernelSupportProjection T x ∈ T.kerᗮ := by
  dsimp [rclikeKernelSupportProjection]
  exact Submodule.starProjection_apply_mem _ _

theorem rclikeMetric_mul_kernelSupportProjection (T : E →L[𝕜] E) :
    T * rclikeKernelSupportProjection T = T := by
  ext x
  change T (rclikeKernelSupportProjection T x) = T x
  let S : Submodule 𝕜 E := T.kerᗮ
  have hdiff : x - rclikeKernelSupportProjection T x ∈ T.ker := by
    have horth : x - rclikeKernelSupportProjection T x ∈ Sᗮ := by
      dsimp [rclikeKernelSupportProjection]
      exact Submodule.sub_starProjection_mem_orthogonal x
    have hSK : Sᗮ = T.ker := by
      change T.kerᗮᗮ = T.ker
      exact Submodule.orthogonal_orthogonal T.ker
    simpa [hSK] using horth
  have hz : T (x - rclikeKernelSupportProjection T x) = 0 := hdiff
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

theorem rclikeKernelSupportProjection_mul_metric
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) :
    rclikeKernelSupportProjection T * T = T := by
  have h := congrArg star (rclikeMetric_mul_kernelSupportProjection T)
  simpa [star_mul, hT.star_eq,
    (rclikeKernelSupportProjection_isSelfAdjoint T).star_eq] using h

def rclikeGraphSemimetricIncidenceDomain
    (T D : E →L[𝕜] E) : Submodule 𝕜 E :=
  T.range.comap (star D * T).toLinearMap

def rclikeGraphSemimetricInverseTerm
    (T D : E →L[𝕜] E) : E →ₗ.[𝕜] E :=
  (rclikeClosedSupportInverse T).comp
    ((star D * T).toLinearMap.toPMap (rclikeGraphSemimetricIncidenceDomain T D))
    (fun x => by
      rw [rclikeClosedSupportInverse_domain]
      exact x.property)

def rclikeGraphSemimetricSymmetrization
    (T D : E →L[𝕜] E) : E →ₗ.[𝕜] E :=
  (2 : 𝕜)⁻¹ •
    ((rclikeKernelSupportProjection T * D *
        rclikeKernelSupportProjection T).toLinearMap +ᵥ
      rclikeGraphSemimetricInverseTerm T D)

theorem rclikeGraphSemimetricSymmetrization_domain (T D : E →L[𝕜] E) :
    (rclikeGraphSemimetricSymmetrization T D).domain =
      rclikeGraphSemimetricIncidenceDomain T D := by
  rfl

theorem rclikeGraphSemimetricSymmetrization_apply
    (T D : E →L[𝕜] E) (x : (rclikeGraphSemimetricSymmetrization T D).domain) :
    rclikeGraphSemimetricSymmetrization T D x =
      (2 : 𝕜)⁻¹ •
        (rclikeKernelSupportProjection T
            (D (rclikeKernelSupportProjection T x)) +
          rclikeClosedSupportInverse T
            ⟨star D (T x), by
              rw [rclikeClosedSupportInverse_domain]
              exact x.property⟩) := by
  rfl

/-- Multiplying the graph symmetrizer by its semimetric cancels the unbounded inverse. -/
theorem rclikeMetric_graphSemimetricSymmetrization_apply
    (T D : E →L[𝕜] E)
    (x : (rclikeGraphSemimetricSymmetrization T D).domain) :
    T (rclikeGraphSemimetricSymmetrization T D x) =
      (2 : 𝕜)⁻¹ •
        (T (D (rclikeKernelSupportProjection T x)) + star D (T x)) := by
  rw [rclikeGraphSemimetricSymmetrization_apply, map_smul, map_add]
  have hP : T (rclikeKernelSupportProjection T
      (D (rclikeKernelSupportProjection T x))) =
      T (D (rclikeKernelSupportProjection T x)) := by
    have h := congrArg (fun A : E →L[𝕜] E =>
      A (D (rclikeKernelSupportProjection T x)))
      (rclikeMetric_mul_kernelSupportProjection T)
    simpa [mul_apply_eq_comp] using h
  have hG : T (rclikeClosedSupportInverse T
      ⟨star D (T x), by
        rw [rclikeClosedSupportInverse_domain]
        exact x.property⟩) = star D (T x) :=
    rclikeClosedSupportInverse_rightInverse T _
  rw [hP, hG]

/-- Bounded extension of the metric times the canonical graph symmetrizer. -/
def graphSemimetricMetricExtension
    (T D : E →L[𝕜] E) : E →L[𝕜] E :=
  (2 : 𝕜)⁻¹ •
    (T * D * rclikeKernelSupportProjection T + star D * T)

theorem graphSemimetricMetricExtension_apply
    (T D : E →L[𝕜] E)
    (x : (rclikeGraphSemimetricSymmetrization T D).domain) :
    graphSemimetricMetricExtension T D x =
      T (rclikeGraphSemimetricSymmetrization T D x) := by
  rw [rclikeMetric_graphSemimetricSymmetrization_apply]
  rfl

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

theorem graphSemimetricMetricExtension_memSchattenClass_one
    {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T) (D : H →L[ℂ] H) :
    MemSchattenClass 1 (graphSemimetricMetricExtension T D) := by
  let P := rclikeKernelSupportProjection T
  have hTD : MemSchattenClass 1 (T ∘L D) :=
    memSchattenClass_one_comp_right hT D
  have hTDP : MemSchattenClass 1 ((T ∘L D) ∘L P) :=
    memSchattenClass_one_comp_right hTD P
  have hstarT : MemSchattenClass 1 ((star D) ∘L T) :=
    memSchattenClass_one_comp_left hT (star D)
  have hadd : MemSchattenClass 1 (((T ∘L D) ∘L P) + (star D) ∘L T) :=
    memSchattenClass_one_add
      (hTDP.isCompactOperator one_pos) (hstarT.isCompactOperator one_pos)
      hTDP hstarT
  exact memSchattenClass_one_smul hadd (2 : ℂ)⁻¹

/-- Trace-ideal blindness: the canonical unbounded graph inverse disappears from the metric trace. -/
theorem opTrace_graphSemimetricMetricExtension_eq_re
    {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T)
    (hself : IsSelfAdjoint T) (D : H →L[ℂ] H) :
    ContinuousLinearMap.opTrace (graphSemimetricMetricExtension T D) =
      (ContinuousLinearMap.opTrace (T ∘L D)).re := by
  let P := rclikeKernelSupportProjection T
  have hTD : MemSchattenClass 1 (T ∘L D) :=
    memSchattenClass_one_comp_right hT D
  have hTDP : MemSchattenClass 1 ((T ∘L D) ∘L P) :=
    memSchattenClass_one_comp_right hTD P
  have hstarT : MemSchattenClass 1 ((star D) ∘L T) :=
    memSchattenClass_one_comp_left hT (star D)
  have hfirst : ContinuousLinearMap.opTrace ((T ∘L D) ∘L P) =
      ContinuousLinearMap.opTrace (T ∘L D) := by
    calc
      ContinuousLinearMap.opTrace ((T ∘L D) ∘L P) =
          ContinuousLinearMap.opTrace (P ∘L (T ∘L D)) :=
        (hTD.one_opTrace_comp_comm P).symm
      _ = ContinuousLinearMap.opTrace (T ∘L D) := by
        congr 1
        ext x
        change P (T (D x)) = T (D x)
        have h := congrArg (fun A : H →L[ℂ] H => A (D x))
          (rclikeKernelSupportProjection_mul_metric T hself)
        simpa [mul_apply_eq_comp] using h
  have hsecond : ContinuousLinearMap.opTrace ((star D) ∘L T) =
      star (ContinuousLinearMap.opTrace (T ∘L D)) := by
    have hadj : ContinuousLinearMap.adjoint (T ∘L D) = (star D) ∘L T := by
      rw [ContinuousLinearMap.adjoint_comp]
      change star D ∘L star T = star D ∘L T
      rw [hself.star_eq]
    calc
      ContinuousLinearMap.opTrace ((star D) ∘L T) =
          ContinuousLinearMap.opTrace (ContinuousLinearMap.adjoint (T ∘L D)) := by
        rw [hadj]
      _ = star (ContinuousLinearMap.opTrace (T ∘L D)) :=
        ContinuousLinearMap.opTrace_adjoint _
  change ContinuousLinearMap.opTrace
      ((2 : ℂ)⁻¹ • (((T ∘L D) ∘L P) + (star D) ∘L T)) = _
  rw [opTrace_smul]
  rw [opTrace_add_of_memSchattenClass_one hTDP hstarT, hfirst, hsecond]
  apply Complex.ext
  · simp
    ring
  · simp

open GaloisForLFunctions.RHTower

/-- Actual Gamma graph-metric correction. -/
def suzukiCausalDepthGammaGraphMetricTraceCorrection
    (clock : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2) (N : ℕ) : ℝ :=
  (ContinuousLinearMap.opTrace
    (graphSemimetricMetricExtension
      suzukiCanonicalCausalDepthGammaEnergyOperator (clock N))).re

theorem suzukiCausalDepthGammaGraphMetricTraceCorrection_eq_boundedObserver
    (clock : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2) (N : ℕ) :
    suzukiCausalDepthGammaGraphMetricTraceCorrection clock N =
      suzukiCausalDepthGammaBoundedObserverTraceCorrection clock N := by
  unfold suzukiCausalDepthGammaGraphMetricTraceCorrection
  rw [opTrace_graphSemimetricMetricExtension_eq_re
    (IsTraceClass.memSchattenClass_one
      suzukiCanonicalCausalDepthGammaEnergyOperator_isTraceClass)
    (by
      unfold suzukiCanonicalCausalDepthGammaEnergyOperator
      unfold suzukiCausalDepthGammaEnergyOperator
      exact IsSelfAdjoint.of_nonneg
        (ContinuousLinearMap.adjoint_comp_self_nonneg _))]
  rfl

/-- Ward semiboundedness forces linear norm growth in the clock before graph inversion. -/
theorem eventually_linear_le_causalDepthGammaTraceNorm_mul_graphClockNorm_of_Ward_bddBelow
    (L : ℝ)
    (clock : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2)
    (lower : ℝ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      lower ≤ suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
          suzukiCausalDepthGammaGraphMetricTraceCorrection clock N)
        (8 * n)) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / 576 ≤
      traceNorm SuzukiCausalDepthGammaTraceL2
          suzukiCanonicalCausalDepthGammaEnergyOperator * ‖clock (8 * n)‖ := by
  apply eventually_linear_le_causalDepthGammaTraceNorm_mul_observerNorm_of_Ward_bddBelow
    L clock lower
  filter_upwards [hlower] with n hn
  simpa only [suzukiCausalDepthGammaGraphMetricTraceCorrection_eq_boundedObserver]
    using hn

/-- The canonical unbounded graph inverse creates no new uniformly bounded Gamma/Ward producer. -/
theorem no_uniformlyBounded_causalDepthGammaGraphMetricTrace_WardProducer :
    ¬ ∃ (L M lower : ℝ)
      (clock : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
        SuzukiCausalDepthGammaTraceL2),
      (∀ N, ‖clock N‖ ≤ M) ∧
      ∀ᶠ n : ℕ in atTop,
        lower ≤ suzukiRectangularWardDefect L
          (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
            suzukiCausalDepthGammaGraphMetricTraceCorrection clock N)
          (8 * n) := by
  rintro ⟨L, M, lower, clock, hclock, hlower⟩
  apply no_uniformlyBounded_causalDepthGammaTrace_WardProducer
  refine ⟨L, M, lower, clock, hclock, ?_⟩
  filter_upwards [hlower] with n hn
  simpa only [suzukiCausalDepthGammaGraphMetricTraceCorrection_eq_boundedObserver]
    using hn

/-- No WOT-bounded bounded clock can gain coercivity from the canonical graph inverse. -/
theorem no_weaklyPointwiseBounded_causalDepthGammaGraphMetricTrace_WardProducer :
    ¬ ∃ (L lower : ℝ)
      (clock : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
        SuzukiCausalDepthGammaTraceL2),
      SuzukiCausalDepthGammaObserverWeaklyPointwiseBounded clock ∧
      ∀ᶠ n : ℕ in atTop,
        lower ≤ suzukiRectangularWardDefect L
          (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
            suzukiCausalDepthGammaGraphMetricTraceCorrection clock N)
          (8 * n) := by
  rintro ⟨L, lower, clock, hclock, hlower⟩
  apply no_weaklyPointwiseBounded_causalDepthGammaTrace_WardProducer
  refine ⟨L, lower, clock, hclock, ?_⟩
  filter_upwards [hlower] with n hn
  simpa only [suzukiCausalDepthGammaGraphMetricTraceCorrection_eq_boundedObserver]
    using hn

/-- Sharp survivor: one fixed clock matrix coefficient must be unbounded. -/
theorem exists_unbounded_causalDepthGammaGraphClock_matrixCoefficient_of_Ward_bddBelow
    (L : ℝ)
    (clock : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2)
    (lower : ℝ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      lower ≤ suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
          suzukiCausalDepthGammaGraphMetricTraceCorrection clock N)
        (8 * n)) :
    ∃ x y : SuzukiCausalDepthGammaTraceL2,
      ¬ BddAbove
        (Set.range fun N : ℕ => ‖inner ℂ (clock N x) y‖) := by
  apply exists_unbounded_causalDepthGammaObserver_matrixCoefficient_of_Ward_bddBelow
    L clock lower
  filter_upwards [hlower] with n hn
  simpa only [suzukiCausalDepthGammaGraphMetricTraceCorrection_eq_boundedObserver]
    using hn

end RHTower
