import GaloisForLFunctions.HTGeometry.ConstitutiveCarrierComposition

/-!
# Three-stage downstream-kernel obstruction filtration

For `D --R--> E --S--> K --T--> A`, the cokernel of the total composite has a
canonical two-step filtration.  Its successive defect layers are controlled by the kernels of the
remaining future tails.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w x y

variable {𝕜 : Type u} {D : Type v} {E : Type w} {K : Type x} {A : Type y}
variable [Field 𝕜]
variable [AddCommGroup D] [Module 𝕜 D]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup K] [Module 𝕜 K]
variable [AddCommGroup A] [Module 𝕜 A]

def tripleCarrierFirstTransition
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    (A ⧸ LinearMap.range ((T.comp S).comp R)) →ₗ[𝕜]
      (A ⧸ LinearMap.range (T.comp S)) :=
  compositeToOuter R (T.comp S)

def tripleCarrierSecondTransition
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    (A ⧸ LinearMap.range (T.comp S)) →ₗ[𝕜]
      (A ⧸ LinearMap.range T) :=
  compositeToOuter S T

def tripleCarrierTotalTransition
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    (A ⧸ LinearMap.range ((T.comp S).comp R)) →ₗ[𝕜]
      (A ⧸ LinearMap.range T) :=
  (tripleCarrierSecondTransition S T).comp (tripleCarrierFirstTransition R S T)

def tripleCarrierFirstFiltration
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    Submodule 𝕜 (A ⧸ LinearMap.range ((T.comp S).comp R)) :=
  LinearMap.ker (tripleCarrierFirstTransition R S T)

def tripleCarrierSecondFiltration
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    Submodule 𝕜 (A ⧸ LinearMap.range ((T.comp S).comp R)) :=
  LinearMap.ker (tripleCarrierTotalTransition R S T)

theorem tripleCarrierFirstFiltration_le_second
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    tripleCarrierFirstFiltration R S T ≤ tripleCarrierSecondFiltration R S T := by
  intro z hz
  rw [tripleCarrierFirstFiltration, LinearMap.mem_ker] at hz
  rw [tripleCarrierSecondFiltration, LinearMap.mem_ker]
  change tripleCarrierSecondTransition S T (tripleCarrierFirstTransition R S T z) = 0
  rw [hz, map_zero]

def tripleCarrierFiltrationInclusion
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    tripleCarrierFirstFiltration R S T →ₗ[𝕜]
      tripleCarrierSecondFiltration R S T :=
  Submodule.inclusion (tripleCarrierFirstFiltration_le_second R S T)

def tripleCarrierMiddleLayerMap
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    tripleCarrierSecondFiltration R S T →ₗ[𝕜]
      LinearMap.ker (tripleCarrierSecondTransition S T) where
  toFun z := ⟨tripleCarrierFirstTransition R S T z.1, by
    rw [LinearMap.mem_ker]
    exact LinearMap.mem_ker.mp z.2⟩
  map_add' z z' := by ext; simp
  map_smul' c z := by ext; simp

theorem tripleCarrierFiltrationInclusion_injective
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    Function.Injective (tripleCarrierFiltrationInclusion R S T) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun z : tripleCarrierSecondFiltration R S T => z.1) hxy

theorem tripleCarrierMiddleLayerMap_surjective
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    Function.Surjective (tripleCarrierMiddleLayerMap R S T) := by
  intro y
  obtain ⟨x, hx⟩ := compositeToOuter_surjective R (T.comp S) y.1
  change tripleCarrierFirstTransition R S T x = y.1 at hx
  have htotal : x ∈ tripleCarrierSecondFiltration R S T := by
    rw [tripleCarrierSecondFiltration, LinearMap.mem_ker]
    change tripleCarrierSecondTransition S T (tripleCarrierFirstTransition R S T x) = 0
    rw [hx]
    exact LinearMap.mem_ker.mp y.2
  refine ⟨⟨x, htotal⟩, ?_⟩
  exact Subtype.ext hx

theorem range_tripleCarrierFiltrationInclusion_eq_ker_middleLayer
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    LinearMap.range (tripleCarrierFiltrationInclusion R S T) =
      LinearMap.ker (tripleCarrierMiddleLayerMap R S T) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change tripleCarrierFirstTransition R S T x.1 = 0
    exact LinearMap.mem_ker.mp x.2
  · intro hz
    rw [LinearMap.mem_ker] at hz
    have hfirst : z.1 ∈ tripleCarrierFirstFiltration R S T := by
      rw [tripleCarrierFirstFiltration, LinearMap.mem_ker]
      have hv := congrArg Subtype.val hz
      exact hv
    refine ⟨⟨z.1, hfirst⟩, ?_⟩
    exact Subtype.ext rfl

theorem tripleCarrierFirstLayer_identification
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    LinearMap.range (secondaryToComposite R (T.comp S)) =
      tripleCarrierFirstFiltration R S T := by
  exact range_secondaryToComposite_eq_ker_compositeToOuter R (T.comp S)

theorem tripleCarrierSecondLayer_identification
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    LinearMap.range (secondaryToComposite S T) =
      LinearMap.ker (tripleCarrierSecondTransition S T) := by
  exact range_secondaryToComposite_eq_ker_compositeToOuter S T

def tripleCarrierFirstLayerEquiv
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    (E ⧸ secondaryCarrierSubmodule R (T.comp S)) ≃ₗ[𝕜]
      tripleCarrierFirstFiltration R S T :=
  (LinearEquiv.ofInjective (secondaryToComposite R (T.comp S))
      (secondaryToComposite_injective R (T.comp S))).trans
    (LinearEquiv.ofEq _ _ (tripleCarrierFirstLayer_identification R S T))

def tripleCarrierSecondLocalEquiv
    (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    (K ⧸ secondaryCarrierSubmodule S T) ≃ₗ[𝕜]
      LinearMap.ker (tripleCarrierSecondTransition S T) :=
  (LinearEquiv.ofInjective (secondaryToComposite S T)
      (secondaryToComposite_injective S T)).trans
    (LinearEquiv.ofEq _ _ (tripleCarrierSecondLayer_identification S T))

def tripleCarrierMiddleGradedEquiv
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    (tripleCarrierSecondFiltration R S T ⧸
        LinearMap.ker (tripleCarrierMiddleLayerMap R S T)) ≃ₗ[𝕜]
      (K ⧸ secondaryCarrierSubmodule S T) :=
  ((tripleCarrierMiddleLayerMap R S T).quotKerEquivRange.trans
      (LinearEquiv.ofTop _
        (LinearMap.range_eq_top.mpr (tripleCarrierMiddleLayerMap_surjective R S T)))).trans
    (tripleCarrierSecondLocalEquiv S T).symm

theorem tripleCarrierTotalTransition_surjective
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    Function.Surjective (tripleCarrierTotalTransition R S T) :=
  (compositeToOuter_surjective S T).comp
    (compositeToOuter_surjective R (T.comp S))

def tripleCarrierOuterGradedEquiv
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    ((A ⧸ LinearMap.range ((T.comp S).comp R)) ⧸
        tripleCarrierSecondFiltration R S T) ≃ₗ[𝕜]
      (A ⧸ LinearMap.range T) :=
  (tripleCarrierTotalTransition R S T).quotKerEquivRange.trans
    (LinearEquiv.ofTop _
      (LinearMap.range_eq_top.mpr (tripleCarrierTotalTransition_surjective R S T)))

theorem tripleCarrierFiltration_short_exact
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    Function.Injective (tripleCarrierFiltrationInclusion R S T) ∧
      LinearMap.range (tripleCarrierFiltrationInclusion R S T) =
        LinearMap.ker (tripleCarrierMiddleLayerMap R S T) ∧
      Function.Surjective (tripleCarrierMiddleLayerMap R S T) := by
  exact ⟨tripleCarrierFiltrationInclusion_injective R S T,
    range_tripleCarrierFiltrationInclusion_eq_ker_middleLayer R S T,
    tripleCarrierMiddleLayerMap_surjective R S T⟩

theorem threeStageDownstreamKernelMechanism_closed
    (R : D →ₗ[𝕜] E) (S : E →ₗ[𝕜] K) (T : K →ₗ[𝕜] A) :
    tripleCarrierFirstFiltration R S T ≤ tripleCarrierSecondFiltration R S T ∧
      LinearMap.range (secondaryToComposite R (T.comp S)) =
        tripleCarrierFirstFiltration R S T ∧
      LinearMap.range (secondaryToComposite S T) =
        LinearMap.ker (tripleCarrierSecondTransition S T) ∧
      Nonempty ((E ⧸ secondaryCarrierSubmodule R (T.comp S)) ≃ₗ[𝕜]
        tripleCarrierFirstFiltration R S T) ∧
      Nonempty ((tripleCarrierSecondFiltration R S T ⧸
        LinearMap.ker (tripleCarrierMiddleLayerMap R S T)) ≃ₗ[𝕜]
        (K ⧸ secondaryCarrierSubmodule S T)) ∧
      Nonempty (((A ⧸ LinearMap.range ((T.comp S).comp R)) ⧸
        tripleCarrierSecondFiltration R S T) ≃ₗ[𝕜]
        (A ⧸ LinearMap.range T)) ∧
      Function.Injective (tripleCarrierFiltrationInclusion R S T) ∧
      LinearMap.range (tripleCarrierFiltrationInclusion R S T) =
        LinearMap.ker (tripleCarrierMiddleLayerMap R S T) ∧
      Function.Surjective (tripleCarrierMiddleLayerMap R S T) := by
  exact ⟨tripleCarrierFirstFiltration_le_second R S T,
    tripleCarrierFirstLayer_identification R S T,
    tripleCarrierSecondLayer_identification S T,
    ⟨tripleCarrierFirstLayerEquiv R S T⟩,
    ⟨tripleCarrierMiddleGradedEquiv R S T⟩,
    ⟨tripleCarrierOuterGradedEquiv R S T⟩,
    tripleCarrierFiltrationInclusion_injective R S T,
    range_tripleCarrierFiltrationInclusion_eq_ker_middleLayer R S T,
    tripleCarrierMiddleLayerMap_surjective R S T⟩

end

end GaloisForLFunctions.HTGeometry
