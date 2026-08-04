import GaloisForLFunctions.RHTower.CCMRationalStrongClassSpaceLFTopology
import GaloisForLFunctions.RHTower.CCMRationalContinuousTraceNormFieldCyclicContinuity
import GaloisForLFunctions.RHTower.ClosedCyclicModuleCokernel

/-!
# Natural topology on the exact CCM strong cyclic target

An exact strong chain has two simultaneous coordinates: its ambient
continuous-field projective tensor and the unique strong class-space function
representing its main-diagonal trace.  The graph topology induced by these two
coordinates is the literal topology used here.  It is neither the older
all-functions coefficientwise topology nor a topology on diagonal traces
alone.

Trace naturality makes the strong coordinate invariant under every face,
degeneracy, and rotation.  Combined with projective continuity of the ambient
operators, this supplies a complete `CyclicModule.Topology` on the exact CCM
target.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RHTower

private abbrev Field := CCMRationalContinuousTraceNormField
private abbrev Ambient (n : ℕ) := CyclicBarTensor ℂ Field n
private abbrev StrongClass := CCMRationalStrongClassSpace
private abbrev ScalarTarget := CCMRationalStrongClassSpaceScalarTarget

/-- Faithful scalar realization as a linear equivalence onto its exact range. -/
def ccmRationalStrongClassSpaceScalarEquiv :
    StrongClass ≃ₗ[ℂ] ScalarTarget :=
  LinearEquiv.ofInjective ccmRationalStrongClassSpaceEvalLinear
    ccmRationalStrongClassSpaceEvalLinear_injective

/-- Main-diagonal trace packaged in the exact scalar strong range. -/
def ccmRationalStrongDiagonalRangeLinear (n : ℕ) :
    CCMRationalStrongCyclicTarget.simplicial.degree n →ₗ[ℂ] ScalarTarget :=
  ((ccmRationalStrongDiagonalTrace n).domRestrict
      (ccmRationalStrongCyclicObjectSubmodule (.mk n))).codRestrict
    ScalarTarget fun x => x.2

/-- Unique `S(C_ℚ)` representative of a strong chain's diagonal trace. -/
def ccmRationalStrongDiagonalCoordinate (n : ℕ) :
    CCMRationalStrongCyclicTarget.simplicial.degree n →ₗ[ℂ] StrongClass :=
  ccmRationalStrongClassSpaceScalarEquiv.symm.toLinearMap.comp
    (ccmRationalStrongDiagonalRangeLinear n)

@[simp]
theorem ccmRationalStrongDiagonalCoordinate_eval
    (n : ℕ) (x : CCMRationalStrongCyclicTarget.simplicial.degree n) :
    ccmRationalStrongClassSpaceEvalLinear
        (ccmRationalStrongDiagonalCoordinate n x) =
      ccmRationalStrongDiagonalTrace n x.1 := by
  have h := ccmRationalStrongClassSpaceScalarEquiv.apply_symm_apply
    (ccmRationalStrongDiagonalRangeLinear n x)
  exact congrArg Subtype.val h

/-- Graph coordinate combining ambient projective chain and exact strong
diagonal representative. -/
def ccmRationalStrongCyclicGraphLinear (n : ℕ) :
    CCMRationalStrongCyclicTarget.simplicial.degree n →ₗ[ℂ]
      (Ambient n × StrongClass) where
  toFun x := (x.1, ccmRationalStrongDiagonalCoordinate n x)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · exact map_add (ccmRationalStrongDiagonalCoordinate n) x y
  map_smul' z x := by
    apply Prod.ext
    · rfl
    · exact map_smul (ccmRationalStrongDiagonalCoordinate n) z x

/-- Graph topology of ambient projective tensor and exact strong diagonal LF
coordinate. -/
@[reducible]
def ccmRationalStrongCyclicDegreeTopology (n : ℕ) :
    TopologicalSpace (CCMRationalStrongCyclicTarget.simplicial.degree n) := by
  letI : TopologicalSpace (Ambient n) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology n
  letI : TopologicalSpace StrongClass :=
    ccmRationalStrongClassSpaceLFTopology
  exact TopologicalSpace.induced (ccmRationalStrongCyclicGraphLinear n)
    inferInstance

theorem ccmRationalStrongCyclicDegreeContinuousAdd (n : ℕ) :
    @ContinuousAdd (CCMRationalStrongCyclicTarget.simplicial.degree n)
      (ccmRationalStrongCyclicDegreeTopology n) inferInstance := by
  letI : TopologicalSpace (Ambient n) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology n
  letI : ContinuousAdd (Ambient n) :=
    ccmRationalContinuousTraceNormFieldProjectiveContinuousAdd n
  letI : TopologicalSpace StrongClass :=
    ccmRationalStrongClassSpaceLFTopology
  letI : ContinuousAdd StrongClass :=
    ccmRationalStrongClassSpaceLFTopology_continuousAdd
  exact continuousAdd_induced (ccmRationalStrongCyclicGraphLinear n)

theorem ccmRationalStrongCyclicDegreeContinuousSMul (n : ℕ) :
    @ContinuousSMul ℂ
      (CCMRationalStrongCyclicTarget.simplicial.degree n)
      inferInstance inferInstance (ccmRationalStrongCyclicDegreeTopology n) := by
  letI : TopologicalSpace (Ambient n) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology n
  letI : ContinuousSMul ℂ (Ambient n) :=
    ccmRationalContinuousTraceNormFieldProjectiveContinuousSMul n
  letI : TopologicalSpace StrongClass :=
    ccmRationalStrongClassSpaceLFTopology
  letI : ContinuousSMul ℂ StrongClass :=
    ccmRationalStrongClassSpaceLFTopology_continuousSMul
  exact continuousSMul_induced (ccmRationalStrongCyclicGraphLinear n)

theorem continuous_ccmRationalStrongCyclicAmbientInclusion (n : ℕ) :
    @Continuous (CCMRationalStrongCyclicTarget.simplicial.degree n)
      (Ambient n) (ccmRationalStrongCyclicDegreeTopology n)
      (ccmRationalContinuousTraceNormFieldProjectiveTopology n)
      (fun x => x.1) := by
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicDegreeTopology n
  letI : TopologicalSpace (Ambient n) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology n
  letI : TopologicalSpace StrongClass :=
    ccmRationalStrongClassSpaceLFTopology
  have hGraph :
      @Continuous (CCMRationalStrongCyclicTarget.simplicial.degree n)
        (Ambient n × StrongClass)
        (ccmRationalStrongCyclicDegreeTopology n) inferInstance
        (ccmRationalStrongCyclicGraphLinear n) :=
    continuous_induced_dom
  exact continuous_fst.comp hGraph

theorem continuous_ccmRationalStrongDiagonalCoordinate (n : ℕ) :
    @Continuous (CCMRationalStrongCyclicTarget.simplicial.degree n)
      StrongClass (ccmRationalStrongCyclicDegreeTopology n)
      ccmRationalStrongClassSpaceLFTopology
      (ccmRationalStrongDiagonalCoordinate n) := by
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicDegreeTopology n
  letI : TopologicalSpace (Ambient n) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology n
  letI : TopologicalSpace StrongClass :=
    ccmRationalStrongClassSpaceLFTopology
  have hGraph :
      @Continuous (CCMRationalStrongCyclicTarget.simplicial.degree n)
        (Ambient n × StrongClass)
        (ccmRationalStrongCyclicDegreeTopology n) inferInstance
        (ccmRationalStrongCyclicGraphLinear n) :=
    continuous_induced_dom
  exact continuous_snd.comp hGraph

theorem ccmRationalStrongDiagonalCoordinate_face
    (n : ℕ) (i : Fin (n + 2))
    (x : CCMRationalStrongCyclicTarget.simplicial.degree (n + 1)) :
    ccmRationalStrongDiagonalCoordinate n
        (CCMRationalStrongCyclicTarget.simplicial.δ i x) =
      ccmRationalStrongDiagonalCoordinate (n + 1) x := by
  apply ccmRationalStrongClassSpaceEvalLinear_injective
  rw [ccmRationalStrongDiagonalCoordinate_eval,
    ccmRationalStrongDiagonalCoordinate_eval]
  change ccmRationalStrongDiagonalTrace n
      (cyclicBarFace (R := ℂ) (A := Field) i x.1) =
    ccmRationalStrongDiagonalTrace (n + 1) x.1
  exact LinearMap.congr_fun
    (ccmRationalStrongDiagonalTrace_comp_face n i) x.1

theorem ccmRationalStrongDiagonalCoordinate_degeneracy
    (n : ℕ) (i : Fin (n + 1))
    (x : CCMRationalStrongCyclicTarget.simplicial.degree n) :
    ccmRationalStrongDiagonalCoordinate (n + 1)
        (CCMRationalStrongCyclicTarget.simplicial.σ i x) =
      ccmRationalStrongDiagonalCoordinate n x := by
  apply ccmRationalStrongClassSpaceEvalLinear_injective
  rw [ccmRationalStrongDiagonalCoordinate_eval,
    ccmRationalStrongDiagonalCoordinate_eval]
  change ccmRationalStrongDiagonalTrace (n + 1)
      (cyclicBarDegeneracy (R := ℂ) (A := Field) i x.1) =
    ccmRationalStrongDiagonalTrace n x.1
  exact LinearMap.congr_fun
    (ccmRationalStrongDiagonalTrace_comp_degeneracy n i) x.1

theorem ccmRationalStrongDiagonalCoordinate_rotate
    (n : ℕ) (x : CCMRationalStrongCyclicTarget.simplicial.degree n) :
    ccmRationalStrongDiagonalCoordinate n
        (CCMRationalStrongCyclicTarget.cyclic n x) =
      ccmRationalStrongDiagonalCoordinate n x := by
  apply ccmRationalStrongClassSpaceEvalLinear_injective
  rw [ccmRationalStrongDiagonalCoordinate_eval,
    ccmRationalStrongDiagonalCoordinate_eval]
  change ccmRationalStrongDiagonalTrace n
      (cyclicBarRotate (R := ℂ) (A := Field) n x.1) =
    ccmRationalStrongDiagonalTrace n x.1
  exact LinearMap.congr_fun
    (ccmRationalStrongDiagonalTrace_comp_rotate n) x.1

theorem continuous_ccmRationalStrongCyclicFace
    {n : ℕ} (i : Fin (n + 2)) :
    @Continuous
      (CCMRationalStrongCyclicTarget.simplicial.degree (n + 1))
      (CCMRationalStrongCyclicTarget.simplicial.degree n)
      (ccmRationalStrongCyclicDegreeTopology (n + 1))
      (ccmRationalStrongCyclicDegreeTopology n)
      (CCMRationalStrongCyclicTarget.simplicial.δ i) := by
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree (n + 1)) :=
    ccmRationalStrongCyclicDegreeTopology (n + 1)
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicDegreeTopology n
  letI : TopologicalSpace (Ambient n) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology n
  letI : TopologicalSpace (Ambient (n + 1)) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology (n + 1)
  letI : TopologicalSpace StrongClass :=
    ccmRationalStrongClassSpaceLFTopology
  rw [continuous_induced_rng]
  apply Continuous.prodMk
  · exact (continuous_ccmRationalContinuousTraceNormFieldFace i).comp
      (continuous_ccmRationalStrongCyclicAmbientInclusion (n + 1))
  · rw [show (fun x => ccmRationalStrongDiagonalCoordinate n
        (CCMRationalStrongCyclicTarget.simplicial.δ i x)) =
        ccmRationalStrongDiagonalCoordinate (n + 1) by
      funext x
      exact ccmRationalStrongDiagonalCoordinate_face n i x]
    exact continuous_ccmRationalStrongDiagonalCoordinate (n + 1)

theorem continuous_ccmRationalStrongCyclicDegeneracy
    {n : ℕ} (i : Fin (n + 1)) :
    @Continuous
      (CCMRationalStrongCyclicTarget.simplicial.degree n)
      (CCMRationalStrongCyclicTarget.simplicial.degree (n + 1))
      (ccmRationalStrongCyclicDegreeTopology n)
      (ccmRationalStrongCyclicDegreeTopology (n + 1))
      (CCMRationalStrongCyclicTarget.simplicial.σ i) := by
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicDegreeTopology n
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree (n + 1)) :=
    ccmRationalStrongCyclicDegreeTopology (n + 1)
  letI : TopologicalSpace (Ambient (n + 1)) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology (n + 1)
  letI : TopologicalSpace (Ambient n) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology n
  letI : TopologicalSpace StrongClass :=
    ccmRationalStrongClassSpaceLFTopology
  rw [continuous_induced_rng]
  apply Continuous.prodMk
  · exact (continuous_ccmRationalContinuousTraceNormFieldDegeneracy i).comp
      (continuous_ccmRationalStrongCyclicAmbientInclusion n)
  · rw [show (fun x => ccmRationalStrongDiagonalCoordinate (n + 1)
        (CCMRationalStrongCyclicTarget.simplicial.σ i x)) =
        ccmRationalStrongDiagonalCoordinate n by
      funext x
      exact ccmRationalStrongDiagonalCoordinate_degeneracy n i x]
    exact continuous_ccmRationalStrongDiagonalCoordinate n

theorem continuous_ccmRationalStrongCyclicRotate (n : ℕ) :
    @Continuous (CCMRationalStrongCyclicTarget.simplicial.degree n)
      (CCMRationalStrongCyclicTarget.simplicial.degree n)
      (ccmRationalStrongCyclicDegreeTopology n)
      (ccmRationalStrongCyclicDegreeTopology n)
      (CCMRationalStrongCyclicTarget.cyclic n) := by
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicDegreeTopology n
  letI : TopologicalSpace (Ambient n) :=
    ccmRationalContinuousTraceNormFieldProjectiveTopology n
  letI : TopologicalSpace StrongClass :=
    ccmRationalStrongClassSpaceLFTopology
  rw [continuous_induced_rng]
  apply Continuous.prodMk
  · exact (continuous_ccmRationalContinuousTraceNormFieldRotate n).comp
      (continuous_ccmRationalStrongCyclicAmbientInclusion n)
  · rw [show (fun x => ccmRationalStrongDiagonalCoordinate n
        (CCMRationalStrongCyclicTarget.cyclic n x)) =
        ccmRationalStrongDiagonalCoordinate n by
      funext x
      exact ccmRationalStrongDiagonalCoordinate_rotate n x]
    exact continuous_ccmRationalStrongDiagonalCoordinate n

@[reducible]
def ccmRationalStrongCyclicObjectTopology :
    ∀ a : SimplexCategoryGenRel,
      TopologicalSpace
        (CCMRationalStrongCyclicTarget.simplicial.obj (.op a)) :=
  SimplexCategoryGenRel.rec ccmRationalStrongCyclicDegreeTopology

theorem continuous_ccmRationalStrongCyclicSimplicialUnop
    {a b : SimplexCategoryGenRel} (g : a ⟶ b) :
    @Continuous
      (CCMRationalStrongCyclicTarget.simplicial.obj (.op b))
      (CCMRationalStrongCyclicTarget.simplicial.obj (.op a))
      (ccmRationalStrongCyclicObjectTopology b)
      (ccmRationalStrongCyclicObjectTopology a)
      (CCMRationalStrongCyclicTarget.simplicial.map g.op) := by
  let P : MorphismProperty SimplexCategoryGenRel := fun a b g =>
    @Continuous
      (CCMRationalStrongCyclicTarget.simplicial.obj (.op b))
      (CCMRationalStrongCyclicTarget.simplicial.obj (.op a))
      (ccmRationalStrongCyclicObjectTopology b)
      (ccmRationalStrongCyclicObjectTopology a)
      (CCMRationalStrongCyclicTarget.simplicial.map g.op)
  apply SimplexCategoryGenRel.hom_induction P
  · intro n
    dsimp [P]
    letI : TopologicalSpace
        (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
      ccmRationalStrongCyclicDegreeTopology n
    rw [CCMRationalStrongCyclicTarget.simplicial.map_id]
    exact continuous_id
  · intro n m u i hu
    dsimp [P] at hu ⊢
    letI : TopologicalSpace
        (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
      ccmRationalStrongCyclicDegreeTopology n
    letI : TopologicalSpace
        (CCMRationalStrongCyclicTarget.simplicial.degree m) :=
      ccmRationalStrongCyclicDegreeTopology m
    letI : TopologicalSpace
        (CCMRationalStrongCyclicTarget.simplicial.degree (m + 1)) :=
      ccmRationalStrongCyclicDegreeTopology (m + 1)
    rw [Functor.map_comp]
    exact hu.comp (continuous_ccmRationalStrongCyclicFace i)
  · intro n m u i hu
    dsimp [P] at hu ⊢
    letI : TopologicalSpace
        (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
      ccmRationalStrongCyclicDegreeTopology n
    letI : TopologicalSpace
        (CCMRationalStrongCyclicTarget.simplicial.degree m) :=
      ccmRationalStrongCyclicDegreeTopology m
    letI : TopologicalSpace
        (CCMRationalStrongCyclicTarget.simplicial.degree (m + 1)) :=
      ccmRationalStrongCyclicDegreeTopology (m + 1)
    rw [Functor.map_comp]
    exact hu.comp (continuous_ccmRationalStrongCyclicDegeneracy i)

theorem continuous_ccmRationalStrongCyclicSimplicial
    {j k : SimplexCategoryGenRelᵒᵖ} (g : j ⟶ k) :
    @Continuous
      (CCMRationalStrongCyclicTarget.simplicial.obj j)
      (CCMRationalStrongCyclicTarget.simplicial.obj k)
      (ccmRationalStrongCyclicObjectTopology j.unop)
      (ccmRationalStrongCyclicObjectTopology k.unop)
      (CCMRationalStrongCyclicTarget.simplicial.map g) :=
  continuous_ccmRationalStrongCyclicSimplicialUnop g.unop

/-- Compatible graph/LF/projective topology on the exact CCM strong cyclic
target. -/
def ccmRationalStrongCyclicTopology :
    CyclicModule.Topology CCMRationalStrongCyclicTarget where
  topology := fun j => ccmRationalStrongCyclicObjectTopology j.unop
  continuousAdd j := by
    rcases j with ⟨⟨n⟩⟩
    exact ccmRationalStrongCyclicDegreeContinuousAdd n
  continuousSMul j := by
    rcases j with ⟨⟨n⟩⟩
    exact ccmRationalStrongCyclicDegreeContinuousSMul n
  simplicial_continuous g :=
    continuous_ccmRationalStrongCyclicSimplicial g
  cyclic_continuous n := continuous_ccmRationalStrongCyclicRotate n

end GaloisForLFunctions.RHTower
