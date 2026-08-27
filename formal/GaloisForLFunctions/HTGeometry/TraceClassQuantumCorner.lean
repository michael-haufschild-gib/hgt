import GaloisForLFunctions.HTGeometry.MatrixOrderedMap
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.HTGeometry.NuclearTraceLaw
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import GaloisForLFunctions.RHTower.TraceClassCyclicity
import GaloisForLFunctions.RHTower.PositiveOperatorTraceComparison
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
# Trace-class quantum corner lifts

The project already supplies the canonical Schatten-one submodule. This file uses that concrete
carrier, proves its closure under arbitrary Hilbert-space sandwiches, and packages normal,
completely-positive trace-nonincreasing operations. A certified isometric corner then yields the
literal lift `rho |-> J_j Phi(J_i† rho J_i) J_j†`, with exact recovery on valid corners and exact
typed composition.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

open ContinuousLinearMap

noncomputable section

/-- The existing concrete approximation-number Schatten-one carrier. -/
abbrev TraceClassOperator (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :=
  RHTower.schattenOneSubmodule (H := H)

variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- Bounded Hilbert sandwiches preserve the genuine approximation-number Schatten-one class. -/
theorem memSchattenClass_one_sandwich (A : H →L[ℂ] K)
    {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T) :
    RHTower.MemSchattenClass 1 ((A ∘L T) ∘L adjoint A) := by
  rw [← RHTower.memRectSchattenClass_iff_memSchattenClass 1]
  apply (RHTower.memRectSchattenClass_one_iff _).mpr
  have hTsum : Summable (fun n => RHTower.rectApproxNumber T n) :=
    (RHTower.memRectSchattenClass_one_iff _).mp
      ((RHTower.memRectSchattenClass_iff_memSchattenClass 1 T).mpr hT)
  exact RHTower.summable_rectApproxNumber_comp_right
    (RHTower.summable_rectApproxNumber_comp_left hTsum A) (adjoint A)

/-- Quantitative trace-norm ideal bound for a bounded Hilbert sandwich. -/
theorem traceNorm_sandwich_le (A : H →L[ℂ] K) (T : H →L[ℂ] H)
    (hT : RHTower.MemSchattenClass 1 T) :
    RHTower.traceNorm K ((A ∘L T) ∘L adjoint A) ≤
      (‖A‖ * ‖adjoint A‖) * RHTower.traceNorm H T := by
  have hrect : Summable (fun n => RHTower.rectApproxNumber T n) :=
    (RHTower.memRectSchattenClass_one_iff T).mp
      ((RHTower.memRectSchattenClass_iff_memSchattenClass 1 T).mpr hT)
  have hleft := RHTower.rectTraceNorm_comp_left_le hrect A
  have hleftSum := RHTower.summable_rectApproxNumber_comp_left hrect A
  calc
    RHTower.traceNorm K ((A ∘L T) ∘L adjoint A) =
        RHTower.rectTraceNorm K K ((A ∘L T) ∘L adjoint A) := rfl
    _ ≤ RHTower.rectTraceNorm H K (A ∘L T) * ‖adjoint A‖ :=
      RHTower.rectTraceNorm_comp_right_le hleftSum (adjoint A)
    _ ≤ (‖A‖ * RHTower.rectTraceNorm H H T) * ‖adjoint A‖ :=
      mul_le_mul_of_nonneg_right hleft (norm_nonneg _)
    _ = (‖A‖ * ‖adjoint A‖) * RHTower.traceNorm H T := by
      change ‖A‖ * RHTower.traceNorm H T * ‖adjoint A‖ = _
      ring

/-- Concrete trace-class action `rho |-> A rho A†` of a bounded Hilbert map. -/
def traceClassSandwich (A : H →L[ℂ] K) :
    TraceClassOperator H →ₗ[ℂ] TraceClassOperator K where
  toFun := fun T => ⟨(A ∘L (T : H →L[ℂ] H)) ∘L adjoint A,
    memSchattenClass_one_sandwich A T.property⟩
  map_add' := by
    intro S T
    apply Subtype.ext
    ext x
    simp [ContinuousLinearMap.comp_apply]
  map_smul' := by
    intro c T
    apply Subtype.ext
    ext x
    simp [ContinuousLinearMap.comp_apply]

/-- Hilbert sandwiches preserve the positive cone. -/
theorem traceClassSandwich_nonneg (A : H →L[ℂ] K) (T : H →L[ℂ] H)
    (hT : 0 ≤ T) : 0 ≤ (A ∘L T) ∘L adjoint A := by
  rw [ContinuousLinearMap.le_def, sub_zero] at hT ⊢
  rw [ContinuousLinearMap.isPositive_iff] at hT ⊢
  constructor
  · intro x y
    change inner ℂ (A (T (adjoint A x))) y =
      inner ℂ x (A (T (adjoint A y)))
    calc
      inner ℂ (A (T (adjoint A x))) y =
          inner ℂ (T (adjoint A x)) (adjoint A y) :=
        (adjoint_inner_right A _ _).symm
      _ = inner ℂ (adjoint A x) (T (adjoint A y)) :=
        hT.1 (adjoint A x) (adjoint A y)
      _ = inner ℂ x (A (T (adjoint A y))) :=
        adjoint_inner_left A _ _
  · intro x
    simpa only [comp_apply, adjoint_inner_right] using hT.2 (adjoint A x)

/-- Algebraic trace-class carrier identified with the existing trace-norm Banach carrier. -/
noncomputable def traceClassEquivSchattenOne :
    TraceClassOperator H ≃ₗ[ℂ] RHTower.SchattenOneOperator H where
  toFun T := ⟨T, T.property⟩
  invFun T := ⟨T.val, T.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A Hilbert sandwich is bounded for the genuine trace norm. -/
noncomputable def schattenOneSandwich (A : H →L[ℂ] K) :
    RHTower.SchattenOneOperator H →L[ℂ] RHTower.SchattenOneOperator K :=
  LinearMap.mkContinuous
    { toFun := fun T => ⟨(A ∘L (T : H →L[ℂ] H)) ∘L adjoint A,
        memSchattenClass_one_sandwich A T.property⟩
      map_add' := by
        intro S T
        apply RHTower.SchattenOneOperator.ext
        ext x
        simp [ContinuousLinearMap.comp_apply]
      map_smul' := by
        intro c T
        apply RHTower.SchattenOneOperator.ext
        ext x
        simp [ContinuousLinearMap.comp_apply] }
    (‖A‖ * ‖adjoint A‖) (fun T => traceNorm_sandwich_le A T T.property)

/-- Hilbert sandwiches compose exactly. -/
theorem traceClassSandwich_comp (B : K →L[ℂ] L) (A : H →L[ℂ] K)
    (ρ : TraceClassOperator H) :
    traceClassSandwich B (traceClassSandwich A ρ) =
      traceClassSandwich (B ∘L A) ρ := by
  apply Subtype.ext
  ext x
  simp [traceClassSandwich, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_comp]

/-- The identity Hilbert map acts identically on trace-class operators. -/
theorem traceClassSandwich_id (ρ : TraceClassOperator H) :
    traceClassSandwich (ContinuousLinearMap.id ℂ H) ρ = ρ := by
  apply Subtype.ext
  ext x
  simp [traceClassSandwich]

/-- A Hilbert isometry retracts its trace-class sandwich exactly. -/
theorem traceClassSandwich_adjoint_apply (J : H →L[ℂ] K)
    (hJ : adjoint J ∘L J = ContinuousLinearMap.id ℂ H)
    (ρ : TraceClassOperator H) :
    traceClassSandwich (adjoint J) (traceClassSandwich J ρ) = ρ := by
  rw [traceClassSandwich_comp]
  rw [hJ]
  exact traceClassSandwich_id ρ

/-- Rectangular cyclicity rewrites a trace-class sandwich on its source carrier. -/
theorem opTrace_sandwich (A : H →L[ℂ] K) (T : H →L[ℂ] H)
    (hT : RHTower.MemSchattenClass 1 T) :
    opTrace ((A ∘L T) ∘L adjoint A) =
      opTrace (T ∘L (adjoint A ∘L A)) := by
  obtain ⟨S, U, hS, hU, hfac⟩ := hT.one_isTraceClass
  rw [hfac]
  calc
    opTrace ((A ∘L (S ∘L U)) ∘L adjoint A) =
        opTrace ((A ∘L S) ∘L (U ∘L adjoint A)) := by
      congr 1
    _ = opTrace ((U ∘L adjoint A) ∘L (A ∘L S)) :=
      ContinuousLinearMap.opTrace_comp_comm (hS.comp_left A)
        (hU.comp_right (adjoint A))
    _ = opTrace ((U ∘L (adjoint A ∘L A)) ∘L S) := by
      congr 1
    _ = opTrace (S ∘L (U ∘L (adjoint A ∘L A))) :=
      ContinuousLinearMap.opTrace_comp_comm
        (hU.comp_right (adjoint A ∘L A)) hS
    _ = opTrace ((S ∘L U) ∘L (adjoint A ∘L A)) := by
      congr 1

/-- Positive trace-class operators, read in the ambient bounded-operator order. -/
def traceClassPositive (T : TraceClassOperator H) : Prop :=
  0 ≤ (T : H →L[ℂ] H)

/-- Quadratic form of a finite operator-valued matrix on a vector family. -/
noncomputable def traceClassMatrixQuadraticForm
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {n : Type} [Fintype n] (M : Matrix n n (TraceClassOperator H)) (x : n → H) : ℂ :=
  ∑ i, ∑ j, inner ℂ (x i) ((M i j : H →L[ℂ] H) (x j))

/-- Exact finite-level positive cone: Hermitian operator matrices with nonnegative quadratic form. -/
def traceClassMatrixCone (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (n : Type) [Fintype n] : Set (Matrix n n (TraceClassOperator H)) := by
  classical
  exact {M | (∀ i j, adjoint (M i j : H →L[ℂ] H) = (M j i : H →L[ℂ] H)) ∧
    ∀ x, 0 ≤ (traceClassMatrixQuadraticForm H M x).re}

/-- Schrödinger-picture normality: the algebraic map has a bounded trace-norm predual lift. -/
def TraceClassNormal (H K : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (φ : TraceClassOperator H →ₗ[ℂ] TraceClassOperator K) : Prop :=
  ∃ Φ : RHTower.SchattenOneOperator H →L[ℂ] RHTower.SchattenOneOperator K,
    ∀ ρ, Φ (traceClassEquivSchattenOne ρ) = traceClassEquivSchattenOne (φ ρ)

/-- Every bounded Hilbert sandwich is completely positive at all finite matrix levels. -/
theorem traceClassSandwich_completelyPositive (A : H →L[ℂ] K) :
    IsCompletelyPositive (traceClassMatrixCone H) (traceClassMatrixCone K)
      (traceClassSandwich A) := by
  intro n _ M hM
  classical
  constructor
  · intro i j
    change adjoint ((A ∘L (M i j : H →L[ℂ] H)) ∘L adjoint A) =
      (A ∘L (M j i : H →L[ℂ] H)) ∘L adjoint A
    rw [adjoint_comp, adjoint_comp, adjoint_adjoint, hM.1 i j]
    rfl
  · intro x
    have hx := hM.2 (fun i => adjoint A (x i))
    change 0 ≤ (∑ i, ∑ j,
      inner ℂ (x i) (A ((M i j : H →L[ℂ] H) (adjoint A (x j))))).re
    simpa only [traceClassMatrixQuadraticForm, adjoint_inner_left] using hx

/-- Every bounded Hilbert sandwich is positive. -/
theorem traceClassSandwich_positive (A : H →L[ℂ] K) :
    ∀ ρ, traceClassPositive ρ → traceClassPositive (traceClassSandwich A ρ) := by
  intro ρ hρ
  exact traceClassSandwich_nonneg A ρ hρ

/-- Every bounded Hilbert sandwich is monotone. -/
theorem traceClassSandwich_monotone (A : H →L[ℂ] K) : Monotone (traceClassSandwich A) := by
  intro ρ σ hρσ
  rw [← sub_nonneg]
  change 0 ≤ ((traceClassSandwich A σ - traceClassSandwich A ρ :
    TraceClassOperator K) : K →L[ℂ] K)
  have hdiff : 0 ≤ (((σ - ρ : TraceClassOperator H) : H →L[ℂ] H)) :=
    sub_nonneg.mpr hρσ
  have heq : ((traceClassSandwich A σ - traceClassSandwich A ρ :
      TraceClassOperator K) : K →L[ℂ] K) =
      (A ∘L ((σ - ρ : TraceClassOperator H) : H →L[ℂ] H)) ∘L adjoint A := by
    ext x
    simp [traceClassSandwich, ContinuousLinearMap.comp_apply]
  rw [heq]
  exact traceClassSandwich_nonneg A _ hdiff

/-- Every bounded Hilbert sandwich is normal through its trace-norm predual lift. -/
theorem traceClassSandwich_normal (A : H →L[ℂ] K) :
    TraceClassNormal H K (traceClassSandwich A) := by
  refine ⟨schattenOneSandwich A, ?_⟩
  intro ρ
  rfl

/-- A normal completely-positive trace-nonincreasing operation on genuine trace-class states. -/
structure TraceClassQuantumOperation (H K : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] where
  map : TraceClassOperator H →ₗ[ℂ] TraceClassOperator K
  completelyPositive :
    IsCompletelyPositive (traceClassMatrixCone H) (traceClassMatrixCone K) map
  positive : ∀ ρ, traceClassPositive ρ → traceClassPositive (map ρ)
  monotone : Monotone map
  traceNonincreasing : ∀ ρ, traceClassPositive ρ →
    (ContinuousLinearMap.opTrace (map ρ : K →L[ℂ] K)).re ≤
      (ContinuousLinearMap.opTrace (ρ : H →L[ℂ] H)).re
  normal : TraceClassNormal H K map

/-- Order-normality is stable under composition of monotone trace-class maps. -/
theorem traceClassNormal_comp {φ : TraceClassOperator H →ₗ[ℂ] TraceClassOperator K}
    {ψ : TraceClassOperator K →ₗ[ℂ] TraceClassOperator L}
    (hφ : TraceClassNormal H K φ) (_hφmono : Monotone φ)
    (hψ : TraceClassNormal K L ψ) :
    TraceClassNormal H L (ψ.comp φ) := by
  obtain ⟨Φ, hΦ⟩ := hφ
  obtain ⟨Ψ, hΨ⟩ := hψ
  refine ⟨Ψ.comp Φ, ?_⟩
  intro ρ
  simp only [ContinuousLinearMap.comp_apply, hΦ, hΨ, LinearMap.comp_apply]

namespace TraceClassQuantumOperation

/-- The identity normal quantum operation. -/
def id (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    TraceClassQuantumOperation H H where
  map := LinearMap.id
  completelyPositive := isCompletelyPositive_id (traceClassMatrixCone H)
  positive := by
    intro ρ hρ
    simpa using hρ
  monotone := by
    intro ρ σ hρσ
    simpa using hρσ
  traceNonincreasing := by
    intro ρ hρ
    exact le_rfl
  normal := by
    refine ⟨ContinuousLinearMap.id ℂ (RHTower.SchattenOneOperator H), ?_⟩
    intro ρ
    rfl

/-- Composition of normal completely-positive trace-nonincreasing operations. -/
def comp (ψ : TraceClassQuantumOperation K L)
    (φ : TraceClassQuantumOperation H K) : TraceClassQuantumOperation H L where
  map := ψ.map.comp φ.map
  completelyPositive := by
    intro n _ x hx
    have hEq : ampMap (ψ.map.comp φ.map) x = ampMap ψ.map (ampMap φ.map x) := by
      ext i j
      rfl
    rw [hEq]
    exact ψ.completelyPositive n _ (φ.completelyPositive n x hx)
  positive := by
    intro ρ hρ
    exact ψ.positive (φ.map ρ) (φ.positive ρ hρ)
  monotone := by
    intro ρ σ hρσ
    exact ψ.monotone (φ.monotone hρσ)
  traceNonincreasing := by
    intro ρ hρ
    exact (ψ.traceNonincreasing (φ.map ρ) (φ.positive ρ hρ)).trans
      (φ.traceNonincreasing ρ hρ)
  normal := traceClassNormal_comp φ.normal φ.monotone ψ.normal

end TraceClassQuantumOperation

/-- Real-valued operator trace of a genuine trace-class state. -/
def traceClassTrace (T : TraceClassOperator H) : ℝ :=
  (ContinuousLinearMap.opTrace (T : H →L[ℂ] H)).re

/-- Positive trace-class states have operator trace equal to their trace norm. -/
theorem traceClassTrace_eq_traceNorm (T : TraceClassOperator H)
    (hT : traceClassPositive T) :
    traceClassTrace T = RHTower.traceNorm H (T : H →L[ℂ] H) := by
  rw [RHTower.traceNorm_eq_re_opTrace_absOp T.property,
    ContinuousLinearMap.absOp_of_nonneg hT]
  rfl

/-- A trace-norm contractive Hilbert sandwich is trace-nonincreasing on positive states. -/
theorem traceClassSandwich_traceNonincreasing (A : H →L[ℂ] K)
    (hA : ‖A‖ * ‖adjoint A‖ ≤ 1) (ρ : TraceClassOperator H)
    (hρ : traceClassPositive ρ) :
    traceClassTrace (traceClassSandwich A ρ) ≤ traceClassTrace ρ := by
  have hout : traceClassPositive (traceClassSandwich A ρ) :=
    traceClassSandwich_positive A ρ hρ
  rw [traceClassTrace_eq_traceNorm _ hout, traceClassTrace_eq_traceNorm _ hρ]
  calc
    RHTower.traceNorm K
        ((traceClassSandwich A ρ : TraceClassOperator K) : K →L[ℂ] K) ≤
        (‖A‖ * ‖adjoint A‖) * RHTower.traceNorm H (ρ : H →L[ℂ] H) :=
      traceNorm_sandwich_le A ρ ρ.property
    _ ≤ 1 * RHTower.traceNorm H (ρ : H →L[ℂ] H) :=
      mul_le_mul_of_nonneg_right hA (RHTower.traceNorm_nonneg _)
    _ = RHTower.traceNorm H (ρ : H →L[ℂ] H) := one_mul _

/-- Exact trace preservation for sandwiches by a Hilbert isometry. -/
theorem traceClassSandwich_tracePreserving (J : H →L[ℂ] K)
    (hJ : adjoint J ∘L J = ContinuousLinearMap.id ℂ H) :
    ∀ ρ, traceClassPositive ρ →
      traceClassTrace (traceClassSandwich J ρ) = traceClassTrace ρ := by
  intro ρ _hρ
  unfold traceClassTrace
  change (opTrace ((J ∘L (ρ : H →L[ℂ] H)) ∘L adjoint J)).re = _
  rw [opTrace_sandwich J ρ ρ.property, hJ]
  simp

/-- Normal completely-positive trace-nonincreasing operation induced by a contraction sandwich. -/
noncomputable def traceClassSandwichOperation (A : H →L[ℂ] K)
    (hA : ‖A‖ * ‖adjoint A‖ ≤ 1) : TraceClassQuantumOperation H K where
  map := traceClassSandwich A
  completelyPositive := traceClassSandwich_completelyPositive A
  positive := traceClassSandwich_positive A
  monotone := traceClassSandwich_monotone A
  traceNonincreasing := by
    intro ρ hρ
    exact traceClassSandwich_traceNonincreasing A hA ρ hρ
  normal := traceClassSandwich_normal A

namespace TraceClassQuantumOperation

/-- Exact trace preservation on positive trace-class states. -/
def tracePreserving (Φ : TraceClassQuantumOperation H K) : Prop :=
  ∀ ρ, traceClassPositive ρ → traceClassTrace (Φ.map ρ) = traceClassTrace ρ

end TraceClassQuantumOperation

/--
A certified Hilbert corner. The map fields are the literal sandwich maps; the operation fields
record their normal CP trace-class behavior without introducing any global axiom.
-/
structure TraceClassQuantumCorner (H W : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] where
  isometry : H →L[ℂ] W
  norm_preserving : ∀ x, ‖isometry x‖ = ‖x‖
  adjoint_comp_id : adjoint isometry ∘L isometry = ContinuousLinearMap.id ℂ H
  inclusion : TraceClassQuantumOperation H W
  compression : TraceClassQuantumOperation W H
  inclusion_apply : inclusion.map = traceClassSandwich isometry
  compression_apply : compression.map = traceClassSandwich (adjoint isometry)
  inclusion_trace_preserving : inclusion.tracePreserving

/-- Isometries and their adjoints have sandwich norm coefficient at most one. -/
theorem isometry_sandwich_norm_product_le_one (J : H →L[ℂ] K)
    (hJ : ∀ x, ‖J x‖ = ‖x‖) : ‖J‖ * ‖adjoint J‖ ≤ 1 := by
  have hnorm : ‖J‖ ≤ 1 := by
    apply J.opNorm_le_bound zero_le_one
    intro x
    rw [hJ x, one_mul]
  have hadj : ‖adjoint J‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact hnorm
  nlinarith [norm_nonneg J, norm_nonneg (adjoint J)]

/-- Any Hilbert isometry determines a literal normal CP trace-class corner. -/
noncomputable def traceClassQuantumCornerOfIsometry (J : H →L[ℂ] K)
    (hnorm : ∀ x, ‖J x‖ = ‖x‖)
    (hJ : adjoint J ∘L J = ContinuousLinearMap.id ℂ H) :
    TraceClassQuantumCorner H K where
  isometry := J
  norm_preserving := hnorm
  adjoint_comp_id := hJ
  inclusion := traceClassSandwichOperation J
    (isometry_sandwich_norm_product_le_one J hnorm)
  compression := traceClassSandwichOperation (adjoint J) (by
    simpa only [adjoint_adjoint, mul_comm] using
      isometry_sandwich_norm_product_le_one J hnorm)
  inclusion_apply := rfl
  compression_apply := rfl
  inclusion_trace_preserving := traceClassSandwich_tracePreserving J hJ

namespace TraceClassQuantumCorner

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- Compression after inclusion is exactly the identity on a certified corner. -/
theorem compression_inclusion_apply (c : TraceClassQuantumCorner H W)
    (ρ : TraceClassOperator H) : c.compression.map (c.inclusion.map ρ) = ρ := by
  rw [c.compression_apply, c.inclusion_apply]
  exact traceClassSandwich_adjoint_apply c.isometry c.adjoint_comp_id ρ

/-- The two concrete corner maps form a split at trace-class level. -/
theorem compression_comp_inclusion (c : TraceClassQuantumCorner H W) :
    c.compression.map.comp c.inclusion.map = LinearMap.id := by
  apply LinearMap.ext
  intro ρ
  exact c.compression_inclusion_apply ρ

end TraceClassQuantumCorner

namespace TraceClassQuantumOperation

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The literal fixed-carrier lift `J_j Phi(J_i† rho J_i) J_j†`. -/
def cornerLift (source : TraceClassQuantumCorner H W)
    (target : TraceClassQuantumCorner K W) (Φ : TraceClassQuantumOperation H K) :
    TraceClassQuantumOperation W W :=
  target.inclusion.comp (Φ.comp source.compression)

/-- The corner lift is completely positive at every finite matrix level. -/
theorem cornerLift_completelyPositive (source : TraceClassQuantumCorner H W)
    (target : TraceClassQuantumCorner K W) (Φ : TraceClassQuantumOperation H K) :
    IsCompletelyPositive (traceClassMatrixCone W) (traceClassMatrixCone W)
      (cornerLift source target Φ).map :=
  (cornerLift source target Φ).completelyPositive

/-- The corner lift is trace-nonincreasing on every positive trace-class state. -/
theorem cornerLift_traceNonincreasing (source : TraceClassQuantumCorner H W)
    (target : TraceClassQuantumCorner K W) (Φ : TraceClassQuantumOperation H K)
    (ρ : TraceClassOperator W) (hρ : traceClassPositive ρ) :
    traceClassTrace ((cornerLift source target Φ).map ρ) ≤ traceClassTrace ρ :=
  (cornerLift source target Φ).traceNonincreasing ρ hρ

/-- The corner lift remains order-normal. -/
theorem cornerLift_normal (source : TraceClassQuantumCorner H W)
    (target : TraceClassQuantumCorner K W) (Φ : TraceClassQuantumOperation H K) :
    TraceClassNormal W W (cornerLift source target Φ).map :=
  (cornerLift source target Φ).normal

/-- Compressing a lift to its target corner recovers the original operation exactly. -/
theorem cornerLift_compress (source : TraceClassQuantumCorner H W)
    (target : TraceClassQuantumCorner K W) (Φ : TraceClassQuantumOperation H K)
    (ρ : TraceClassOperator W) :
    target.compression.map ((cornerLift source target Φ).map ρ) =
      Φ.map (source.compression.map ρ) := by
  change target.compression.map
    (target.inclusion.map (Φ.map (source.compression.map ρ))) = _
  rw [target.compression_inclusion_apply]

/-- The lift agrees exactly with `Phi` on valid source-corner inputs. -/
theorem cornerLift_include (source : TraceClassQuantumCorner H W)
    (target : TraceClassQuantumCorner K W) (Φ : TraceClassQuantumOperation H K)
    (ρ : TraceClassOperator H) :
    (cornerLift source target Φ).map (source.inclusion.map ρ) =
      target.inclusion.map (Φ.map ρ) := by
  change target.inclusion.map
    (Φ.map (source.compression.map (source.inclusion.map ρ))) = _
  rw [source.compression_inclusion_apply]

/-- Lifted composable quantum operations compose exactly on the fixed carrier. -/
theorem cornerLift_comp (source : TraceClassQuantumCorner H W)
    (middle : TraceClassQuantumCorner K W) (target : TraceClassQuantumCorner L W)
    (Φ : TraceClassQuantumOperation H K) (Ψ : TraceClassQuantumOperation K L) :
    (cornerLift middle target Ψ).map.comp (cornerLift source middle Φ).map =
      (cornerLift source target (Ψ.comp Φ)).map := by
  apply LinearMap.ext
  intro ρ
  change target.inclusion.map
    (Ψ.map (middle.compression.map
      (middle.inclusion.map (Φ.map (source.compression.map ρ))))) = _
  rw [middle.compression_inclusion_apply]
  rfl

/-- A trace-preserving operation preserves normalization exactly on valid corner states. -/
theorem trace_cornerLift_include_eq_of_tracePreserving
    (source : TraceClassQuantumCorner H W) (target : TraceClassQuantumCorner K W)
    (Φ : TraceClassQuantumOperation H K) (hΦ : Φ.tracePreserving)
    (ρ : TraceClassOperator H) (hρ : traceClassPositive ρ) :
    traceClassTrace ((cornerLift source target Φ).map (source.inclusion.map ρ)) =
      traceClassTrace ρ := by
  rw [cornerLift_include]
  calc
    traceClassTrace (target.inclusion.map (Φ.map ρ)) = traceClassTrace (Φ.map ρ) :=
      target.inclusion_trace_preserving _ (Φ.positive ρ hρ)
    _ = traceClassTrace ρ := hΦ ρ hρ

end TraceClassQuantumOperation

end
end GaloisForLFunctions.HTGeometry
