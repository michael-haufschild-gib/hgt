import GaloisForLFunctions.HTGeometry.MatrixOrderedMap
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
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

/-- Positive trace-class operators, read in the ambient bounded-operator order. -/
def traceClassPositive (T : TraceClassOperator H) : Prop :=
  0 ≤ (T : H →L[ℂ] H)

/-- The genuine finite-level positive cone on trace-class operator matrices. -/
def traceClassMatrixCone (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (n : Type) [Fintype n] : Set (Matrix n n (TraceClassOperator H)) := by
  classical
  exact {M | 0 ≤ CStarMatrix.ofMatrix
    (M.map (RHTower.schattenOneSubmodule (H := H)).subtype)}

/-- Order-normality on the trace-class carrier: every existing directed supremum is preserved. -/
def TraceClassNormal (H K : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (φ : TraceClassOperator H →ₗ[ℂ] TraceClassOperator K) : Prop :=
  ∀ ⦃d : Set (TraceClassOperator H)⦄, d.Nonempty → DirectedOn (· ≤ ·) d →
    ∀ ⦃s : TraceClassOperator H⦄, IsLUB d s → IsLUB (φ '' d) (φ s)

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
    (hφ : TraceClassNormal H K φ) (hφmono : Monotone φ)
    (hψ : TraceClassNormal K L ψ) :
    TraceClassNormal H L (ψ.comp φ) := by
  intro d hdne hdir s hsup
  have hdir_image : DirectedOn (· ≤ ·) (φ '' d) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
    exact ⟨φ z, ⟨z, hz, rfl⟩, hφmono hxz, hφmono hyz⟩
  have himage_ne : (φ '' d).Nonempty := hdne.image φ
  have hcomp : (fun x => ψ (φ x)) '' d = ψ '' (φ '' d) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  change IsLUB ((fun x => ψ (φ x)) '' d) (ψ (φ s))
  rw [hcomp]
  exact hψ himage_ne hdir_image (hφ hdne hdir hsup)

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
    intro u hu s hs
    simpa using hs

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
