import Mathlib.Algebra.DirectSum.Module

/-!
# One fixed carrier for every typed linear event network

For a set-indexed family of event carriers `M i`, put every carrier into the algebraic direct sum.
A typed event `f : M i →ₗ[R] M j` then becomes the block endomorphism

`lof j ∘ f ∘ component i`.

The lift is faithful, recovers the original event by corner compression, preserves addition, and
preserves every composable history exactly. Thus even a complete set-indexed typed linear network
cannot witness fundamental carrier change from its source and target types alone. Any physical
carrier-change claim must specify extra structure that a permissible fixed-carrier realization is
required to preserve.

This is the arbitrary-network successor of the four-block construction in
`EventOrderDiamond.lean`. It is elementary direct-sum/linking-algebra infrastructure, not new
scientific knowledge.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped DirectSum

noncomputable section

variable {R ι : Type*} [Semiring R] [DecidableEq ι]
variable (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The one algebraic direct-sum carrier containing every typed event carrier. -/
abbrev eventNetworkFixedCarrier :=
  ⨁ i, M i

/--
Lift a typed event to the corresponding source-to-target block of one fixed direct-sum carrier.
-/
def typedEventCornerLift {i j : ι} (f : M i →ₗ[R] M j) :
    eventNetworkFixedCarrier M →ₗ[R] eventNetworkFixedCarrier M :=
  (DirectSum.lof R ι M j).comp
    (f.comp (DirectSum.component R ι M i))

/-- Compressing a lifted event back to its source and target corners recovers the event exactly. -/
theorem typedEventCornerLift_recover {i j : ι} (f : M i →ₗ[R] M j) :
    (DirectSum.component R ι M j).comp
        ((typedEventCornerLift M f).comp (DirectSum.lof R ι M i)) = f := by
  ext x
  simp [typedEventCornerLift]

/-- Distinct typed events have distinct fixed-carrier corner lifts. -/
theorem typedEventCornerLift_injective {i j : ι} :
    Function.Injective (typedEventCornerLift M :
      (M i →ₗ[R] M j) →
        eventNetworkFixedCarrier M →ₗ[R] eventNetworkFixedCarrier M) := by
  intro f g h
  have h' := congrArg
    (fun F =>
      (DirectSum.component R ι M j).comp
        (F.comp (DirectSum.lof R ι M i))) h
  simpa [typedEventCornerLift_recover] using h'

/--
Fixed-carrier lifting preserves typed composition exactly. Iteration gives exact reconstruction of
every finite composable history in the full event network.
-/
theorem typedEventCornerLift_comp {i j k : ι}
    (f : M i →ₗ[R] M j) (g : M j →ₗ[R] M k) :
    (typedEventCornerLift M g).comp (typedEventCornerLift M f) =
      typedEventCornerLift M (g.comp f) := by
  ext x
  simp [typedEventCornerLift]

/-- A typed identity becomes the idempotent projection onto that type's direct-sum corner. -/
theorem typedEventCornerLift_id (i : ι) :
    typedEventCornerLift M (LinearMap.id : M i →ₗ[R] M i) =
      (DirectSum.lof R ι M i).comp (DirectSum.component R ι M i) := by
  rfl

/-- Parallel-history addition is preserved by the fixed-carrier corner lift. -/
@[simp]
theorem typedEventCornerLift_add {i j : ι}
    (f g : M i →ₗ[R] M j) :
    typedEventCornerLift M (f + g) =
      typedEventCornerLift M f + typedEventCornerLift M g := by
  ext x
  simp [typedEventCornerLift]

section Ring

variable {S κ : Type*} [Ring S] [DecidableEq κ]
variable (N : κ → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]

/-- Parallel-history additive inverses are preserved by the fixed-carrier corner lift. -/
@[simp]
theorem typedEventCornerLift_neg {i j : κ}
    (f : N i →ₗ[S] N j) :
    typedEventCornerLift N (-f) = -typedEventCornerLift N f := by
  ext x
  simp [typedEventCornerLift]

/-- In particular, every typed order defect is the compression of the corresponding lifted defect. -/
@[simp]
theorem typedEventCornerLift_sub {i j : κ}
    (f g : N i →ₗ[S] N j) :
    typedEventCornerLift N (f - g) =
      typedEventCornerLift N f - typedEventCornerLift N g := by
  simp [sub_eq_add_neg]

end Ring

section CommSemiring

variable {S κ : Type*} [CommSemiring S] [DecidableEq κ]
variable (N : κ → Type*) [∀ i, AddCommMonoid (N i)] [∀ i, Module S (N i)]

/-- Scalar weighting of parallel histories is preserved over a commutative coefficient semiring. -/
@[simp]
theorem typedEventCornerLift_smul {i j : κ}
    (c : S) (f : N i →ₗ[S] N j) :
    typedEventCornerLift N (c • f) = c • typedEventCornerLift N f := by
  ext x
  simp [typedEventCornerLift]

end CommSemiring

end

end GaloisForLFunctions.HTGeometry
