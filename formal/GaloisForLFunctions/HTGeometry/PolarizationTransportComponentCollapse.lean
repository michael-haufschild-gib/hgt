import GaloisForLFunctions.HTGeometry.ReducedH0Components

/-!
# Polarization transport collapses orientation surgery to component data

A finite simplicial constraint complex carrying a one-dimensional real coherence line at every
vertex has a Boolean orientation at each vertex.  The orientation is *transport-compatible* when
every restriction along an edge is an isometry of the one-dimensional forms.  An isometry between
one-dimensional nondegenerate forms preserves the sign of the form, so a transport-compatible
orientation is constant along edges, hence constant on connected components.

This module proves the resulting classification unconditionally:

* `HTGeometry.compatibleOrientationEquivComponents` — transport-compatible orientations are exactly
  the Boolean functions on the set of connected components of the `1`-skeleton;
* `HTGeometry.card_compatibleOrientation` — there are `2 ^ (number of components)` of them;
* `HTGeometry.compatibleOrientationEquivBool` — a connected complex has exactly two;
* `HTGeometry.uniquePointedCompatibleOrientation` — pointing one vertex positively leaves a
  singleton;
* `HTGeometry.sameSign_of_isometryScalar` and `HTGeometry.compatible_signOrientation` — the
  one-dimensional isometry step, valid over any linearly ordered field, which is what makes a
  transported polarization a compatible orientation in the first place.

The concrete boundary-wedge seed `∂σʳ ∧ ∂σˢ` is in `HTGeometry.WedgeRealization`.
-/

namespace GaloisForLFunctions.HTGeometry

open SimpleGraph

noncomputable section

/-! ## The one-dimensional isometry step -/

section Isometry

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **An isometry of one-dimensional nondegenerate forms preserves the sign of the form.**  If the
linear map `x ↦ t * x` carries the form `x ↦ cu * x ^ 2` to the form `x ↦ cv * x ^ 2`, and the
source form is nondegenerate, then the two coefficients have the same sign. -/
theorem sameSign_of_isometryScalar {cu cv t : R} (hcu : cu ≠ 0)
    (h : ∀ x : R, cv * (t * x) ^ 2 = cu * x ^ 2) :
    (0 < cu ↔ 0 < cv) := by
  have h1 : cv * t ^ 2 = cu := by simpa using h 1
  have ht : t ≠ 0 := by
    intro ht0
    apply hcu
    rw [← h1, ht0]
    ring
  have hsq : 0 < t ^ 2 := by positivity
  constructor
  · intro hpos
    rcases lt_trichotomy cv 0 with hneg | hzero | hpos'
    · exact absurd (h1 ▸ mul_neg_of_neg_of_pos hneg hsq) (not_lt.2 hpos.le)
    · exact absurd (by rw [← h1, hzero, zero_mul]) (ne_of_gt hpos)
    · exact hpos'
  · intro hpos
    rw [← h1]
    exact mul_pos hpos hsq

/-- The Boolean orientation read off from a family of one-dimensional form coefficients. -/
def signOrientation {V : Type*} (c : V → R) : V → Bool := fun v => decide (0 < c v)

/-- Transport along an isometry does not change the Boolean orientation. -/
theorem signOrientation_eq_of_isometryScalar {V : Type*} {c : V → R} {u v : V} {t : R}
    (hcu : c u ≠ 0) (h : ∀ x : R, c v * (t * x) ^ 2 = c u * x ^ 2) :
    signOrientation c u = signOrientation c v := by
  unfold signOrientation
  exact decide_eq_decide.2 (sameSign_of_isometryScalar hcu h)

end Isometry

/-! ## Finite simplicial constraint complexes and their `1`-skeleta -/

/-- A finite simplicial constraint complex: a downward-closed family of finite vertex sets. -/
structure ConstraintComplex (V : Type*) where
  /-- The faces of the complex. -/
  IsFace : Finset V → Prop
  /-- Faces are closed under passing to subsets. -/
  down_closed : ∀ {J K : Finset V}, K ⊆ J → IsFace J → IsFace K

variable {V : Type*} [DecidableEq V]

/-- The `1`-skeleton of a constraint complex, as a simple graph on its vertices. -/
def ConstraintComplex.skeleton (X : ConstraintComplex V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ X.IsFace {u, v}
  symm := by
    rintro u v ⟨hne, hface⟩
    exact ⟨hne.symm, by rwa [Finset.pair_comm]⟩
  loopless := fun _ h => h.1 rfl

@[simp]
theorem ConstraintComplex.skeleton_adj (X : ConstraintComplex V) (u v : V) :
    X.skeleton.Adj u v ↔ u ≠ v ∧ X.IsFace {u, v} := Iff.rfl

/-! ## The classification -/

variable (G : SimpleGraph V)

/-- A Boolean orientation transported unchanged across every edge. -/
def CompatibleOrientation : Type _ := {ε : V → Bool // ∀ u v, G.Adj u v → ε u = ε v}

instance : CoeFun (CompatibleOrientation G) (fun _ => V → Bool) where
  coe ε := ε.1

/-- **Polarization-transport law.**  Transport-compatible Boolean orientations are exactly the
Boolean functions on the set of connected components: the residual sign freedom of a
restriction-compatible polarization is exactly component freedom. -/
def compatibleOrientationEquivComponents :
    CompatibleOrientation G ≃ (G.ConnectedComponent → Bool) where
  toFun ε := ConnectedComponent.lift ε.1
    (fun v w p _ => eq_of_reachable_of_adj_invariant G Bool ε.2 ⟨p⟩)
  invFun g := ⟨fun v => g (G.connectedComponentMk v),
    fun u v huv => congrArg g (ConnectedComponent.sound huv.reachable)⟩
  left_inv ε := by apply Subtype.ext; funext v; rfl
  right_inv g := by
    funext c
    induction c using ConnectedComponent.ind with
    | _ v => rfl

/-- The compatible orientation fibre has exactly `2 ^ (number of components)` points. -/
theorem card_compatibleOrientation [Fintype V] [DecidableRel G.Adj] :
    Nat.card (CompatibleOrientation G) = 2 ^ Nat.card G.ConnectedComponent := by
  classical
  rw [Nat.card_congr (compatibleOrientationEquivComponents G)]
  simp [Nat.card_eq_fintype_card, Fintype.card_fun]

/-- **Connected polarization collapse.**  On a connected complex the compatible fibre has exactly
two points. -/
def compatibleOrientationEquivBool (hG : G.Connected) :
    CompatibleOrientation G ≃ Bool := by
  haveI : Nonempty V := hG.nonempty
  haveI : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk (Classical.arbitrary V)⟩
  haveI : Subsingleton G.ConnectedComponent :=
    ⟨fun c d => by
      induction c using ConnectedComponent.ind with
      | _ v =>
        induction d using ConnectedComponent.ind with
        | _ w => exact ConnectedComponent.sound (hG.preconnected v w)⟩
  exact (compatibleOrientationEquivComponents G).trans
    (Equiv.funUnique G.ConnectedComponent Bool |>.trans (Equiv.refl Bool)) |>.trans (Equiv.refl Bool)

/-- A compatible orientation on a connected complex is determined by its value at any vertex. -/
theorem compatibleOrientation_eq_of_connected (hG : G.Connected)
    (ε : CompatibleOrientation G) (u v : V) : ε.1 u = ε.1 v :=
  eq_of_reachable_of_adj_invariant G Bool ε.2 (hG.preconnected u v)

/-- **Positive pointing kills the last global sign.**  On a connected complex, exactly one
compatible orientation is positive at a prescribed vertex. -/
instance uniquePointedCompatibleOrientation (hG : G.Connected) (v₀ : V) :
    Unique {ε : CompatibleOrientation G // ε.1 v₀ = true} where
  default := ⟨⟨fun _ => true, fun _ _ _ => rfl⟩, rfl⟩
  uniq := by
    rintro ⟨⟨ε, hε⟩, hv⟩
    apply Subtype.ext
    apply Subtype.ext
    funext v
    exact (eq_of_reachable_of_adj_invariant G Bool hε (hG.preconnected v v₀)).trans hv

/-- A polarization by one-dimensional nondegenerate forms whose edge restrictions are isometries
induces a transport-compatible Boolean orientation. -/
def compatible_signOrientation {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (c : V → R) (hc : ∀ v, c v ≠ 0)
    (t : ∀ u v : V, G.Adj u v → R)
    (hiso : ∀ (u v : V) (h : G.Adj u v), ∀ x : R, c v * (t u v h * x) ^ 2 = c u * x ^ 2) :
    CompatibleOrientation G :=
  ⟨signOrientation c, fun u v h => signOrientation_eq_of_isometryScalar (hc u) (hiso u v h)⟩

end

end GaloisForLFunctions.HTGeometry
