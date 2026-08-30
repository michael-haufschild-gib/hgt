import Mathlib.Tactic

/-!
# Higher-slot context-response geometry

A complete response on finite binary source trees defines a canonical context quotient. One-hole
contexts force the quotient relation to be a congruence for branched composition. The quotient is
reachable and context-observable, and every other reachable context-observable realization of the
same response is uniquely equivalent to it while preserving marks, binary composition, and report.

This is the set-level branched presentation-invariance theorem used by Constitutive Process Geometry.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w w'

/-- Finite rooted binary source expressions. -/
inductive ResponseTree (A : Type u) : Type u
  | leaf (a : A)
  | fork (left right : ResponseTree A)
  deriving DecidableEq

/-- One-hole intervention contexts for binary source expressions. -/
inductive ResponseContext (A : Type u) : Type u
  | hole
  | forkLeft (context : ResponseContext A) (right : ResponseTree A)
  | forkRight (left : ResponseTree A) (context : ResponseContext A)
  deriving DecidableEq

namespace ResponseContext

/-- Plug one source expression into the unique hole. -/
def plug {A : Type u} : ResponseContext A → ResponseTree A → ResponseTree A
  | .hole, t => t
  | .forkLeft c right, t => .fork (plug c t) right
  | .forkRight left c, t => .fork left (plug c t)

/-- Nested intervention: first execute `inner`, then `outer`. -/
def comp {A : Type u} : ResponseContext A → ResponseContext A → ResponseContext A
  | .hole, inner => inner
  | .forkLeft outer right, inner => .forkLeft (comp outer inner) right
  | .forkRight left outer, inner => .forkRight left (comp outer inner)

@[simp] theorem plug_hole {A : Type u} (t : ResponseTree A) :
    plug .hole t = t := rfl

@[simp] theorem plug_forkLeft {A : Type u} (c : ResponseContext A)
    (right t : ResponseTree A) :
    plug (.forkLeft c right) t = .fork (plug c t) right := rfl

@[simp] theorem plug_forkRight {A : Type u} (left t : ResponseTree A)
    (c : ResponseContext A) :
    plug (.forkRight left c) t = .fork left (plug c t) := rfl

@[simp] theorem plug_comp {A : Type u} (outer inner : ResponseContext A)
    (t : ResponseTree A) :
    plug (comp outer inner) t = plug outer (plug inner t) := by
  induction outer with
  | hole => rfl
  | forkLeft outer right ih => simp [comp, ih]
  | forkRight left outer ih => simp [comp, ih]

@[simp] theorem comp_hole_left {A : Type u} (c : ResponseContext A) :
    comp .hole c = c := rfl

@[simp] theorem comp_hole_right {A : Type u} (c : ResponseContext A) :
    comp c .hole = c := by
  induction c <;> simp [comp, *]

theorem comp_assoc {A : Type u} (a b c : ResponseContext A) :
    comp (comp a b) c = comp a (comp b c) := by
  induction a <;> simp [comp, *]

end ResponseContext

/-- Two source expressions are equivalent when every legal one-hole context reports equally. -/
def ContextEquivalent {A : Type u} {Y : Type v} (r : ResponseTree A → Y)
    (t s : ResponseTree A) : Prop :=
  ∀ c : ResponseContext A,
    r (ResponseContext.plug c t) = r (ResponseContext.plug c s)

theorem contextEquivalent_equivalence {A : Type u} {Y : Type v}
    (r : ResponseTree A → Y) : Equivalence (ContextEquivalent r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t c
    rfl
  · intro t s h c
    exact (h c).symm
  · intro t s u hts hsu c
    exact (hts c).trans (hsu c)

theorem contextEquivalent_plug {A : Type u} {Y : Type v}
    (r : ResponseTree A → Y) {t s : ResponseTree A}
    (h : ContextEquivalent r t s) (c : ResponseContext A) :
    ContextEquivalent r (c.plug t) (c.plug s) := by
  intro outer
  simpa only [ResponseContext.plug_comp] using h (outer.comp c)

theorem contextEquivalent_fork_left {A : Type u} {Y : Type v}
    (r : ResponseTree A → Y) {t s right : ResponseTree A}
    (h : ContextEquivalent r t s) :
    ContextEquivalent r (.fork t right) (.fork s right) := by
  intro outer
  simpa [ResponseContext.plug_comp, ResponseContext.plug] using
    h (outer.comp (.forkLeft .hole right))

theorem contextEquivalent_fork_right {A : Type u} {Y : Type v}
    (r : ResponseTree A → Y) {left t s : ResponseTree A}
    (h : ContextEquivalent r t s) :
    ContextEquivalent r (.fork left t) (.fork left s) := by
  intro outer
  simpa [ResponseContext.plug_comp, ResponseContext.plug] using
    h (outer.comp (.forkRight left .hole))

theorem contextEquivalent_fork {A : Type u} {Y : Type v}
    (r : ResponseTree A → Y) {t₀ t₁ s₀ s₁ : ResponseTree A}
    (h₀ : ContextEquivalent r t₀ s₀) (h₁ : ContextEquivalent r t₁ s₁) :
    ContextEquivalent r (.fork t₀ t₁) (.fork s₀ s₁) := by
  intro outer
  exact (contextEquivalent_fork_left r h₀ outer).trans
    (contextEquivalent_fork_right r h₁ outer)

/-- The complete context-response setoid of a source law. -/
def contextSetoid {A : Type u} {Y : Type v} (r : ResponseTree A → Y) :
    Setoid (ResponseTree A) where
  r := ContextEquivalent r
  iseqv := contextEquivalent_equivalence r

/-- Canonical law state: source expressions modulo every complete contextual response. -/
abbrev ContextState {A : Type u} {Y : Type v} (r : ResponseTree A → Y) :=
  Quotient (contextSetoid r)

/-- Descended marked leaf. -/
def contextStateLeaf {A : Type u} {Y : Type v} (r : ResponseTree A → Y) (a : A) :
    ContextState r := Quotient.mk _ (.leaf a)

/-- Descended higher-slot composition. -/
def contextStateFork {A : Type u} {Y : Type v} (r : ResponseTree A → Y) :
    ContextState r → ContextState r → ContextState r :=
  fun x y => Quotient.liftOn₂ x y
    (fun t s => Quotient.mk _ (.fork t s))
    (fun t₀ t₁ s₀ s₁ ht hs => Quotient.sound (contextEquivalent_fork r
      (show ContextEquivalent r t₀ s₀ from ht)
      (show ContextEquivalent r t₁ s₁ from hs)))

/-- Descended root reporter. -/
def contextStateResponse {A : Type u} {Y : Type v} (r : ResponseTree A → Y) :
    ContextState r → Y :=
  fun x => Quotient.liftOn x r (fun t s h =>
    (show ContextEquivalent r t s from h) .hole)

/-- Every syntax context acts on the canonical law state. -/
def contextStateAct {A : Type u} {Y : Type v} (r : ResponseTree A → Y)
    (c : ResponseContext A) : ContextState r → ContextState r :=
  Quotient.map c.plug (fun t s h => contextEquivalent_plug r
    (show ContextEquivalent r t s from h) c)

@[simp] theorem contextStateFork_mk {A : Type u} {Y : Type v}
    (r : ResponseTree A → Y) (t s : ResponseTree A) :
    contextStateFork r (Quotient.mk _ t) (Quotient.mk _ s) =
      Quotient.mk _ (.fork t s) := rfl

@[simp] theorem contextStateResponse_mk {A : Type u} {Y : Type v}
    (r : ResponseTree A → Y) (t : ResponseTree A) :
    contextStateResponse r (Quotient.mk _ t) = r t := rfl

@[simp] theorem contextStateAct_mk {A : Type u} {Y : Type v}
    (r : ResponseTree A → Y) (c : ResponseContext A) (t : ResponseTree A) :
    contextStateAct r c (Quotient.mk _ t) = Quotient.mk _ (c.plug t) := rfl

/-- Complete context responses jointly separate canonical law states. -/
theorem contextState_contextObservable {A : Type u} {Y : Type v}
    (r : ResponseTree A → Y) {x y : ContextState r}
    (h : ∀ c, contextStateResponse r (contextStateAct r c x) =
      contextStateResponse r (contextStateAct r c y)) : x = y := by
  induction x using Quotient.inductionOn with
  | _ t =>
    induction y using Quotient.inductionOn with
    | _ s =>
      apply Quotient.sound
      change ContextEquivalent r t s
      intro c
      simpa using h c

/-- A presentation of one binary constitutive process. -/
structure BinaryResponsePresentation (A : Type u) (Y : Type v) where
  Carrier : Type w
  leaf : A → Carrier
  fork : Carrier → Carrier → Carrier
  report : Carrier → Y

namespace BinaryResponsePresentation

/-- Evaluate a source expression in a presentation. -/
def eval {A : Type u} {Y : Type v} (P : BinaryResponsePresentation.{u,v,w} A Y) :
    ResponseTree A → P.Carrier
  | .leaf a => P.leaf a
  | .fork t s => P.fork (eval P t) (eval P s)

/-- Execute a one-hole context around an arbitrary presentation state. -/
def evalContext {A : Type u} {Y : Type v} (P : BinaryResponsePresentation.{u,v,w} A Y) :
    ResponseContext A → P.Carrier → P.Carrier
  | .hole, x => x
  | .forkLeft c right, x => P.fork (evalContext P c x) (eval P right)
  | .forkRight left c, x => P.fork (eval P left) (evalContext P c x)

@[simp] theorem evalContext_eval {A : Type u} {Y : Type v}
    (P : BinaryResponsePresentation.{u,v,w} A Y) (c : ResponseContext A)
    (t : ResponseTree A) :
    P.evalContext c (P.eval t) = P.eval (c.plug t) := by
  induction c <;> simp [evalContext, eval, ResponseContext.plug, *]

def Realizes {A : Type u} {Y : Type v} (P : BinaryResponsePresentation.{u,v,w} A Y)
    (r : ResponseTree A → Y) : Prop :=
  ∀ t, P.report (P.eval t) = r t

def Reachable {A : Type u} {Y : Type v} (P : BinaryResponsePresentation.{u,v,w} A Y) : Prop :=
  Function.Surjective P.eval

def ContextObservable {A : Type u} {Y : Type v}
    (P : BinaryResponsePresentation.{u,v,w} A Y) : Prop :=
  ∀ x y, (∀ c, P.report (P.evalContext c x) = P.report (P.evalContext c y)) → x = y

end BinaryResponsePresentation

/-- A reachable and context-observable realization of one complete source response. -/
structure MinimalBinaryRealization {A : Type u} {Y : Type v} (r : ResponseTree A → Y) where
  presentation : BinaryResponsePresentation.{u,v,w} A Y
  realizes : presentation.Realizes r
  reachable : presentation.Reachable
  observable : presentation.ContextObservable

namespace MinimalBinaryRealization

variable {A : Type u} {Y : Type v} {r : ResponseTree A → Y}

/-- The canonical quotient evaluates into any minimal realization. -/
def canonicalTo (P : MinimalBinaryRealization.{u,v,w} r) :
    ContextState r → P.presentation.Carrier :=
  fun x => Quotient.liftOn x P.presentation.eval (by
    intro t s hts
    change ContextEquivalent r t s at hts
    apply P.observable
    intro c
    rw [P.presentation.evalContext_eval, P.presentation.evalContext_eval,
      P.realizes, P.realizes]
    exact hts c)

@[simp] theorem canonicalTo_mk (P : MinimalBinaryRealization.{u,v,w} r)
    (t : ResponseTree A) :
    P.canonicalTo (Quotient.mk _ t) = P.presentation.eval t := rfl

theorem canonicalTo_surjective (P : MinimalBinaryRealization.{u,v,w} r) :
    Function.Surjective P.canonicalTo := by
  intro x
  obtain ⟨t, rfl⟩ := P.reachable x
  exact ⟨Quotient.mk _ t, rfl⟩

theorem canonicalTo_injective (P : MinimalBinaryRealization.{u,v,w} r) :
    Function.Injective P.canonicalTo := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ t =>
    induction y using Quotient.inductionOn with
    | _ s =>
      apply Quotient.sound
      change ContextEquivalent r t s
      intro c
      have h := congrArg (fun z => P.presentation.report (P.presentation.evalContext c z)) hxy
      change P.presentation.report (P.presentation.evalContext c (P.presentation.eval t)) =
        P.presentation.report (P.presentation.evalContext c (P.presentation.eval s)) at h
      rw [P.presentation.evalContext_eval, P.presentation.evalContext_eval,
        P.realizes, P.realizes] at h
      exact h

/-- Canonical unique carrier equivalence from context states to a minimal realization. -/
noncomputable def canonicalEquiv (P : MinimalBinaryRealization.{u,v,w} r) :
    ContextState r ≃ P.presentation.Carrier :=
  Equiv.ofBijective P.canonicalTo ⟨P.canonicalTo_injective, P.canonicalTo_surjective⟩

@[simp] theorem canonicalEquiv_mk (P : MinimalBinaryRealization.{u,v,w} r)
    (t : ResponseTree A) :
    P.canonicalEquiv (Quotient.mk _ t) = P.presentation.eval t := rfl

theorem canonicalEquiv_leaf (P : MinimalBinaryRealization.{u,v,w} r) (a : A) :
    P.canonicalEquiv (contextStateLeaf r a) = P.presentation.leaf a := rfl

theorem canonicalEquiv_fork (P : MinimalBinaryRealization.{u,v,w} r)
    (x y : ContextState r) :
    P.canonicalEquiv (contextStateFork r x y) =
      P.presentation.fork (P.canonicalEquiv x) (P.canonicalEquiv y) := by
  induction x using Quotient.inductionOn with
  | _ t =>
    induction y using Quotient.inductionOn with
    | _ s => rfl

theorem canonicalEquiv_report (P : MinimalBinaryRealization.{u,v,w} r)
    (x : ContextState r) :
    P.presentation.report (P.canonicalEquiv x) = contextStateResponse r x := by
  induction x using Quotient.inductionOn with
  | _ t => exact P.realizes t

/-- The equivalence from one minimal realization to another. -/
noncomputable def equiv (P : MinimalBinaryRealization.{u,v,w} r)
    (Q : MinimalBinaryRealization.{u,v,w'} r) :
    P.presentation.Carrier ≃ Q.presentation.Carrier :=
  P.canonicalEquiv.symm.trans Q.canonicalEquiv

@[simp] theorem equiv_eval (P : MinimalBinaryRealization.{u,v,w} r)
    (Q : MinimalBinaryRealization.{u,v,w'} r) (t : ResponseTree A) :
    P.equiv Q (P.presentation.eval t) = Q.presentation.eval t := by
  change Q.canonicalEquiv (P.canonicalEquiv.symm (P.canonicalEquiv (Quotient.mk _ t))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem equiv_leaf (P : MinimalBinaryRealization.{u,v,w} r)
    (Q : MinimalBinaryRealization.{u,v,w'} r) (a : A) :
    P.equiv Q (P.presentation.leaf a) = Q.presentation.leaf a := by
  simpa [BinaryResponsePresentation.eval] using P.equiv_eval Q (.leaf a)

theorem equiv_fork (P : MinimalBinaryRealization.{u,v,w} r)
    (Q : MinimalBinaryRealization.{u,v,w'} r) (x y : P.presentation.Carrier) :
    P.equiv Q (P.presentation.fork x y) =
      Q.presentation.fork (P.equiv Q x) (P.equiv Q y) := by
  obtain ⟨t, rfl⟩ := P.reachable x
  obtain ⟨s, rfl⟩ := P.reachable y
  simpa [BinaryResponsePresentation.eval] using P.equiv_eval Q (.fork t s)

theorem equiv_report (P : MinimalBinaryRealization.{u,v,w} r)
    (Q : MinimalBinaryRealization.{u,v,w'} r) (x : P.presentation.Carrier) :
    Q.presentation.report (P.equiv Q x) = P.presentation.report x := by
  obtain ⟨t, rfl⟩ := P.reachable x
  rw [P.equiv_eval Q, P.realizes, Q.realizes]

theorem equiv_unique (P : MinimalBinaryRealization.{u,v,w} r)
    (Q : MinimalBinaryRealization.{u,v,w'} r)
    (e : P.presentation.Carrier ≃ Q.presentation.Carrier)
    (hleaf : ∀ a, e (P.presentation.leaf a) = Q.presentation.leaf a)
    (hfork : ∀ x y, e (P.presentation.fork x y) =
      Q.presentation.fork (e x) (e y)) : e = P.equiv Q := by
  apply Equiv.ext
  intro x
  obtain ⟨t, rfl⟩ := P.reachable x
  induction t with
  | leaf a =>
    rw [BinaryResponsePresentation.eval, hleaf, P.equiv_leaf]
  | fork t s iht ihs =>
    rw [BinaryResponsePresentation.eval, hfork, iht, ihs, P.equiv_fork]

/-- Unique marked equivalence theorem for complete higher-slot response. -/
theorem existsUnique_equiv (P : MinimalBinaryRealization.{u,v,w} r)
    (Q : MinimalBinaryRealization.{u,v,w'} r) :
    ∃! e : P.presentation.Carrier ≃ Q.presentation.Carrier,
      (∀ a, e (P.presentation.leaf a) = Q.presentation.leaf a) ∧
      (∀ x y, e (P.presentation.fork x y) =
        Q.presentation.fork (e x) (e y)) ∧
      (∀ x, Q.presentation.report (e x) = P.presentation.report x) := by
  refine ⟨P.equiv Q, ⟨P.equiv_leaf Q, P.equiv_fork Q, P.equiv_report Q⟩, ?_⟩
  intro e he
  exact P.equiv_unique Q e he.1 he.2.1

end MinimalBinaryRealization

end GaloisForLFunctions.HTGeometry

