import GaloisForLFunctions.HTGeometry.ConstitutiveUnaryLawRepair
import Mathlib.Tactic

/-!
# Observer-induced relational law renormalization

A deterministic source law always has a canonical relation after observation.  The relation is
single-valued exactly when the law preserves the observer kernel.  Observation is strict under
serial pushforward, whereas law execution is only lax: relational composition may splice two
different source histories at an observationally equal midpoint.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-- Direct image of the graph of a deterministic source law under an observer. -/
def EffectiveLawRelation {X : Type u} {B : Type v} (q : X → B) (f : X → X) : B → B → Prop :=
  fun b c ↦ ∃ x, q x = b ∧ q (f x) = c

/-- Execution-order composition of binary relations. -/
def LawRelationComp {B : Type v} (R S : B → B → Prop) : B → B → Prop :=
  fun b c ↦ ∃ d, R b d ∧ S d c

/-- One input has at most one output. -/
def LawRelationRightUnique {B : Type v} (R : B → B → Prop) : Prop :=
  ∀ ⦃b c d⦄, R b c → R b d → c = d

/-- Every input has an output. -/
def LawRelationTotal {B : Type v} (R : B → B → Prop) : Prop :=
  ∀ b, ∃ c, R b c

/-- Direct image of a relation under a further observer. -/
def LawRelationPushforward {B : Type v} {C : Type w} (p : B → C)
    (R : B → B → Prop) : C → C → Prop :=
  fun c d ↦ ∃ b b', p b = c ∧ p b' = d ∧ R b b'

theorem effectiveLawRelation_id_iff {X : Type u} {B : Type v}
    (q : X → B) (hq : Function.Surjective q) (b c : B) :
    EffectiveLawRelation q id b c ↔ b = c := by
  constructor
  · rintro ⟨x, rfl, hxc⟩
    simpa using hxc
  · intro hbc
    obtain ⟨x, rfl⟩ := hq b
    exact ⟨x, rfl, hbc.symm.trans rfl⟩

theorem effectiveLawRelation_total {X : Type u} {B : Type v}
    (q : X → B) (hq : Function.Surjective q) (f : X → X) :
    LawRelationTotal (EffectiveLawRelation q f) := by
  intro b
  obtain ⟨x, rfl⟩ := hq b
  exact ⟨q (f x), x, rfl, rfl⟩

theorem effectiveLawRelation_rightUnique_iff_kernelPreserved
    {X : Type u} {B : Type v} (q : X → B) (f : X → X) :
    LawRelationRightUnique (EffectiveLawRelation q f) ↔
      UnaryPreserves f (ObserverKernel q) := by
  constructor
  · intro h x y hxy
    change q x = q y at hxy
    change q (f x) = q (f y)
    exact h ⟨x, rfl, rfl⟩ ⟨y, hxy.symm, rfl⟩
  · intro h b c d hbc hbd
    rcases hbc with ⟨x, hxb, hxc⟩
    rcases hbd with ⟨y, hyb, hyd⟩
    have hxy : ObserverKernel q x y := hxb.trans hyb.symm
    exact hxc.symm.trans ((h hxy).trans hyd)

theorem effectiveLawRelation_unique_descended
    {X : Type u} {B : Type v} (q : X → B) (hq : Function.Surjective q) (f : X → X)
    (hf : LawRelationRightUnique (EffectiveLawRelation q f)) :
    ∃! fbar : B → B, ∀ x, q (f x) = fbar (q x) := by
  have hpres : UnaryPreserves f (ObserverKernel q) :=
    (effectiveLawRelation_rightUnique_iff_kernelPreserved q f).1 hf
  obtain ⟨fbar, hbar⟩ := descended_of_observerKernel_preserved q f hpres
  refine ⟨fbar, hbar, ?_⟩
  intro g hg
  funext b
  obtain ⟨x, rfl⟩ := hq b
  exact (hbar x).symm.trans (hg x)

theorem effectiveLawRelation_eq_graph_of_descended
    {X : Type u} {B : Type v} (q : X → B) (hq : Function.Surjective q)
    (f : X → X) (fbar : B → B) (hbar : ∀ x, q (f x) = fbar (q x)) (b c : B) :
    EffectiveLawRelation q f b c ↔ fbar b = c := by
  constructor
  · rintro ⟨x, rfl, hxc⟩
    exact (hbar x).symm.trans hxc
  · intro hbc
    obtain ⟨x, rfl⟩ := hq b
    exact ⟨x, rfl, (hbar x).trans hbc⟩

theorem effectiveLawRelation_comp_subset
    {X : Type u} {B : Type v} (q : X → B) (f g : X → X) :
    ∀ ⦃b c⦄, EffectiveLawRelation q (g ∘ f) b c →
      LawRelationComp (EffectiveLawRelation q f) (EffectiveLawRelation q g) b c := by
  rintro b c ⟨x, hxb, hxc⟩
  refine ⟨q (f x), ⟨x, hxb, rfl⟩, ?_⟩
  exact ⟨f x, rfl, hxc⟩

theorem effectiveLawRelation_comp_exact_of_later_preserves
    {X : Type u} {B : Type v} (q : X → B) (f g : X → X)
    (hg : UnaryPreserves g (ObserverKernel q)) (b c : B) :
    LawRelationComp (EffectiveLawRelation q f) (EffectiveLawRelation q g) b c ↔
      EffectiveLawRelation q (g ∘ f) b c := by
  constructor
  · rintro ⟨d, ⟨x, hxb, hxd⟩, ⟨y, hyd, hyc⟩⟩
    have hfy : ObserverKernel q (f x) y := hxd.trans hyd.symm
    exact ⟨x, hxb, (hg hfy).trans hyc⟩
  · exact effectiveLawRelation_comp_subset q f g

theorem kernelPreserved_of_constant_prelaw_exact
    {X : Type u} {B : Type v} [Nonempty X] (q : X → B) (g : X → X)
    (h : ∀ y b c,
      LawRelationComp (EffectiveLawRelation q (fun _ ↦ y)) (EffectiveLawRelation q g) b c →
        EffectiveLawRelation q (g ∘ fun _ ↦ y) b c) :
    UnaryPreserves g (ObserverKernel q) := by
  intro y z hyz
  change q y = q z at hyz
  change q (g y) = q (g z)
  let x₀ : X := Classical.choice inferInstance
  have hpre : EffectiveLawRelation q (fun _ ↦ y) (q x₀) (q y) :=
    ⟨x₀, rfl, rfl⟩
  have hpost : EffectiveLawRelation q g (q y) (q (g z)) :=
    ⟨z, hyz.symm, rfl⟩
  rcases h y (q x₀) (q (g z)) ⟨q y, hpre, hpost⟩ with ⟨x, _hx, hout⟩
  simpa [Function.comp_def] using hout

theorem kernelPreserved_iff_constant_prelaw_exact
    {X : Type u} {B : Type v} [Nonempty X] (q : X → B) (g : X → X) :
    UnaryPreserves g (ObserverKernel q) ↔
      ∀ y b c,
        LawRelationComp (EffectiveLawRelation q (fun _ ↦ y))
            (EffectiveLawRelation q g) b c ↔
          EffectiveLawRelation q (g ∘ fun _ ↦ y) b c := by
  constructor
  · intro hg y b c
    exact effectiveLawRelation_comp_exact_of_later_preserves q (fun _ ↦ y) g hg b c
  · intro h
    exact kernelPreserved_of_constant_prelaw_exact q g
      (fun y b c hcomp ↦ (h y b c).1 hcomp)

theorem effectiveLawRelation_serialObserver
    {X : Type u} {B : Type v} {C : Type w} (q : X → B) (p : B → C)
    (f : X → X) (c d : C) :
    EffectiveLawRelation (p ∘ q) f c d ↔
      LawRelationPushforward p (EffectiveLawRelation q f) c d := by
  constructor
  · rintro ⟨x, hxc, hxd⟩
    exact ⟨q x, q (f x), hxc, hxd, x, rfl, rfl⟩
  · rintro ⟨b, b', hbc, hbd, x, hxb, hxb'⟩
    exact ⟨x, hxb ▸ hbc, hxb' ▸ hbd⟩

theorem deterministicLaw_misses_branch
    {X : Type u} {B : Type v} (q : X → B) (f : X → X)
    {b c d : B} (hbc : EffectiveLawRelation q f b c)
    (hbd : EffectiveLawRelation q f b d) (hcd : c ≠ d) (h : B → B) :
    ∃ x, h (q x) ≠ q (f x) := by
  by_cases hh : h b = c
  · rcases hbd with ⟨x, hxb, hxd⟩
    refine ⟨x, ?_⟩
    rw [hxb, hxd, hh]
    exact hcd
  · rcases hbc with ⟨x, hxb, hxc⟩
    refine ⟨x, ?_⟩
    rwa [hxb, hxc]

/-! ## Four-state sharp cells -/

abbrev RelationalLawState := Bool × Bool

def relationalLawObserver : RelationalLawState → Bool := Prod.fst

def relationalLawPre (_ : RelationalLawState) : RelationalLawState := (true, false)

def relationalLawLater (x : RelationalLawState) : RelationalLawState := (x.2, false)

theorem relationalLawObserver_surjective : Function.Surjective relationalLawObserver := by
  intro b
  exact ⟨(b, false), rfl⟩

theorem relationalLawPre_effective (b : Bool) :
    EffectiveLawRelation relationalLawObserver relationalLawPre b true := by
  exact ⟨(b, false), rfl, rfl⟩

theorem relationalLawLater_effective (b c : Bool) :
    EffectiveLawRelation relationalLawObserver relationalLawLater b c := by
  exact ⟨(b, c), rfl, rfl⟩

theorem relationalLawComposite_only_false {b c : Bool}
    (h : EffectiveLawRelation relationalLawObserver
      (relationalLawLater ∘ relationalLawPre) b c) :
    c = false := by
  rcases h with ⟨x, _hxb, hxc⟩
  simpa [relationalLawLater, relationalLawPre, relationalLawObserver,
    Function.comp_def] using hxc.symm

theorem relationalLaw_strict_splice_witness :
    LawRelationComp
        (EffectiveLawRelation relationalLawObserver relationalLawPre)
        (EffectiveLawRelation relationalLawObserver relationalLawLater)
        false true ∧
      ¬ EffectiveLawRelation relationalLawObserver
        (relationalLawLater ∘ relationalLawPre) false true := by
  constructor
  · exact ⟨true, relationalLawPre_effective false,
      relationalLawLater_effective true true⟩
  · intro h
    have := relationalLawComposite_only_false h
    simp at this

theorem relationalLaw_fine_deterministic :
    LawRelationRightUnique (EffectiveLawRelation id relationalLawLater) := by
  apply (effectiveLawRelation_rightUnique_iff_kernelPreserved id relationalLawLater).2
  intro x y hxy
  change x = y at hxy
  simpa [hxy]

theorem relationalLaw_coarse_branching :
    ¬ LawRelationRightUnique
      (EffectiveLawRelation relationalLawObserver relationalLawLater) := by
  intro h
  have hft : false = true :=
    h (relationalLawLater_effective false false)
      (relationalLawLater_effective false true)
  simp at hft

theorem relationalLaw_constantObserver_deterministic :
    LawRelationRightUnique
      (EffectiveLawRelation (fun _ : RelationalLawState ↦ Unit.unit) relationalLawLater) := by
  intro b c d _hbc _hbd
  exact Subsingleton.elim c d

/-- Closed theorem package: relation survival, descent classification, lax composition, strict
observer scaling, and a strict splice/branching countermodel. -/
theorem relationalLawRenormalization_unconditional :
    (∀ {X : Type u} {B : Type v} (q : X → B), Function.Surjective q →
      ∀ f : X → X, LawRelationTotal (EffectiveLawRelation q f)) ∧
    (∀ {X : Type u} {B : Type v} (q : X → B) (f : X → X),
      LawRelationRightUnique (EffectiveLawRelation q f) ↔
        UnaryPreserves f (ObserverKernel q)) ∧
    (∀ {X : Type u} {B : Type v} (q : X → B) (f g : X → X),
      ∀ ⦃b c⦄, EffectiveLawRelation q (g ∘ f) b c →
        LawRelationComp (EffectiveLawRelation q f) (EffectiveLawRelation q g) b c) ∧
    (∀ {X : Type u} {B : Type v} {C : Type w} (q : X → B) (p : B → C)
      (f : X → X) (c d : C),
      EffectiveLawRelation (p ∘ q) f c d ↔
        LawRelationPushforward p (EffectiveLawRelation q f) c d) ∧
    (LawRelationComp
        (EffectiveLawRelation relationalLawObserver relationalLawPre)
        (EffectiveLawRelation relationalLawObserver relationalLawLater)
        false true ∧
      ¬ EffectiveLawRelation relationalLawObserver
        (relationalLawLater ∘ relationalLawPre) false true) := by
  exact ⟨
    (fun q hq f ↦ effectiveLawRelation_total q hq f),
    effectiveLawRelation_rightUnique_iff_kernelPreserved,
    effectiveLawRelation_comp_subset,
    effectiveLawRelation_serialObserver,
    relationalLaw_strict_splice_witness⟩

end GaloisForLFunctions.HTGeometry
