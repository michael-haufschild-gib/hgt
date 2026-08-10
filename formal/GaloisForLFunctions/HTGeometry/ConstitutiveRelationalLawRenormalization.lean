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

/-- Direct image of a composite is contained in the composite of the direct images.  The latter
may match two distinct intermediate states having the same observation. -/
theorem lawRelationPushforward_comp_subset {B : Type v} {C : Type w}
    (p : B → C) (R S : B → B → Prop) :
    ∀ ⦃c d⦄, LawRelationPushforward p (LawRelationComp R S) c d →
      LawRelationComp (LawRelationPushforward p R) (LawRelationPushforward p S) c d := by
  rintro c d ⟨b, b', hbc, hb'd, m, hbm, hmb'⟩
  exact ⟨p m, ⟨b, m, hbc, rfl, hbm⟩, ⟨m, b', rfl, hb'd, hmb'⟩⟩

/-- An injective observer introduces no new intermediate-state splices. -/
theorem lawRelationPushforward_comp_exact_of_injective {B : Type v} {C : Type w}
    (p : B → C) (hp : Function.Injective p) (R S : B → B → Prop) (c d : C) :
    LawRelationComp (LawRelationPushforward p R) (LawRelationPushforward p S) c d ↔
      LawRelationPushforward p (LawRelationComp R S) c d := by
  constructor
  · rintro ⟨e, ⟨b, m₁, hbc, hm₁e, hbm₁⟩, ⟨m₂, b', hm₂e, hb'd, hm₂b'⟩⟩
    have hmm : m₁ = m₂ := hp (hm₁e.trans hm₂e.symm)
    subst m₂
    exact ⟨b, b', hbc, hb'd, m₁, hbm₁, hm₂b'⟩
  · intro hcomp
    exact lawRelationPushforward_comp_subset p R S hcomp

/-- Direct image preserves all relation compositions exactly iff the observer is injective. -/
theorem lawRelationPushforward_comp_exact_iff_injective {B : Type v} {C : Type w}
    (p : B → C) :
    (∀ (R S : B → B → Prop) (c d : C),
      LawRelationComp (LawRelationPushforward p R) (LawRelationPushforward p S) c d →
        LawRelationPushforward p (LawRelationComp R S) c d) ↔
      Function.Injective p := by
  constructor
  · intro h x y hxy
    let R : B → B → Prop := fun a b ↦ a = x ∧ b = x
    let S : B → B → Prop := fun a b ↦ a = y ∧ b = y
    have hR : LawRelationPushforward p R (p x) (p x) :=
      ⟨x, x, rfl, rfl, rfl, rfl⟩
    have hS : LawRelationPushforward p S (p x) (p y) :=
      ⟨y, y, hxy.symm, rfl, rfl, rfl⟩
    rcases h R S (p x) (p y) ⟨p x, hR, hS⟩ with
      ⟨a, b, _ha, _hb, m, ⟨_haX, hmX⟩, ⟨hmY, _hbY⟩⟩
    exact hmX.symm.trans hmY
  · intro hp R S c d hcomp
    exact (lawRelationPushforward_comp_exact_of_injective p hp R S c d).1 hcomp

theorem effectiveLawRelation_id_iff {X : Type u} {B : Type v}
    (q : X → B) (hq : Function.Surjective q) (b c : B) :
    EffectiveLawRelation q id b c ↔ b = c := by
  constructor
  · rintro ⟨x, rfl, hxc⟩
    simpa using hxc
  · intro hbc
    obtain ⟨x, hx⟩ := hq b
    exact ⟨x, hx, by simpa using hx.trans hbc⟩

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
  exact (hg x).symm.trans (hbar x)

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
  · intro hcomp
    exact effectiveLawRelation_comp_subset q f g hcomp

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
    exact ⟨x, (congrArg p hxb).trans hbc, (congrArg p hxb').trans hbd⟩

/-- Serial observation and serial execution form a canonical two-step inclusion filtration:
first source-execution splices survive pushforward, then coarse midpoint matching may add more. -/
theorem effectiveLawRelation_interchange_filtration
    {X : Type u} {B : Type v} {C : Type w} (q : X → B) (p : B → C)
    (f g : X → X) :
    (∀ ⦃c d⦄, EffectiveLawRelation (p ∘ q) (g ∘ f) c d →
      LawRelationPushforward p
        (LawRelationComp (EffectiveLawRelation q f) (EffectiveLawRelation q g)) c d) ∧
    (∀ ⦃c d⦄, LawRelationPushforward p
        (LawRelationComp (EffectiveLawRelation q f) (EffectiveLawRelation q g)) c d →
      LawRelationComp
        (LawRelationPushforward p (EffectiveLawRelation q f))
        (LawRelationPushforward p (EffectiveLawRelation q g)) c d) := by
  constructor
  · intro c d hdirect
    rcases (effectiveLawRelation_serialObserver q p (g ∘ f) c d).1 hdirect with
      ⟨b, b', hbc, hb'd, hsource⟩
    exact ⟨b, b', hbc, hb'd, effectiveLawRelation_comp_subset q f g hsource⟩
  · exact lawRelationPushforward_comp_subset p
      (EffectiveLawRelation q f) (EffectiveLawRelation q g)

/-- If the later source law descends at the fine observer, the first interchange layer is exact. -/
theorem effectiveLawRelation_interchange_first_exact_of_later_preserves
    {X : Type u} {B : Type v} {C : Type w} (q : X → B) (p : B → C)
    (f g : X → X) (hg : UnaryPreserves g (ObserverKernel q)) (c d : C) :
    EffectiveLawRelation (p ∘ q) (g ∘ f) c d ↔
      LawRelationPushforward p
        (LawRelationComp (EffectiveLawRelation q f) (EffectiveLawRelation q g)) c d := by
  constructor
  · intro hdirect
    rcases (effectiveLawRelation_serialObserver q p (g ∘ f) c d).1 hdirect with
      ⟨b, b', hbc, hb'd, hsource⟩
    exact ⟨b, b', hbc, hb'd,
      (effectiveLawRelation_comp_exact_of_later_preserves q f g hg b b').2 hsource⟩
  · rintro ⟨b, b', hbc, hb'd, hcomp⟩
    apply (effectiveLawRelation_serialObserver q p (g ∘ f) c d).2
    exact ⟨b, b', hbc, hb'd,
      (effectiveLawRelation_comp_exact_of_later_preserves q f g hg b b').1 hcomp⟩

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
    have htf : true = false := relationalLawComposite_only_false h
    exact Bool.noConfusion htf

/-- First independence cell: execution creates a strict splice while the further observer is
injective, so the second interchange layer adds nothing. -/
theorem relationalLaw_firstInterchangeGap_strict :
    (¬ EffectiveLawRelation ((id : Bool → Bool) ∘ relationalLawObserver)
      (relationalLawLater ∘ relationalLawPre) false true) ∧
    LawRelationPushforward (id : Bool → Bool)
      (LawRelationComp
        (EffectiveLawRelation relationalLawObserver relationalLawPre)
        (EffectiveLawRelation relationalLawObserver relationalLawLater)) false true ∧
    LawRelationComp
      (LawRelationPushforward (id : Bool → Bool)
        (EffectiveLawRelation relationalLawObserver relationalLawPre))
      (LawRelationPushforward (id : Bool → Bool)
        (EffectiveLawRelation relationalLawObserver relationalLawLater)) false true := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply relationalLaw_strict_splice_witness.2
    change EffectiveLawRelation relationalLawObserver
      (relationalLawLater ∘ relationalLawPre) false true at h
    exact h
  · exact ⟨false, true, rfl, rfl, relationalLaw_strict_splice_witness.1⟩
  · refine ⟨true, ?_, ?_⟩
    · exact ⟨false, true, rfl, rfl, relationalLawPre_effective false⟩
    · exact ⟨true, true, rfl, rfl, relationalLawLater_effective true true⟩

theorem relationalLaw_fine_deterministic :
    LawRelationRightUnique (EffectiveLawRelation id relationalLawLater) := by
  apply (effectiveLawRelation_rightUnique_iff_kernelPreserved id relationalLawLater).2
  intro x y hxy
  change x = y at hxy
  subst y
  rfl

/-- Second independence cell: fine function graphs compose exactly, while the noninjective further
observer creates a strict new midpoint splice. -/
theorem relationalLaw_secondInterchangeGap_strict :
    (¬ EffectiveLawRelation (relationalLawObserver ∘ id)
      (relationalLawLater ∘ relationalLawPre) false true) ∧
    (¬ LawRelationPushforward relationalLawObserver
      (LawRelationComp
        (EffectiveLawRelation id relationalLawPre)
        (EffectiveLawRelation id relationalLawLater)) false true) ∧
    LawRelationComp
      (LawRelationPushforward relationalLawObserver
        (EffectiveLawRelation id relationalLawPre))
      (LawRelationPushforward relationalLawObserver
        (EffectiveLawRelation id relationalLawLater)) false true := by
  have hlater :
      UnaryPreserves relationalLawLater (ObserverKernel (id : RelationalLawState → RelationalLawState)) :=
    (effectiveLawRelation_rightUnique_iff_kernelPreserved id relationalLawLater).1
      relationalLaw_fine_deterministic
  have hfirst := effectiveLawRelation_interchange_first_exact_of_later_preserves
    (id : RelationalLawState → RelationalLawState) relationalLawObserver
    relationalLawPre relationalLawLater hlater false true
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply relationalLaw_strict_splice_witness.2
    change EffectiveLawRelation relationalLawObserver
      (relationalLawLater ∘ relationalLawPre) false true at h
    exact h
  · intro hmiddle
    apply relationalLaw_strict_splice_witness.2
    have hdirect := hfirst.2 hmiddle
    change EffectiveLawRelation relationalLawObserver
      (relationalLawLater ∘ relationalLawPre) false true at hdirect
    exact hdirect
  · refine ⟨true, ?_, ?_⟩
    · exact ⟨(false, false), (true, false), rfl, rfl,
        (false, false), rfl, rfl⟩
    · exact ⟨(true, true), (true, false), rfl, rfl,
        (true, true), rfl, rfl⟩

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

/-- Closed interchange package: every serial observer/execution square has two nested defect
layers, and the observer-induced layer vanishes for all relations exactly at injective observers. -/
theorem relationalLawInterchange_unconditional :
    (∀ {X : Type u} {B : Type v} {C : Type w} (q : X → B) (p : B → C)
      (f g : X → X),
      (∀ ⦃c d⦄, EffectiveLawRelation (p ∘ q) (g ∘ f) c d →
        LawRelationPushforward p
          (LawRelationComp (EffectiveLawRelation q f) (EffectiveLawRelation q g)) c d) ∧
      (∀ ⦃c d⦄, LawRelationPushforward p
          (LawRelationComp (EffectiveLawRelation q f) (EffectiveLawRelation q g)) c d →
        LawRelationComp
          (LawRelationPushforward p (EffectiveLawRelation q f))
          (LawRelationPushforward p (EffectiveLawRelation q g)) c d)) ∧
    (∀ {B : Type v} {C : Type w} (p : B → C),
      (∀ (R S : B → B → Prop) (c d : C),
        LawRelationComp (LawRelationPushforward p R) (LawRelationPushforward p S) c d →
          LawRelationPushforward p (LawRelationComp R S) c d) ↔
        Function.Injective p) := by
  exact ⟨effectiveLawRelation_interchange_filtration,
    lawRelationPushforward_comp_exact_iff_injective⟩

end GaloisForLFunctions.HTGeometry
