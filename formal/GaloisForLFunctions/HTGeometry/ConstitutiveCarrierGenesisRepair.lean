import GaloisForLFunctions.HTGeometry.ConstitutiveBipolarObserverRepair

/-!
# Conservative carrier genesis and bipolar repair

A two-sided conservative extension of unary law language transports every finite word in both
directions along the old-carrier map.  The future-retaining repair therefore pulls back exactly.
The future-forgetting repair has only a one-sided comparison: fresh states may mediate new
identifications among old states.  A compatible semantic retraction restores exactness.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- Every old law lifts to the enlarged carrier and every enlarged law restricts to an old law. -/
def ConservativeUnaryLawExtension {α : Type u} {β : Type v} (j : α → β)
    (F : Set (α → α)) (G : Set (β → β)) : Prop :=
  (∀ f ∈ F, ∃ g ∈ G, ∀ x, g (j x) = j (f x)) ∧
  (∀ g ∈ G, ∃ f ∈ F, ∀ x, g (j x) = j (f x))

/-- A retraction compatible with the observer relations and every enlarged law. -/
def CompatibleUnaryLawRetraction {α : Type u} {β : Type v} (j : α → β)
    (F : Set (α → α)) (G : Set (β → β))
    (Eα : α → α → Prop) (Eβ : β → β → Prop) (r : β → α) : Prop :=
  (∀ x, r (j x) = x) ∧
  (∀ ⦃y z⦄, Eβ y z → Eα (r y) (r z)) ∧
  (∀ g ∈ G, ∃ f ∈ F, ∀ y, r (g y) = f (r y))

/-- Every enlarged word restricts to an admitted old word. -/
theorem conservativeUnaryLawExtension_restrict_word {α : Type u} {β : Type v}
    {j : α → β} {F : Set (α → α)} {G : Set (β → β)}
    (h : ConservativeUnaryLawExtension j F G) (word : List (β → β))
    (hword : UnaryLawWordAdmitted G word) :
    ∃ oldWord : List (α → α), UnaryLawWordAdmitted F oldWord ∧
      ∀ x, UnaryLawWordRun word (j x) = j (UnaryLawWordRun oldWord x) := by
  induction word with
  | nil =>
      exact ⟨[], by simp [UnaryLawWordAdmitted], fun _ ↦ rfl⟩
  | cons g tail ih =>
      have hg : g ∈ G := hword g (by simp)
      obtain ⟨f, hf, hfg⟩ := h.2 g hg
      have htail : UnaryLawWordAdmitted G tail := by
        intro k hk
        exact hword k (by simp [hk])
      obtain ⟨oldTail, holdTail, hrun⟩ := ih htail
      refine ⟨f :: oldTail, ?_, ?_⟩
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact hf
        · exact holdTail k hk
      · intro x
        simp only [unaryLawWordRun_cons]
        rw [hfg x, hrun (f x)]

/-- Every admitted old word lifts to an enlarged word. -/
theorem conservativeUnaryLawExtension_lift_word {α : Type u} {β : Type v}
    {j : α → β} {F : Set (α → α)} {G : Set (β → β)}
    (h : ConservativeUnaryLawExtension j F G) (word : List (α → α))
    (hword : UnaryLawWordAdmitted F word) :
    ∃ newWord : List (β → β), UnaryLawWordAdmitted G newWord ∧
      ∀ x, UnaryLawWordRun newWord (j x) = j (UnaryLawWordRun word x) := by
  induction word with
  | nil =>
      exact ⟨[], by simp [UnaryLawWordAdmitted], fun _ ↦ rfl⟩
  | cons f tail ih =>
      have hf : f ∈ F := hword f (by simp)
      obtain ⟨g, hg, hfg⟩ := h.1 f hf
      have htail : UnaryLawWordAdmitted F tail := by
        intro k hk
        exact hword k (by simp [hk])
      obtain ⟨newTail, hnewTail, hrun⟩ := ih htail
      refine ⟨g :: newTail, ?_, ?_⟩
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact hg
        · exact hnewTail k hk
      · intro x
        simp only [unaryLawWordRun_cons]
        rw [hfg x, hrun (f x)]

/-- Future-retaining repair obeys exact base change along conservative carrier genesis. -/
theorem unaryLawInterior_pullback_conservative {α : Type u} {β : Type v}
    {j : α → β} {F : Set (α → α)} {G : Set (β → β)}
    {Eα : α → α → Prop} {Eβ : β → β → Prop}
    (h : ConservativeUnaryLawExtension j F G)
    (hE : ∀ x y, Eα x y ↔ Eβ (j x) (j y)) (x y : α) :
    UnaryLawInterior G Eβ (j x) (j y) ↔ UnaryLawInterior F Eα x y := by
  constructor
  · intro hnew oldWord holdWord
    obtain ⟨newWord, hnewWord, hrun⟩ :=
      conservativeUnaryLawExtension_lift_word h oldWord holdWord
    have hrel := hnew newWord hnewWord
    rw [hrun x, hrun y] at hrel
    exact (hE _ _).mpr hrel
  · intro hold newWord hnewWord
    obtain ⟨oldWord, holdWord, hrun⟩ :=
      conservativeUnaryLawExtension_restrict_word h newWord hnewWord
    have hrel := hold oldWord holdWord
    apply (hE _ _).mp at hrel
    rw [hrun x, hrun y]
    exact hrel

/-- Future-forgetting repair has a canonical lax comparison along carrier genesis. -/
theorem unaryLawClosure_pullback_lax {α : Type u} {β : Type v}
    {j : α → β} {F : Set (α → α)} {G : Set (β → β)}
    {Eα : α → α → Prop} {Eβ : β → β → Prop}
    (h : ConservativeUnaryLawExtension j F G)
    (hE : ∀ x y, Eα x y ↔ Eβ (j x) (j y)) :
    ∀ ⦃x y⦄, UnaryLawClosure F Eα x y → UnaryLawClosure G Eβ (j x) (j y) := by
  let R : α → α → Prop := fun x y ↦ UnaryLawClosure G Eβ (j x) (j y)
  have hReq : Equivalence R := by
    exact ⟨fun x ↦ (unaryLawClosure_equivalence G Eβ).refl (j x),
      fun hxy ↦ (unaryLawClosure_equivalence G Eβ).symm hxy,
      fun hxy hyz ↦ (unaryLawClosure_equivalence G Eβ).trans hxy hyz⟩
  have hbase : ∀ ⦃x y⦄, Eα x y → R x y := by
    intro x y hxy
    exact unaryLawClosure_contains G Eβ ((hE x y).mp hxy)
  have hpres : ∀ f ∈ F, UnaryPreserves f R := by
    intro f hf
    obtain ⟨g, hg, hfg⟩ := h.1 f hf
    intro x y hxy
    have hnext := unaryLawClosure_preserves G Eβ hg hxy
    rw [hfg x, hfg y] at hnext
    exact hnext
  exact unaryLawClosure_least hReq hbase hpres

/-- A semantic retraction compatible with laws and relations gives the missing reverse comparison. -/
theorem unaryLawClosure_pullback_of_compatibleRetraction {α : Type u} {β : Type v}
    {j : α → β} {F : Set (α → α)} {G : Set (β → β)}
    {Eα : α → α → Prop} {Eβ : β → β → Prop} {r : β → α}
    (hr : CompatibleUnaryLawRetraction j F G Eα Eβ r) :
    ∀ ⦃x y⦄, UnaryLawClosure G Eβ (j x) (j y) → UnaryLawClosure F Eα x y := by
  let S : β → β → Prop := fun y z ↦ UnaryLawClosure F Eα (r y) (r z)
  have hSeq : Equivalence S := by
    exact ⟨fun y ↦ (unaryLawClosure_equivalence F Eα).refl (r y),
      fun hyz ↦ (unaryLawClosure_equivalence F Eα).symm hyz,
      fun hyz hzw ↦ (unaryLawClosure_equivalence F Eα).trans hyz hzw⟩
  have hbase : ∀ ⦃y z⦄, Eβ y z → S y z := by
    intro y z hyz
    exact unaryLawClosure_contains F Eα (hr.2.1 hyz)
  have hpres : ∀ g ∈ G, UnaryPreserves g S := by
    intro g hg
    obtain ⟨f, hf, hfg⟩ := hr.2.2 g hg
    intro y z hyz
    have hnext := unaryLawClosure_preserves F Eα hf hyz
    rw [← hfg y, ← hfg z] at hnext
    exact hnext
  intro x y hxy
  have hresult : S (j x) (j y) := unaryLawClosure_least hSeq hbase hpres hxy
  simpa [S, hr.1 x, hr.1 y] using hresult

/-- In the retraction chamber, future-forgetting repair also obeys exact base change. -/
theorem unaryLawClosure_pullback_conservative_iff {α : Type u} {β : Type v}
    {j : α → β} {F : Set (α → α)} {G : Set (β → β)}
    {Eα : α → α → Prop} {Eβ : β → β → Prop} {r : β → α}
    (h : ConservativeUnaryLawExtension j F G)
    (hE : ∀ x y, Eα x y ↔ Eβ (j x) (j y))
    (hr : CompatibleUnaryLawRetraction j F G Eα Eβ r) (x y : α) :
    UnaryLawClosure G Eβ (j x) (j y) ↔ UnaryLawClosure F Eα x y := by
  exact ⟨(fun hxy ↦ unaryLawClosure_pullback_of_compatibleRetraction hr hxy),
    (fun hxy ↦ unaryLawClosure_pullback_lax h hE hxy)⟩

/-! ## Sharp three-state fresh-return cell -/

/-- Embed two old Boolean states as the fixed states of the bipolar repair cell. -/
def carrierGenesisInjection : Bool → BipolarRepairState
  | false => .a
  | true => .c

theorem carrierGenesisInjection_injective : Function.Injective carrierGenesisInjection := by
  intro x y h
  cases x <;> cases y <;> simp [carrierGenesisInjection] at h ⊢

theorem carrierGenesisCell_conservativeExtension :
    ConservativeUnaryLawExtension carrierGenesisInjection
      ({id} : Set (Bool → Bool))
      ({bipolarRepairStep} : Set (BipolarRepairState → BipolarRepairState)) := by
  constructor
  · intro f hf
    simp only [Set.mem_singleton_iff] at hf
    subst f
    refine ⟨bipolarRepairStep, by simp, ?_⟩
    intro x
    cases x <;> rfl
  · intro g hg
    simp only [Set.mem_singleton_iff] at hg
    subst g
    refine ⟨id, by simp, ?_⟩
    intro x
    cases x <;> rfl

theorem carrierGenesisCell_relationRestriction (x y : Bool) :
    x = y ↔ BipolarRepairRelation (carrierGenesisInjection x) (carrierGenesisInjection y) := by
  cases x <;> cases y <;>
    simp [carrierGenesisInjection, BipolarRepairRelation, ObserverKernel, bipolarRepairObserver]

theorem carrierGenesisOldInterior_eq_equality :
    UnaryLawInterior ({id} : Set (Bool → Bool)) Eq = Eq := by
  apply (unaryLawInterior_fixed_iff ({id} : Set (Bool → Bool)) Eq
    ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩).2
  intro f hf
  simp only [Set.mem_singleton_iff] at hf
  subst f
  intro x y hxy
  exact hxy

theorem carrierGenesisOldClosure_eq_equality :
    UnaryLawClosure ({id} : Set (Bool → Bool)) Eq = Eq := by
  apply (unaryLawClosure_fixed_iff ({id} : Set (Bool → Bool)) Eq
    ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩).2
  intro f hf
  simp only [Set.mem_singleton_iff] at hf
  subst f
  intro x y hxy
  exact hxy

/-- The old coarse repair separates the two old states, while the enlarged coarse repair joins
them through the fresh state. -/
def CarrierGenesisFreshReturnDefect : Prop :=
  UnaryLawClosure
      ({bipolarRepairStep} : Set (BipolarRepairState → BipolarRepairState))
      BipolarRepairRelation (carrierGenesisInjection false) (carrierGenesisInjection true) ∧
    ¬ UnaryLawClosure ({id} : Set (Bool → Bool)) Eq false true

/-- Carrier growth changes no old execution but makes coarse repair identify the two old states. -/
theorem carrierGenesisCell_freshReturn_strict : CarrierGenesisFreshReturnDefect := by
  constructor
  · rw [bipolarRepairClosure_eq_universal]
    trivial
  · rw [carrierGenesisOldClosure_eq_equality]
    exact Bool.false_ne_true

theorem carrierGenesisCell_finePullback_exact (x y : Bool) :
    UnaryLawInterior
        ({bipolarRepairStep} : Set (BipolarRepairState → BipolarRepairState))
        BipolarRepairRelation (carrierGenesisInjection x) (carrierGenesisInjection y) ↔
      UnaryLawInterior ({id} : Set (Bool → Bool)) Eq x y := by
  exact unaryLawInterior_pullback_conservative
    carrierGenesisCell_conservativeExtension carrierGenesisCell_relationRestriction x y

theorem carrierGenesisCell_noCompatibleRetraction :
    ¬ ∃ r : BipolarRepairState → Bool,
      CompatibleUnaryLawRetraction carrierGenesisInjection
        ({id} : Set (Bool → Bool))
        ({bipolarRepairStep} : Set (BipolarRepairState → BipolarRepairState))
        Eq BipolarRepairRelation r := by
  rintro ⟨r, hr⟩
  have hab : BipolarRepairRelation .a .b := rfl
  have hrab : r .a = r .b := hr.2.1 hab
  obtain ⟨f, hf, hfg⟩ := hr.2.2 bipolarRepairStep (by simp)
  simp only [Set.mem_singleton_iff] at hf
  subst f
  have hstep := hfg BipolarRepairState.b
  have hra : r BipolarRepairState.a = false := hr.1 false
  have hrc : r BipolarRepairState.c = true := hr.1 true
  simp only [bipolarRepairStep, id_eq] at hstep
  have hfalseTrue : false = true := hra.symm.trans (hrab.trans (hstep.symm.trans hrc))
  exact Bool.false_ne_true hfalseTrue

/-- Unconditional capstone: exact fine base change, lax coarse base change, the retraction chamber,
and a strict fresh-return defect with unchanged old execution. -/
theorem carrierGenesisRepairMechanism_unconditional :
    (∀ (α : Type u) (β : Type v) (j : α → β)
      (F : Set (α → α)) (G : Set (β → β))
      (Eα : α → α → Prop) (Eβ : β → β → Prop),
      ConservativeUnaryLawExtension j F G →
      (∀ x y, Eα x y ↔ Eβ (j x) (j y)) →
      ∀ x y, UnaryLawInterior G Eβ (j x) (j y) ↔ UnaryLawInterior F Eα x y) ∧
    (∀ (α : Type u) (β : Type v) (j : α → β)
      (F : Set (α → α)) (G : Set (β → β))
      (Eα : α → α → Prop) (Eβ : β → β → Prop),
      ConservativeUnaryLawExtension j F G →
      (∀ x y, Eα x y ↔ Eβ (j x) (j y)) →
      ∀ ⦃x y⦄, UnaryLawClosure F Eα x y → UnaryLawClosure G Eβ (j x) (j y)) ∧
    (∀ (α : Type u) (β : Type v) (j : α → β)
      (F : Set (α → α)) (G : Set (β → β))
      (Eα : α → α → Prop) (Eβ : β → β → Prop) (r : β → α),
      ConservativeUnaryLawExtension j F G →
      (∀ x y, Eα x y ↔ Eβ (j x) (j y)) →
      CompatibleUnaryLawRetraction j F G Eα Eβ r →
      ∀ x y, UnaryLawClosure G Eβ (j x) (j y) ↔ UnaryLawClosure F Eα x y) ∧
    Function.Injective carrierGenesisInjection ∧
    CarrierGenesisFreshReturnDefect ∧
    (¬ ∃ r : BipolarRepairState → Bool,
      CompatibleUnaryLawRetraction carrierGenesisInjection
        ({id} : Set (Bool → Bool))
        ({bipolarRepairStep} : Set (BipolarRepairState → BipolarRepairState))
        Eq BipolarRepairRelation r) := by
  exact ⟨(fun _ _ _ _ _ _ _ h hE ↦ unaryLawInterior_pullback_conservative h hE),
    (fun _ _ _ _ _ _ _ h hE ↦ unaryLawClosure_pullback_lax h hE),
    (fun _ _ _ _ _ _ _ _ h hE hr ↦ unaryLawClosure_pullback_conservative_iff h hE hr),
    carrierGenesisInjection_injective,
    carrierGenesisCell_freshReturn_strict,
    carrierGenesisCell_noCompatibleRetraction⟩

end GaloisForLFunctions.HTGeometry
