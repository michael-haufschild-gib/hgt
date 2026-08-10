import GaloisForLFunctions.HTGeometry.ConstitutiveSemanticTransportArityPromotion

/-!
# Controlled naturality and symmetry allocation

When old semantic fibres are group orbits, an equivariant reporter is operationally effective
exactly when the old symmetry moves an attained response.  Deterministic equivariance preserves
point stabilizers (Curie's principle), while fixing an auxiliary mark restricts a jointly
equivariant law to the mark stabilizer.  Thus invariant output, equivariant symmetry export, and
marked symmetry reduction are distinct formation channels.

All declarations are source-independent.  No RH or route premise occurs.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w z

namespace ControlledNaturalityMechanics

/-- Old semantic fibres are exactly the orbits of the declared symmetry action. -/
def OrbitCompleteReporter {G : Type u} {X : Type v} {Q : Type w}
    [Group G] [MulAction G X] (q : X → Q) : Prop :=
  ∀ (x y : X), q x = q y ↔ y ∈ MulAction.orbit G x

/-- A reporter transports the source action into the target action. -/
def EquivariantReporter {G : Type u} {X : Type v} {Z : Type w}
    [Group G] [MulAction G X] [MulAction G Z] (c : X → Z) : Prop :=
  ∀ (g : G) (x : X), c (g • x) = g • c x

/-- Operational novelty relative to an arbitrary old semantic reporter. -/
def ReporterEffectiveRelative {X : Type u} {Q : Type v} {Z : Type w}
    (q : X → Q) (c : X → Z) : Prop :=
  ¬ ReporterDeterminedBy q c

/-- **Symmetry-export criterion.** Under orbit-complete old semantics, an equivariant reporter is
effective exactly when some old symmetry moves an attained response. -/
theorem reporterEffectiveRelative_iff_symmetry_export
    {G : Type u} {X : Type v} {Q : Type w} {Z : Type z}
    [Group G] [MulAction G X] [MulAction G Z]
    (q : X → Q) (c : X → Z) (hq : OrbitCompleteReporter (G := G) q)
    (hc : EquivariantReporter (G := G) c) :
    ReporterEffectiveRelative q c ↔ ∃ (g : G) (x : X), g • c x ≠ c x := by
  constructor
  · intro h
    unfold ReporterEffectiveRelative ReporterDeterminedBy at h
    push Not at h
    obtain ⟨x, y, hqxy, hcxy⟩ := h
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp ((hq x y).mp hqxy)
    subst y
    refine ⟨g, x, ?_⟩
    intro hfixed
    exact hcxy ((hc g x).trans hfixed).symm
  · rintro ⟨g, x, hmoved⟩ hdescent
    have hqxy : q x = q (g • x) :=
      (hq x (g • x)).mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩)
    have hcxy : c x = c (g • x) := hdescent hqxy
    exact hmoved (hcxy.trans (hc g x)).symm

/-- Equivalent inertness law: an equivariant reporter descends through complete orbit semantics
exactly when the group fixes every attained response. -/
theorem reporterDeterminedBy_iff_attained_fixed
    {G : Type u} {X : Type v} {Q : Type w} {Z : Type z}
    [Group G] [MulAction G X] [MulAction G Z]
    (q : X → Q) (c : X → Z) (hq : OrbitCompleteReporter (G := G) q)
    (hc : EquivariantReporter (G := G) c) :
    ReporterDeterminedBy q c ↔ ∀ (g : G) (x : X), g • c x = c x := by
  constructor
  · intro h g x
    have hqxy : q x = q (g • x) :=
      (hq x (g • x)).mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩)
    exact (h hqxy |>.trans (hc g x)).symm
  · intro h x y hqxy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp ((hq x y).mp hqxy)
    subst y
    exact ((hc g x).trans (h g x)).symm

/-- An invariant attained target cannot split an orbit-complete semantic fibre. -/
theorem invariantAttainedReporter_inert
    {G : Type u} {X : Type v} {Q : Type w} {Z : Type z}
    [Group G] [MulAction G X] [MulAction G Z]
    (q : X → Q) (c : X → Z) (hq : OrbitCompleteReporter (G := G) q)
    (hc : EquivariantReporter (G := G) c)
    (hfixed : ∀ (g : G) (x : X), g • c x = c x) :
    ReporterDeterminedBy q c :=
  (reporterDeterminedBy_iff_attained_fixed q c hq hc).mpr hfixed

/-- **Curie stabilizer inheritance.** Every input symmetry remains an output symmetry under a
deterministic equivariant reporter. -/
theorem input_stabilizer_le_output_stabilizer
    {G : Type u} {X : Type v} {Z : Type w}
    [Group G] [MulAction G X] [MulAction G Z]
    (c : X → Z) (hc : EquivariantReporter (G := G) c) (x : X) :
    MulAction.stabilizer G x ≤ MulAction.stabilizer G (c x) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  calc
    g • c x = c (g • x) := (hc g x).symm
    _ = c x := congrArg c hg

/-- Joint equivariance of a law depending on a source mark. -/
def JointlyEquivariantLaw {G : Type u} {X : Type v} {M : Type w} {Z : Type z}
    [Group G] [MulAction G X] [MulAction G M] [MulAction G Z]
    (F : X → M → Z) : Prop :=
  ∀ (g : G) (x : X) (m : M), F (g • x) (g • m) = g • F x m

/-- Fixing a mark retains deterministic equivariance under every symmetry stabilizing that mark. -/
theorem fixedMark_equivariant_under_stabilizer
    {G : Type u} {X : Type v} {M : Type w} {Z : Type z}
    [Group G] [MulAction G X] [MulAction G M] [MulAction G Z]
    (F : X → M → Z) (hF : JointlyEquivariantLaw (G := G) F)
    (m : M) (g : G) (hg : g ∈ MulAction.stabilizer G m) (x : X) :
    F (g • x) m = g • F x m := by
  have hm : g • m = m := MulAction.mem_stabilizer_iff.mp hg
  calc
    F (g • x) m = F (g • x) (g • m) := by rw [hm]
    _ = g • F x m := hF g x m

/-! ## Sharp scope cells -/

/-- Constant semantics on two states. -/
def unitSemantics : Bool → Unit := fun _ ↦ ()

/-- Identity Boolean reporter. -/
def boolIdentityReporter : Bool → Bool := id

/-- Without orbit-completeness, an effective reporter can have no moved target value: the trivial
group has singleton orbits while the old reporter has one two-point fibre. -/
theorem orbitCompleteness_is_loadBearing :
    ReporterEffectiveRelative unitSemantics boolIdentityReporter ∧
    (∀ (g : Unit) (x : Bool), g • boolIdentityReporter x = boolIdentityReporter x) ∧
    ¬ OrbitCompleteReporter (G := Unit) unitSemantics := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hv : boolIdentityReporter false = boolIdentityReporter true := h rfl
    simp [boolIdentityReporter] at hv
  · intro g x
    cases g
    rfl
  · intro h
    have horbit : true ∈ MulAction.orbit Unit false := (h false true).mp rfl
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp horbit
    cases g
    simp at hg

/-- Constant jointly equivariant law used to show that a moved mark alone need not create an
effective reporter. -/
def constantMarkedLaw : Unit → Bool → Unit := fun _ _ ↦ ()

theorem constantMarkedLaw_jointlyEquivariant :
    JointlyEquivariantLaw (G := Equiv.Perm Bool) constantMarkedLaw := by
  intro g x m
  rfl

/-- A genuinely moved mark can feed a reporter which remains constant and operationally inert. -/
theorem marking_is_not_sufficient :
    (∃ g : Equiv.Perm Bool, g • false ≠ false) ∧
    ReporterDeterminedBy (fun _ : Unit ↦ ()) (fun x ↦ constantMarkedLaw x false) := by
  constructor
  · exact ⟨Equiv.swap false true, by simp⟩
  · intro x y hxy
    rfl

/-- Closed capstone combining both sharp scope cells. -/
theorem controlledNaturalityMechanics_closed :
    (ReporterEffectiveRelative unitSemantics boolIdentityReporter ∧
      (∀ (g : Unit) (x : Bool), g • boolIdentityReporter x = boolIdentityReporter x) ∧
      ¬ OrbitCompleteReporter (G := Unit) unitSemantics) ∧
    ((∃ g : Equiv.Perm Bool, g • false ≠ false) ∧
      ReporterDeterminedBy (fun _ : Unit ↦ ()) (fun x ↦ constantMarkedLaw x false)) :=
  ⟨orbitCompleteness_is_loadBearing, marking_is_not_sufficient⟩

end ControlledNaturalityMechanics

end GaloisForLFunctions.HTGeometry
