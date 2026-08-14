import GaloisForLFunctions.HTGeometry.ConstitutiveAnalyticAdmissionHull
import Mathlib.Topology.Maps.Proper.Basic

namespace HTGeometry

noncomputable section

open Function Set Topology
open scoped BigOperators

/-!
# Closed analytic-admission hull

This module closes the coordinate-free topology and reporter-duality surface of bipolar admission.
On a compact Hausdorff source, the scalar-reporter relation is the least closed equivalence
containing the primitive relation.  It is therefore an extensive, monotone, idempotent closure
operator, has the expected join law, and gives exact algebraic/analytic conflict criteria.  The
critical shell also carries the paper's exact finitely-supported Dirac total-variation loss.
-/

/-- Graph of a binary relation, regarded as a subset of the square. -/
def admissionRelationGraph {X : Type*} (R : X → X → Prop) : Set (X × X) :=
  {p | R p.1 p.2}

/-- A setoid has closed graph in the source square. -/
def IsClosedAdmissionSetoid {X : Type*} [TopologicalSpace X] (s : Setoid X) : Prop :=
  IsClosed (admissionRelationGraph s)

/-- For a closed setoid on a compact space, its quotient map is closed. -/
theorem quotientMk_isClosedMap_of_isClosedAdmissionSetoid
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (s : Setoid X) (hs : IsClosedAdmissionSetoid s) :
    IsClosedMap (Quotient.mk' : X → Quotient s) := by
  intro C hC
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
  let A : Set (X × X) := admissionRelationGraph s ∩ (Set.univ ×ˢ C)
  have hA : IsClosed A := hs.inter (isClosed_univ.prod hC)
  have hsat :
      (Quotient.mk' : X → Quotient s) ⁻¹' ((Quotient.mk' : X → Quotient s) '' C) =
        Prod.fst '' A := by
    ext x
    constructor
    · rintro ⟨y, hyC, hyx⟩
      refine ⟨(x, y), ⟨?_, ⟨Set.mem_univ x, hyC⟩⟩, rfl⟩
      exact s.symm ((Quotient.eq).mp hyx)
    · rintro ⟨p, ⟨hp, -, hpC⟩, hpx⟩
      subst x
      refine ⟨p.2, hpC, ?_⟩
      exact (Quotient.eq).mpr (s.symm hp)
  rw [hsat]
  exact isClosedMap_fst_of_compactSpace A hA

/-- A closed equivalence relation on a compact Hausdorff space has Hausdorff quotient. -/
theorem t2Space_quotient_of_isClosedAdmissionSetoid
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (s : Setoid X) (hs : IsClosedAdmissionSetoid s) : T2Space (Quotient s) := by
  have hqclosed := quotientMk_isClosedMap_of_isClosedAdmissionSetoid s hs
  constructor
  intro a b hab
  obtain ⟨x, rfl⟩ := Quotient.exists_rep a
  obtain ⟨y, rfl⟩ := Quotient.exists_rep b
  let Fx : Set X := {z | s z x}
  let Fy : Set X := {z | s z y}
  have hFx : IsClosed Fx := by
    change IsClosed ((fun z : X => (z, x)) ⁻¹' admissionRelationGraph s)
    exact hs.preimage (continuous_id.prodMk continuous_const)
  have hFy : IsClosed Fy := by
    change IsClosed ((fun z : X => (z, y)) ⁻¹' admissionRelationGraph s)
    exact hs.preimage (continuous_id.prodMk continuous_const)
  have hdisj : Disjoint Fx Fy := Set.disjoint_left.mpr (by
    intro z hzx hzy
    apply hab
    exact (Quotient.eq).mpr (s.trans (s.symm hzx) hzy))
  have hsub : Fx ⊆ Fyᶜ := Set.disjoint_left.mp hdisj
  obtain ⟨U, hUopen, hFxU, hclU⟩ :=
    normal_exists_closure_subset hFx hFy.isOpen_compl hsub
  let q : X → Quotient s := Quotient.mk'
  let OA : Set (Quotient s) := (q '' Uᶜ)ᶜ
  let OB : Set (Quotient s) := (q '' closure U)ᶜ
  have hOAopen : IsOpen OA :=
    (hqclosed Uᶜ (isClosed_compl_iff.mpr hUopen)).isOpen_compl
  have hOBopen : IsOpen OB :=
    (hqclosed (closure U) isClosed_closure).isOpen_compl
  have hxOA : q x ∈ OA := by
    intro hx
    rcases hx with ⟨z, hzU, hzx⟩
    exact hzU (hFxU ((Quotient.eq).mp hzx))
  have hyOB : q y ∈ OB := by
    intro hy
    rcases hy with ⟨z, hzcl, hzy⟩
    exact (hclU hzcl) ((Quotient.eq).mp hzy)
  refine ⟨OA, OB, hOAopen, hOBopen, hxOA, hyOB, ?_⟩
  apply Set.disjoint_left.mpr
  intro c hcA hcB
  obtain ⟨z, hz⟩ := Quotient.exists_rep c
  have hzU : z ∈ U := by
    by_contra hznot
    exact hcA ⟨z, hznot, hz⟩
  exact hcB ⟨z, subset_closure hzU, hz⟩

theorem analyticAdmissionRel_refl
    {X : Type*} [TopologicalSpace X] (R : X → X → Prop) (x : X) :
    analyticAdmissionRel R x x := rfl

theorem analyticAdmissionRel_symm
    {X : Type*} [TopologicalSpace X] {R : X → X → Prop} {x y : X}
    (hxy : analyticAdmissionRel R x y) : analyticAdmissionRel R y x :=
  hxy.symm

theorem analyticAdmissionRel_trans
    {X : Type*} [TopologicalSpace X] {R : X → X → Prop} {x y z : X}
    (hxy : analyticAdmissionRel R x y) (hyz : analyticAdmissionRel R y z) :
    analyticAdmissionRel R x z :=
  hxy.trans hyz

/-- Analytic admission, bundled as an equivalence relation. -/
def analyticAdmissionSetoid {X : Type*} [TopologicalSpace X]
    (R : X → X → Prop) : Setoid X where
  r := analyticAdmissionRel R
  iseqv := ⟨analyticAdmissionRel_refl R, @analyticAdmissionRel_symm X _ R,
    @analyticAdmissionRel_trans X _ R⟩

/-- The analytic-admission relation has closed graph. -/
theorem isClosed_analyticAdmissionRel
    {X : Type*} [TopologicalSpace X] (R : X → X → Prop) :
    IsClosed (admissionRelationGraph (analyticAdmissionRel R)) := by
  change IsClosed {p : X × X |
    analyticAdmissionMk R p.1 = analyticAdmissionMk R p.2}
  exact isClosed_eq
    ((continuous_analyticAdmissionMk R).comp continuous_fst)
    ((continuous_analyticAdmissionMk R).comp continuous_snd)

theorem analyticAdmissionSetoid_isClosed
    {X : Type*} [TopologicalSpace X] (R : X → X → Prop) :
    IsClosedAdmissionSetoid (analyticAdmissionSetoid R) :=
  isClosed_analyticAdmissionRel R

/-- The canonical analytic-admission map is surjective. -/
theorem analyticAdmissionMk_surjective
    {X : Type*} [TopologicalSpace X] (R : X → X → Prop) :
    Function.Surjective (analyticAdmissionMk R) := by
  intro q
  induction q using T2Quotient.inductionOn with
  | _ a =>
      induction a using Quotient.inductionOn with
      | _ x => exact ⟨x, rfl⟩

/-- Uniqueness clause in the continuous-Hausdorff universal property. -/
theorem analyticAdmissionObserverLift_unique
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {R : X → X → Prop} (q : X → Y) (hq : Continuous q)
    (hR : ∀ x y, R x y → q x = q y)
    (g : AnalyticAdmission R → Y)
    (hg : ∀ x, g (analyticAdmissionMk R x) = q x) :
    g = analyticAdmissionObserverLift q hq hR := by
  funext z
  obtain ⟨x, rfl⟩ := analyticAdmissionMk_surjective R z
  rw [hg, analyticAdmissionObserverLift_mk]

/-- **Least closed-equivalence theorem.** Analytic admission lies below every closed equivalence
relation containing the primitive relation. -/
theorem analyticAdmissionRel_least_closed_equivalence
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {R : X → X → Prop} (s : Setoid X)
    (hs : IsClosedAdmissionSetoid s)
    (hR : ∀ x y, R x y → s x y)
    {x y : X} (hxy : analyticAdmissionRel R x y) : s x y := by
  letI : T2Space (Quotient s) :=
    t2Space_quotient_of_isClosedAdmissionSetoid s hs
  have hqxy : (Quotient.mk' x : Quotient s) = Quotient.mk' y :=
    analyticAdmissionRel_erases_every_continuous_T2_observer hxy
      (Quotient.mk' : X → Quotient s) continuous_quotient_mk'
      (fun a b hab => (Quotient.eq).mpr (hR a b hab))
  exact (Quotient.eq).mp hqxy

theorem analyticAdmissionRel_le_closedSetoid_iff
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {R : X → X → Prop} (s : Setoid X)
    (hs : IsClosedAdmissionSetoid s) :
    (∀ x y, analyticAdmissionRel R x y → s x y) ↔
      ∀ x y, R x y → s x y := by
  constructor
  · intro h x y hxy
    exact h x y (analyticAdmissionRel_contains hxy)
  · intro h x y hxy
    exact analyticAdmissionRel_least_closed_equivalence s hs h hxy

/-- Extensivity of analytic admission. -/
theorem analyticAdmissionRel_extensive
    {X : Type*} [TopologicalSpace X] {R : X → X → Prop} {x y : X}
    (hxy : R x y) : analyticAdmissionRel R x y :=
  analyticAdmissionRel_contains hxy

/-- Monotonicity of analytic admission. -/
theorem analyticAdmissionRel_mono
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {R S : X → X → Prop} (hRS : ∀ x y, R x y → S x y)
    {x y : X} (hxy : analyticAdmissionRel R x y) :
    analyticAdmissionRel S x y := by
  exact analyticAdmissionRel_least_closed_equivalence
    (analyticAdmissionSetoid S) (analyticAdmissionSetoid_isClosed S)
    (fun a b hab => analyticAdmissionRel_contains (hRS a b hab)) hxy

/-- Idempotence of analytic admission. -/
theorem analyticAdmissionRel_idempotent
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (R : X → X → Prop) (x y : X) :
    analyticAdmissionRel (analyticAdmissionRel R) x y ↔
      analyticAdmissionRel R x y := by
  constructor
  · exact analyticAdmissionRel_least_closed_equivalence
      (analyticAdmissionSetoid R) (analyticAdmissionSetoid_isClosed R)
      (fun _ _ h => h)
  · exact analyticAdmissionRel_contains

/-- Continuous real reporters that unitize a relation. -/
def continuousRealReporterPolar
    {X : Type*} [TopologicalSpace X] (R : X → X → Prop) : Set C(X, ℝ) :=
  {f | ∀ x y, R x y → f x = f y}

/-- Reporter polar converts relation union into reporter intersection. -/
theorem continuousRealReporterPolar_union
    {X : Type*} [TopologicalSpace X] (R S : X → X → Prop) :
    continuousRealReporterPolar (fun x y => R x y ∨ S x y) =
      continuousRealReporterPolar R ∩ continuousRealReporterPolar S := by
  ext f
  constructor
  · intro hf
    exact ⟨fun x y h => hf x y (Or.inl h), fun x y h => hf x y (Or.inr h)⟩
  · rintro ⟨hR, hS⟩ x y (h | h)
    · exact hR x y h
    · exact hS x y h

/-- A continuous reporter unitizes a relation iff it unitizes its analytic hull. -/
theorem continuousRealReporter_unitizes_admission_iff
    {X : Type*} [TopologicalSpace X] (R : X → X → Prop) (f : C(X, ℝ)) :
    (∀ x y, analyticAdmissionRel R x y → f x = f y) ↔
      ∀ x y, R x y → f x = f y := by
  constructor
  · intro h x y hxy
    exact h x y (analyticAdmissionRel_contains hxy)
  · intro h x y hxy
    exact analyticAdmissionRel_erases_every_continuous_T2_observer
      hxy f f.continuous h

/-- Analytic hull of a union is unchanged after separately saturating both relations. -/
theorem analyticAdmissionRel_union_admissions
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (R S : X → X → Prop) (x y : X) :
    analyticAdmissionRel (fun a b => R a b ∨ S a b) x y ↔
      analyticAdmissionRel
        (fun a b => analyticAdmissionRel R a b ∨ analyticAdmissionRel S a b) x y := by
  rw [analyticAdmissionRel_iff_continuous_real_observers,
    analyticAdmissionRel_iff_continuous_real_observers]
  constructor
  · intro h f hf
    apply h f
    intro a b hab
    rcases hab with hab | hab
    · exact hf a b (Or.inl (analyticAdmissionRel_contains hab))
    · exact hf a b (Or.inr (analyticAdmissionRel_contains hab))
  · intro h f hf
    apply h f
    intro a b hab
    rcases hab with hab | hab
    · exact analyticAdmissionRel_erases_every_continuous_T2_observer
        hab f f.continuous (fun u v huv => hf u v (Or.inl huv))
    · exact analyticAdmissionRel_erases_every_continuous_T2_observer
        hab f f.continuous (fun u v huv => hf u v (Or.inr huv))

/-- An observer unitizes a relation. -/
def RelationUnitizing {X Y : Type*} (R : X → X → Prop) (q : X → Y) : Prop :=
  ∀ x y, R x y → q x = q y

/-- An observer is lossless for a declared conflict relation. -/
def ConflictLossless {X Y : Type*} (C : X → X → Prop) (q : X → Y) : Prop :=
  ∀ x y, C x y → q x ≠ q y

theorem algebraicAdmissionMk_unitizing
    {X : Type*} (R : X → X → Prop) :
    RelationUnitizing R (algebraicAdmissionMk R) := by
  intro x y hxy
  exact Quotient.sound (Relation.EqvGen.rel x y hxy)

theorem algebraicAdmissionMk_lossless_iff
    {X : Type*} (R C : X → X → Prop) :
    ConflictLossless C (algebraicAdmissionMk R) ↔
      ∀ x y, C x y → ¬ Relation.EqvGen R x y := by
  constructor
  · intro h x y hC hEq
    exact h x y hC (Quotient.sound hEq)
  · intro h x y hC hmk
    exact h x y hC ((Quotient.eq).mp hmk)

theorem algebraicObserver_exists_iff_conflict_disjoint
    {X : Type*} (R C : X → X → Prop) :
    (∃ q : X → AlgebraicAdmission R,
      RelationUnitizing R q ∧ ConflictLossless C q) ↔
      ∀ x y, C x y → ¬ Relation.EqvGen R x y := by
  constructor
  · rintro ⟨q, hR, hC⟩ x y hxy hEq
    exact hC x y hxy (eqvGen_observer_eq q hR x y hEq)
  · intro h
    exact ⟨algebraicAdmissionMk R, algebraicAdmissionMk_unitizing R,
      (algebraicAdmissionMk_lossless_iff R C).2 h⟩

theorem analyticAdmissionMk_unitizing
    {X : Type*} [TopologicalSpace X] (R : X → X → Prop) :
    RelationUnitizing R (analyticAdmissionMk R) := by
  intro x y hxy
  exact analyticAdmissionRel_contains hxy

theorem analyticAdmissionMk_lossless_iff
    {X : Type*} [TopologicalSpace X] (R C : X → X → Prop) :
    ConflictLossless C (analyticAdmissionMk R) ↔
      ∀ x y, C x y → ¬ analyticAdmissionRel R x y := by
  rfl

theorem analyticObserver_exists_iff_conflict_disjoint
    {X : Type*} [TopologicalSpace X] (R C : X → X → Prop) :
    (∃ q : C(X, AnalyticAdmission R),
      RelationUnitizing R q ∧ ConflictLossless C q) ↔
      ∀ x y, C x y → ¬ analyticAdmissionRel R x y := by
  constructor
  · rintro ⟨q, hR, hC⟩ x y hxy hAdm
    exact hC x y hxy
      (analyticAdmissionRel_erases_every_continuous_T2_observer
        hAdm q q.continuous hR)
  · intro h
    let q : C(X, AnalyticAdmission R) :=
      ⟨analyticAdmissionMk R, continuous_analyticAdmissionMk R⟩
    exact ⟨q, analyticAdmissionMk_unitizing R,
      (analyticAdmissionMk_lossless_iff R C).2 h⟩

/-- Distinctions erased analytically but not algebraically. -/
def analyticCriticalShell
    {X : Type*} [TopologicalSpace X] (R : X → X → Prop) (x y : X) : Prop :=
  analyticAdmissionRel R x y ∧ ¬ Relation.EqvGen R x y

/-- The admission-only obstruction is exactly conflict intersected with the critical shell. -/
theorem conflict_analytic_obstruction_eq_criticalShell
    {X : Type*} [TopologicalSpace X] (R C : X → X → Prop) :
    (admissionRelationGraph C ∩ admissionRelationGraph (analyticAdmissionRel R)) \
        (admissionRelationGraph C ∩ admissionRelationGraph (Relation.EqvGen R)) =
      admissionRelationGraph C ∩ admissionRelationGraph (analyticCriticalShell R) := by
  ext p
  simp only [admissionRelationGraph, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq,
    analyticCriticalShell]
  aesop

/-- Total variation of two finitely supported real profiles. -/
def finitelySupportedTotalVariation {X : Type*} (mu nu : X →₀ ℝ) : ℝ :=
  (1 / 2 : ℝ) * (mu - nu).sum fun _ a => |a|

/-- Finitely supported Dirac profile. -/
def finitelySupportedDirac {X : Type*} (x : X) : X →₀ ℝ :=
  Finsupp.single x 1

theorem finitelySupportedDirac_totalVariation
    {X : Type*} {x y : X} (hxy : x ≠ y) :
    finitelySupportedTotalVariation
      (finitelySupportedDirac x) (finitelySupportedDirac y) = 1 := by
  classical
  have hsupp :
      (finitelySupportedDirac x - finitelySupportedDirac y).support = {x, y} := by
    ext z
    by_cases hzx : z = x
    · subst z
      simp [finitelySupportedDirac, hxy]
    · by_cases hzy : z = y
      · subst z
        simp [finitelySupportedDirac, Ne.symm hxy]
      · simp [finitelySupportedDirac, hzx, hzy]
  rw [finitelySupportedTotalVariation, Finsupp.sum, hsupp]
  simp only [Finset.sum_insert, Finset.mem_singleton, hxy, not_false_eq_true,
    Finset.sum_singleton, finitelySupportedDirac, Finsupp.sub_apply,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne hxy,
    Finsupp.single_eq_of_ne (Ne.symm hxy), sub_zero, zero_sub, abs_one, abs_neg]
  ring

theorem finitelySupportedDirac_pushforward_totalVariation_zero
    {X Y : Type*} (q : X → Y) {x y : X} (hxy : q x = q y) :
    finitelySupportedTotalVariation
      ((finitelySupportedDirac x).mapDomain q)
      ((finitelySupportedDirac y).mapDomain q) = 0 := by
  classical
  change finitelySupportedTotalVariation
    ((Finsupp.single x 1).mapDomain q) ((Finsupp.single y 1).mapDomain q) = 0
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, hxy]
  simp [finitelySupportedTotalVariation]

theorem analyticCriticalShell_dirac_totalVariation
    {X : Type*} [TopologicalSpace X] {R : X → X → Prop} {x y : X}
    (hxy : analyticCriticalShell R x y) :
    finitelySupportedTotalVariation
      (finitelySupportedDirac x) (finitelySupportedDirac y) = 1 := by
  apply finitelySupportedDirac_totalVariation
  intro heq
  subst y
  exact hxy.2 (Relation.EqvGen.refl x)

theorem analyticCriticalShell_pushforward_totalVariation_zero
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {R : X → X → Prop} {x y : X}
    (hxy : analyticCriticalShell R x y)
    (q : X → Y) (hq : Continuous q) (hR : RelationUnitizing R q) :
    finitelySupportedTotalVariation
      ((finitelySupportedDirac x).mapDomain q)
      ((finitelySupportedDirac y).mapDomain q) = 0 := by
  apply finitelySupportedDirac_pushforward_totalVariation_zero q
  exact analyticAdmissionRel_erases_every_continuous_T2_observer
    hxy.1 q hq hR

/-- Bundled unconditional bipolar-admission capstone. -/
theorem closedAnalyticAdmissionHull_capstone
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (R S : X → X → Prop) :
    IsClosedAdmissionSetoid (analyticAdmissionSetoid R) ∧
    (∀ x y, R x y → analyticAdmissionRel R x y) ∧
    (∀ x y, analyticAdmissionRel (analyticAdmissionRel R) x y ↔
      analyticAdmissionRel R x y) ∧
    (∀ x y, analyticAdmissionRel (fun a b => R a b ∨ S a b) x y ↔
      analyticAdmissionRel
        (fun a b => analyticAdmissionRel R a b ∨ analyticAdmissionRel S a b) x y) := by
  exact ⟨analyticAdmissionSetoid_isClosed R, fun _ _ => analyticAdmissionRel_contains,
    analyticAdmissionRel_idempotent R, analyticAdmissionRel_union_admissions R S⟩

end

end HTGeometry
