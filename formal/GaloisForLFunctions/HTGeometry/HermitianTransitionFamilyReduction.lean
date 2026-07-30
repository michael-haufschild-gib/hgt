import GaloisForLFunctions.HTGeometry.RealFiniteAnalyticEscape
import GaloisForLFunctions.HTGeometry.LocalInteractionLiftAnalyticRelationLaw
import GaloisForLFunctions.HTGeometry.HermitianLocalExtensionChart

/-!
# One Hermitian channel detects a finite observable family

A finite family of Hermitian endpoint observables can be replaced by one
real linear combination without losing any transition detected by the
family.  This is the finite-dimensional bridge from a physical local
observable algebra to the single transition channel used by the local
extension theorem.
-/

open Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Real linear combinations of a finite complex matrix family. -/
def realMatrixFamilyCombination
    {α η : Type*} [Fintype η]
    (transition : η → Matrix α α ℂ)
    (p : η → ℝ) :
    Matrix α α ℂ :=
  fun a b => ∑ i, (p i : ℂ) * transition i a b

@[simp] theorem realMatrixFamilyCombination_apply
    {α η : Type*} [Fintype η]
    (transition : η → Matrix α α ℂ)
    (p : η → ℝ) (a b : α) :
    realMatrixFamilyCombination transition p a b =
      ∑ i, (p i : ℂ) * transition i a b := by
  rfl

/-- Union of all transition-support graphs detected by a matrix family. -/
def transitionFamilySupportGraph
    {α η : Type*}
    (transition : η → Matrix α α ℂ) :
    SimpleGraph α where
  Adj a b :=
    ∃ i, (transitionSupportGraph (transition i)).Adj a b
  symm := ⟨by
    rintro a b ⟨i, hi⟩
    exact ⟨i, hi.symm⟩⟩
  loopless := ⟨by
    rintro a ⟨i, hi⟩
    exact hi.ne rfl⟩

@[simp] theorem transitionFamilySupportGraph_adj
    {α η : Type*}
    (transition : η → Matrix α α ℂ)
    (a b : α) :
    (transitionFamilySupportGraph transition).Adj a b ↔
      ∃ i, (transitionSupportGraph (transition i)).Adj a b :=
  Iff.rfl

/-- Each matrix entry of the real family combination is real analytic in
the coefficient packet. -/
theorem realMatrixFamilyCombination_apply_analyticAt
    {α η : Type*} [Fintype η]
    (transition : η → Matrix α α ℂ)
    (a b : α) (p : η → ℝ) :
    AnalyticAt ℝ
      (fun q =>
        realMatrixFamilyCombination transition q a b) p := by
  simp only [realMatrixFamilyCombination_apply]
  apply Finset.analyticAt_fun_sum
  intro i hi
  let coord : (η → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) i
  let entry : (η → ℝ) →L[ℝ] ℂ :=
    coord.smulRight (transition i a b)
  have hentry := entry.analyticAt p
  convert hentry using 1
  ext q
  simp [entry, coord, Complex.real_smul]

/-- One real coefficient packet simultaneously keeps every ordered matrix
entry that is nonzero in at least one member of a finite family. -/
theorem exists_realMatrixFamilyCombination_preserves_support
    {α η : Type*} [Fintype α] [Fintype η]
    [DecidableEq α] [DecidableEq η]
    (transition : η → Matrix α α ℂ) :
    ∃ p : η → ℝ, ∀ a b,
      (∃ i, transition i a b ≠ 0) →
        realMatrixFamilyCombination transition p a b ≠ 0 := by
  let I :=
    {ab : α × α //
      ∃ i, transition i ab.1 ab.2 ≠ 0}
  let f : I → (η → ℝ) → ℂ :=
    fun ab p =>
      realMatrixFamilyCombination
        transition p ab.1.1 ab.1.2
  have hf :
      ∀ ab, AnalyticOnNhd ℝ (f ab) Set.univ := by
    intro ab p hp
    exact realMatrixFamilyCombination_apply_analyticAt
      transition ab.1.1 ab.1.2 p
  have hne :
      ∀ ab, ∃ p ∈ (Set.univ : Set (η → ℝ)),
        f ab p ≠ 0 := by
    intro ab
    obtain ⟨i, hi⟩ := ab.2
    refine ⟨Pi.single i 1, Set.mem_univ _, ?_⟩
    simp only [f, realMatrixFamilyCombination_apply,
      Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · simpa using hi
    · intro j hj hji
      simp [hji]
    · intro hiuniv
      exact absurd (Finset.mem_univ i) hiuniv
  obtain ⟨p, hpU, hp⟩ :=
    exists_forall_neZero_of_finite_analyticOnNhd_real_local
      f Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty hf hne
  refine ⟨p, ?_⟩
  intro a b hab
  let ab : I := ⟨(a, b), hab⟩
  exact hp ab

/-- Real combinations preserve Hermiticity. -/
theorem realMatrixFamilyCombination_isHermitian
    {α η : Type*} [Fintype η]
    (transition : η → Matrix α α ℂ)
    (htransition : ∀ i, (transition i).IsHermitian)
    (p : η → ℝ) :
    (realMatrixFamilyCombination transition p).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  simp only [realMatrixFamilyCombination]
  change
    (starRingEnd ℂ) (∑ i, (p i : ℂ) * transition i b a) =
      ∑ i, (p i : ℂ) * transition i a b
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul]
  have ht :
      (starRingEnd ℂ) (transition i b a) =
        transition i a b := by
    simpa [Complex.star_def] using
      (htransition i).apply a b
  rw [ht]
  simp

/-- A single Hermitian combination contains the union of all transition
support graphs detected by a finite Hermitian family. -/
theorem exists_hermitianTransition_supports_family
    {α η : Type*} [Fintype α] [Fintype η]
    [DecidableEq α] [DecidableEq η]
    (transition : η → Matrix α α ℂ)
    (htransition : ∀ i, (transition i).IsHermitian) :
    ∃ p : η → ℝ,
      (realMatrixFamilyCombination transition p).IsHermitian ∧
      ∀ i,
        transitionSupportGraph (transition i) ≤
          transitionSupportGraph
            (realMatrixFamilyCombination transition p) := by
  obtain ⟨p, hp⟩ :=
    exists_realMatrixFamilyCombination_preserves_support
      transition
  refine ⟨p,
    realMatrixFamilyCombination_isHermitian
      transition htransition p, ?_⟩
  intro i a b hab
  refine ⟨hab.1, mul_ne_zero ?_ ?_⟩
  · exact hp a b ⟨i,
      fun hzero => hab.2 (by simp [hzero])⟩
  · exact hp b a ⟨i,
      fun hzero => hab.2 (by simp [hzero])⟩

/-- The union support graph of the family is contained in the support graph
of one Hermitian real combination. -/
theorem exists_hermitianTransition_familyGraph_le
    {α η : Type*} [Fintype α] [Fintype η]
    [DecidableEq α] [DecidableEq η]
    (transition : η → Matrix α α ℂ)
    (htransition : ∀ i, (transition i).IsHermitian) :
    ∃ p : η → ℝ,
      (realMatrixFamilyCombination transition p).IsHermitian ∧
      transitionFamilySupportGraph transition ≤
        transitionSupportGraph
          (realMatrixFamilyCombination transition p) := by
  obtain ⟨p, hpHermitian, hp⟩ :=
    exists_hermitianTransition_supports_family
      transition htransition
  refine ⟨p, hpHermitian, ?_⟩
  intro a b hab
  obtain ⟨i, hi⟩ := hab
  exact hp i hi

/-- If the physical observable family has connected interaction lift, one
Hermitian observable in its real span has connected interaction lift. -/
theorem exists_hermitianTransition_preconnected_crossLayerLift
    {α η ρ : Type*} [Fintype α] [Fintype η]
    [DecidableEq α] [DecidableEq η]
    (transition : η → Matrix α α ℂ)
    (htransition : ∀ i, (transition i).IsHermitian)
    (hlift :
      (crossLayerLiftGraph
        (transitionFamilySupportGraph transition) ρ).Preconnected) :
    ∃ p : η → ℝ,
      (realMatrixFamilyCombination transition p).IsHermitian ∧
      (crossLayerLiftGraph
        (transitionSupportGraph
          (realMatrixFamilyCombination transition p)) ρ).Preconnected := by
  obtain ⟨p, hpHermitian, hpGraph⟩ :=
    exists_hermitianTransition_familyGraph_le
      transition htransition
  refine ⟨p, hpHermitian, hlift.mono ?_⟩
  intro x y hxy
  exact ⟨hpGraph hxy.1, hxy.2⟩

end

end GaloisForLFunctions.HTGeometry
