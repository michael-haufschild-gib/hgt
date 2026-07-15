import GaloisForLFunctions.HTGeometry.ParabolicOrbifoldTwelveCharge
import Mathlib.GroupTheory.Index

/-!
# Crystallographic index diagram for parabolic orbifold towers

An affine lift of a parabolic-orbifold covering conjugates the source deck group to a finite-index
subgroup `K` of the target deck group `G`.  If `N` is the normal target translation subgroup, then
the conjugated source translation subgroup is exactly `K ⊓ N`.  This file formalizes the complete
index diagram behind that geometric input.

The source holonomy order is `[K : K ⊓ N] = N.relIndex K`, the target holonomy order is
`[G : N] = N.index`, the covering degree is `[G : K] = K.index`, and the translation-lattice
index is `[N : K ⊓ N] = K.relIndex N`.  Computing the index of `K ⊓ N` in `G` through `K` and
through `N` gives the exact degree factorization.  Normality of `N` also gives the holonomy
divisibility that drives the existing finite-signature stabilization theorem.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section IndexDiagram

variable {G : Type*} [Group G]

/-- The holonomy of a subgroup injects into the target quotient by a normal translation subgroup;
at the finite-index level this is the exact divisibility of the two holonomy orders. -/
theorem crystallographic_sourceHolonomy_dvd_targetHolonomy
    (K N : Subgroup G) [N.Normal] :
    N.relIndex K ∣ N.index :=
  N.relIndex_dvd_index_of_normal K

/-- **Crystallographic cross-index law.**  Computing `[G : K ⊓ N]` first through `K` and then
through `N` gives

`[G:K] [K:K⊓N] = [G:N] [N:K⊓N]`.
-/
theorem crystallographic_degree_mul_sourceHolonomy_eq_targetHolonomy_mul_latticeIndex
    (K N : Subgroup G) :
    K.index * N.relIndex K = N.index * K.relIndex N := by
  have hK := Subgroup.relIndex_mul_index (H := N ⊓ K) (K := K) inf_le_right
  have hN := Subgroup.relIndex_mul_index (H := N ⊓ K) (K := N) inf_le_left
  rw [Subgroup.inf_relIndex_right N K] at hK
  rw [Subgroup.inf_relIndex_left N K] at hN
  calc
    K.index * N.relIndex K = N.relIndex K * K.index := Nat.mul_comm _ _
    _ = (N ⊓ K).index := hK
    _ = K.relIndex N * N.index := hN.symm
    _ = N.index * K.relIndex N := Nat.mul_comm _ _

/-- The cross-index law and nonzero source holonomy turn holonomy divisibility into the literal
covering-degree factorization. -/
theorem crystallographic_degree_factorization
    (K N : Subgroup G) [N.Normal] (hsource : 0 < N.relIndex K) :
    ∃ q : ℕ,
      N.index = N.relIndex K * q ∧
      K.index = q * K.relIndex N := by
  obtain ⟨q, hq⟩ := crystallographic_sourceHolonomy_dvd_targetHolonomy K N
  refine ⟨q, hq, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left hsource
  calc
    N.relIndex K * K.index = K.index * N.relIndex K := Nat.mul_comm _ _
    _ = N.index * K.relIndex N :=
      crystallographic_degree_mul_sourceHolonomy_eq_targetHolonomy_mul_latticeIndex K N
    _ = (N.relIndex K * q) * K.relIndex N := by rw [hq]
    _ = N.relIndex K * (q * K.relIndex N) := by rw [Nat.mul_assoc]

/-- Once source and target holonomy orders agree, the entire covering degree is pure translation
lattice index. -/
theorem crystallographic_degree_eq_latticeIndex_of_holonomy_eq
    (K N : Subgroup G) (hsource : 0 < N.relIndex K)
    (hholonomy : N.index = N.relIndex K) :
    K.index = K.relIndex N := by
  apply Nat.mul_right_cancel hsource
  calc
    K.index * N.relIndex K = N.index * K.relIndex N :=
      crystallographic_degree_mul_sourceHolonomy_eq_targetHolonomy_mul_latticeIndex K N
    _ = N.relIndex K * K.relIndex N := by rw [hholonomy]
    _ = K.relIndex N * N.relIndex K := Nat.mul_comm _ _

end IndexDiagram

/-- The formal group-theoretic data supplied by one affine universal-cover lift.  `sourceDeck` is
the conjugated source deck group inside the target deck group and `targetTranslation` is the normal
target translation subgroup.  Their intersection is therefore the conjugated source translation
subgroup. -/
structure ParabolicCrystallographicStep
    (source target : ParabolicSphereSignature) where
  Deck : Type*
  [deckGroup : Group Deck]
  sourceDeck : Subgroup Deck
  targetTranslation : Subgroup Deck
  [targetTranslationNormal : targetTranslation.Normal]
  sourceHolonomyOrder_eq :
    targetTranslation.relIndex sourceDeck = source.holonomyOrder
  targetHolonomyOrder_eq :
    targetTranslation.index = target.holonomyOrder
  latticeIndex_pos : 0 < sourceDeck.relIndex targetTranslation
  compact_eq : source.isCompact = target.isCompact

namespace ParabolicCrystallographicStep

variable {source target : ParabolicSphereSignature}

/-- Orbifold covering degree, expressed as the deck-group index of the affine-lifted source. -/
def degree (step : ParabolicCrystallographicStep source target) : ℕ := by
  letI := step.deckGroup
  exact step.sourceDeck.index

/-- Index of the affine image of the source translation lattice in the target translation
lattice. -/
def latticeIndex (step : ParabolicCrystallographicStep source target) : ℕ := by
  letI := step.deckGroup
  exact step.sourceDeck.relIndex step.targetTranslation

theorem latticeIndex_positive (step : ParabolicCrystallographicStep source target) :
    0 < step.latticeIndex := by
  letI := step.deckGroup
  exact step.latticeIndex_pos

/-- The affine crystallographic inclusion injects finite rotational holonomy. -/
theorem holonomyOrder_dvd (step : ParabolicCrystallographicStep source target) :
    source.holonomyOrder ∣ target.holonomyOrder := by
  letI := step.deckGroup
  letI := step.targetTranslationNormal
  rw [← step.sourceHolonomyOrder_eq, ← step.targetHolonomyOrder_eq]
  exact crystallographic_sourceHolonomy_dvd_targetHolonomy
    step.sourceDeck step.targetTranslation

/-- Exact phasewise factorization of covering degree into holonomy enlargement and translation
lattice index. -/
theorem degree_factorization (step : ParabolicCrystallographicStep source target) :
    ∃ q : ℕ,
      target.holonomyOrder = source.holonomyOrder * q ∧
      step.degree = q * step.latticeIndex := by
  letI := step.deckGroup
  letI := step.targetTranslationNormal
  have hsource : 0 < step.targetTranslation.relIndex step.sourceDeck := by
    rw [step.sourceHolonomyOrder_eq]
    exact source.holonomyOrder_pos
  obtain ⟨q, hq, hdegree⟩ := crystallographic_degree_factorization
    step.sourceDeck step.targetTranslation hsource
  refine ⟨q, ?_, ?_⟩
  · simpa [step.sourceHolonomyOrder_eq, step.targetHolonomyOrder_eq] using hq
  · simpa [degree, latticeIndex] using hdegree

/-- After holonomy freezes, phasewise degree is exactly the lattice index. -/
theorem degree_eq_latticeIndex_of_holonomy_eq
    (step : ParabolicCrystallographicStep source target)
    (hholonomy : source.holonomyOrder = target.holonomyOrder) :
    step.degree = step.latticeIndex := by
  letI := step.deckGroup
  have hsource : 0 < step.targetTranslation.relIndex step.sourceDeck := by
    rw [step.sourceHolonomyOrder_eq]
    exact source.holonomyOrder_pos
  apply crystallographic_degree_eq_latticeIndex_of_holonomy_eq
    step.sourceDeck step.targetTranslation hsource
  rw [step.targetHolonomyOrder_eq, step.sourceHolonomyOrder_eq, hholonomy]

end ParabolicCrystallographicStep

/-- Compact/cuspidal type is constant across every finite interval of a compatible parabolic
tower. -/
theorem parabolicSphereTower_isCompact_eq_of_le
    (signature : ℕ → ParabolicSphereSignature)
    (hcompact : ∀ i, (signature i).isCompact = (signature (i + 1)).isCompact)
    {i j : ℕ} (hij : i ≤ j) :
    (signature i).isCompact = (signature j).isCompact := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j _ ih => exact ih.trans (hcompact j)

/-- The complete tower form of the height-two holonomy law: no two strict enhancements can occur
at separated phases. -/
theorem parabolicSphereTower_no_two_strict_holonomy_enlargements
    (signature : ℕ → ParabolicSphereSignature)
    (hdiv : ∀ i, (signature i).holonomyOrder ∣
      (signature (i + 1)).holonomyOrder)
    (hcompact : ∀ i, (signature i).isCompact = (signature (i + 1)).isCompact) :
    ¬ ∃ i j k : ℕ,
      i < j ∧ j < k ∧
      (signature i).holonomyOrder < (signature j).holonomyOrder ∧
      (signature j).holonomyOrder < (signature k).holonomyOrder := by
  rintro ⟨i, j, k, hij, hjk, hstrictij, hstrictjk⟩
  have hcompactij := parabolicSphereTower_isCompact_eq_of_le signature hcompact hij.le
  have hcompactjk := parabolicSphereTower_isCompact_eq_of_le signature hcompact hjk.le
  have hdivij := dvd_holonomyOrder_of_le signature hdiv hij.le
  have hdivjk := dvd_holonomyOrder_of_le signature hdiv hjk.le
  rcases parabolicHolonomyOrder_no_two_strict_enlargements
      (signature i) (signature j) (signature k)
      hcompactij hcompactjk hdivij hdivjk with heq | heq
  · exact hstrictij.ne heq
  · exact hstrictjk.ne heq

/-- **Parabolic affine-crystallographic tower capstone.**  The affine deck inclusions give
holonomy divisibility and exact phasewise degree factorization.  The six-signature poset then
allows at most one strict enhancement, supplies a stable charge at most six, freezes the complete
signature, and makes every later degree a pure lattice index. -/
theorem parabolicCrystallographicTower_singleEnhancement_indexFactorization
    (signature : ℕ → ParabolicSphereSignature)
    (step : ∀ i, ParabolicCrystallographicStep (signature i) (signature (i + 1))) :
    (∀ i, (signature i).holonomyOrder ∣
      (signature (i + 1)).holonomyOrder) ∧
    (∀ i, ∃ q : ℕ,
      (signature (i + 1)).holonomyOrder =
        (signature i).holonomyOrder * q ∧
      (step i).degree = q * (step i).latticeIndex) ∧
    (¬ ∃ i j k : ℕ,
      i < j ∧ j < k ∧
      (signature i).holonomyOrder < (signature j).holonomyOrder ∧
      (signature j).holonomyOrder < (signature k).holonomyOrder) ∧
    ∃ N charge : ℕ,
      charge = (signature N).holonomyOrder ∧
      charge ≤ 6 ∧ charge ∣ 12 ∧
      (∀ i, (signature i).holonomyOrder ∣ charge) ∧
      (∀ n, N ≤ n → signature n = signature N) ∧
      ∀ n, N ≤ n → (step n).degree = (step n).latticeIndex := by
  have hdiv : ∀ i, (signature i).holonomyOrder ∣
      (signature (i + 1)).holonomyOrder :=
    fun i => (step i).holonomyOrder_dvd
  have hcompact : ∀ i, (signature i).isCompact =
      (signature (i + 1)).isCompact :=
    fun i => (step i).compact_eq
  refine ⟨hdiv, fun i => (step i).degree_factorization,
    parabolicSphereTower_no_two_strict_holonomy_enlargements signature hdiv hcompact, ?_⟩
  obtain ⟨N, charge, hcharge, hle, hdvd12, hbefore, hstable⟩ :=
    parabolicSphereTower_has_protocol_charge signature hdiv
  have hsignature := parabolicSphereSignature_eventually_constant signature hdiv hcompact
  obtain ⟨M, hM⟩ := hsignature
  let N₀ := max N M
  refine ⟨N₀, charge, ?_, hle, hdvd12, ?_, ?_, ?_⟩
  · exact (hstable N₀ (le_max_left _ _)).symm
  · exact hbefore
  · intro n hn
    exact (hM n (le_trans (le_max_right _ _) hn)).trans
      (hM N₀ (le_max_right _ _)).symm
  · intro n hn
    apply (step n).degree_eq_latticeIndex_of_holonomy_eq
    have hncharge := hstable n (le_trans (le_max_left _ _) hn)
    have hsucccharge := hstable (n + 1)
      (le_trans (le_trans (le_max_left _ _) hn) (Nat.le_succ n))
    exact hncharge.trans hsucccharge.symm

end

end GaloisForLFunctions.HTGeometry
