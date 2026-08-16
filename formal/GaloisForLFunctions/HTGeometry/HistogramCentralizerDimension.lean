import GaloisForLFunctions.HTGeometry.OrderedReplicaPushforward
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# The centralizer of a collective replica Hamiltonian

The commutant of a diagonal matrix is the space of matrices supported on the pairs of equal
diagonal entries, so its dimension is the number of such pairs.  For a collective replica
Hamiltonian the diagonal entries are indexed by ordered level tuples and the entry of a tuple is
the sum of its level energies; when no nontrivial balanced integer relation holds among the
energies, two tuples carry the same collective energy exactly when they have the same multiplicity
histogram.

Consequently the centralizer dimension is the number of ordered tuple pairs with a common
histogram, which is the sum of the squared multinomial coefficients over histograms and, normalized
by the total number of pairs, the collision probability of two independent uniform histograms.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The commutant of a diagonal matrix -/

section Commutant

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The commutant of a matrix inside the full matrix algebra. -/
def commutantSubmodule (A : Matrix n n ℂ) : Submodule ℂ (Matrix n n ℂ) :=
  LinearMap.ker (LinearMap.mulLeft ℂ A - LinearMap.mulRight ℂ A)

theorem mem_commutantSubmodule {A X : Matrix n n ℂ} :
    X ∈ commutantSubmodule A ↔ A * X = X * A := by
  rw [commutantSubmodule, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, sub_eq_zero]

theorem stdBasis_apply' (p : n × n) (i j : n) :
    Matrix.stdBasis ℂ n n p i j = if p.1 = i ∧ p.2 = j then (1 : ℂ) else 0 := by
  classical
  by_cases h1 : p.1 = i
  · by_cases h2 : p.2 = j
    · subst h1
      subst h2
      simp [Matrix.stdBasis]
    · simp [Matrix.stdBasis, Pi.single_apply, h1, h2]
  · simp [Matrix.stdBasis, Pi.single_apply, h1]

theorem mem_commutantSubmodule_diagonal {E : n → ℂ} {X : Matrix n n ℂ} :
    X ∈ commutantSubmodule (Matrix.diagonal E) ↔ ∀ i j, E i ≠ E j → X i j = 0 := by
  rw [mem_commutantSubmodule]
  constructor
  · intro h i j hij
    have hentry := congrFun (congrFun h i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
    have hsub : (E i - E j) * X i j = 0 := by
      rw [sub_mul, hentry]
      ring
    rcases mul_eq_zero.mp hsub with h1 | h2
    · exact absurd (sub_eq_zero.mp h1) hij
    · exact h2
  · intro h
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : E i = E j
    · rw [hij]
    · rw [h i j hij]
      ring

/-- The pairs of levels carrying equal energy. -/
def levelAgreementFinset (E : n → ℂ) : Finset (n × n) :=
  Finset.univ.filter fun p => E p.1 = E p.2

/-- The commutant of a diagonal matrix is spanned by the matrix units supported on pairs of equal
diagonal entries. -/
theorem commutantSubmodule_diagonal_eq_span (E : n → ℂ) :
    commutantSubmodule (Matrix.diagonal E) =
      Submodule.span ℂ (Set.range (fun p : {p : n × n // E p.1 = E p.2} =>
        Matrix.stdBasis ℂ n n p.1)) := by
  classical
  refine le_antisymm ?_ ?_
  · intro X hX
    rw [mem_commutantSubmodule_diagonal] at hX
    have hrep : X = ∑ p ∈ levelAgreementFinset E, X p.1 p.2 • Matrix.stdBasis ℂ n n p := by
      ext i j
      rw [Matrix.sum_apply, Finset.sum_apply]
      rw [Finset.sum_eq_single (i, j)]
      · by_cases hij : E i = E j
        · rw [Matrix.smul_apply, stdBasis_apply']
          simp
        · rw [Finset.sum_eq_zero, hX i j hij]
          intro p hp
          rw [Matrix.smul_apply, stdBasis_apply']
          rw [levelAgreementFinset, Finset.mem_filter] at hp
          have hne : ¬ (p.1 = i ∧ p.2 = j) := by
            rintro ⟨rfl, rfl⟩
            exact hij hp.2
          rw [if_neg hne, smul_zero]
      · intro p _ hp
        rw [Matrix.smul_apply, stdBasis_apply']
        have hne : ¬ (p.1 = i ∧ p.2 = j) := by
          rintro ⟨rfl, rfl⟩
          exact hp rfl
        rw [if_neg hne, smul_zero]
      · intro hmem
        rw [levelAgreementFinset, Finset.mem_filter] at hmem
        push Not at hmem
        exact hX i j (hmem (Finset.mem_univ _))
    rw [hrep]
    refine Submodule.sum_mem _ fun p hp => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [levelAgreementFinset, Finset.mem_filter] at hp
    exact ⟨⟨p, hp.2⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    rw [SetLike.mem_coe, mem_commutantSubmodule_diagonal]
    intro i j hij
    rw [stdBasis_apply']
    have hne : ¬ ((p : n × n).1 = i ∧ (p : n × n).2 = j) := by
      rintro ⟨rfl, rfl⟩
      exact hij p.2
    rw [if_neg hne]

/-- **The commutant dimension of a diagonal matrix is the number of equal-energy level pairs.** -/
theorem finrank_commutantSubmodule_diagonal (E : n → ℂ) :
    Module.finrank ℂ (commutantSubmodule (Matrix.diagonal E)) =
      (levelAgreementFinset E).card := by
  classical
  rw [commutantSubmodule_diagonal_eq_span E]
  rw [finrank_span_eq_card
    ((Matrix.stdBasis ℂ n n).linearIndependent.comp
      (fun p : {p : n × n // E p.1 = E p.2} => (p : n × n)) Subtype.val_injective)]
  rw [levelAgreementFinset, Fintype.card_subtype]

end Commutant

/-! ## Collective replica energies -/

section Replica

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The collective energy of an ordered replica tuple. -/
def collectiveReplicaEnergy (E : I → ℝ) {r : ℕ} (α : Fin r → I) : ℝ := ∑ a, E (α a)

/-- The collective energy of a tuple depends only on its multiplicity histogram. -/
theorem collectiveReplicaEnergy_eq_sum_multiplicity (E : I → ℝ) {r : ℕ} (α : Fin r → I) :
    collectiveReplicaEnergy E α = ∑ j, (orderedReplicaMultiplicity α j : ℝ) * E j := by
  classical
  rw [collectiveReplicaEnergy,
    ← Finset.sum_fiberwise_of_maps_to (g := α) (fun a _ => Finset.mem_univ (α a))
      (fun a => E (α a))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (fun a ha => by
      rw [(Finset.mem_filter.mp ha).2] : ∀ a ∈ Finset.univ.filter fun a => α a = j,
        E (α a) = E j)]
  rw [Finset.sum_const, orderedReplicaMultiplicity, nsmul_eq_mul]

/-- **Maximal projective spectral rank.**  No nontrivial integer relation of zero total charge
holds among the level energies. -/
def MaximalProjectiveRank (E : I → ℝ) : Prop :=
  ∀ k : I → ℤ, ∑ j, k j = 0 → ∑ j, (k j : ℝ) * E j = 0 → k = 0

/-- **Under maximal projective rank two tuples share a collective energy exactly when they share a
multiplicity histogram.** -/
theorem collectiveReplicaEnergy_eq_iff_multiplicity_eq {E : I → ℝ} (hE : MaximalProjectiveRank E)
    {r : ℕ} (α β : Fin r → I) :
    collectiveReplicaEnergy E α = collectiveReplicaEnergy E β ↔
      orderedReplicaMultiplicity α = orderedReplicaMultiplicity β := by
  classical
  constructor
  · intro h
    set k : I → ℤ := fun j =>
      (orderedReplicaMultiplicity α j : ℤ) - (orderedReplicaMultiplicity β j : ℤ) with hk
    have hcharge : ∑ j, k j = 0 := by
      have hα : ∑ j, (orderedReplicaMultiplicity α j : ℤ) = (r : ℤ) := by
        have := (Finset.mem_piAntidiag.mp (orderedReplicaMultiplicity_mem_piAntidiag α)).1
        exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) this
      have hβ : ∑ j, (orderedReplicaMultiplicity β j : ℤ) = (r : ℤ) := by
        have := (Finset.mem_piAntidiag.mp (orderedReplicaMultiplicity_mem_piAntidiag β)).1
        exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) this
      rw [hk, Finset.sum_sub_distrib, hα, hβ, sub_self]
    have haction : ∑ j, (k j : ℝ) * E j = 0 := by
      have hexp : ∀ j, ((k j : ℤ) : ℝ) * E j =
          (orderedReplicaMultiplicity α j : ℝ) * E j -
            (orderedReplicaMultiplicity β j : ℝ) * E j := by
        intro j
        rw [hk]
        push_cast
        ring
      rw [Finset.sum_congr rfl fun j _ => hexp j, Finset.sum_sub_distrib,
        ← collectiveReplicaEnergy_eq_sum_multiplicity,
        ← collectiveReplicaEnergy_eq_sum_multiplicity, h, sub_self]
    have hzero := hE k hcharge haction
    funext j
    have := congrFun hzero j
    rw [hk] at this
    simp only [Pi.zero_apply, sub_eq_zero] at this
    exact_mod_cast this
  · intro h
    rw [collectiveReplicaEnergy_eq_sum_multiplicity, collectiveReplicaEnergy_eq_sum_multiplicity, h]

/-! ## The histogram collision count -/

/-- The number of ordered replica tuple pairs sharing a multiplicity histogram. -/
def replicaHistogramCollision (I : Type*) [Fintype I] [DecidableEq I] (r : ℕ) : ℕ :=
  (Finset.univ.filter fun q : (Fin r → I) × (Fin r → I) =>
    orderedReplicaMultiplicity q.1 = orderedReplicaMultiplicity q.2).card

/-- **Equation (11).**  The histogram collision count is the sum of squared multinomial
coefficients over multiplicity histograms. -/
theorem replicaHistogramCollision_eq_sum_sq (r : ℕ) :
    replicaHistogramCollision I r =
      ∑ p ∈ Finset.univ.piAntidiag r, (Nat.multinomial Finset.univ p) ^ 2 := by
  classical
  rw [replicaHistogramCollision,
    Finset.card_eq_sum_card_fiberwise
      (f := fun q : (Fin r → I) × (Fin r → I) => orderedReplicaMultiplicity q.1)
      (t := Finset.univ.piAntidiag r)
      (fun q _ => orderedReplicaMultiplicity_mem_piAntidiag q.1)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hfiber :
      ((Finset.univ.filter fun q : (Fin r → I) × (Fin r → I) =>
          orderedReplicaMultiplicity q.1 = orderedReplicaMultiplicity q.2).filter
          fun q => orderedReplicaMultiplicity q.1 = p) =
        (Finset.univ.filter fun α : Fin r → I => orderedReplicaMultiplicity α = p) ×ˢ
          (Finset.univ.filter fun β : Fin r → I => orderedReplicaMultiplicity β = p) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨hq, hp1⟩
      exact ⟨hp1, hp1 ▸ hq.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h1, h2], h1⟩
  rw [hfiber, Finset.card_product, card_fiber_orderedReplicaMultiplicity hp,
    card_fiber_orderedReplicaMultiplicity hp, sq]

/-- **Equation (15).**  The total number of ordered replica tuple pairs. -/
theorem card_orderedReplicaPair (r : ℕ) :
    Fintype.card ((Fin r → I) × (Fin r → I)) = (Fintype.card I) ^ (2 * r) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, two_mul, pow_add]

/-! ## The centralizer dimension -/

/-- **Equation (12).**  Under maximal projective rank the centralizer of the collective replica
Hamiltonian has dimension the histogram collision count. -/
theorem finrank_commutantSubmodule_collectiveReplicaEnergy {E : I → ℝ}
    (hE : MaximalProjectiveRank E) (r : ℕ) :
    Module.finrank ℂ
        (commutantSubmodule (Matrix.diagonal
          (fun α : Fin r → I => (collectiveReplicaEnergy E α : ℂ)))) =
      replicaHistogramCollision I r := by
  classical
  rw [finrank_commutantSubmodule_diagonal, replicaHistogramCollision, levelAgreementFinset]
  congr 1
  refine Finset.filter_congr fun q _ => ?_
  constructor
  · intro h
    exact (collectiveReplicaEnergy_eq_iff_multiplicity_eq hE q.1 q.2).mp
      (by exact_mod_cast h)
  · intro h
    exact_mod_cast (collectiveReplicaEnergy_eq_iff_multiplicity_eq hE q.1 q.2).mpr h

/-! ## Universal bounds on the histogram collision count -/

/-- The histogram collision count as a sum over the first tuple of its fibre size. -/
theorem replicaHistogramCollision_eq_sum_fiber (r : ℕ) :
    replicaHistogramCollision I r =
      ∑ α : Fin r → I, Nat.multinomial Finset.univ (orderedReplicaMultiplicity α) := by
  classical
  rw [replicaHistogramCollision,
    Finset.card_eq_sum_card_fiberwise
      (f := fun q : (Fin r → I) × (Fin r → I) => q.1) (t := Finset.univ)
      (fun q _ => Finset.mem_univ q.1)]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hfiber :
      ((Finset.univ.filter fun q : (Fin r → I) × (Fin r → I) =>
          orderedReplicaMultiplicity q.1 = orderedReplicaMultiplicity q.2).filter
          fun q => q.1 = α) =
        {α} ×ˢ (Finset.univ.filter fun β : Fin r → I =>
          orderedReplicaMultiplicity β = orderedReplicaMultiplicity α) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hq, rfl⟩
      exact ⟨rfl, hq.symm⟩
    · rintro ⟨rfl, h2⟩
      exact ⟨h2.symm, rfl⟩
  rw [hfiber, Finset.card_product, Finset.card_singleton, one_mul,
    card_fiber_orderedReplicaMultiplicity (orderedReplicaMultiplicity_mem_piAntidiag α)]

/-- **Equation (16).**  The histogram collision count lies between the number of ordered tuples and
its product with the replica factorial. -/
theorem replicaHistogramCollision_bounds (r : ℕ) :
    (Fintype.card I) ^ r ≤ replicaHistogramCollision I r ∧
      replicaHistogramCollision I r ≤ Nat.factorial r * (Fintype.card I) ^ r := by
  classical
  rw [replicaHistogramCollision_eq_sum_fiber]
  have hcard : (Finset.univ : Finset (Fin r → I)).card = (Fintype.card I) ^ r := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  constructor
  · calc (Fintype.card I) ^ r = ∑ _α : Fin r → I, 1 := by
          rw [Finset.sum_const, hcard, smul_eq_mul, mul_one]
      _ ≤ ∑ α : Fin r → I, Nat.multinomial Finset.univ (orderedReplicaMultiplicity α) := by
          refine Finset.sum_le_sum fun α _ => ?_
          exact Nat.one_le_iff_ne_zero.mpr (Nat.multinomial_ne_zero)
  · calc ∑ α : Fin r → I, Nat.multinomial Finset.univ (orderedReplicaMultiplicity α)
        ≤ ∑ _α : Fin r → I, Nat.factorial r := by
          refine Finset.sum_le_sum fun α _ => ?_
          refine multinomial_le_factorial ?_
          exact (Finset.mem_piAntidiag.mp (orderedReplicaMultiplicity_mem_piAntidiag α)).1
      _ = Nat.factorial r * (Fintype.card I) ^ r := by
          rw [Finset.sum_const, hcard, smul_eq_mul, mul_comm]

end Replica

end GaloisForLFunctions.HTGeometry
