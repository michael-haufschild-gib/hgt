import GaloisForLFunctions.HTGeometry.StokesContactRealization
import GaloisForLFunctions.HTGeometry.StokesUniversalContactLaw

/-!
# Integral contact hierarchies realize certified fission data

An integral contact hierarchy is a symmetric acute integer matrix whose diagonal is strictly
smallest.  Rescaled by trivial ramification it becomes a decorated Stokes core whose contact
matrix is acute and whose integral diagonal obstruction is strict, hence it carries a rooted
skeleton.  Every finite label set with at least two labels admits such a hierarchy, so the
universal complementary-contact master law is unconditional and non-vacuous.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

/-- A symmetric acute integral matrix whose diagonal is strictly smallest in its row. -/
structure IntegerContactHierarchy (n : ℕ) where
  /-- Integral contact height of a pair of labels. -/
  h : Fin n → Fin n → ℤ
  h_symm : ∀ i j, h i j = h j i
  h_acute : ∀ i j k, h i j ≤ max (h i k) (h j k)
  h_diagonal_lt : ∀ {i j}, i ≠ j → h i i < h i j

namespace IntegerContactHierarchy

variable {n : ℕ} (H : IntegerContactHierarchy n)

/-- The decorated Stokes core with trivial ramification carried by an integral hierarchy. -/
def toCore : DecoratedStokesCore n where
  B := H.h
  B_symm := H.h_symm
  ramification := fun _ => 1
  ramification_pos := fun _ => Nat.one_pos

@[simp] theorem toCore_B (i j : Fin n) : H.toCore.B i j = H.h i j := rfl

@[simp] theorem toCore_ramification (i : Fin n) : H.toCore.ramification i = 1 := rfl

theorem toCore_contact_self (i : Fin n) :
    H.toCore.realContactMatrix i i = (H.h i i : ℝ) := by
  simp only [DecoratedStokesCore.realContactMatrix, DecoratedStokesCore.contactMatrix_self,
    DecoratedStokesCore.diagonalContact, toCore_ramification, toCore_B]
  push_cast
  ring

theorem toCore_contact_of_ne {i j : Fin n} (hij : i ≠ j) :
    H.toCore.realContactMatrix i j = 1 + (H.h i j : ℝ) := by
  rw [DecoratedStokesCore.realContactMatrix, H.toCore.contactMatrix_of_ne hij]
  simp only [DecoratedStokesCore.pairContact, toCore_ramification, toCore_B]
  push_cast
  ring

/-- The rescaled contact matrix of an integral hierarchy is acute. -/
theorem toCore_acute (i j k : Fin n) :
    H.toCore.realContactMatrix i j ≤
      max (H.toCore.realContactMatrix i k) (H.toCore.realContactMatrix j k) := by
  by_cases hij : i = j
  · subst hij
    rw [H.toCore_contact_self i, max_self]
    by_cases hik : i = k
    · subst hik
      rw [H.toCore_contact_self i]
    · rw [H.toCore_contact_of_ne hik]
      have : (H.h i i : ℝ) ≤ (H.h i k : ℝ) := by exact_mod_cast (H.h_diagonal_lt hik).le
      linarith
  · rw [H.toCore_contact_of_ne hij]
    by_cases hik : i = k
    · subst hik
      have hji : j ≠ i := Ne.symm hij
      rw [H.toCore_contact_self i, H.toCore_contact_of_ne hji]
      have : (H.h j i : ℝ) = (H.h i j : ℝ) := by exact_mod_cast (H.h_symm j i)
      rw [this]
      exact le_max_right _ _
    · by_cases hjk : j = k
      · subst hjk
        rw [H.toCore_contact_self j, H.toCore_contact_of_ne hij]
        exact le_max_left _ _
      · rw [H.toCore_contact_of_ne hik, H.toCore_contact_of_ne hjk]
        have hacute : (H.h i j : ℝ) ≤ max (H.h i k : ℝ) (H.h j k : ℝ) := by
          exact_mod_cast H.h_acute i j k
        rcases max_cases ((H.h i k : ℝ)) ((H.h j k : ℝ)) with ⟨heq, _⟩ | ⟨heq, _⟩ <;>
          rw [heq] at hacute
        · exact le_trans (by linarith) (le_max_left _ _)
        · exact le_trans (by linarith) (le_max_right _ _)

/-- The integral diagonal obstruction of an integral hierarchy is strict. -/
theorem toCore_strict (i j : Fin n) (hij : i ≠ j) :
    (H.toCore.ramification j : ℤ) * (H.toCore.B i i - 1) <
      (H.toCore.ramification i : ℤ) * H.toCore.B i j := by
  simp only [toCore_ramification, toCore_B, Nat.cast_one, one_mul]
  have := H.h_diagonal_lt hij
  omega

/-- Every integral contact hierarchy carries a rooted fission skeleton. -/
theorem nonempty_rootedRealization (hn : 1 < n) :
    Nonempty H.toCore.RootedRealization :=
  (H.toCore.nonempty_rootedRealization_iff hn).mpr
    ⟨H.toCore_acute, fun i j hij => H.toCore_strict i j hij⟩

/-- The certified fission datum of an integral contact hierarchy. -/
noncomputable def certifiedDatum (hn : 1 < n) : CertifiedFissionDatum n where
  core := H.toCore
  rooted := Classical.choice (H.nonempty_rootedRealization hn)

@[simp] theorem certifiedDatum_core (hn : 1 < n) : (H.certifiedDatum hn).core = H.toCore := rfl

end IntegerContactHierarchy

/-- The two-level contact hierarchy of a label partition: distinct labels in one block have
contact `1`, labels in different blocks have contact `2`. -/
def twoLevelHierarchy {n m : ℕ} (f : Fin n → Fin m) : IntegerContactHierarchy n where
  h i j := if i = j then 0 else if f i = f j then 1 else 2
  h_symm := by
    intro i j
    show (if i = j then (0 : ℤ) else if f i = f j then 1 else 2) =
      (if j = i then (0 : ℤ) else if f j = f i then 1 else 2)
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij.symm]
    · rw [if_neg hij, if_neg (Ne.symm hij)]
      by_cases hf : f i = f j
      · rw [if_pos hf, if_pos hf.symm]
      · rw [if_neg hf, if_neg (Ne.symm hf)]
  h_acute := by
    intro i j k
    show (if i = j then (0 : ℤ) else if f i = f j then 1 else 2) ≤
      max (if i = k then (0 : ℤ) else if f i = f k then 1 else 2)
        (if j = k then (0 : ℤ) else if f j = f k then 1 else 2)
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      refine le_max_of_le_left ?_
      split_ifs <;> norm_num
    · rw [if_neg hij]
      by_cases hf : f i = f j
      · rw [if_pos hf]
        by_cases hik : i = k
        · subst hik
          refine le_max_of_le_right (le_of_eq ?_)
          rw [if_neg (Ne.symm hij), if_pos hf.symm]
        · refine le_max_of_le_left ?_
          rw [if_neg hik]
          split_ifs <;> norm_num
      · rw [if_neg hf]
        by_cases hfik : f i = f k
        · have hjk : j ≠ k := fun hc => hf (hfik.trans (congrArg f hc).symm)
          have hfjk : ¬ f j = f k := fun hc => hf (hfik.trans hc.symm)
          refine le_max_of_le_right (le_of_eq ?_)
          rw [if_neg hjk, if_neg hfjk]
        · have hik : i ≠ k := fun hc => hfik (congrArg f hc)
          refine le_max_of_le_left (le_of_eq ?_)
          rw [if_neg hik, if_neg hfik]
  h_diagonal_lt := by
    intro i j hij
    show (if i = i then (0 : ℤ) else if f i = f i then 1 else 2) <
      (if i = j then (0 : ℤ) else if f i = f j then 1 else 2)
    rw [if_pos rfl, if_neg hij]
    split_ifs <;> norm_num

/-- **Certified fission data exist.**  Every label set with at least two labels carries a
decorated Stokes core together with a rooted fission skeleton realizing its rescaled contact
matrix. -/
theorem nonempty_certifiedFissionDatum {n : ℕ} (hn : 1 < n) :
    Nonempty (CertifiedFissionDatum n) :=
  ⟨(twoLevelHierarchy (fun i : Fin n => i)).certifiedDatum hn⟩

/-- **Unconditional universal complementary-contact law.**  For every label set with at least two
labels there is a certified fission datum, and every certified fission datum satisfies the strict
integral obstruction, threshold tomography, the tree-metric axioms, the four-point law, strict
negative type, and the explicit squared-Euclidean realization. -/
theorem exists_certifiedFissionDatum_master_law {n : ℕ} (hn : 1 < n) :
    ∃ datum : CertifiedFissionDatum n,
      (∀ i j, i ≠ j →
        (datum.core.ramification j : ℤ) * (datum.core.B i i - 1) <
          (datum.core.ramification i : ℤ) * datum.core.B i j) ∧
      datum.rooted.tree.hierarchy = datum.rooted.tree.visibleHierarchy ∧
      (∀ i j, datum.core.energy i j = datum.core.energy j i) ∧
      (∀ i j, datum.core.energy i j = 0 ↔ i = j) ∧
      (∀ i j k,
        datum.core.energy i k ≤ datum.core.energy i j + datum.core.energy j k) ∧
      (∀ i j k l,
        MaxTwice (datum.core.energy i j + datum.core.energy k l)
          (datum.core.energy i k + datum.core.energy j l)
          (datum.core.energy i l + datum.core.energy j k)) ∧
      (∀ x : Fin n → ℝ, (∑ i, x i = 0) → x ≠ 0 →
        (∑ i, ∑ j, x i * x j * datum.core.energy i j) < 0) ∧
      (∀ i j,
        (∑ e, (datum.rooted.tree.canonicalCuts.toPositivePendantCutFamily.feature i e -
          datum.rooted.tree.canonicalCuts.toPositivePendantCutFamily.feature j e) ^ 2) =
            datum.core.energy i j) := by
  obtain ⟨datum⟩ := nonempty_certifiedFissionDatum hn
  exact ⟨datum, datum.universal_contact_master_law⟩

end IrregularStokes
end GaloisForLFunctions
