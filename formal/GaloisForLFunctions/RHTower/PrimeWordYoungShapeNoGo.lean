import GaloisForLFunctions.RHTower.PrimeWordEnsembleBoundaryTomography
import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Support tomography is blind to prime-word Young shape

The multiplicities of the letters in a length-`n` prime word form a partition of `n`.  This is the
finite Young shape retained by the proposed Edrei--Thoma detour.  The scalar support-cardinality
boundary germ does not determine it: `[0,0,0,1]` and `[0,0,1,1]` have the same two-letter support
and identical scalar deformations, but multiplicity partitions `[3,1]` and `[2,2]`.

The positive repair is exact and finite: keep the full word through `Nat.Partition.ofSym`, and only
then pass to its multiplicity partition.
-/

namespace GaloisForLFunctions.RHTower

/-- The partition of word length formed by the nonzero letter multiplicities. -/
def primeWordMultiplicityPartition {α : Type*} [DecidableEq α]
    (w : List α) : Nat.Partition w.length :=
  Nat.Partition.ofSym (Sym.ofVector ⟨w, rfl⟩)

def multiplicityWord31 : List (Fin 2) := [0, 0, 0, 1]
def multiplicityWord22 : List (Fin 2) := [0, 0, 1, 1]

def multiplicityEnsemble31 : Finset (List (Fin 2)) := {multiplicityWord31}
def multiplicityEnsemble22 : Finset (List (Fin 2)) := {multiplicityWord22}
def multiplicityUnitWeight (_ : List (Fin 2)) : ℤ := 1

/-- The counterexample words have exactly the same distinct-letter support. -/
theorem multiplicityWords_support_eq :
    GaloisForLFunctions.primeWordSupport multiplicityWord31 =
      GaloisForLFunctions.primeWordSupport multiplicityWord22 := by
  simp [multiplicityWord31, multiplicityWord22, GaloisForLFunctions.primeWordSupport]

/-- Hence the scalar marked deformations, and all their boundary jets, coincide. -/
theorem multiplicityEnsemble_deformation_eq :
    primeWordEnsembleDeformation multiplicityEnsemble31 multiplicityUnitWeight =
      primeWordEnsembleDeformation multiplicityEnsemble22 multiplicityUnitWeight := by
  simp [primeWordEnsembleDeformation, multiplicityEnsemble31, multiplicityEnsemble22,
    multiplicityUnitWeight, multiplicityWord31, multiplicityWord22,
    GaloisForLFunctions.primeWordSupport, primeSupportMarkedDeformation]

/-- The first full word has multiplicity partition `[3,1]`. -/
theorem multiplicityWord31_partition_parts :
    (primeWordMultiplicityPartition multiplicityWord31).parts = ({3, 1} : Multiset ℕ) := by
  decide

/-- The second full word has multiplicity partition `[2,2]`. -/
theorem multiplicityWord22_partition_parts :
    (primeWordMultiplicityPartition multiplicityWord22).parts = ({2, 2} : Multiset ℕ) := by
  decide

theorem multiplicityWords_partition_ne :
    primeWordMultiplicityPartition multiplicityWord31 ≠
      primeWordMultiplicityPartition multiplicityWord22 := by
  intro h
  have hc := congrArg (fun p => p.parts.count 3) h
  norm_num [primeWordMultiplicityPartition, Nat.Partition.ofSym, Sym.ofVector,
    multiplicityWord31, multiplicityWord22] at hc

/-- Positive no-go capstone: the complete scalar boundary germ and support coincide, while the
Young multiplicity partition differs. -/
theorem boundaryGerm_blind_to_multiplicityPartition :
    (∀ r : ℕ,
      ((derivative^[r])
        (primeWordEnsembleDeformation multiplicityEnsemble31 multiplicityUnitWeight)).eval 1 =
      ((derivative^[r])
        (primeWordEnsembleDeformation multiplicityEnsemble22 multiplicityUnitWeight)).eval 1) ∧
      GaloisForLFunctions.primeWordSupport multiplicityWord31 =
        GaloisForLFunctions.primeWordSupport multiplicityWord22 ∧
      primeWordMultiplicityPartition multiplicityWord31 ≠
        primeWordMultiplicityPartition multiplicityWord22 := by
  refine ⟨?_, multiplicityWords_support_eq, multiplicityWords_partition_ne⟩
  intro r
  rw [multiplicityEnsemble_deformation_eq]

/-- Fresh-letter Young branching: adjoining a previously absent prime letter inserts one new
row of length one in the multiplicity partition.  This is the first exact one-box edge of the
prime-word Young graph. -/
theorem primeWordMultiplicityPartition_cons_fresh_parts {α : Type*} [DecidableEq α]
    (x : α) (w : List α) (hx : x ∉ w) :
    (primeWordMultiplicityPartition (x :: w)).parts =
      1 ::ₘ (primeWordMultiplicityPartition w).parts := by
  have hcountx : w.count x = 0 := List.count_eq_zero.mpr hx
  have hmap : w.dedup.map (fun y => (x :: w).count y) =
      w.dedup.map (fun y => w.count y) := by
    apply List.map_congr_left
    intro y hy
    have hyx : y ≠ x := by
      intro hyx
      subst y
      exact hx (List.mem_dedup.mp hy)
    simp [hyx.symm]
  simp [primeWordMultiplicityPartition, Nat.Partition.ofSym, Sym.ofVector,
    hx, hcountx, hmap]

/-- Repeated-letter Young branching: adjoining an already present prime letter replaces its
current multiplicity `k` by `k + 1`.  Together with the fresh-letter theorem, this gives the full
one-box branching rule for prime-word multiplicity partitions. -/
theorem primeWordMultiplicityPartition_cons_existing_parts {α : Type*} [DecidableEq α]
    (x : α) (w : List α) (hx : x ∈ w) :
    (primeWordMultiplicityPartition (x :: w)).parts =
      (w.count x + 1) ::ₘ
        (primeWordMultiplicityPartition w).parts.erase (w.count x) := by
  let l := w.dedup
  let r := l.erase x
  have hxl : x ∈ l := List.mem_dedup.mpr hx
  have hlperm : l.Perm (x :: r) := List.perm_cons_erase hxl
  have hrmap : r.map (fun y => (x :: w).count y) =
      r.map (fun y => w.count y) := by
    apply List.map_congr_left
    intro y hy
    have hyx : y ≠ x := (List.nodup_dedup w).mem_erase_iff.mp hy |>.1
    simp [hyx.symm]
  have hnewList : ((x :: w).dedup.map fun y => (x :: w).count y).Perm
      ((w.count x + 1) :: r.map fun y => w.count y) := by
    rw [List.dedup_cons_of_mem hx]
    calc
      (l.map fun y => (x :: w).count y).Perm
          ((x :: r).map fun y => (x :: w).count y) := hlperm.map _
      _ = (w.count x + 1) :: r.map (fun y => w.count y) := by
        simp [hrmap]
  have holdList : (w.dedup.map fun y => w.count y).Perm
      ((w.count x) :: r.map fun y => w.count y) := by
    simpa [l] using hlperm.map (fun y => w.count y)
  have hnew : (primeWordMultiplicityPartition (x :: w)).parts =
      ((↑((w.count x + 1) :: r.map fun y => w.count y) : Multiset ℕ)) := by
    simp only [primeWordMultiplicityPartition, Nat.Partition.ofSym, Sym.ofVector,
      Multiset.coe_dedup, Multiset.coe_count]
    exact Multiset.coe_eq_coe.mpr hnewList
  have hold : (primeWordMultiplicityPartition w).parts =
      ((↑((w.count x) :: r.map fun y => w.count y) : Multiset ℕ)) := by
    simp only [primeWordMultiplicityPartition, Nat.Partition.ofSym, Sym.ofVector,
      Multiset.coe_dedup, Multiset.coe_count]
    exact Multiset.coe_eq_coe.mpr holdList
  rw [hnew, hold]
  simp

/-- Exact squarefree-column law: a word with no repeated prime labels has Young shape consisting
only of rows of length one.  This identifies the positive squarefree/Möbius source sector with the
pure-column boundary of the Young graph. -/
theorem primeWordMultiplicityPartition_parts_eq_replicate_one_of_nodup
    {α : Type*} [DecidableEq α] (w : List α) (hw : w.Nodup) :
    (primeWordMultiplicityPartition w).parts = Multiset.replicate w.length 1 := by
  induction w with
  | nil => simp [primeWordMultiplicityPartition, Nat.Partition.ofSym, Sym.ofVector]
  | cons x w ih =>
      rw [primeWordMultiplicityPartition_cons_fresh_parts x w (List.nodup_cons.mp hw).1]
      rw [ih (List.nodup_cons.mp hw).2]
      simp

/-- The squarefree-column law is sharp: the Young shape is a full column exactly when the prime
word is squarefree.  Repeated prime powers are therefore precisely the rows that the Bernoulli
Möbius sector cannot see. -/
theorem primeWordMultiplicityPartition_parts_eq_replicate_one_iff_nodup
    {α : Type*} [DecidableEq α] (w : List α) :
    (primeWordMultiplicityPartition w).parts = Multiset.replicate w.length 1 ↔ w.Nodup := by
  constructor
  · intro hparts
    induction w with
    | nil => simp
    | cons x w ih =>
        by_cases hx : x ∈ w
        · have hbranch := primeWordMultiplicityPartition_cons_existing_parts x w hx
          have hmem : w.count x + 1 ∈
              (primeWordMultiplicityPartition (x :: w)).parts := by
            rw [hbranch]
            simp
          rw [hparts] at hmem
          have hone : w.count x + 1 = 1 := Multiset.eq_of_mem_replicate hmem
          have hpos : 0 < w.count x := List.count_pos_iff.mpr hx
          omega
        · apply List.nodup_cons.mpr
          refine ⟨hx, ih ?_⟩
          have hbranch := primeWordMultiplicityPartition_cons_fresh_parts x w hx
          rw [hbranch] at hparts
          simpa using hparts
  · exact primeWordMultiplicityPartition_parts_eq_replicate_one_of_nodup w

end GaloisForLFunctions.RHTower
