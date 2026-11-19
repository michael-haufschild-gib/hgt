import GaloisForLFunctions.HTGeometry.Lattices.IntegralQuadraticRootShell
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Simple directions of a norm-one shell over the integers

An integer functional can avoid all root hyperplanes simultaneously. Its
positive indecomposable roots are independent and generate every root up
to sign with nonnegative integral coefficients. Their off-diagonal doubled
pairings are zero or minus one, even when the form is nonclassical.
-/

noncomputable section
open Finset IsAddIndecomposable
namespace GaloisForLFunctions.HTGeometry.IntegralRootShell
variable {J : Type*} [Fintype J]

private theorem separate_finite (Q : Form J) (S : Finset (Root Q)) :
    ∃ f : Module.Dual ℤ (Lattice J), ∀ x ∈ S, f x.val≠0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert x S _ ih =>
    obtain ⟨f,hf⟩ := ih
    by_cases hx : f x.val=0
    · obtain ⟨j,hj⟩ : ∃ j, x.val j≠0 := by
        by_contra! hz
        have h : x.val=0 := funext hz
        have he := x.property
        rw [h,Q.map_zero] at he
        omega
      let bad (y : Root Q) := -(y.val j)/(f y.val)
      obtain ⟨t,ht⟩ := (S.image bad).exists_notMem
      refine ⟨t • f+LinearMap.proj j,?_⟩
      intro y hy
      rcases mem_insert.mp hy with e|hy
      · subst y
        change t*f x.val+x.val j≠0
        simpa only [hx,mul_zero,zero_add] using hj
      · change t*f y.val+y.val j≠0
        intro h
        apply ht
        refine mem_image.mpr ⟨y,hy,?_⟩
        unfold bad
        rw [← eq_neg_of_add_eq_zero_left h,Int.mul_ediv_cancel _ (hf y hy)]
    · exact ⟨f,fun y hy => (mem_insert.mp hy).elim (fun h => h ▸ hx) (hf y)⟩

/-- Integer-valued orientation of the entire finite root shell. -/
def orientation (Q : Form J) (hQ : Q.PosDef) : Module.Dual ℤ (Lattice J) := by
  classical
  letI : Finite (Root Q) := finite_roots Q hQ
  letI := Fintype.ofFinite (Root Q)
  exact (separate_finite Q univ).choose

theorem orientation_regular (Q : Form J) (hQ : Q.PosDef) (x : Root Q) :
    orientation Q hQ x.val≠0 := by
  classical
  letI : Finite (Root Q) := finite_roots Q hQ
  letI := Fintype.ofFinite (Root Q)
  exact (separate_finite Q univ).choose_spec x (mem_univ x)

def simpleSet (Q : Form J) (hQ : Q.PosDef) : Set (Root Q) :=
  baseOf (datum Q hQ).root (orientation Q hQ).toAddMonoidHom

/-- The root lines have a simple system already in the original integer
lattice. Spanning the full ambient space is unnecessary. -/
theorem simple_independent (Q : Form J) (hQ : Q.PosDef) :
    LinearIndependent ℤ (fun i : simpleSet Q hQ => i.val.val) := by
  letI : Finite (Root Q) := finite_roots Q hQ
  exact (datum Q hQ).linearIndepOn_root_baseOf' (orientation Q hQ) (orientation_regular Q hQ)

/-- Every root up to sign is a sum with nonnegative integral multiplicities
of the roots selected by the orientation. -/
theorem simple_generate (Q : Form J) (hQ : Q.PosDef) (x : Root Q) :
    x.val ∈ AddSubmonoid.closure (Subtype.val '' simpleSet Q hQ) ∨
    -x.val ∈ AddSubmonoid.closure (Subtype.val '' simpleSet Q hQ) := by
  let P := datum Q hQ
  letI : Finite (Root Q) := finite_roots Q hQ
  letI := P.indexNeg
  exact mem_or_neg_mem_closure_baseOf P.root (orientation Q hQ).toAddMonoidHom x
    (orientation_regular Q hQ x) (by simp)

/-- Distinct simple directions are orthogonal or have doubled inner
product minus one. -/
theorem simple_angles (Q : Form J) (hQ : Q.PosDef) (i j : simpleSet Q hQ) (hne : i≠j) :
    Q.polarBilin i.val.val j.val.val=0 ∨ Q.polarBilin i.val.val j.val.val= -1 := by
  let P := datum Q hQ
  letI : Finite (Root Q) := finite_roots Q hQ
  have ne : i.val≠j.val := fun e => hne (Subtype.ext e)
  have nonpos := P.baseOf_pairwise_pairing_le_zero (orientation Q hQ).toAddMonoidHom
    (orientation_regular Q hQ) j.property i.property ne.symm
  have e : P.pairingIn ℤ j.val i.val = Q.polarBilin i.val.val j.val.val :=
    P.algebraMap_pairingIn ℤ j.val i.val
  change P.pairingIn ℤ j.val i.val ≤ 0 at nonpos
  rw [e] at nonpos
  have orient (k : simpleSet Q hQ) : 0<orientation Q hQ k.val.val := k.property.1
  rcases root_angles Q hQ i.val j.val with h|h|h|h|h
  · exact (ne (Subtype.ext h)).elim
  · have hi := orient i
    rw [h,map_neg] at hi
    linarith only [hi,orient j]
  · exact Or.inr h
  · exact Or.inl h
  · omega

/-- The simple graph occupies at most the ambient integer rank. -/
theorem simple_card_le (Q : Form J) (hQ : Q.PosDef) : Nat.card (simpleSet Q hQ) ≤ Fintype.card J := by
  classical
  letI : Finite (Root Q) := finite_roots Q hQ
  letI := Fintype.ofFinite (simpleSet Q hQ)
  simpa only [Nat.card_eq_fintype_card,Module.finrank_pi] using
    (simple_independent Q hQ).fintype_card_le_finrank

#print axioms orientation_regular
#print axioms simple_independent
#print axioms simple_generate
#print axioms simple_angles
#print axioms simple_card_le
end GaloisForLFunctions.HTGeometry.IntegralRootShell
