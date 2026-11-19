import GaloisForLFunctions.HTGeometry.Lattices.IntegralRootSimpleDirections
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# The Cartan graph of an integral norm-one shell

The simple directions give an integer coordinate chart for every norm-one
vector. The doubled energy matrix is two times the identity minus the
adjacency matrix. Consequently each root has an all-nonnegative or
all-nonpositive coefficient vector, and the graph energy is positive
on every nonzero integer vector.
-/

noncomputable section
open Finset Matrix
namespace GaloisForLFunctions.HTGeometry.IntegralRootShell
variable {J : Type*} [Fintype J] (Q : Form J) (hQ : Q.PosDef)

abbrev Vertex := simpleSet Q hQ

instance vertexFintype : Fintype (Vertex Q hQ) := by
  letI : Finite (Root Q) := finite_roots Q hQ
  exact Fintype.ofFinite _

/-- Edges are exactly pairs with negative doubled inner product. -/
def cartanGraph : SimpleGraph (Vertex Q hQ) where
  Adj i j := Q.polarBilin i.val.val j.val.val= -1
  symm := ⟨fun i j h => (QuadraticMap.polar_comm Q j.val.val i.val.val).trans h⟩
  loopless := ⟨fun i => by
    change Q.polarBilin i.val.val i.val.val≠ -1
    rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_self,two_nsmul,i.val.property]
    norm_num⟩

/-- Integral synthesis from the simple directions. -/
def synth (a : Vertex Q hQ → ℤ) := ∑ i, a i • i.val.val

theorem synth_add (a b : Vertex Q hQ → ℤ) : synth Q hQ (a+b)=synth Q hQ a+synth Q hQ b := by
  simp only [synth,Pi.add_apply,add_smul,sum_add_distrib]

theorem synth_neg (a : Vertex Q hQ → ℤ) : synth Q hQ (-a)= -synth Q hQ a := by
  simp only [synth,Pi.neg_apply,neg_smul,sum_neg_distrib]

theorem synth_injective : Function.Injective (synth Q hQ) := by
  intro a b h
  have hz : synth Q hQ (a-b)=0 := by rw [sub_eq_add_neg,synth_add,synth_neg,h,add_neg_cancel]
  funext i
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp (simple_independent Q hQ) (a-b) hz i)

private theorem in_positive_span (x : Lattice J)
    (hx : x ∈ AddSubmonoid.closure (Subtype.val '' simpleSet Q hQ)) :
    ∃ a : Vertex Q hQ → ℤ, (∀ i, 0≤a i) ∧ synth Q hQ a=x := by
  classical
  induction hx using AddSubmonoid.closure_induction with
  | mem y hy =>
    obtain ⟨i,hi,rfl⟩ := hy
    let j : Vertex Q hQ := ⟨i,hi⟩
    refine ⟨fun k => if k=j then 1 else 0,fun k => by by_cases h : k=j <;> simp [h],?_⟩
    simp [synth,ite_smul,j]
  | zero => exact ⟨0,fun _ => le_rfl,by simp [synth]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a,ha,e⟩ := hx
    obtain ⟨b,hb,f⟩ := hy
    exact ⟨a+b,fun i => add_nonneg (ha i) (hb i),by rw [synth_add,e,f]⟩

/-- Unique integral simple-root coordinates, with a common sign in every
coordinate. This also applies when roots span a proper ambient sublattice. -/
theorem unique_root_coordinates (x : Root Q) :
    ∃! a : Vertex Q hQ → ℤ, synth Q hQ a=x.val ∧ ((∀ i, 0≤a i) ∨ (∀ i, a i≤0)) := by
  have ex : ∃ a : Vertex Q hQ → ℤ, synth Q hQ a=x.val ∧ ((∀ i, 0≤a i) ∨ (∀ i, a i≤0)) := by
    rcases simple_generate Q hQ x with h|h
    · obtain ⟨a,ha,e⟩ := in_positive_span Q hQ _ h
      exact ⟨a,e,Or.inl ha⟩
    · obtain ⟨a,ha,e⟩ := in_positive_span Q hQ _ h
      exact ⟨-a,by rw [synth_neg,e,neg_neg],Or.inr fun i => neg_nonpos.mpr (ha i)⟩
  obtain ⟨a,ha⟩ := ex
  exact ⟨a,ha,fun b hb => synth_injective Q hQ (hb.1.trans ha.1.symm)⟩

/-- Weight two on the diagonal and minus one on each directed edge. -/
def cartanEntry (i j : Vertex Q hQ) : ℤ := by
  classical
  exact (if i=j then 2 else 0)-(if (cartanGraph Q hQ).Adj i j then 1 else 0)

theorem pair_eq_cartan (i j : Vertex Q hQ) : Q.polarBilin i.val.val j.val.val=cartanEntry Q hQ i j := by
  classical
  by_cases h : i=j
  · subst j
    simp [cartanEntry,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_self,i.val.property]
  · rcases simple_angles Q hQ i j h with e|e
    · have he : ¬(cartanGraph Q hQ).Adj i j := by change _≠ -1; omega
      simp [cartanEntry,h,he,e]
    · have he : (cartanGraph Q hQ).Adj i j := e
      simp [cartanEntry,h,he,e]

/-- Polarization in the integral simple-root coordinates. -/
theorem cartan_bilinear (a b : Vertex Q hQ → ℤ) :
    Q.polarBilin (synth Q hQ a) (synth Q hQ b) = ∑ i, ∑ j, a i*b j*cartanEntry Q hQ i j := by
  simp only [synth,map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,mul_sum,
    pair_eq_cartan,mul_assoc]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => mul_left_comm _ _ _

/-- Exact energy in graph coordinates, with both orientations of each edge. -/
theorem cartan_energy (a : Vertex Q hQ → ℤ) :
    2*Q (synth Q hQ a) = ∑ i, ∑ j, a i*a j*cartanEntry Q hQ i j := by
  have e : Q.polarBilin (synth Q hQ a) (synth Q hQ a)=2*Q (synth Q hQ a) := by
    rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_self,two_nsmul,two_mul]
  exact e.symm.trans (cartan_bilinear Q hQ a a)

/-- Strict positivity of the graph energy excludes every affine or
indefinite induced diagram. -/
theorem cartan_energy_pos (a : Vertex Q hQ → ℤ) (ha : a≠0) :
    0 < ∑ i, ∑ j, a i*a j*cartanEntry Q hQ i j := by
  have hz : synth Q hQ a≠0 := fun e => ha (synth_injective Q hQ (e.trans (by simp [synth])))
  rw [← cartan_energy]
  exact mul_pos (by norm_num) (hQ _ hz)

#print axioms unique_root_coordinates
#print axioms pair_eq_cartan
#print axioms cartan_energy
#print axioms cartan_energy_pos
end GaloisForLFunctions.HTGeometry.IntegralRootShell
