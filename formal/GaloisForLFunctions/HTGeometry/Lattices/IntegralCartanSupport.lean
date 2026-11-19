import GaloisForLFunctions.HTGeometry.Lattices.IntegralRootCartanGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connected support of an integral unit vector

Splitting a simple-root expansion along a cut with no edge between
occupied vertices splits its quadratic energy into two integers. Two
nonempty parts cost at least two. Every unit vector therefore has
connected induced support, even in a reducible ambient root system.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry.IntegralRootShell
variable {J : Type*} [Fintype J] (Q : Form J) (hQ : Q.PosDef)

private theorem nonzero_synth {a : Vertex Q hQ → ℤ} (ha : a≠0) : synth Q hQ a≠0 := by
  intro h
  apply ha
  exact synth_injective Q hQ (h.trans (by simp [synth]))

private theorem cut_energy (a b : Vertex Q hQ → ℤ)
    (cross : ∀ i j, a i≠0 → b j≠0 → i≠j ∧ ¬(cartanGraph Q hQ).Adj i j) :
    Q (synth Q hQ (a+b))=Q (synth Q hQ a)+Q (synth Q hQ b) := by
  classical
  have orth : Q.polarBilin (synth Q hQ a) (synth Q hQ b)=0 := by
    rw [cartan_bilinear]
    apply sum_eq_zero
    intro i _
    apply sum_eq_zero
    intro j _
    by_cases ha : a i=0
    · rw [ha,zero_mul,zero_mul]
    by_cases hb : b j=0
    · rw [hb,mul_zero,zero_mul]
    obtain ⟨ne,noEdge⟩ := cross i j ha hb
    simp [cartanEntry,ne,noEdge]
  rw [synth_add,QuadraticMap.map_add Q,← QuadraticMap.polarBilin_apply_apply,orth,add_zero]

/-- Two nonempty mutually nonadjacent pieces of an integral expansion
have total energy at least two. -/
theorem separated_energy (a b : Vertex Q hQ → ℤ) (ha : a≠0) (hb : b≠0)
    (cross : ∀ i j, a i≠0 → b j≠0 → i≠j ∧ ¬(cartanGraph Q hQ).Adj i j) :
    2≤Q (synth Q hQ (a+b)) := by
  rw [cut_energy Q hQ a b cross]
  have hp := hQ _ (nonzero_synth Q hQ ha)
  have hq := hQ _ (nonzero_synth Q hQ hb)
  omega

/-- The unique expansion of an actual root in the simple coordinates. -/
def rootCoordinates (x : Root Q) : Vertex Q hQ → ℤ := (unique_root_coordinates Q hQ x).exists.choose

theorem synth_rootCoordinates (x : Root Q) : synth Q hQ (rootCoordinates Q hQ x)=x.val :=
  (unique_root_coordinates Q hQ x).exists.choose_spec.1

theorem coordinates_nonzero (x : Root Q) : rootCoordinates Q hQ x≠0 := by
  intro hz
  have he := x.property
  rw [← synth_rootCoordinates Q hQ x,hz] at he
  simp [synth] at he

/-- The induced graph on the nonzero coordinates of every root is connected. -/
theorem root_support_connected (x : Root Q) :
    ((cartanGraph Q hQ).induce {i | rootCoordinates Q hQ x i≠0}).Connected := by
  classical
  let a := rootCoordinates Q hQ x
  let S : Set (Vertex Q hQ) := {i | a i≠0}
  let G := (cartanGraph Q hQ).induce S
  change G.Connected
  rw [SimpleGraph.connected_iff]
  constructor
  · intro u v
    by_contra disconnected
    let inside := fun i : Vertex Q hQ => ∃ hi : i∈S, G.Reachable u ⟨i,hi⟩
    let b := fun i => if inside i then a i else 0
    let c := fun i => if inside i then 0 else a i
    have split : b+c=a := by
      funext i
      by_cases h : inside i <;> simp [b,c,h]
    have hu : inside u.val := ⟨u.property,SimpleGraph.Reachable.refl u⟩
    have hv : ¬inside v.val := fun ⟨_,h⟩ => disconnected h
    have hb : b≠0 := by
      intro e
      exact u.property (by simpa only [b,if_pos hu,Pi.zero_apply] using congrFun e u.val)
    have hc : c≠0 := by
      intro e
      exact v.property (by simpa only [c,if_neg hv,Pi.zero_apply] using congrFun e v.val)
    have cross (i j) (hi : b i≠0) (hj : c j≠0) : i≠j ∧ ¬(cartanGraph Q hQ).Adj i j := by
      have lb : inside i := by by_contra no; exact hi (if_neg no)
      have rc : ¬inside j := fun yes => hj (if_pos yes)
      have sj : j∈S := fun hz => hj (by simp [c,rc,hz])
      obtain ⟨si,path⟩ := lb
      refine ⟨fun e => rc (e ▸ ⟨si,path⟩),fun edge => rc ⟨sj,?_⟩⟩
      exact path.trans ((SimpleGraph.induce_adj.mpr edge : G.Adj ⟨i,si⟩ ⟨j,sj⟩).reachable)
    have tooBig := separated_energy Q hQ b c hb hc cross
    rw [split,show synth Q hQ a=x.val from synth_rootCoordinates Q hQ x,x.property] at tooBig
    omega
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp (coordinates_nonzero Q hQ x)
    exact ⟨⟨i,hi⟩⟩

#print axioms separated_energy
#print axioms root_support_connected
end GaloisForLFunctions.HTGeometry.IntegralRootShell
