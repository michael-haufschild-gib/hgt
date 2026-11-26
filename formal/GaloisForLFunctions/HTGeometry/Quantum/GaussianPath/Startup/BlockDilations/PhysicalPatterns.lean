import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.IdealCount
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PhysicalRotation

/-! # Finite circuit count for physically dilated Pauli samples -/

open Finset Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

/-- Couplings internal to one selected packet. A crossing bond is never
dilated, even if its two adjacent packets are both selected. -/
def selectedLabels (R : I→Finset (Fin (n+2))) (x : I→Bool) : Finset (PathLabel n) := by
  classical
  exact univ.filter fun l => ∃ i, x i=true ∧ PathWordSupportedIn (R i) l

omit [DecidableEq I] in
private theorem selected_generator (R : I→Finset (Fin (n+2)))
    (hR : Pairwise (fun i j => Disjoint (R i) (R j))) (x : I→Bool) (u : PathShell n) :
    pathHamiltonian (restrictShell (selectedLabels R x) u)=
      ∑ i, if x i then pathHamiltonianOnSites (R i) u else 0 := by
  classical
  let Y := fun (l : PathLabel n) => (u l:ℂ) • finitePauliMatrix (pathWord l)
  let p := fun i l => x i=true ∧ PathWordSupportedIn (R i) l
  have row (i : I) : (if x i then pathHamiltonianOnSites (R i) u else 0)=
      ∑ l : PathLabel n, if p i l then Y l else 0 := by
    by_cases hx : x i=true
    · rw [if_pos hx]
      apply sum_congr rfl
      intro l _
      by_cases hl : PathWordSupportedIn (R i) l <;> simp [p,hx,hl,Y]
    · simp [p,hx]
  rw [pathHamiltonian_eq_sum]
  simp_rw [row]
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  by_cases hl : ∃ i, p i l
  · obtain ⟨i,hi⟩ := hl
    have hm : l∈selectedLabels R x := mem_filter.mpr ⟨mem_univ _,i,hi⟩
    rw [sum_eq_single i]
    · simp [restrictShell,hm,hi,Y]
    · intro j _ hji
      exact if_neg (fun hj => packet_support_intersects hj.2 hi.2 (hR hji))
    · exact fun hn => (hn (mem_univ i)).elim
  · have hm : l∉selectedLabels R x := fun h => hl (mem_filter.mp h).2
    have hnone (i : I) : ¬p i l := fun hi => hl ⟨i,hi⟩
    simp [restrictShell,hm,hnone]

/-- Every physically rescaled sample is close to its binary packet
rotation, at the original measurement date, with its own explicit
boundary error. -/
theorem pattern_error (R : I→Finset (Fin (n+2))) (hR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (u : PathShell n) (x : I→Bool) {t a : ℝ} (ht : 0≤t) (ha : 0≤a) :
    let S := selectedLabels R x
    ‖unitaryEvolution (pathHamiltonian (dilateShell S a u)) t-
      idealPattern R u x (t*a) (unitaryEvolution (pathHamiltonian u) t)‖ ≤ t^2*a*boundaryMass u S := by
  intro S
  simpa only [idealPattern,selected_generator R hR x u,S] using physical_rotation_error u S ha ht

/-- The number of physical samples fitting s gates is bounded directly
by the number of regular spatial packets. The largest boundary error
among the patterns is charged once in the accuracy. -/
theorem physical_pattern_count (R : I→Finset (Fin (n+2))) (hR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (u : PathShell n) {t a : ℝ} (ht : 0≤t) (ha : 0≤a) (ε : ℝ) (r s : ℕ) :
    open Classical in
    let δ := univ.sup' univ_nonempty (fun x : I→Bool => t^2*a*boundaryMass u (selectedLabels R x))
    let G := univ.filter fun i => regularPacket (R i) u (t*a) (ε+δ) r
    let C := univ.filter fun x : I→Bool => HasProjectiveCircuitApproximation (n+2) ε s
      (unitaryEvolution (pathHamiltonian (dilateShell (selectedLabels R x) a u)) t)
    C.card*2^(Fintype.card I-2*s/(r+1))≤3^G.card*4^(Fintype.card I-G.card) := by
  classical
  intro δ G C
  let W := unitaryEvolution (pathHamiltonian u) t
  let B := univ.filter fun x : I→Bool => HasProjectiveCircuitApproximation (n+2) (ε+δ) s
    (idealPattern R u x (t*a) W)
  have hsub : C⊆B := by
    intro x hx
    obtain ⟨z,hz,A,hA,hfit⟩ := (mem_filter.mp hx).2
    refine mem_filter.mpr ⟨mem_univ _,z,hz,A,hA,?_⟩
    let U := unitaryEvolution (pathHamiltonian (dilateShell (selectedLabels R x) a u)) t
    let V := idealPattern R u x (t*a) W
    have hmax : t^2*a*boundaryMass u (selectedLabels R x)≤δ :=
      le_sup' (fun y : I→Bool => t^2*a*boundaryMass u (selectedLabels R y)) (mem_univ x)
    have hd : ‖U-V‖≤δ := (pattern_error R hR u x ht ha).trans hmax
    have hh := norm_sub_le_norm_sub_add_norm_sub V U (z • A.eval.val)
    rw [norm_sub_rev V U] at hh
    exact hh.trans ((add_le_add hd hfit).trans_eq (add_comm ..))
  exact (Nat.mul_le_mul_right _ (card_le_card hsub)).trans (ideal_pattern_count R hR u W (t*a) (ε+δ) r s)

#print axioms pattern_error
#print axioms physical_pattern_count
end
end GaloisForLFunctions.HTGeometry.BlockDilations
