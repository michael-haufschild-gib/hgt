import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.Packets

/-! # The three independent blocks left by deleting two path bonds -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds
open DiagonalSynthesis Subregister
noncomputable section

def leftBlock {n : ℕ} (a : Fin (n+1)) := Finset.Iic a.castSucc
def middleBlock {n : ℕ} (a b : Fin (n+1)) := Finset.Ioc a.castSucc b.castSucc
def rightBlock {n : ℕ} (b : Fin (n+1)) := Finset.Ioi b.castSucc

private theorem site_partition {n : ℕ} {a b : Fin (n+1)} (hab : a < b) (i : Fin (n+2)) (X : Register (n+2)) :
    X = (if i ∈ leftBlock a then X else 0) + (if i ∈ middleBlock a b then X else 0) +
      (if i ∈ rightBlock b then X else 0) := by
  simp only [leftBlock,middleBlock,rightBlock,Finset.mem_Iic,Finset.mem_Ioc,Finset.mem_Ioi]
  have h := Fin.castSucc_lt_castSucc_iff.mpr hab
  by_cases hl : i ≤ a.castSucc
  · simp [hl,not_lt_of_ge hl,not_lt_of_ge (hl.trans h.le)]
  · by_cases hr : i ≤ b.castSucc <;> simp [hl,lt_of_not_ge hl,hr]

private theorem edge_partition {n : ℕ} {a b : Fin (n+1)} (hab : a < b) (g : Fin (n+1)) (X : Register (n+2)) :
    X = (if g.castSucc ∈ leftBlock a ∧ g.succ ∈ leftBlock a then X else 0) +
      (if g.castSucc ∈ middleBlock a b ∧ g.succ ∈ middleBlock a b then X else 0) +
      (if g.castSucc ∈ rightBlock b ∧ g.succ ∈ rightBlock b then X else 0) +
      (if g=a then X else 0) + (if g=b then X else 0) := by
  have hL : (g.castSucc ∈ leftBlock a ∧ g.succ ∈ leftBlock a) ↔ g < a := by
    simp only [leftBlock,Finset.mem_Iic,Fin.le_def,Fin.lt_def,Fin.val_castSucc,Fin.val_succ]; omega
  have hM : (g.castSucc ∈ middleBlock a b ∧ g.succ ∈ middleBlock a b) ↔ a < g ∧ g < b := by
    simp only [middleBlock,Finset.mem_Ioc,Fin.le_def,Fin.lt_def,Fin.val_castSucc,Fin.val_succ]; omega
  have hR : (g.castSucc ∈ rightBlock b ∧ g.succ ∈ rightBlock b) ↔ b < g := by
    simp only [rightBlock,Finset.mem_Ioi,Fin.lt_def,Fin.val_castSucc,Fin.val_succ]; omega
  simp only [hL,hM,hR]
  rcases lt_trichotomy g a with h|rfl|h
  · simp [h,h.ne,(h.trans hab).ne,not_lt_of_gt h,not_lt_of_gt (h.trans hab)]
  · simp [hab,hab.ne,not_lt_of_gt hab]
  · rcases lt_trichotomy g b with q|rfl|q
    · simp [h,q,not_lt_of_gt h,not_lt_of_gt q,h.ne',q.ne]
    · simp [h,not_lt_of_gt h,h.ne']
    · simp [h,q,not_lt_of_gt h,not_lt_of_gt q,h.ne',q.ne']

/-- The only discarded terms are exactly the two crossing interactions. -/
theorem sub_three_packets {n : ℕ} (u : PathShell n) {a b : Fin (n+1)} (hab : a < b) :
    pathHamiltonian u - (packet u (leftBlock a) + packet u (middleBlock a b) + packet u (rightBlock b)) =
      edgePart u a + edgePart u b := by
  have hs := Finset.sum_congr (s := Finset.univ) rfl
    (fun (i : Fin (n+2)) _ => site_partition hab i (onsiteAt u i))
  have he := Finset.sum_congr (s := Finset.univ) rfl
    (fun (g : Fin (n+1)) _ => edge_partition hab g (edgePart u g))
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true] at hs he
  have ho : onsitePart u = ∑ i, onsiteAt u i := by
    simp only [onsitePart,onsiteAt,Fintype.sum_prod_type]
  rw [pathHamiltonian,ho,hs,he]
  unfold packet
  abel

/-- Uniform exact simulation cost of the decoupled blocks, independent of time. -/
theorem three_block_synthesis {n : ℕ} (u : PathShell n) (a b : Fin (n+1)) (hab : a < b)
    (hL : 2 ≤ (leftBlock a).card) (hM : 2 ≤ (middleBlock a b).card) (hR : 2 ≤ (rightBlock b).card) (t : ℝ) :
    let L := leftBlock a
    let M := middleBlock a b
    let R := rightBlock b
    Realizes (packetCost L.card+packetCost M.card+packetCost R.card)
      (unitaryEvolution (packet u L + packet u M + packet u R) t) := by
  intro L M R
  have hLM : Disjoint L M := Finset.disjoint_left.mpr fun _ hl hm =>
    (Finset.mem_Ioc.mp hm).1.not_ge (Finset.mem_Iic.mp hl)
  have hMR : Disjoint (L ∪ M) R := by
    apply Finset.disjoint_left.mpr
    intro i hi hr
    rcases Finset.mem_union.mp hi with hl|hm
    · exact (Finset.mem_Ioi.mp hr).not_ge ((Finset.mem_Iic.mp hl).trans (Fin.castSucc_lt_castSucc_iff.mpr hab).le)
    · exact (Finset.mem_Ioi.mp hr).not_ge (Finset.mem_Ioc.mp hm).2
  have hs : IsSiteSupported (A := fun _ : Fin (n+2) => Bool) (L ∪ M) (packet u L + packet u M) :=
    (IsSiteSupported.mono Finset.subset_union_left (packet_supported u L)).add
      (IsSiteSupported.mono Finset.subset_union_right (packet_supported u M))
  rw [unitaryEvolution_add_of_isSiteSupported_disjoint hMR hs (packet_supported u R),
    unitaryEvolution_add_of_isSiteSupported_disjoint hLM (packet_supported u L) (packet_supported u M)]
  exact ((packet_exact_evolution u L hL t).mul (packet_exact_evolution u M hM t)).mul
    (packet_exact_evolution u R hR t)

#print axioms sub_three_packets
#print axioms three_block_synthesis
end
end GaloisForLFunctions.HTGeometry.WeakBonds
