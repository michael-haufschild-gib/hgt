import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.BufferedCuts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.OwnedPatterns

/-! # Physical Pauli labels of the least-energy cut in each full buffer -/

open Finset
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
variable {n N : ℕ}

abbrev fullBuffers (n N : ℕ) := Fin ((n+1)/(3*N))
abbrev packetIndices (n N : ℕ) := Fin ((n+1)/(3*N)+1)

private def offsets (hN : 0<N) (p : fullBuffers n N→Fin N) (b : fullBuffers n N) : Fin (3*N) :=
  ⟨3*(p b).val,Nat.mul_lt_mul_of_pos_left (p b).isLt (by decide)⟩

private def edgeAt (hN : 0<N) (b : fullBuffers n N) (j : Fin N) : Fin (n+1) :=
  bufferEdge (by omega : 0<3*N) (fun _ => ⟨3*j.val,Nat.mul_lt_mul_of_pos_left j.isLt (by decide)⟩) b

/-- Nine physical coordinates at each candidate bond, at offsets 0,3,6,… . -/
def bondLabels (hN : 0<N) (b : fullBuffers n N) (j : Fin N) (k : Fin 9) : PathLabel n :=
  .inr (edgeAt hN b j,(finProdFinEquiv (m:=3) (n:=3)).symm k)

/-- The block index has the same type for every choice of seams. -/
def bufferedOwner (hN : 0<N) (p : fullBuffers n N→Fin N) (v : Fin (n+2)) : packetIndices n N :=
  Fin.cast (congrArg (·+1) (bufferedCuts_card (by omega : 0<3*N) (offsets hN p)))
    (intervalOf (bufferedCuts (by omega) (offsets hN p)) v)

theorem bufferedOwner_size (hN : 0<N) (p : fullBuffers n N→Fin N) (i : packetIndices n N) :
    (sites (bufferedOwner hN p) i).card≤2*(3*N) := by
  let C := bufferedCuts (by omega : 0<3*N) (offsets hN p)
  have hC := congrArg (·+1) (bufferedCuts_card (by omega : 0<3*N) (offsets hN p))
  let j := Fin.cast hC.symm i
  have he : sites (bufferedOwner hN p) i=sites (intervalOf C) j := by
    ext v
    simp only [sites,mem_filter,mem_univ,true_and,bufferedOwner,Fin.ext_iff,Fin.val_cast,j,C]
  rw [he]
  exact buffered_packet_size _ _ _

/-- The crossing labels are exactly the nine interactions on each selected bond. -/
theorem bufferedOwner_cut (hN : 0<N) (p : fullBuffers n N→Fin N) :
    cutLabels (bufferedOwner hN p)=univ.image (fun j : fullBuffers n N × Fin 9 =>
      bondLabels hN j.1 (p j.1) j.2) := by
  classical
  let C := bufferedCuts (by omega : 0<3*N) (offsets hN p)
  have hc (e : Fin (n+1)) :
      bufferedOwner hN p e.castSucc≠bufferedOwner hN p e.succ ↔ e∈C := by
    simpa only [bufferedOwner,ne_eq,Fin.ext_iff,Fin.val_cast,C] using interval_crosses C e
  ext q
  rcases q with ⟨v,a⟩ | ⟨e,ab⟩
  · constructor
    · exact fun h => ((mem_filter.mp h).2 : False).elim
    · intro h
      obtain ⟨j,_,hj⟩ := mem_image.mp h
      cases hj
  · change _ ↔ _
    rw [cutLabels,mem_filter, and_iff_right (mem_univ _)]
    change (bufferedOwner hN p e.castSucc≠bufferedOwner hN p e.succ) ↔ _
    rw [hc]
    constructor
    · intro he
      obtain ⟨b,_,hb⟩ := mem_image.mp he
      refine mem_image.mpr ⟨(b,finProdFinEquiv ab),mem_univ _,?_⟩
      simp only [bondLabels,Equiv.symm_apply_apply]
      exact congrArg (fun f => (Sum.inr (f,ab) : PathLabel n)) hb
    · intro hy
      obtain ⟨⟨b,k⟩,_,hb⟩ := mem_image.mp hy
      refine mem_image.mpr ⟨b,mem_univ _,?_⟩
      exact congrArg Prod.fst (Sum.inr.inj hb)

theorem cutLabel_count (hN : 0<N) (p : fullBuffers n N→Fin N) :
    (cutLabels (bufferedOwner hN p)).card≤9*((n+1)/(3*N)) := by
  rw [bufferedOwner_cut]
  apply card_image_le.trans
  simp only [card_univ,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm]

/-- If just one candidate lies in a δ-box, every coefficient on the
chosen bond is at most 3δ, irrespective of ties and of the other buffers. -/
theorem minimum_bond_coordinate {I : Type*} [Fintype I] [LinearOrder I] {ι : Type*}
    (L : I→Fin 9→ι) (z : ι→ℝ) (i j : I) {δ : ℝ} (hδ : 0≤δ)
    (hmin : IsFirstMinimum (fun k => bondSquare (L k) z) i)
    (hsmall : ∀ k, |z (L j k)|≤δ) (k : Fin 9) : |z (L i k)|≤3*δ := by
  have h₁ := single_le_sum (fun (l : Fin 9) _ => sq_nonneg (z (L i l))) (mem_univ k)
  have h₂ := sum_le_sum (s:=univ) (fun (l : Fin 9) _ => pow_le_pow_left₀ (abs_nonneg _) (hsmall l) 2)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,sq_abs,Nat.cast_ofNat] at h₂
  have h₃ := (h₁.trans (hmin.1 j)).trans h₂
  nlinarith only [h₃,sq_abs (z (L i k)),abs_nonneg (z (L i k)),hδ]

#print axioms bufferedOwner_cut
#print axioms cutLabel_count
#print axioms minimum_bond_coordinate
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
