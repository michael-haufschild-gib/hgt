import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.WeakEdgeSweep
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.CutMass

/-! # Deterministic circuit price of removing the weakest Pauli bonds -/

open Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
variable {n : ℕ}

/-- Every admissible circuit pays for all but twice the count of weak
bonds and an explicit inverse-time correction from the total cut mass. -/
theorem deficit_price (u : PathShell n) (s : ℕ) {h t : ℝ} (hh : 0<h) (ht : t≠0)
    (hc : HasProjectiveCircuitApproximation (n+2) (1/4) s (unitaryEvolution (pathHamiltonian u) t))
    (hsmall : |t| * ‖u‖≤1/100) :
    (n+1:ℕ) < (s:ℝ)+2*((weakEdges u h).card:ℝ)+9*π/(2 * |t| * h) := by
  classical
  obtain ⟨z,hz,C,hC,hfit⟩ := hc
  obtain ⟨c,hcut,hprice⟩ := all_axes_sparse_cut u C t z hz hfit hsmall
  let F := crossed c
  let W := weakEdges u h
  let J (e : Fin (n+1)) := ∑ ab : Fin 3×Fin 3, |u (.inr (e,ab))|
  have hJ (e : Fin (n+1)) : 0≤J e := sum_nonneg fun _ _ => abs_nonneg _
  have hsum : ((F\W).card:ℝ)*h≤∑ e∈F, J e := by
    calc
      _ = ∑ _e∈F\W, h := by simp only [sum_const,nsmul_eq_mul]
      _ ≤ ∑ e∈F\W, J e := by
        apply sum_le_sum
        intro e he
        have hbad : ¬∀ ab : Fin 3×Fin 3, |u (.inr (e,ab))|≤h :=
          fun hw => (mem_sdiff.mp he).2 (mem_filter.mpr ⟨mem_univ _,hw⟩)
        obtain ⟨ab,hab⟩ := not_forall.mp hbad
        exact (le_of_not_ge hab).trans (single_le_sum (fun k _ => abs_nonneg (u (.inr (e,k)))) (mem_univ ab))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun e _ _ => hJ e)
  have hcard : F.card≤(F\W).card+W.card := by
    rw [←card_sdiff_add_card_inter F W]
    exact Nat.add_le_add_left (card_le_card inter_subset_right) _
  have hnum : ((n+1:ℕ):ℝ) ≤ s+2*(((F\W).card:ℝ)+W.card) := by
    exact_mod_cast hcut.trans (Nat.add_le_add hC (Nat.mul_le_mul_left 2 hcard))
  have hscale : 0<2 * |t| * h := mul_pos (mul_pos two_pos (abs_pos.mpr ht)) hh
  have hm := (mul_le_mul_of_nonneg_left hsum (show 0≤4 * |t| by positivity)).trans_lt hprice
  have hwindow : 2*((F\W).card:ℝ)<9*π/(2 * |t| * h) := by
    apply (lt_div_iff₀ hscale).mpr
    calc _ = 4 * |t| * (((F\W).card:ℝ)*h) := by ring
         _ < _ := hm
  linarith only [hnum,hwindow]

#print axioms deficit_price
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
