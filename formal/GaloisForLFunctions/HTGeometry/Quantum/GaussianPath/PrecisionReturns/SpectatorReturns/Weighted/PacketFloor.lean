import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.Weighted.JoinedForest
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.Weighted.ContinuousFloor

/-! # Cost in physical time of one extra collision between energy packets -/

open Finset Filter Set MeasureTheory Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
noncomputable section

/-- A collision between two representatives at precision ε^β adds β
to the time exponent of n+1 independent tight leaf gaps. All edges and
both representatives can be chosen after observing the time and spectrum. -/
theorem gaussian_joined_gap_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k n : ℕ,
      let I := Fin (k+3)→Bool
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∀ a K β L : ℝ, 0<a → 0<K → 0<β → β≤1 → 0≤L → L<(n:ℝ)+β →
        ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ (l r : Fin (n+1)→I) (x y : I), Function.Injective l →
          (∀ i j, r i≠l j) → x≠y → (∀ i, x≠l i) → (∀ i, y≠l i) → ∀ t≥a,
          (∀ i, latticeClose (t*(E (l i)-E (r i))/(2*π)) (K*ε)) →
          latticeClose (t*(E x-E y)/(2*π)) (K*ε^β) → L<log t/log (1/ε) := by
  classical
  filter_upwards [gaussian_spectral_forms] with ω hh k n
  intro I E a K β L ha hK hβ hβ' hL hlim
  let valid (l r : Fin (n+1)→I) (x y : I) := Function.Injective l ∧ (∀ i j, r i≠l j) ∧
    x≠y ∧ (∀ i, x≠l i) ∧ ∀ i, y≠l i
  let w : Fin (n+1+1)→ℝ := Fin.cons 1 (Fin.cons β fun _ => 1)
  have hw : ∀ i, 0<w i := Fin.cases zero_lt_one (Fin.cases hβ (fun _ => zero_lt_one))
  have hmax : ∀ i : Fin (n+1), w i.succ≤w 0 := Fin.cases hβ' (fun _ => le_rfl)
  have hsum : L<∑ i : Fin (n+1), w i.succ := by
    rw [Fin.sum_univ_succ]
    simpa only [w,Fin.cons_succ,Fin.cons_zero,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,add_comm β] using hlim
  let bound (l r : Fin (n+1)→I) (x y : I) (ε : ℝ) := valid l r x y →
    ∀ t≥a, (∀ i, latticeClose (t*(E (l i)-E (r i))/(2*π)) (K*ε)) →
      latticeClose (t*(E x-E y)/(2*π)) (K*ε^β) → L<log t/log (1/ε)
  have fixed (l r : Fin (n+1)→I) (x y : I) : ∀ᶠ ε in 𝓝[>] (0:ℝ), bound l r x y ε := by
    by_cases h : valid l r x y
    · let A := joinedRows l r x y
      let g := fun i => action (A i) E
      obtain ⟨hg,hy⟩ := hh k (n+1) A (joined_balanced l r x y) (joined_independent l r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
      have hwtime := weighted_gap_floor (Nat.succ_pos n) g hg hy w hw hmax ha hK hL hsum
      filter_upwards [hwtime] with ε ht _
      intro t hat hf he
      apply ht t hat
      refine Fin.cases ?_ (Fin.cases ?_ (fun i => ?_))
      · simpa only [g,A,joinedRows,w,Fin.cons_zero,edge_action,gapTurn,rpow_one] using hf 0
      · simpa only [g,A,joinedRows,w,Fin.cons_zero,Fin.cons_succ,edge_action,gapTurn] using he
      · simpa only [g,A,joinedRows,w,Fin.cons_succ,edge_action,gapTurn,rpow_one] using hf i.succ
    · exact .of_forall fun _ hv => (h hv).elim
  filter_upwards [eventually_all.mpr fun l => eventually_all.mpr fun r =>
    eventually_all.mpr fun x => eventually_all.mpr (fixed l r x)] with ε hall
  exact fun l r x y hi hd hxy hx hy => hall l r x y ⟨hi,hd,hxy,hx,hy⟩

#print axioms gaussian_joined_gap_floor
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
