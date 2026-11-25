import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.FinitePrefixes.BoxDifferences
import Mathlib.Order.Fin.Basic

/-! # Weighted return of all successive energy gaps -/

open Finset
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence
noncomputable section

/-- Accumulate displacements along the ordered list of levels. -/
def primitive {d : ℕ} (u : Fin d → ℝ) : Fin (d+1) → ℝ :=
  Fin.induction 0 fun i z => z+u i

/-- A bound on each successive displacement controls the displacement
between every pair, with constant measured in energy rather than index. -/
theorem primitive_lipschitz {d : ℕ} (w : Fin (d+1) → ℝ) (u : Fin d → ℝ) (b : ℝ)
    (hb : ∀ i, |u i|≤b*(w i.succ-w i.castSucc)) {i j : Fin (d+1)} (hij : i≤j) :
    |primitive u j-primitive u i|≤b*(w j-w i) := by
  have up : Monotone fun k => b*w k+primitive u k := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    rw [show primitive u k.succ=primitive u k.castSucc+u k from Fin.induction_succ ..]
    linarith only [(abs_le.mp (hb k)).1]
  have dn : Monotone fun k => b*w k-primitive u k := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    rw [show primitive u k.succ=primitive u k.castSucc+u k from Fin.induction_succ ..]
    linarith only [(abs_le.mp (hb k)).2]
  exact abs_le.mpr ⟨by linarith only [up hij],by linarith only [dn hij]⟩

/-- One chosen gap is synchronized exactly. Each remaining gap has
its own subdivision count, so the deadline omits the chosen factor. -/
theorem synchronize_gaps {d : ℕ} (g : Fin d → ℝ) (p : Fin d) (hp : 0<g p)
    (Q : {k : Fin d // k≠p} → ℕ) (hQ : ∀ k, 0<Q k) :
    ∃ (q : ℕ) (m : Fin d → ℤ), 0<q ∧ q≤∏ k, Q k ∧
      (q:ℝ)/g p*g p=(m p:ℝ) ∧ ∀ k : {k : Fin d // k≠p}, |(q:ℝ)/g p*g k-m k|<1/Q k := by
  classical
  let β (k : {k : Fin d // k≠p}) := g k/g p
  obtain ⟨S,hs,hall⟩ := FinitePrefixes.many_box_returns β Q hQ 1
  obtain ⟨q,hq,hpos⟩ : ∃ q∈S, 0<q := by
    by_contra! h
    have hh := Finset.card_le_card (show S⊆{0} from fun n hn => Finset.mem_singleton.mpr (Nat.eq_zero_of_le_zero (h n hn)))
    rw [card_singleton] at hh
    omega
  obtain ⟨hqQ,hd⟩ := hall q hq
  choose m hm using hd
  let M (i : Fin d) : ℤ := if hi : i=p then (q:ℤ) else m ⟨i,hi⟩
  refine ⟨q,M,hpos,by simpa only [mul_one] using hqQ,?_,?_⟩
  · simp only [M,dif_pos rfl,Int.cast_natCast,div_mul_cancel₀ _ hp.ne']
  · intro k
    rw [show M k=m k from dif_neg k.property,show (q:ℝ)/g p*g k=q*β k by dsimp only [β]; ring]
    exact hm k

#print axioms primitive_lipschitz
#print axioms synchronize_gaps
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence
