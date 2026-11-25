import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.FinitePrefixes.BoxDifferences
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.ScalarFace

/-! # Backward returns with the two closing phases fixed -/

open Finset Set Real
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap
open EmptyVisitFlux
noncomputable section
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Levels strictly between the two arc endpoints. -/
abbrev InteriorLevel (i j : I) := {k : I // k≠i ∧ k≠j}

private theorem coe_integer (m : ℤ) : ((m:ℝ):UnitAddCircle)=0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨m,by simp⟩

omit [Fintype I] [DecidableEq I] in
private theorem subtract_time (w : I → ℝ) (i k : I) (v t : ℝ) :
    flow w (v-t) k-flow w (v-t) i =
      flow w v k-flow w v i-((t*(w k-w i):ℝ):UnitAddCircle) := by
  change (((v-t)*w k:ℝ):UnitAddCircle)-(((v-t)*w i:ℝ):UnitAddCircle) = _
  simp only [flow,←AddCircle.coe_sub]
  congr 1
  ring

/-- A backward shift by a positive whole number of closing-gap
periods fixes both endpoints and keeps all other levels in the arc.
Each factor in the deadline is set by that level's own clearance. -/
theorem previous_contact (w : I → ℝ) {r v : ℝ} {i j : I} (hr : 0<r) (hf : inwardFace w r v i j)
    (y : InteriorLevel i j → ℝ) (hy : ∀ k, (y k:UnitAddCircle)=flow w v k.val-flow w v i)
    (Q : InteriorLevel i j → ℕ) (hQ : ∀ k, 0<Q k)
    (hm : ∀ k, 1/(Q k:ℝ) ≤ min (y k) (r-y k)) :
    ∃ q : ℕ, 0<q ∧ q ≤ (∏ k, Q k) ∧ flow w (v-(q:ℝ)/(w i-w j))∈anchoredUnitArc i r := by
  classical
  let g := w i-w j
  have hg : 0<g := sub_pos.mpr hf.1
  let β (k : InteriorLevel i j) := (w k.val-w i)/g
  obtain ⟨S,hs,hall⟩ := FinitePrefixes.many_box_returns β Q hQ 1
  obtain ⟨q,hq,hpos⟩ : ∃ q∈S, 0<q := by
    by_contra! h
    have hsub : S⊆({0} : Finset ℕ) := fun n hn => Finset.mem_singleton.mpr (Nat.eq_zero_of_le_zero (h n hn))
    have hh := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hh
    omega
  obtain ⟨hb,hd⟩ := hall q hq
  refine ⟨q,hpos,by simpa only [mul_one] using hb,?_⟩
  intro k hki
  rw [subtract_time]
  by_cases hkj : k=j
  · subst k
    have ht : (q:ℝ)/(w i-w j)*(w j-w i)=((-q:ℤ):ℝ) := by
      push_cast
      rw [show w j-w i= -(w i-w j) by ring,mul_neg,div_mul_cancel₀ _ hg.ne']
    rw [hf.2.1,ht,coe_integer,sub_zero]
    exact ⟨r,⟨hr.le,le_rfl⟩,rfl⟩
  · let l : InteriorLevel i j := ⟨k,hki,hkj⟩
    obtain ⟨m,hdm⟩ := hd l
    obtain ⟨hlo,hhi⟩ := abs_lt.mp hdm
    have hml := (le_min_iff.mp (hm l)).1
    have hmr := (le_min_iff.mp (hm l)).2
    refine ⟨y l-((q:ℝ)*β l-m),⟨by linarith only [hhi,hml],by linarith only [hlo,hmr]⟩,?_⟩
    have ht : (q:ℝ)/(w i-w j)*(w k-w i)=(q:ℝ)*β l := by dsimp [β,l,g]; ring
    rw [ht,AddCircle.coe_sub,AddCircle.coe_sub,coe_integer,sub_zero,hy]

#print axioms previous_contact
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap
