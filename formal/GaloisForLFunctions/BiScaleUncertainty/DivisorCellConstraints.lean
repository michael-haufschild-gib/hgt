import GaloisForLFunctions.BiScaleUncertainty.CellPrefixHilbert
import GaloisForLFunctions.BiScaleUncertainty.DivisorGridRunGeometry

/-!
# Closed cell constraints and finite-component conservation

Zero cumulative currents at inactive nodes define a complete Hilbert domain.
They are equivalent to zero total current on every finite active-edge component.
An admissible current constant along all active edges must vanish.
-/

noncomputable section
open Set
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

def divisorCellSpace (d : ℕ) (D : Set ℕ) : Submodule ℝ TraceData where
  carrier := {w | ∀ k, ¬ divisorGridActive d D k → cellPrefixL (k+1) w = 0}
  zero_mem' := by intro k _; exact map_zero _
  add_mem' := by
    intro w z hw hz k hk
    rw [map_add, hw k hk, hz k hk, add_zero]
  smul_mem' := by
    intro c w hw k hk
    rw [map_smul, hw k hk, smul_zero]

theorem mem_divisorCellSpace_iff (d : ℕ) (D : Set ℕ) (w : TraceData) :
    w ∈ divisorCellSpace d D ↔
      ∀ k, ¬ divisorGridActive d D k → cellPrefixL (k+1) w = 0 := Iff.rfl

theorem isClosed_divisorCellSpace (d : ℕ) (D : Set ℕ) :
    IsClosed (divisorCellSpace d D : Set TraceData) := by
  have he : (divisorCellSpace d D : Set TraceData) =
      ⋂ k, ⋂ (_ : ¬ divisorGridActive d D k), {w | cellPrefixL (k+1) w = 0} := by
    ext w
    simp only [mem_iInter, mem_setOf_eq]
    rfl
  rw [he]
  exact isClosed_iInter fun k => isClosed_iInter fun _ =>
    isClosed_eq (cellPrefixL (k+1)).continuous continuous_const

instance divisorCellSpace_completeSpace (d : ℕ) (D : Set ℕ) :
    CompleteSpace (divisorCellSpace d D) :=
  (isClosed_divisorCellSpace d D).completeSpace_coe

theorem divisorGradient_mem (d : ℕ) (D : Set ℕ) (v : DivisorGridData d D) :
    traceGradient v.1 ∈ divisorCellSpace d D := by
  intro k hk
  rw [cellPrefixL_gradient, divisorGridData_off d D v hk]

theorem not_divisorGridActive_zero (d : ℕ) (D : Set ℕ) :
    ¬ divisorGridActive d D 0 := by
  rintro ⟨e, _, he⟩
  have := Nat.le_of_dvd (by omega : 0 < 0+1) he
  omega

theorem mem_divisorCellSpace_univ (d : ℕ) (w : TraceData) :
    w ∈ divisorCellSpace d Set.univ ↔ w 0 = 0 := by
  constructor
  · intro h
    have hz := h 0 (not_divisorGridActive_zero d Set.univ)
    simpa only [cellPrefixL_succ, cellPrefixL_zero, zero_add] using hz
  · intro hw k hk
    have hk0 : k = 0 := by
      by_contra hn
      exact hk (divisorGrid_univ_active d k (by omega))
    subst k
    simp only [cellPrefixL_succ, cellPrefixL_zero, hw, add_zero]

/-- Half-open cell interval with both external edges absent and all internal edges active. -/
def DivisorFiniteComponent (d : ℕ) (D : Set ℕ) (a b : ℕ) : Prop :=
  a < b ∧ (a = 0 ∨ ¬ divisorGridActive d D (a-1)) ∧
    ¬ divisorGridActive d D (b-1) ∧
    ∀ k, a ≤ k → k+1 < b → divisorGridActive d D k

def divisorCellStart (d : ℕ) (D : Set ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => if divisorGridActive d D k then divisorCellStart d D k else k+1

theorem divisorCellStart_le (d : ℕ) (D : Set ℕ) (k : ℕ) : divisorCellStart d D k ≤ k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => simp only [divisorCellStart]; split_ifs <;> omega

theorem divisorCellStart_left (d : ℕ) (D : Set ℕ) (k : ℕ) :
    divisorCellStart d D k = 0 ∨ ¬ divisorGridActive d D (divisorCellStart d D k - 1) := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
      simp only [divisorCellStart]
      split_ifs with hk
      · exact ih
      · exact Or.inr (by simpa only [Nat.add_sub_cancel] using hk)

theorem divisorCellStart_internal (d : ℕ) (D : Set ℕ) (k i : ℕ)
    (hi : divisorCellStart d D k ≤ i) (hik : i < k) : divisorGridActive d D i := by
  induction k with
  | zero => omega
  | succ k ih =>
      simp only [divisorCellStart] at hi
      split_ifs at hi with hk
      · by_cases he : i = k
        · simpa only [he] using hk
        · exact ih hi (by omega)
      · omega

theorem divisorCellStart_component (d : ℕ) (D : Set ℕ) (k : ℕ)
    (hk : ¬ divisorGridActive d D k) :
    DivisorFiniteComponent d D (divisorCellStart d D k) (k+1) := by
  refine ⟨by have := divisorCellStart_le d D k; omega,
    divisorCellStart_left d D k, by simpa only [Nat.add_sub_cancel] using hk, ?_⟩
  intro i hi hik
  exact divisorCellStart_internal d D k i hi (by omega)

theorem divisorCell_component_sum_zero (d : ℕ) (D : Set ℕ) (w : divisorCellSpace d D)
    (a b : ℕ) (h : DivisorFiniteComponent d D a b) : ∑ j ∈ Finset.Ico a b, w.1 j = 0 := by
  rw [cellPrefixL_interval a b (Nat.le_of_lt h.1)]
  have hb : cellPrefixL b w.1 = 0 := by
    have hz := w.2 (b-1) h.2.2.1
    have hbpos : 1 ≤ b := by have := h.1; omega
    simpa only [Nat.sub_add_cancel hbpos] using hz
  have ha : cellPrefixL a w.1 = 0 := by
    rcases h.2.1 with ha | ha
    · rw [ha, cellPrefixL_zero]
    · by_cases ha0 : a = 0
      · rw [ha0, cellPrefixL_zero]
      · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ a)] using w.2 (a-1) ha
  rw [hb, ha, sub_self]

theorem mem_divisorCellSpace_iff_components (d : ℕ) (D : Set ℕ) (w : TraceData) :
    w ∈ divisorCellSpace d D ↔
      ∀ a b, DivisorFiniteComponent d D a b → ∑ j ∈ Finset.Ico a b, w j = 0 := by
  constructor
  · intro hw
    exact divisorCell_component_sum_zero d D ⟨w, hw⟩
  · intro h k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        let a := divisorCellStart d D k
        have hak : a ≤ k := divisorCellStart_le d D k
        have hs := h a (k+1) (divisorCellStart_component d D k hk)
        rw [cellPrefixL_interval a (k+1) (by omega)] at hs
        have ha : cellPrefixL a w = 0 := by
          by_cases ha0 : a = 0
          · rw [ha0, cellPrefixL_zero]
          · have hp := (divisorCellStart_left d D k).resolve_left ha0
            have hz := ih (a-1) (by omega) hp
            simpa only [Nat.sub_add_cancel (by omega : 1 ≤ a)] using hz
        linarith only [hs, ha]

theorem divisorCell_eq_zero_of_adjacent (d : ℕ) (D : Set ℕ) (w : TraceData)
    (hw : w ∈ divisorCellSpace d D)
    (ha : ∀ k, divisorGridActive d D k → w k = w (k+1)) : w = 0 := by
  apply lp.ext
  funext j
  change w j = 0
  induction j using Nat.strong_induction_on with
  | h j ih =>
      by_cases hg : ∃ n, ¬ divisorGridActive d D (j+n)
      · let n := Nat.find hg
        have hn : ¬ divisorGridActive d D (j+n) := Nat.find_spec hg
        have hc (i : ℕ) (hi : i ≤ n) : w (j+i) = w j := by
          induction i with
          | zero => simp
          | succ i hii =>
              have hp : divisorGridActive d D (j+i) := by
                by_contra hp
                have := Nat.find_min' hg hp
                omega
              rw [show j+(i+1) = (j+i)+1 by omega, ← ha (j+i) hp]
              exact hii (by omega)
        have hbefore : ∑ i ∈ Finset.range j, w i = 0 :=
          Finset.sum_eq_zero (fun i hi => ih i (Finset.mem_range.mp hi))
        have hsum : (∑ i ∈ Finset.range (n+1), w (j+i)) = ((n+1 : ℕ) : ℝ)*w j := by
          calc
            _ = ∑ _i ∈ Finset.range (n+1), w j :=
              Finset.sum_congr rfl (fun i hi => hc i (by have := Finset.mem_range.mp hi; omega))
            _ = _ := by simp
        have hz := hw (j+n) hn
        rw [cellPrefixL_apply, show j+n+1 = j+(n+1) by omega,
          Finset.sum_range_add, hbefore, hsum, zero_add] at hz
        exact (mul_eq_zero.mp hz).resolve_left (by positivity)
      · have hc (i : ℕ) : w (j+i) = w j := by
          induction i with
          | zero => simp
          | succ i hii =>
              have hp : divisorGridActive d D (j+i) := by
                by_contra hp
                exact hg ⟨i, hp⟩
              rw [show j+(i+1) = (j+i)+1 by omega, ← ha (j+i) hp, hii]
        exact traceData_tail_constant_zero w j (w j) hc

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
