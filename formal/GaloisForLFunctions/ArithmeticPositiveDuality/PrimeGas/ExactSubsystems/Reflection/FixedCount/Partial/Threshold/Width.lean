import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Threshold.Outgoing

/-! # Absolute damping from the width of a bounded prime spectrum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold

open Peak.Ranks.Capped

variable {S : Finset Nat.Primes} (c : S → ℕ) (m : ℕ)

def width := if m ≤ capacity c then -baseline reversePrice c m-baseline price c m else 0

theorem energy_eq_iff {x y : State c m} : energy (level x) = energy (level y) ↔ x=y := by
  constructor
  · intro h
    have hh := (energy_pair_iff x y x x).mp (by rw [h])
    exact state_ext fun i => Nat.add_left_cancel (hh i)
  · rintro rfl; rfl

theorem edge_maxima (w : State c m) :
    IsGreatest (lowerEdge c m) (width c m) ∧ IsGreatest (upperEdge c m) (width c m) := by
  obtain ⟨g,u,_,_,lo,hi,ext⟩ := anchors w
  have feas := (feasible_iff c m).mp ⟨w⟩
  rw [width,if_pos feas]
  constructor
  · refine ⟨⟨u,?_⟩,?_⟩
    · change energy (level u)-baseline price c m = _
      rw [hi,neg_neg]
    · rintro _ ⟨x,rfl⟩
      change energy (level x)-baseline price c m ≤ _
      linarith only [hi,(ext x).2]
  · refine ⟨⟨g,?_⟩,?_⟩
    · change -energy (level g)-baseline reversePrice c m = _
      linarith only [lo]
    · rintro _ ⟨x,rfl⟩
      change -energy (level x)-baseline reversePrice c m ≤ _
      linarith only [lo,(ext x).1]

theorem width_zero_iff : width c m = 0 ↔ Subsingleton (State c m) := by
  by_cases hn : Nonempty (State c m)
  · obtain ⟨w⟩ := hn
    obtain ⟨g,u,_,_,lo,hi,ext⟩ := anchors w
    rw [width,if_pos ((feasible_iff c m).mp ⟨w⟩),lo,hi,neg_neg,sub_eq_zero]
    constructor
    · intro eq
      exact ⟨fun x y => (energy_eq_iff c m).mp (by linarith only [eq,(ext x).1,(ext x).2,(ext y).1,(ext y).2])⟩
    · intro h
      exact congrArg (fun x : State c m => energy (level x)) (h.elim u g)
  · have hm : ¬m ≤ capacity c := fun h => hn ((feasible_iff c m).mpr h)
    rw [width,if_neg hm]
    exact ⟨fun _ => ⟨fun x _ => (hn ⟨x⟩).elim⟩,fun _ => rfl⟩

theorem thermal_empty (hn : ¬Nonempty (State c m)) (t : ℝ) : thermalLosses c m t = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro _ ⟨x,_⟩
  exact hn ⟨x⟩

private theorem scaled_sup {A : Set ℝ} {d t : ℝ} (h : IsGreatest A d) (ht : 0 ≤ t) :
    sSup (scale t A) = t*d :=
  (show IsGreatest (scale t A) (t*d) from
    ⟨⟨d,h.1,rfl⟩,fun _ ⟨_,hx,he⟩ => he ▸ mul_le_mul_of_nonneg_left (h.2 hx) ht⟩).csSup_eq

theorem max_loss (t : ℝ) : sSup (thermalLosses c m t) = |t| * width c m := by
  by_cases hw : Nonempty (State c m)
  · obtain ⟨w⟩ := hw
    obtain ⟨hl,hu⟩ := edge_maxima c m w
    rcases le_total 0 t with pos | neg
    · rw [(thermal_edges c m w t pos).1,abs_of_nonneg pos,scaled_sup hl pos]
    · have eq := (thermal_edges c m w (-t) (neg_nonneg.mpr neg)).2
      rw [neg_neg] at eq
      rw [eq,abs_of_nonpos neg,scaled_sup hu (neg_nonneg.mpr neg)]
  · rw [thermal_empty c m hw,width,if_neg (fun h => hw ((feasible_iff c m).mpr h)),Real.sSup_empty,mul_zero]

/-- Every sector with two distinct states detects isometric composition by zero maximum loss. -/
theorem zero_max_iff_isometry (hn : Nontrivial (State c m)) (s : ℂ) :
    sSup (outputSpectrum c m s) = 0 ↔ ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  obtain ⟨x,y,hxy⟩ := hn.exists_pair_ne
  have hw : width c m ≠ 0 := fun h => hxy (((width_zero_iff c m).mp h).elim x y)
  rw [spectrum_eq,max_loss,mul_eq_zero,or_iff_left hw,abs_eq_zero,split_isometric_iff]
  constructor <;> intro h <;> linarith only [h]

#print axioms energy_eq_iff
#print axioms edge_maxima
#print axioms width_zero_iff
#print axioms max_loss
#print axioms zero_max_iff_isometry

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold
