import GaloisForLFunctions.HTGeometry.KleinbockMargulis.SmoothGoodOne

/-!
# Absolute sublevel bounds from a finite derivative

A real function with its derivative of order `k` bounded away from zero has at most `2k`
crossings of the two sublevel boundaries. The interval-length estimate for a derivative chain
therefore gives an absolute sublevel-measure bound, independent of the ambient interval length.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

open HTGeometry.KleinbockMargulis

/-- Constant in the absolute sublevel estimate for a derivative of order `k`. -/
def derivativeSublevelConstant (k : ℕ) (A : ℝ) : ℝ :=
  (2 * k + 1) * (k + 2) * (((k + 1).factorial : ℝ) / A) ^ ((k : ℝ)⁻¹)

theorem derivativeSublevelConstant_nonneg (k : ℕ) {A : ℝ} (hA : 0 < A) :
    0 ≤ derivativeSublevelConstant k A := by
  unfold derivativeSublevelConstant
  positivity

/-- A nonvanishing derivative controls the total measure of small values, without requiring
a chosen nonzero value of the original function. -/
theorem volume_sublevel_le_of_derivative_lower {F : ℕ → ℝ → ℝ} {k : ℕ}
    (hk : 1 ≤ k) {a b A : ℝ} (hA : 0 < A)
    (hF : IsDerivChain k F (Ioo a b))
    (hlow : ∀ x ∈ Ioo a b, A ≤ |F k x|) {ε : ℝ} (hε : 0 < ε) :
    volume {x ∈ Ioo a b | |F 0 x| < ε} ≤
      ENNReal.ofReal (derivativeSublevelConstant k A * ε ^ ((k : ℝ)⁻¹)) := by
  classical
  let S : Set ℝ := {x ∈ Ioo a b | |F 0 x| < ε}
  have hne : ∀ x ∈ Ioo a b, F k x ≠ 0 := by
    intro x hx hz
    have := hlow x hx
    rw [hz, abs_zero] at this
    linarith
  have hfin (c : ℝ) : {x | x ∈ Ioo a b ∧ F 0 x = c}.Finite :=
    finite_level_set ordConnected_Ioo hF hk hne c
  let Z := (hfin ε).toFinset ∪ (hfin (-ε)).toFinset
  have hcard : Z.card ≤ 2 * k := by
    have h1 : (hfin ε).toFinset.card ≤ k :=
      card_le_of_chain_ne_zero ordConnected_Ioo hF hk hne ε _
        (fun x hx => (hfin ε).mem_toFinset.mp hx)
    have h2 : (hfin (-ε)).toFinset.card ≤ k :=
      card_le_of_chain_ne_zero ordConnected_Ioo hF hk hne (-ε) _
        (fun x hx => (hfin (-ε)).mem_toFinset.mp hx)
    exact (Finset.card_union_le _ _).trans (by omega)
  have hZmem : ∀ x ∈ Z, x ∈ Ioo a b ∧ |F 0 x| = ε := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have h : x ∈ Ioo a b ∧ F 0 x = ε := (hfin ε).mem_toFinset.mp hx
      exact ⟨h.1, by rw [h.2, abs_of_pos hε]⟩
    · have h : x ∈ Ioo a b ∧ F 0 x = -ε := (hfin (-ε)).mem_toFinset.mp hx
      exact ⟨h.1, by rw [h.2, abs_neg, abs_of_pos hε]⟩
  have hconv : ∀ x ∈ S, ∀ y ∈ S, x < y →
      (∀ w ∈ Ioo x y, w ∉ Z) → Ioo x y ⊆ S := by
    intro x hx y hy _ hno w hw
    have hwab : w ∈ Ioo a b := ⟨hx.1.1.trans hw.1, hw.2.trans hy.1.2⟩
    refine ⟨hwab, ?_⟩
    by_contra hc
    have hcont : ContinuousOn (fun t => |F 0 t|) (Icc x w) :=
      (hF.continuousOn 0 (by omega) (ordConnected_Ioo.out hx.1 hwab)).abs
    obtain ⟨v, hv, heq⟩ := intermediate_value_Icc hw.1.le hcont
      (show ε ∈ Icc (|F 0 x|) (|F 0 w|) from ⟨hx.2.le, le_of_not_gt hc⟩)
    have hvx : x < v := lt_of_le_of_ne hv.1 (by
      intro h; subst v; exact hx.2.ne heq)
    have hvy : v < y := hv.2.trans_lt hw.2
    have hvab : v ∈ Ioo a b := ⟨hx.1.1.trans hvx, hvy.trans hy.1.2⟩
    apply hno v ⟨hvx, hvy⟩
    rcases (abs_eq hε.le).mp heq with h | h
    · exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr ⟨hvab, h⟩)
    · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr ⟨hvab, h⟩)
  let L : ℝ := ((k : ℝ) + 2) * (((k + 1).factorial : ℝ) * ε / A) ^ ((k : ℝ)⁻¹)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hlen : ∀ u v : ℝ, Ioo u v ⊆ S → v - u ≤ L := by
    intro u v huv
    by_cases hlt : u < v
    · exact interval_length_le ordConnected_Ioo hF hk hA hlow hε hlt
        (fun x hx => (huv hx).1) (fun x hx => (huv hx).2)
    · exact (sub_nonpos.mpr (le_of_not_gt hlt)).trans hL
  have hbound := volume_le_of_cuts (2 * k) a b Z hcard (fun x hx => (hZmem x hx).1)
    S L hL (fun _ hx => hx.1)
    (fun x hx hxs => hxs.2.ne (hZmem x hx).2) hconv hlen
  have hcr : (Z.card : ℝ) + 1 ≤ 2 * (k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hcard 1
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  calc ((Z.card : ℝ) + 1) * L ≤ (2 * (k : ℝ) + 1) * L :=
        mul_le_mul_of_nonneg_right hcr hL
    _ = derivativeSublevelConstant k A * ε ^ ((k : ℝ)⁻¹) := by
        dsimp [L, derivativeSublevelConstant]
        rw [show ((k + 1).factorial : ℝ) * ε / A =
          (((k + 1).factorial : ℝ) / A) * ε by ring,
          Real.mul_rpow (by positivity) hε.le]
        ring

#print axioms volume_sublevel_le_of_derivative_lower

end GaloisForLFunctions.InfiniteRankWeilTheory
