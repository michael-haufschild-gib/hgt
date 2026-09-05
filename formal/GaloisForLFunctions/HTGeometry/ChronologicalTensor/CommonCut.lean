import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Padding

/-!
# Concentrating outer padding at a common chronological cut

Every generated outer window contains the distinguished zero coordinate.
Concentrating the entire padding variation there, with sign aligned to the
inner displacement, preserves cost and simultaneously maximizes all absolute
outer factors. This includes the padding-window geometry of nested outer chords.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def anchoredWindow {n : ℕ} (W : Finset (Fin n)) : Finset (Fin (n+1)) :=
  insert 0 (W.map (Fin.succEmb n))

def alignedPadding {n : ℕ} (S : ℝ) (q : Fin n → ℝ) : ℝ :=
  if 0 ≤ S then variation q else -variation q

def outerResponse {n k : ℕ} (W : Fin k → Finset (Fin n))
    (S R : ℝ) (q : Fin (n+1) → ℝ) : ℝ :=
  R * ∏ j, (S+windowValue (anchoredWindow (W j)) q)

theorem anchoredWindow_value_cons {n : ℕ} (W : Finset (Fin n)) (p : ℝ) (q : Fin n → ℝ) :
    windowValue (anchoredWindow W) (Fin.cons p q) = p+windowValue W q := by
  have hn : (0 : Fin (n+1)) ∉ W.map (Fin.succEmb n) := by simp
  simp only [anchoredWindow,windowValue,Finset.sum_insert hn,Fin.cons_zero,Finset.sum_map,
    Fin.coe_succEmb,Fin.cons_succ]

theorem alignedPadding_data {n : ℕ} (S : ℝ) (q : Fin n → ℝ) :
    |alignedPadding S q| = variation q ∧
      |S+alignedPadding S q| = |S|+variation q := by
  have hV := variation_nonneg q
  by_cases hS : 0 ≤ S
  · simp only [alignedPadding,if_pos hS,abs_of_nonneg hV,abs_of_nonneg hS,
      abs_of_nonneg (add_nonneg hS hV),and_self]
  · have hs : S ≤ 0 := le_of_not_ge hS
    simp only [alignedPadding,if_neg hS,abs_neg,abs_of_nonneg hV,abs_of_nonpos hs,
      abs_of_nonpos (show S+-variation q ≤ 0 by linarith only [hs,hV])]
    constructor
    · trivial
    · ring

theorem outerResponse_bound {n k : ℕ} (W : Fin k → Finset (Fin n))
    (S R : ℝ) (q : Fin (n+1) → ℝ) :
    |outerResponse W S R q| ≤ |R| * (|S|+variation q)^k := by
  have hp := Finset.prod_le_prod
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => abs_nonneg (S+windowValue (anchoredWindow (W j)) q))
    (fun j _ => (abs_add_le S _).trans (add_le_add le_rfl (windowValue_bound (anchoredWindow (W j)) q)))
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hp
  rw [outerResponse,abs_mul,Finset.abs_prod]
  exact mul_le_mul_of_nonneg_left hp (abs_nonneg R)

theorem outerResponse_collapsed {n k : ℕ} (W : Fin k → Finset (Fin n)) (S R p : ℝ) :
    outerResponse W S R (Fin.cons p (fun _ => 0)) = R*(S+p)^k := by
  simp only [outerResponse,anchoredWindow_value_cons]
  simp only [windowValue,Finset.sum_const_zero,add_zero,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem commonCut_collapse_cost {n : ℕ} (S : ℝ) (q : Fin (n+1) → ℝ) :
    variation (Fin.cons (alignedPadding S q) (fun _ : Fin n => 0)) = variation q := by
  rw [variation_cons,(alignedPadding_data S q).1]
  simp [variation]

theorem commonCut_collapse_dominates {n k : ℕ} (W : Fin k → Finset (Fin n))
    (S R : ℝ) (q : Fin (n+1) → ℝ) :
    |outerResponse W S R q| ≤
      |outerResponse W S R (Fin.cons (alignedPadding S q) (fun _ => 0))| := by
  rw [outerResponse_collapsed,abs_mul,abs_pow,(alignedPadding_data S q).2]
  exact outerResponse_bound W S R q

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
