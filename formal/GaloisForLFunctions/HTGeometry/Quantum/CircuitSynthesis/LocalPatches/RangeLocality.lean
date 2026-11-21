import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.InteractionPicture

/-! # Finite propagation of nested commutators on a path -/
open NormedSpace Finset
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- Sum of the interactions at sites in the half-open interval [l,r). -/
def intervalSum (X : ℕ → A) (l r : ℕ) := ∑ j ∈ Ico l r, X j

private def jet (X : ℕ → A) (i : ℕ) : ℕ → A
  | 0 => X i
  | k+1 => bracketStep (intervalSum X (i-(k+1)) i) (jet X i k)

/-- The k-th commutator uses only sites i−k through i. -/
private theorem jet_commute (X : ℕ → A) (i k : ℕ) (y : A)
    (h : ∀ j, i-k ≤ j → j ≤ i → Commute y (X j)) : Commute y (jet X i k) := by
  induction k with
  | zero => exact h i (by omega) le_rfl
  | succ k ih =>
    have he := ih (fun j hl hu => h j (by omega) hu)
    have hs : Commute y (intervalSum X (i-(k+1)) i) := Commute.sum_right _ _ _ (fun j hj =>
      h j (mem_Ico.mp hj).1 (mem_Ico.mp hj).2.le)
    exact (he.mul_right hs).sub_right (hs.mul_right he)

private theorem next_jet (X : ℕ → A) (hX : ∀ q j, q+1 < j → Commute (X q) (X j))
    (i k l : ℕ) (hl : l ≤ i-(k+1)) :
    bracketStep (intervalSum X l i) (jet X i k) = jet X i (k+1) := by
  let m := i-(k+1)
  have hc : Commute (jet X i k) (intervalSum X l m) := Commute.sum_right _ _ _ (fun q hq =>
    (jet_commute X i k (X q) (fun j hj _ => hX q j (by
      have hh := (mem_Ico.mp hq).2
      dsimp [m] at hh
      omega))).symm)
  have split : intervalSum X l i = intervalSum X l m + intervalSum X m i :=
    (sum_Ico_consecutive X hl (Nat.sub_le ..)).symm
  change bracketStep (intervalSum X l i) _ = bracketStep (intervalSum X m i) _
  rw [split]
  dsimp only [bracketStep]
  rw [mul_add,add_mul,hc.eq]
  abel

private theorem iter_patch_eq (X : ℕ → A) (hX : ∀ q j, q+1 < j → Commute (X q) (X j))
    (i p k : ℕ) (hk : k ≤ p) :
    (bracketStep (intervalSum X (i-p) i))^[k] (X i) = jet X i k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih (by omega),next_jet X hX i k _ (by omega)]

private theorem iter_norm (a x : A) (p : ℕ) :
    ‖(bracketStep a)^[p] x‖ ≤ (2*‖a‖)^p*‖x‖ := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply']
    let y := (bracketStep a)^[p] x
    calc
      ‖bracketStep a y‖ ≤ ‖y‖*‖a‖+‖a‖*‖y‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ = (2*‖a‖)*‖y‖ := by ring
      _ ≤ (2*‖a‖)*((2*‖a‖)^p*‖x‖) := mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [pow_succ]; ring

/-- Cutting off the preceding prefix p sites from the inserted interaction
gives an error bounded solely by that patch and the inserted term. -/
theorem path_patch_error (X : ℕ → A) (hskew : ∀ j, X j ∈ skewAdjoint A)
    (hX : ∀ q j, q+1 < j → Commute (X q) (X j)) (i p : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    let a := intervalSum X 0 i
    let b := intervalSum X (i-p) i
    ‖exp (t • a)*exp (t • (-b))*exp (t • (b+X i))-exp (t • (a+X i))‖ ≤
      2*(2*‖b‖)^p*‖X i‖*t^(p+1) := by
  intro a b
  have hm l : intervalSum X l i ∈ skewAdjoint A :=
    (skewAdjoint A).sum_mem fun j _ => hskew j
  have hsame (j : ℕ) (hj : j < p) :
      bracketStep a ((bracketStep b)^[j] (X i)) = bracketStep b ((bracketStep b)^[j] (X i)) := by
    rw [show (bracketStep b)^[j] (X i) = jet X i j from iter_patch_eq X hX _ _ _ hj.le]
    exact (next_jet X hX i j 0 (Nat.zero_le _)).trans (next_jet X hX i j _ (by omega)).symm
  have he := insertion_error a b (X i) (hm _) (hm _) (hskew i) p hsame t ht
  calc
    _ ≤ _ := he
    _ ≤ (2*((2*‖b‖)^p*‖X i‖))*t^(p+1) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (iter_norm b _ p) (by norm_num)) (pow_nonneg ht _)
    _ = _ := by ring

#print axioms path_patch_error
end
end GaloisForLFunctions.HTGeometry.LocalPatches
