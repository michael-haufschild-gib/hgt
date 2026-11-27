import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Sharp.Polynomial

/-! # Positive weights with a prescribed first failed reciprocal moment -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Sharp

open Polynomial Finset

variable {n : ℕ}

private def scale (i : Fin n) : ℝ := (n : ℝ)+1+(i.val : ℝ)
private def base (n : ℕ) (i : Fin n) := scale i / scale i.rev

private theorem positive_scale (i : Fin n) : 0<scale i := by unfold scale; positivity

private theorem scale_mono : StrictMono (scale (n := n)) := by
  intro i j hij
  have h : (i.val : ℝ)<(j.val : ℝ) := Nat.cast_lt.mpr (show i.val<j.val from hij)
  unfold scale
  linarith only [h]

private theorem base_mono : StrictMono (base n) := by
  intro i j hij
  calc base n i < scale j / scale i.rev :=
         (div_lt_div_iff_of_pos_right (positive_scale _)).mpr (scale_mono hij)
       _ ≤ base n j := div_le_div_of_nonneg_left (positive_scale j).le (positive_scale _)
         (scale_mono (Fin.rev_lt_rev.mpr hij)).le

private theorem base_inside (i : Fin n) : 0<base n i ∧ base n i<2 := by
  refine ⟨div_pos (positive_scale _) (positive_scale _),(div_lt_iff₀ (positive_scale _)).mpr ?_⟩
  have small : (i.val : ℝ)<n := Nat.cast_lt.mpr i.isLt
  have nonneg : (0 : ℝ) ≤ i.rev.val := Nat.cast_nonneg _
  unfold scale
  linarith only [small,nonneg]

private theorem base_product (n : ℕ) : ∏ i, base n i=1 := by
  have remap := Equiv.prod_comp Fin.revPerm (scale (n := n))
  change (∏ i : Fin n, scale i.rev) = _ at remap
  simp only [base,prod_div_distrib,remap,div_self (prod_pos (fun i _ => positive_scale i)).ne']

private theorem base_matches (n : ℕ) : Matches (base n) (fun i => (base n i)⁻¹) := by
  refine ⟨Fin.revPerm,fun i => ?_⟩
  change scale i / scale i.rev = (scale i.rev / scale i.rev.rev)⁻¹
  rw [Fin.rev_rev,inv_div]

private theorem agrees_iff_coeff (u : Fin n → ℝ) (ht : ∏ i, u i=1) {k : ℕ} (hk : k ≤ n) :
    Agrees u (fun i => (u i)⁻¹) k ↔ ∀ j ≤ k, (plusPoly u).coeff j=(plusPoly u).coeff (n-j) := by
  have size : k ≤ Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using hk
  rw [reciprocal_agrees_iff u ht size]
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  rw [Fintype.card_fin,coeff_plus u (hj.trans hk),coeff_plus u (Nat.sub_le _ _),Nat.sub_sub_self (hj.trans hk)]
  exact eq_comm

private theorem mirrored (n : ℕ) {j : ℕ} (hj : j ≤ n) :
    (plusPoly (base n)).coeff j = (plusPoly (base n)).coeff (n-j) :=
  (agrees_iff_coeff _ (base_product n) (le_refl n)).mp (fun k _ _ => moment_congr (base_matches n) k) j hj

/-- Every moment order below half the dimension can be the first one that distinguishes
a list of positive product-one weights from its reciprocal. -/
theorem exists_first_failure (n r : ℕ) (hr : 1 ≤ r) (hrange : r ≤ cutoff n) :
    ∃ u : Fin n → ℝ, (∀ i, 0<u i) ∧ (∏ i, u i)=1 ∧ Agrees u (fun i => (u i)⁻¹) (r-1) ∧
      moment u r ≠ moment (fun i => (u i)⁻¹) r := by
  have hlt : 2*r<n := by unfold cutoff at hrange; omega
  obtain ⟨u,a,ha,hp,he⟩ := perturb_coefficient (base n) base_mono.injective base_inside (r := r) (by omega)
  have coeff (j : ℕ) : (plusPoly u).coeff j = (plusPoly (base n)).coeff j + (if r=j then a else 0) := by
    rw [he,coeff_add,coeff_monomial]
  have prod_one : ∏ i, u i=1 := by
    rw [← constant_plus,coeff,if_neg (by omega : r ≠ 0),add_zero,constant_plus,base_product]
  have low : Agrees u (fun i => (u i)⁻¹) (r-1) := by
    apply (agrees_iff_coeff u prod_one (by omega : r-1 ≤ n)).mpr
    intro j hj
    rw [coeff,coeff,if_neg (by omega : r≠j),if_neg (by omega : r≠n-j),add_zero,add_zero]
    exact mirrored n (by omega)
  refine ⟨u,hp,prod_one,low,fun heq => ?_⟩
  have all : Agrees u (fun i => (u i)⁻¹) r := by
    intro j hj hjr
    rcases hjr.lt_or_eq with hj' | rfl
    · exact low j hj (by omega)
    · exact heq
  have fails := (agrees_iff_coeff u prod_one (by omega : r ≤ n)).mp all r le_rfl
  rw [coeff,coeff,if_pos rfl,if_neg (by omega : r≠n-r),add_zero,mirrored n (by omega : r ≤ n)] at fails
  linarith only [ha,fails]

#print axioms exists_first_failure

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Sharp
