import GaloisForLFunctions.HTGeometry.QuantitativeLieProductFormula

/-!
# Lie products controlled by total generator norm

Expanding the product to first order costs at most half the square of
the total integrated norm. A unitary factor preserves each propagated
error, including for arbitrarily long lists.
-/
open NormedSpace
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

local instance : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A

omit [Nontrivial A] in
private theorem list_exp_linear_error (z : List A) (hz : ∀ x ∈ z, x ∈ skewAdjoint A) (t : ℝ) :
    ‖(z.map fun x => exp (t • x)).prod - (1 + t • z.sum)‖ ≤
      (z.map norm).sum^2 * |t|^2 / 2 := by
  induction z with
  | nil => simp
  | cons x z ih =>
    let U := exp (t • x)
    let P := (z.map fun y => exp (t • y)).prod
    let S := (z.map norm).sum
    have hx := hz x List.mem_cons_self
    have hU : U ∈ unitary A := exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hx)
    have h1 : ‖U-1‖ ≤ ‖x‖*|t| := by
      simpa [U,cstarExponentialTaylor] using norm_exp_sub_cstarExponentialTaylor_le x hx 0 t
    have h2 : ‖U-(1+t • x)‖ ≤ ‖x‖^2*|t|^2/2 := by
      simpa [U,cstarExponentialTaylor_one] using norm_exp_sub_cstarExponentialTaylor_le x hx 1 t
    have htail : ‖P-(1+t • z.sum)‖ ≤ S^2*|t|^2/2 :=
      ih (fun y hy => hz y (List.mem_cons_of_mem _ hy))
    have hsum : ‖z.sum‖ ≤ S := norm_list_sum_le z
    have hcross : ‖(U-1)*(t • z.sum)‖ ≤ (‖x‖*|t|) * (|t| * S) := by
      apply (norm_mul_le _ _).trans
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul h1 (mul_le_mul_of_nonneg_left hsum (abs_nonneg t))
        (mul_nonneg (abs_nonneg t) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (abs_nonneg _))
    have he : U*P-(1+t • (x+z.sum)) =
        U*(P-(1+t • z.sum)) + (U-(1+t • x)) + (U-1)*(t • z.sum) := by
      have expand (a b : A) : U*P-(1+(a+b)) =
          U*(P-(1+b)) + (U-(1+a)) + (U-1)*b := by noncomm_ring
      rw [smul_add]
      exact expand _ _
    change ‖U*P-(1+t • (x+z.sum))‖ ≤ (‖x‖+S)^2*|t|^2/2
    rw [he]
    calc
      _ ≤ (‖U*(P-(1+t • z.sum))‖ + ‖U-(1+t • x)‖) + ‖(U-1)*(t • z.sum)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (S^2*|t|^2/2 + ‖x‖^2*|t|^2/2) + (‖x‖*|t|)*(|t| * S) := by
        rw [CStarRing.norm_mem_unitary_mul _ hU]
        exact add_le_add (add_le_add htail h2) hcross
      _ = _ := by ring

/-- First-order Lie product error is controlled by total interaction mass
for all real times, uniformly in the number of factors. -/
theorem list_lie_product_mass_error (z : List A) (hz : ∀ x ∈ z, x ∈ skewAdjoint A) (t : ℝ) :
    ‖(z.map fun x => exp (t • x)).prod - exp (t • z.sum)‖ ≤ (z.map norm).sum^2 * |t|^2 := by
  have hs := list_sum_mem_addSubgroup (skewAdjoint A) z hz
  have h0 := list_exp_linear_error z hz t
  have h1 : ‖exp (t • z.sum)-(1+t • z.sum)‖ ≤ ‖z.sum‖^2*|t|^2/2 := by
    simpa [cstarExponentialTaylor_one] using norm_exp_sub_cstarExponentialTaylor_le z.sum hs 1 t
  have h2 := norm_sub_le_norm_sub_add_norm_sub ((z.map fun x => exp (t • x)).prod)
    (1+t • z.sum) (exp (t • z.sum))
  rw [norm_sub_rev (1+t • z.sum)] at h2
  have h3 : ‖z.sum‖^2*|t|^2/2 ≤ (z.map norm).sum^2*|t|^2/2 := by
    gcongr; exact norm_list_sum_le z
  linarith only [h0,h1,h2,h3]

/-- Repeating a mass-controlled Lie step r times leaves an error at most
the square of the integrated mass divided by r. -/
theorem list_lie_product_pow_mass_error (z : List A) (hz : ∀ x ∈ z, x ∈ skewAdjoint A)
    (t : ℝ) (r : ℕ) (hr : 0 < r) :
    ‖(z.map fun x => exp ((t/(r:ℝ)) • x)).prod^r - exp (t • z.sum)‖ ≤
      (z.map norm).sum^2*|t|^2/r := by
  let h := t/(r:ℝ)
  let U := (z.map fun x => exp (h • x)).prod
  let V := exp (h • z.sum)
  have hU : U ∈ unitary A := list_exp_product_mem_unitary z hz h
  have hV : V ∈ unitary A := exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.smul_mem h (list_sum_mem_addSubgroup (skewAdjoint A) z hz))
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  have he : V^r = exp (t • z.sum) := by
    dsimp [V,h]; rw [exp_real_smul_pow]; congr 2; field_simp
  rw [← he]
  calc
    _ ≤ (r:ℝ)*‖U-V‖ := unitary_pow_norm_sub_pow_le U V hU hV r
    _ ≤ (r:ℝ)*((z.map norm).sum^2*|h|^2) :=
      mul_le_mul_of_nonneg_left (list_lie_product_mass_error z hz h) hr'.le
    _ = _ := by dsimp [h]; rw [abs_div,abs_of_pos hr']; field_simp

#print axioms list_lie_product_pow_mass_error
end
end GaloisForLFunctions.HTGeometry
