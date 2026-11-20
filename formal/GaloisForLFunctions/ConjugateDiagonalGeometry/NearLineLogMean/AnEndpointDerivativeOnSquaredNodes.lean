import Mathlib.Algebra.Group.ForwardDiff
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds

/-!
# One-sided derivative samples on squared nodes

Fold a centered binomial difference of order 2q by sending its signed grid
coordinate j-q to (j-q)²/q². Dividing by the folded coordinate turns its
vanishing moments into the derivative functional at zero. Every sample lies
in [0,1], and normalization at the central binomial coefficient bounds each
weight by q².
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def signedRow (q j : ℕ) : ℝ := (-1:ℝ)^(2*q-j)*(2*q).choose j

private def centralWeight (q j : ℕ) : ℝ := signedRow q j/signedRow q q

/-- The folded grid; its center maps to the endpoint zero. -/
def squareNode (q j : ℕ) : ℝ := ((j:ℝ)-q)^2/(q:ℝ)^2

/-- Coefficient of f(node)-f(0) in the endpoint derivative formula. -/
def squareNodeWeight (q j : ℕ) : ℝ := -centralWeight q j/squareNode q j

private theorem signedRow_abs (q j : ℕ) : |signedRow q j| = ((2*q).choose j:ℝ) := by
  simp [signedRow,abs_mul,abs_pow]

private theorem signedRow_center_ne (q : ℕ) : signedRow q q ≠ 0 := by
  have hp : 0 < (2*q).choose q := Nat.choose_pos (by omega)
  exact abs_pos.mp (by rw [signedRow_abs]; exact_mod_cast hp)

private theorem centralWeight_abs_le_one (q j : ℕ) : |centralWeight q j| ≤ 1 := by
  rw [centralWeight,abs_div,div_le_one (abs_pos.mpr (signedRow_center_ne q)),signedRow_abs,signedRow_abs]
  have h := Nat.choose_le_middle j (2*q)
  rw [show 2*q/2=q by omega] at h
  exact_mod_cast h

theorem squareNode_mem (q j : ℕ) (hq : 0 < q) (hj : j ∈ range (2*q+1)) :
    squareNode q j ∈ Set.Icc (0:ℝ) 1 := by
  have hqr : (0:ℝ)<q := Nat.cast_pos.mpr hq
  have hjr : (j:ℝ) ≤ 2*q := by exact_mod_cast (Nat.le_of_lt_succ (mem_range.mp hj))
  have hd : |(j:ℝ)-q| ≤ q := abs_le.mpr ⟨by linarith only [Nat.cast_nonneg (α:=ℝ) j],by linarith only [hjr]⟩
  refine ⟨div_nonneg (sq_nonneg _) (sq_nonneg _),(div_le_one (sq_pos_of_pos hqr)).mpr ?_⟩
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hd 2

private theorem squareNode_center (q : ℕ) : squareNode q q=0 := by simp [squareNode]

private theorem squareNode_ne {q j : ℕ} (hq : 0 < q) (hj : j ≠ q) : squareNode q j ≠ 0 := by
  exact div_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (by exact_mod_cast hj))) (pow_ne_zero _ (Nat.cast_ne_zero.mpr hq.ne'))

theorem squareNodeWeight_abs_le (q j : ℕ) (hq : 0 < q) :
    |squareNodeWeight q j| ≤ (q:ℝ)^2 := by
  by_cases hj : j=q
  · subst j; simp [squareNodeWeight,squareNode_center]
  have hd : (1:ℝ) ≤ |(j:ℝ)-q| := by
    rcases lt_or_gt_of_ne hj with h|h
    · have hh : (j:ℝ)+1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt h
      rw [abs_of_nonpos (by linarith only [hh])]
      linarith only [hh]
    · have hh : (q:ℝ)+1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
      rw [abs_of_nonneg (by linarith only [hh])]
      linarith only [hh]
  have hnode : 0 < squareNode q j := lt_of_le_of_ne
    (div_nonneg (sq_nonneg _) (sq_nonneg _)) (squareNode_ne hq hj).symm
  rw [squareNodeWeight,abs_div,abs_neg,abs_of_pos hnode,div_le_iff₀ hnode]
  have he : (q:ℝ)^2*squareNode q j=((j:ℝ)-q)^2 := by
    unfold squareNode
    field_simp [Nat.cast_ne_zero.mpr hq.ne']
  rw [he]
  exact (centralWeight_abs_le_one q j).trans (by simpa only [sq_abs] using one_le_pow₀ hd (n:=2))

private theorem centered_row_power (q k : ℕ) (hk : k < 2*q) :
    (∑ j ∈ range (2*q+1), signedRow q j*((j:ℝ)-q)^k)=0 := by
  have hz : (fwdDiff (1:ℝ))^[2*q] (fun x : ℝ => x^k) (-(q:ℝ))=0 := by
    rw [fwdDiff_iter_pow_eq_zero_of_lt hk]; rfl
  rw [fwdDiff_iter_eq_sum_shift] at hz
  rw [←hz]
  apply sum_congr rfl
  intro j _
  rw [zsmul_eq_mul]
  simp only [signedRow,nsmul_eq_mul,mul_one,Int.cast_mul,Int.cast_pow,Int.cast_neg,
    Int.cast_one,Int.cast_natCast,sub_eq_add_neg,add_comm (-(q:ℝ))]

private theorem folded_row_power (q k : ℕ) (hk : k < q) :
    (∑ j ∈ range (2*q+1), centralWeight q j*(squareNode q j)^k)=0 := by
  let C := (signedRow q q)⁻¹/((q:ℝ)^2)^k
  calc _ = ∑ j ∈ range (2*q+1), (signedRow q j*((j:ℝ)-q)^(2*k))*C := by
          apply sum_congr rfl
          intro j _
          dsimp only [C,centralWeight,squareNode]
          rw [div_pow,←pow_mul]
          ring
    _ = 0 := by rw [←sum_mul,centered_row_power q (2*k) (by omega),zero_mul]

private theorem weight_times_node {q : ℕ} (hq : 0 < q) (j : ℕ) :
    squareNodeWeight q j*squareNode q j=(if j=q then 1 else 0)-centralWeight q j := by
  by_cases hj : j=q
  · subst j
    simp [squareNode_center,centralWeight,div_self (signedRow_center_ne q)]
  · rw [squareNodeWeight,div_mul_cancel₀ _ (squareNode_ne hq hj),if_neg hj,zero_sub]

/-- All powers through q are differentiated exactly. The first moment is
one and every higher moment through that degree vanishes. -/
theorem squareNode_derivative_moment {q k : ℕ} (hk : k < q) :
    (∑ j ∈ range (2*q+1), squareNodeWeight q j*(squareNode q j)^(k+1)) =
      if k=0 then 1 else 0 := by
  have hq : 0 < q := by omega
  have h (j : ℕ) : squareNodeWeight q j*(squareNode q j)^(k+1) =
      (if j=q then (squareNode q q)^k else 0)-centralWeight q j*(squareNode q j)^k := by
    rw [pow_succ',←mul_assoc,weight_times_node hq,sub_mul]
    by_cases hj : j=q <;> simp [hj]
  simp_rw [h]
  rw [sum_sub_distrib,folded_row_power q k hk,sub_zero]
  have hmem : q ∈ range (2*q+1) := mem_range.mpr (by omega)
  by_cases hzero : k=0 <;> simp [squareNode_center,hzero,hmem]

private theorem squareNode_taylor_exact {q : ℕ} (hq : 0 < q) (z : ℂ) :
    (∑ j ∈ range (2*q+1), (squareNodeWeight q j:ℂ)*
      ((∑ k ∈ range (q+1), ((squareNode q j:ℂ)*z)^k/(k.factorial:ℂ))-1)) = z := by
  have he (j : ℕ) : (∑ k ∈ range (q+1), ((squareNode q j:ℂ)*z)^k/(k.factorial:ℂ))-1 =
      ∑ k ∈ range q, ((squareNode q j:ℂ)*z)^(k+1)/((k+1).factorial:ℂ) := by
    rw [sum_range_succ']; simp
  simp_rw [he,mul_sum]
  rw [sum_comm]
  have H (k : ℕ) (hk : k ∈ range q) :
      (∑ j ∈ range (2*q+1), (squareNodeWeight q j:ℂ)*(((squareNode q j:ℂ)*z)^(k+1)/((k+1).factorial:ℂ))) =
      if k=0 then z else 0 := by
    have hc := congrArg Complex.ofReal (squareNode_derivative_moment (mem_range.mp hk))
    simp only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow] at hc
    calc _ = (∑ j ∈ range (2*q+1), (squareNodeWeight q j:ℂ)*(squareNode q j:ℂ)^(k+1))*
            (z^(k+1)/((k+1).factorial:ℂ)) := by
            rw [sum_mul]; exact sum_congr rfl fun _ _ => by rw [mul_pow]; ring
      _ = _ := by rw [hc]; by_cases h : k=0 <;> simp [h]
  rw [sum_congr rfl H]
  simp [hq]

/-- A complex exponential and its actual endpoint derivative. The factor
outside the Taylor remainder grows only polynomially in the order. -/
theorem squareNode_exponential_error {q : ℕ} (hq : 0 < q) (z : ℂ) :
    ‖(∑ j ∈ range (2*q+1), (squareNodeWeight q j:ℂ)*(Complex.exp ((squareNode q j:ℂ)*z)-1))-z‖ ≤
      (2*q+1:ℕ)*(q:ℝ)^2*((‖z‖^(q+1)/(q+1).factorial)*Real.exp ‖z‖) := by
  let E := (‖z‖^(q+1)/(q+1).factorial)*Real.exp ‖z‖
  let P (j : ℕ) := ∑ k ∈ range (q+1), ((squareNode q j:ℂ)*z)^k/(k.factorial:ℂ)
  have he : (∑ j ∈ range (2*q+1), (squareNodeWeight q j:ℂ)*(Complex.exp ((squareNode q j:ℂ)*z)-1))-z =
      ∑ j ∈ range (2*q+1), (squareNodeWeight q j:ℂ)*(Complex.exp ((squareNode q j:ℂ)*z)-P j) := by
    conv_lhs => rhs; rw [←squareNode_taylor_exact hq z]
    rw [←sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by dsimp [P]; ring
  rw [he]
  have hterm (j : ℕ) (hj : j ∈ range (2*q+1)) :
      ‖(squareNodeWeight q j:ℂ)*(Complex.exp ((squareNode q j:ℂ)*z)-P j)‖ ≤ (q:ℝ)^2*E := by
    have hn := squareNode_mem q j hq hj
    have hsmall : ‖(squareNode q j:ℂ)*z‖ ≤ ‖z‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hn.2
    have H := _root_.RHTower.norm_complex_exp_sub_sum_le_factorial_tail ((squareNode q j:ℂ)*z) (q+1)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    apply mul_le_mul (squareNodeWeight_abs_le q j hq) (H.trans ?_) (norm_nonneg _) (sq_nonneg _)
    exact mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hsmall _) (Nat.cast_nonneg _))
      (Real.exp_le_exp.mpr hsmall) (Real.exp_pos _).le (by positivity)
  calc _ ≤ ∑ j ∈ range (2*q+1), ‖(squareNodeWeight q j:ℂ)*(Complex.exp ((squareNode q j:ℂ)*z)-P j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range (2*q+1), (q:ℝ)^2*E := sum_le_sum hterm
    _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul,E,mul_assoc]

#print axioms squareNode_derivative_moment
#print axioms squareNode_exponential_error

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
