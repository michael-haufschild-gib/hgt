import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedShift.CenteredPoles

/-!
# Moment laws for the balanced child displacements

Reflection annihilates all odd centered moments. Telescoping the cubic
across adjacent half-digit intervals gives the exact second moment and
a positive quadratic penalty for every change of center.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedShift

open BalancedContinuation

theorem centered_digit_value (t : ExceptionalTime) (j : ℕ) (d : Fin (radix t j)) :
    displacement t j (center t j) d = (d.val:ℝ)-((radix t j:ℝ)-1)/2 := by
  have hr := ((symmetric_digits_iff_center t j (center t j)).mpr rfl) d
  have h : d.val+d.rev.val+1=radix t j := by rw [Fin.val_rev]; omega
  have hp : (d.val:ℝ)+(d.rev.val:ℝ)+1=radix t j := by exact_mod_cast h
  unfold displacement at hr ⊢
  linarith only [hp,hr]

private theorem odd_sum_reflection {C : ℕ} (Y : Fin C → ℝ) (m : ℕ) (hr : ∀ d, Y d.rev = -Y d) :
    ∑ d, (Y d)^(2*m+1) = 0 := by
  let f (d : Fin C) := (Y d)^(2*m+1)
  have ho : Odd (2*m+1) := ⟨m,rfl⟩
  have h (d : Fin C) : f (Fin.revPerm d) = -f d := by
    rw [Fin.revPerm_apply]
    exact (congrArg (fun x : ℝ => x^(2*m+1)) (hr d)).trans (ho.neg_pow (Y d))
  have he : -(∑ d, f d) = ∑ d, f d := calc
    -(∑ d, f d) = ∑ d, -f d := by rw [Finset.sum_neg_distrib]
    _ = ∑ d, f (Fin.revPerm d) := Finset.sum_congr rfl (fun d _ => (h d).symm)
    _ = ∑ d, f d := Equiv.sum_comp Fin.revPerm f
  change ∑ d, f d = 0
  linarith only [he]

theorem centered_odd_moment (t : ExceptionalTime) (j m : ℕ) :
    ∑ d : Fin (radix t j), (displacement t j (center t j) d)^(2*m+1) = 0 :=
  odd_sum_reflection (displacement t j (center t j)) m fun d =>
    eq_neg_of_add_eq_zero_right (((symmetric_digits_iff_center t j (center t j)).mpr rfl) d)

/-- Consecutive intervals between centered half-digit endpoints give a discrete integral. -/
theorem centered_telescope {A : Type*} [AddCommGroup A] (t : ExceptionalTime) (j : ℕ) (F : ℝ → A) :
    ∑ d : Fin (radix t j), (F (displacement t j (center t j) d+1/2)-
      F (displacement t j (center t j) d-1/2)) =
      F ((radix t j:ℝ)/2)-F (-(radix t j:ℝ)/2) := by
  let C := radix t j
  let G (k : ℕ) := F ((k:ℝ)-(C:ℝ)/2)
  have h (d : Fin C) : F (displacement t j (center t j) d+1/2)-
      F (displacement t j (center t j) d-1/2) = G (d.val+1)-G d.val := by
    rw [centered_digit_value]
    unfold G
    push_cast
    congr 1 <;> congr 1 <;> ring
  rw [Finset.sum_congr rfl (fun d _ => h d),Fin.sum_univ_eq_sum_range
    (fun k => G (k+1)-G k),Finset.sum_range_sub]
  unfold G
  push_cast
  congr 1 <;> congr 1 <;> ring

theorem centered_second_moment (t : ExceptionalTime) (j : ℕ) :
    12*(∑ d : Fin (radix t j), (displacement t j (center t j) d)^2) =
      (radix t j:ℝ)*((radix t j:ℝ)^2-1) := by
  let Y := displacement t j (center t j)
  have he := centered_telescope t j (fun x : ℝ => x^3)
  have h (x : ℝ) : (x+1/2)^3-(x-1/2)^3 = 3*x^2+1/4 := by ring
  simp only [h,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at he
  linarith only [he]

/-- Mean squared displacement of one balanced composition step. -/
def meanSquare (t : ExceptionalTime) (j : ℕ) (a : ℝ) :=
  (∑ d : Fin (radix t j), (displacement t j a d)^2)/(radix t j:ℝ)

theorem mean_square_formula (t : ExceptionalTime) (j : ℕ) (a : ℝ) :
    meanSquare t j a = ((radix t j:ℝ)^2-1)/12+(base t j-1)^2*(a-center t j)^2 := by
  let c := center t j
  let q := (base t j-1)*(c-a)
  let Y := displacement t j c
  have hterm (d : Fin (radix t j)) : (displacement t j a d)^2 = (Y d)^2+Y d*(2*q)+q^2 := by
    unfold Y q displacement
    ring
  have h₁ : ∑ d, Y d = 0 := by simpa only [Nat.mul_zero,Nat.zero_add,pow_one] using centered_odd_moment t j 0
  have h₂ : 12*(∑ d, (Y d)^2) = (radix t j:ℝ)*((radix t j:ℝ)^2-1) := centered_second_moment t j
  unfold meanSquare
  rw [Finset.sum_congr rfl (fun d _ => hterm d),Finset.sum_add_distrib,Finset.sum_add_distrib,
    ← Finset.sum_mul,h₁,zero_mul,add_zero,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  apply (div_eq_iff (by exact_mod_cast (tailRadix t j).pos.ne' : (radix t j:ℝ) ≠ 0)).mpr
  dsimp only [q,c]
  linear_combination h₂/12

/-- The spectral center is the unique minimizer of the squared displacement. -/
theorem mean_square_minimum (t : ExceptionalTime) (j : ℕ) (a : ℝ) :
    0 < meanSquare t j (center t j) ∧ meanSquare t j (center t j) ≤ meanSquare t j a ∧
      (meanSquare t j a = meanSquare t j (center t j) ↔ a = center t j) := by
  have hC : (1:ℝ) < radix t j := by exact_mod_cast radix_gt_one t j
  have hB : 0 < base t j-1 := by rw [base_sq]; nlinarith only [hC,sq_nonneg ((radix t j:ℝ)-1)]
  have hv : 0 < ((radix t j:ℝ)^2-1)/12 := by rw [← base_sq]; positivity
  rw [mean_square_formula,mean_square_formula]
  simp only [sub_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,add_zero]
  refine ⟨hv,le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)),?_⟩
  rw [add_eq_left,mul_eq_zero,or_iff_right (pow_ne_zero 2 hB.ne'),sq_eq_zero_iff,sub_eq_zero]

/-- A finite minimization over the child displacements characterizes full-gas isometry
at every pole in the two-strip continuation. -/
theorem isometry_iff_minimizes_mean_square (t : ExceptionalTime) (j : ℕ) (a : Shift) :
    (∀ s : {z : ℂ // -(3/2) < z.re ∧ meromorphicOrderAt (extension t j a.val) z < 0},
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s.val f x) ↔
      ∀ v : ℝ, meanSquare t j a.val ≤ meanSquare t j v := by
  rw [all_poles_isometric_iff_center]
  constructor
  · intro he v
    rw [he]
    exact (mean_square_minimum t j v).2.1
  · intro hall
    apply (mean_square_minimum t j a.val).2.2.mp
    exact le_antisymm (hall (center t j)) (mean_square_minimum t j a.val).2.1

#print axioms isometry_iff_minimizes_mean_square
#print axioms centered_odd_moment
#print axioms centered_telescope
#print axioms centered_second_moment
#print axioms mean_square_formula
#print axioms mean_square_minimum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedShift
