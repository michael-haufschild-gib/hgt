import GaloisForLFunctions.ThetaCuspSections.LegendrePolynomialKernel
import GaloisForLFunctions.HTGeometry.SturmSelfAdjoint

/-!
# Weighted energies of Legendre derivatives

Differentiating the Legendre equation produces the Sturm operator for
weight `(1-x²)^r`. Its vanishing endpoint flux gives an exact recurrence
for every mixed derivative energy, retaining orthogonality at every order.
-/

open MeasureTheory Set Polynomial
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections
open GaloisForLFunctions.SelectivePositivityAndThresholdLaws

/-- The polynomial form of Bonnet's recurrence. -/
def legendrePoly : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => C (1 / ((n : ℝ) + 2)) *
      (C (2 * (n : ℝ) + 3) * X * legendrePoly (n + 1) - C ((n : ℝ) + 1) * legendrePoly n)

theorem legendrePoly_eval (n : ℕ) (x : ℝ) : (legendrePoly n).eval x = legP n x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp only [legendrePoly, eval_one, legP_zero]
    · simp only [legendrePoly, eval_X, Nat.zero_add, legP_one]
    · simp only [legendrePoly, eval_mul, eval_sub, eval_C, eval_X,
        ih (n + 1) (by omega), ih n (by omega), legP_succ_succ]
      ring

/-- Formal derivatives retain polynomial smoothness at all orders. -/
def legendreDerivative (n : ℕ) : ℕ → ℝ[X]
  | 0 => legendrePoly n
  | r + 1 => (legendreDerivative n r).derivative

theorem hasDerivAt_legendreDerivative (n r : ℕ) (x : ℝ) :
    HasDerivAt (fun t => (legendreDerivative n r).eval t)
      ((legendreDerivative n (r + 1)).eval x) x :=
  (legendreDerivative n r).hasDerivAt x

private theorem derivative_zero_eval (n : ℕ) (x : ℝ) :
    (legendreDerivative n 0).eval x = legP n x := legendrePoly_eval n x

private theorem derivative_one_eval (n : ℕ) (x : ℝ) :
    (legendreDerivative n 1).eval x = legP' n x := by
  have hh := hasDerivAt_legendreDerivative n 0 x
  simp only [derivative_zero_eval] at hh
  exact hh.unique (hasDerivAt_legP n x)

private theorem derivative_adjacent (n : ℕ) (x : ℝ) :
    legP' (n + 1) x = ((n : ℝ) + 1) * legP n x + x * legP' n x ∧
      x * legP' (n + 1) x - legP' n x = ((n : ℝ) + 1) * legP (n + 1) x := by
  induction n with
  | zero => simp [legP, legP']
  | succ n ih =>
    have hb := legP_bonnet n x
    have hd : legP' (n + 2) x = (2 * (n : ℝ) + 3) * legP (n + 1) x + legP' n x := rfl
    push_cast
    constructor
    · rw [hd]
      linarith only [ih.2]
    · rw [hd]
      linear_combination -hb - ih.1

private theorem legendre_base_flux (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t => (1 - t ^ 2) * legP' n t)
      (-(n : ℝ) * ((n : ℝ) + 1) * legP n x) x := by
  rcases n with _ | n
  · simp only [legP', mul_zero, Nat.cast_zero, neg_zero, zero_mul]
    exact hasDerivAt_const x 0
  · have he : (fun t : ℝ => (1 - t ^ 2) * legP' (n + 1) t) =
        fun t => ((n : ℝ) + 1) * (legP n t - t * legP (n + 1) t) := by
      funext t
      obtain ⟨h1, h2⟩ := derivative_adjacent n t
      linear_combination h1 - t * h2
    rw [he]
    have hd := ((hasDerivAt_legP n x).sub
      ((hasDerivAt_id' x).mul (hasDerivAt_legP (n + 1) x))).const_mul ((n : ℝ) + 1)
    refine hd.congr_deriv ?_
    push_cast
    linear_combination -((n : ℝ) + 1) * (derivative_adjacent n x).2

/-- The eigenvalue lost after taking `r` derivatives. -/
def legendreDerivativeEigen (n r : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) + 1) - (r : ℝ) * ((r : ℝ) + 1)

/-- Every differentiated Legendre polynomial satisfies its weighted Sturm equation. -/
theorem legendreDerivative_equation (n r : ℕ) (x : ℝ) :
    (1 - x ^ 2) * (legendreDerivative n (r + 2)).eval x -
      2 * ((r : ℝ) + 1) * x * (legendreDerivative n (r + 1)).eval x +
      legendreDerivativeEigen n r * (legendreDerivative n r).eval x = 0 := by
  induction r generalizing x with
  | zero =>
    have hd := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).mul
      (hasDerivAt_legendreDerivative n 1 x)
    simp only [derivative_one_eval] at hd
    have hh := hd.unique (legendre_base_flux n x)
    simp only [legendreDerivativeEigen, Nat.cast_zero, zero_mul, sub_zero,
      zero_add, derivative_zero_eval, derivative_one_eval]
    norm_num only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
      Nat.reduceSub, pow_one, mul_one, zero_sub] at hh
    nlinarith only [hh]
  | succ r ih =>
    have he : (fun t : ℝ => (1 - t ^ 2) * (legendreDerivative n (r + 2)).eval t -
        2 * ((r : ℝ) + 1) * t * (legendreDerivative n (r + 1)).eval t +
        legendreDerivativeEigen n r * (legendreDerivative n r).eval t) = fun _ => 0 :=
      funext (fun t => ih t)
    have hW := (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
    have hd := ((hW.mul (hasDerivAt_legendreDerivative n (r + 2) x)).sub
      (((hasDerivAt_id x).mul (hasDerivAt_legendreDerivative n (r + 1) x)).const_mul
        (2 * ((r : ℝ) + 1)))).add
      ((hasDerivAt_legendreDerivative n r x).const_mul (legendreDerivativeEigen n r))
    change HasDerivAt (fun t => (1 - t ^ 2) * (legendreDerivative n (r + 2)).eval t -
      2 * ((r : ℝ) + 1) * (t * (legendreDerivative n (r + 1)).eval t) +
      legendreDerivativeEigen n r * (legendreDerivative n r).eval t) _ x at hd
    have he' : (fun t : ℝ => (1 - t ^ 2) * (legendreDerivative n (r + 2)).eval t -
      2 * ((r : ℝ) + 1) * (t * (legendreDerivative n (r + 1)).eval t) +
      legendreDerivativeEigen n r * (legendreDerivative n r).eval t) = fun _ => 0 := by
        convert he using 1
        funext t
        ring
    rw [he'] at hd
    have hh := hd.unique (hasDerivAt_const x (0 : ℝ))
    norm_num only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
      Nat.reduceSub, pow_one, mul_one, zero_sub] at hh
    simp only [legendreDerivativeEigen, Nat.cast_add, Nat.cast_one] at hh ⊢
    linear_combination hh

/-- Vanishing endpoint flux exposes the exact derivative-energy recurrence. -/
theorem hasDerivAt_weighted_legendreFlux (n r : ℕ) (x : ℝ) :
    HasDerivAt (fun t => (1 - t ^ 2) ^ (r + 1) * (legendreDerivative n (r + 1)).eval t)
      (-legendreDerivativeEigen n r * ((1 - x ^ 2) ^ r * (legendreDerivative n r).eval x)) x := by
  have hW := (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
  have hd := (hW.pow (r + 1)).mul (hasDerivAt_legendreDerivative n (r + 1) x)
  apply hd.congr_deriv
  norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, zero_sub,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.pow_apply, Pi.sub_apply]
  rw [pow_succ]
  linear_combination (1 - x ^ 2) ^ r * legendreDerivative_equation n r x

/-- Mixed polynomial energy in the natural derivative weight. -/
def weightedLegendreEnergy (r n m : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1,
    (1 - x ^ 2) ^ r * (legendreDerivative n r).eval x * (legendreDerivative m r).eval x

/-- One integration by parts pays the next weight exactly. -/
theorem weightedLegendreEnergy_succ (r n m : ℕ) :
    weightedLegendreEnergy (r + 1) n m =
      legendreDerivativeEigen m r * weightedLegendreEnergy r n m := by
  have hh := _root_.HTGeometry.integral_mul_sturm_eq_neg
    (w := fun x : ℝ => (1 - x ^ 2) ^ (r + 1))
    (u := fun x => (legendreDerivative n r).eval x)
    (u' := fun x => (legendreDerivative n (r + 1)).eval x)
    (v' := fun x => (legendreDerivative m (r + 1)).eval x)
    (wv' := fun x => -legendreDerivativeEigen m r *
      ((1 - x ^ 2) ^ r * (legendreDerivative m r).eval x))
    (a := (-1 : ℝ)) (b := 1)
    (by simp) (by simp)
    (fun x _ => hasDerivAt_legendreDerivative n r x)
    (fun x _ => hasDerivAt_weighted_legendreFlux m r x)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  have hl : (fun x : ℝ => (legendreDerivative n r).eval x *
      (-legendreDerivativeEigen m r * ((1 - x ^ 2) ^ r * (legendreDerivative m r).eval x))) =
      fun x => -legendreDerivativeEigen m r *
        ((1 - x ^ 2) ^ r * (legendreDerivative n r).eval x * (legendreDerivative m r).eval x) := by
    funext x
    ring
  have hr : (fun x : ℝ => (legendreDerivative n (r + 1)).eval x *
      ((1 - x ^ 2) ^ (r + 1) * (legendreDerivative m (r + 1)).eval x)) =
      fun x => (1 - x ^ 2) ^ (r + 1) *
        (legendreDerivative n (r + 1)).eval x * (legendreDerivative m (r + 1)).eval x := by
    funext x
    ring
  rw [hl, hr, intervalIntegral.integral_const_mul] at hh
  change -legendreDerivativeEigen m r * weightedLegendreEnergy r n m =
    -weightedLegendreEnergy (r + 1) n m at hh
  linarith only [hh]

/-- Distinct Legendre modes remain orthogonal after every weighted derivative. -/
theorem weightedLegendreEnergy_eq_zero {n m : ℕ} (hne : n ≠ m) (r : ℕ) :
    weightedLegendreEnergy r n m = 0 := by
  induction r with
  | zero =>
    simpa only [weightedLegendreEnergy, pow_zero, one_mul, derivative_zero_eval] using legP_orthog hne
  | succ r ih => rw [weightedLegendreEnergy_succ, ih, mul_zero]

/-- The exact norm retains every eigenvalue from the derivative ladder. -/
theorem weightedLegendreEnergy_self (r n : ℕ) :
    weightedLegendreEnergy r n n =
      (∏ j ∈ Finset.range r, legendreDerivativeEigen n j) * (2 / (2 * (n : ℝ) + 1)) := by
  induction r with
  | zero =>
    simpa only [weightedLegendreEnergy, pow_zero, one_mul, derivative_zero_eval,
      Finset.range_zero, Finset.prod_empty, ← sq] using legP_sq_integral n
  | succ r ih =>
    rw [weightedLegendreEnergy_succ, ih, Finset.prod_range_succ]
    ring

/-- The adjacent derivative difference persists at every differentiation order. -/
theorem legendreDerivative_difference (n r : ℕ) (x : ℝ) :
    (legendreDerivative (n + 2) (r + 1)).eval x =
      (2 * (n : ℝ) + 3) * (legendreDerivative (n + 1) r).eval x +
        (legendreDerivative n (r + 1)).eval x := by
  induction r generalizing x with
  | zero => simp only [Nat.zero_add, derivative_one_eval, derivative_zero_eval, legP']
  | succ r ih =>
    have he : (fun t : ℝ => (legendreDerivative (n + 2) (r + 1)).eval t) =
        fun t => (2 * (n : ℝ) + 3) * (legendreDerivative (n + 1) r).eval t +
          (legendreDerivative n (r + 1)).eval t := funext ih
    have hl := hasDerivAt_legendreDerivative (n + 2) (r + 1) x
    have hr := ((hasDerivAt_legendreDerivative (n + 1) r x).const_mul
      (2 * (n : ℝ) + 3)).add (hasDerivAt_legendreDerivative n (r + 1) x)
    rw [he] at hl
    exact hl.unique hr

/-- Bonnet's recurrence at derivative order `r` retains its negative lower mode. -/
theorem legendreDerivative_bonnet (n r : ℕ) (x : ℝ) :
    ((n : ℝ) + 2 - r) * (legendreDerivative (n + 2) r).eval x =
      (2 * (n : ℝ) + 3) * x * (legendreDerivative (n + 1) r).eval x -
        ((n : ℝ) + 1 + r) * (legendreDerivative n r).eval x := by
  induction r generalizing x with
  | zero =>
    simpa only [Nat.cast_zero, sub_zero, add_zero, derivative_zero_eval] using legP_bonnet n x
  | succ r ih =>
    have he : (fun t : ℝ => ((n : ℝ) + 2 - r) * (legendreDerivative (n + 2) r).eval t) =
        fun t => (2 * (n : ℝ) + 3) * t * (legendreDerivative (n + 1) r).eval t -
          ((n : ℝ) + 1 + r) * (legendreDerivative n r).eval t := funext ih
    have hl := (hasDerivAt_legendreDerivative (n + 2) r x).const_mul ((n : ℝ) + 2 - r)
    have hr := (((hasDerivAt_id x).const_mul (2 * (n : ℝ) + 3)).mul
      (hasDerivAt_legendreDerivative (n + 1) r x)).sub
        ((hasDerivAt_legendreDerivative n r x).const_mul ((n : ℝ) + 1 + r))
    rw [he] at hl
    have hh := hl.unique hr
    simp only [id_eq, mul_one, Nat.cast_add, Nat.cast_one] at hh ⊢
    linear_combination hh - legendreDerivative_difference n r x

#print axioms legendreDerivative_equation
#print axioms weightedLegendreEnergy_eq_zero
#print axioms weightedLegendreEnergy_self
#print axioms legendreDerivative_bonnet

end GaloisForLFunctions.ThetaCuspSections
