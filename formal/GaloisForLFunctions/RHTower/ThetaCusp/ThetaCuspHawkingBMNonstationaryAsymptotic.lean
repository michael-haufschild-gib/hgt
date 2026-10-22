import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNonstationaryIntegrationByParts
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNonstationaryPolynomial

/-! Exact leading source moments with a uniform, analytically admitted remainder. -/
namespace RHTower.D4BMJointSource
open Complex Set
open scoped Polynomial
noncomputable section
set_option autoImplicit false

def nonstationaryIteratedMoment (n k : ℕ) (w : ℂ) : ℂ :=
  nonstationaryMoment (nonstationaryPolynomial n k) (2*k) w

theorem nonstationaryIteratedMoment_recurrence (n k : ℕ) (w : ℂ)
    (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    (w+1)*nonstationaryIteratedMoment n k w+nonstationaryIteratedMoment n (k+1) w =
      (nonstationaryPolynomial n k).eval 1/(5:ℂ)^(2*k+1) := by
  have h := nonstationaryMoment_recurrence (nonstationaryPolynomial n k) (2*k) w hw hw1
  norm_num [nonstationaryWeight,pow_succ,div_div] at h
  change (w+1)*nonstationaryMoment (nonstationaryPolynomial n k) (2*k) w+
    nonstationaryMoment (nonstationaryWeightStep (nonstationaryPolynomial n k) (2*k)) (2*(k+1)) w = _
  rw [show 2*(k+1)=2*k+2 by omega]
  exact h

theorem nonstationaryIteratedMoment_shift (n k : ℕ) (w : ℂ)
    (hw : -2 < w.re) (hw1 : w+1 ≠ 0) (hk : k ≤ n) :
    (w+1)^k*nonstationaryIteratedMoment n 0 w = (-1:ℂ)^k*nonstationaryIteratedMoment n k w := by
  revert hk
  induction k with
  | zero => intro _; simp only [pow_zero,one_mul]
  | succ k ih =>
    intro hk
    have hr := nonstationaryIteratedMoment_recurrence n k w hw hw1
    rw [nonstationaryPolynomial_one_eq_zero n k (by omega),zero_div] at hr
    have he : (w+1)*nonstationaryIteratedMoment n k w = -nonstationaryIteratedMoment n (k+1) w := by
      linear_combination hr
    calc
      _ = (w+1)*((w+1)^k*nonstationaryIteratedMoment n 0 w) := by rw [pow_succ]; ring
      _ = (-1:ℂ)^k*((w+1)*nonstationaryIteratedMoment n k w) := by rw [ih (by omega)]; ring
      _ = (-1:ℂ)^k*(-nonstationaryIteratedMoment n (k+1) w) := by rw [he]
      _ = _ := by rw [pow_succ]; ring

/-- Finite endpoint vanishing and one further integration give a uniform leading-term error. -/
theorem nonstationaryMoment_leading_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re ∈ Icc (-(3/2):ℝ) (-1) → w+1 ≠ 0 →
      ‖(w+1)*((w+1)^(n+1)*nonstationaryIteratedMoment n 0 w-
        (-1:ℂ)^n*((nonstationaryPolynomial n n).eval 1/(5:ℂ)^(2*n+1)))‖ ≤ C := by
  obtain ⟨C,hC0,hC⟩ := nonstationaryMoment_step_uniform_bound
    (nonstationaryPolynomial n (n+1)) (2*(n+1))
  let c := (nonstationaryPolynomial n (n+1)).eval 1/(5:ℂ)^(2*(n+1)+1)
  refine ⟨‖c‖+C,add_nonneg (norm_nonneg _) hC0,?_⟩
  intro w hw hw1
  have hwr : -2 < w.re := by linarith [hw.1]
  have hh := nonstationaryIteratedMoment_shift n n w hwr hw1 le_rfl
  have h0 := nonstationaryIteratedMoment_recurrence n n w hwr hw1
  have h1 := nonstationaryIteratedMoment_recurrence n (n+1) w hwr hw1
  have hb : ‖nonstationaryIteratedMoment n (n+2) w‖ ≤ C := by
    change ‖nonstationaryMoment (nonstationaryWeightStep (nonstationaryPolynomial n (n+1))
      (2*(n+1))) (2*(n+2)) w‖ ≤ C
    rw [show 2*(n+2)=2*(n+1)+2 by omega]
    exact (hC w hw).2
  have he : (w+1)*((w+1)^(n+1)*nonstationaryIteratedMoment n 0 w-
      (-1:ℂ)^n*((nonstationaryPolynomial n n).eval 1/(5:ℂ)^(2*n+1))) =
      (-1:ℂ)^(n+1)*(c-nonstationaryIteratedMoment n (n+2) w) := by
    dsimp only [c]
    simp only [pow_succ]
    linear_combination (w+1)^(2 : ℕ)*hh+(-1:ℂ)^n*(w+1)*h0-(-1:ℂ)^n*h1
  rw [he]
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl hb)

theorem nonstationaryMoment_second_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re ∈ Icc (-(3/2):ℝ) (-1) → w+1 ≠ 0 →
      ‖(w+1)*((w+1)^(3 : ℕ)*nonstationaryMoment ((1-Polynomial.X)^(2 : ℕ)) 0 w-(2/125:ℂ))‖ ≤ C := by
  obtain ⟨C,hC0,hC⟩ := nonstationaryMoment_leading_bound 2
  refine ⟨C,hC0,?_⟩
  intro w hw hw1
  have h := hC w hw hw1
  norm_num only [nonstationaryPolynomial_second_leading] at h
  simpa only [nonstationaryIteratedMoment,nonstationaryPolynomial] using h

theorem nonstationaryMoment_fourth_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re ∈ Icc (-(3/2):ℝ) (-1) → w+1 ≠ 0 →
      ‖(w+1)*((w+1)^(5 : ℕ)*nonstationaryMoment ((1-Polynomial.X)^(4 : ℕ)) 0 w-(24/3125:ℂ))‖ ≤ C := by
  obtain ⟨C,hC0,hC⟩ := nonstationaryMoment_leading_bound 4
  refine ⟨C,hC0,?_⟩
  intro w hw hw1
  have h := hC w hw hw1
  norm_num only [nonstationaryPolynomial_fourth_leading] at h
  simpa only [nonstationaryIteratedMoment,nonstationaryPolynomial] using h

end
end RHTower.D4BMJointSource
