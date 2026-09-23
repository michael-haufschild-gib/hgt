import GaloisForLFunctions.RHTower.ThetaCuspFirstAtomGaussianJetLimits

/-!
# Explicit first-atom derivative bounds at every order

A triangular recurrence for Gaussian monomials retains the actual source scale.
It bounds the nth first-atom derivative by 3(4q)^n times first-atom mass when
q >= n+3, without coefficient-mass constants or asymptotic thresholds.
-/

namespace RHTower
noncomputable section

/-- A Gaussian monomial at the literal first-atom scale. -/
def thetaCuspGaussianScaleMoment (m : ℕ) (x : ℝ) : ℝ :=
  Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x) *
    thetaCuspSingleAtomReflectionScale 1 x^m

/-- Exact triangular derivative recurrence for Gaussian monomials. -/
def thetaCuspGaussianScaleJet : ℕ → ℕ → ℝ → ℝ
  | 0, m, x => thetaCuspGaussianScaleMoment m x
  | n+1, m, x => (2*(m : ℝ)+1/2)*thetaCuspGaussianScaleJet n m x -
      2*thetaCuspGaussianScaleJet n (m+1) x

/-- The literal Gaussian monomial differentiates to the adjacent-moment combination. -/
theorem hasDerivAt_thetaCuspGaussianScaleMoment (m : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspGaussianScaleMoment m)
      ((2*(m : ℝ)+1/2)*thetaCuspGaussianScaleMoment m x -
        2*thetaCuspGaussianScaleMoment (m+1) x) x := by
  have hq := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
  have he := ((hasDerivAt_id x).div_const 2 |>.sub hq).exp
  exact (he.mul (hq.pow m)).congr_deriv (by
    cases m with
    | zero => simp [thetaCuspGaussianScaleMoment]; ring
    | succ m =>
      simp only [thetaCuspGaussianScaleMoment, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel, Pi.pow_apply, Pi.sub_apply, id_eq, pow_succ]
      ring)

/-- Every finite Gaussian jet differentiates to its successor. -/
theorem hasDerivAt_thetaCuspGaussianScaleJet (n m : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspGaussianScaleJet n m) (thetaCuspGaussianScaleJet (n+1) m x) x := by
  induction n generalizing m with
  | zero => exact hasDerivAt_thetaCuspGaussianScaleMoment m x
  | succ n ih => exact ((ih m).const_mul (2*(m : ℝ)+1/2)).sub ((ih (m+1)).const_mul 2)

/-- Actual first-atom derivatives are the same two Gaussian-monomial jets at every order. -/
theorem iteratedDeriv_firstAtom_eq_gaussianScaleJets (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => thetaCuspSourceTerm y 1) x =
      4*thetaCuspGaussianScaleJet n 2 x - 6*thetaCuspGaussianScaleJet n 1 x := by
  have h : ∀ k : ℕ, iteratedDeriv k (fun y : ℝ => thetaCuspSourceTerm y 1) =
      fun y => 4*thetaCuspGaussianScaleJet k 2 y - 6*thetaCuspGaussianScaleJet k 1 y := by
    intro k
    induction k with
    | zero =>
      funext y
      rw [iteratedDeriv_zero, thetaCuspSourceTerm_one_eq_scale_profile]
      simp only [thetaCuspGaussianScaleJet, thetaCuspGaussianScaleMoment]
      ring
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext y
      exact (((hasDerivAt_thetaCuspGaussianScaleJet k 2 y).const_mul 4).sub
        ((hasDerivAt_thetaCuspGaussianScaleJet k 1 y).const_mul 6)).deriv
  exact congrFun (h n) x

/-- A quantitative Gaussian jet bound whose scale threshold grows linearly with order. -/
theorem abs_thetaCuspGaussianScaleJet_le (n m : ℕ) {x : ℝ}
    (hq : ((m+n : ℕ) : ℝ)+1 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspGaussianScaleJet n m x| ≤
      (4*thetaCuspSingleAtomReflectionScale 1 x)^n * thetaCuspGaussianScaleMoment m x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let e := Real.exp (x/2-q)
  have hq0 : 0 ≤ q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  change ((m+n : ℕ) : ℝ)+1 ≤ q at hq
  change |thetaCuspGaussianScaleJet n m x| ≤ (4*q)^n*(e*q^m)
  induction n generalizing m with
  | zero =>
    change |e*q^m| ≤ (4*q)^(0 : ℕ)*(e*q^m)
    rw [pow_zero, one_mul, abs_of_nonneg (by positivity : 0 ≤ e*q^m)]
  | succ n ih =>
    have h0 := ih m (by push_cast at hq ⊢; linarith)
    have h1 := ih (m+1) (by push_cast at hq ⊢; linarith)
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmq : (m : ℝ)+1 ≤ q := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast at hq
      linarith
    have hb : 0 ≤ (4*q)^n*(e*q^m) := by positivity
    calc
      |thetaCuspGaussianScaleJet (n+1) m x| ≤
          |(2*(m : ℝ)+1/2)*thetaCuspGaussianScaleJet n m x| +
            |2*thetaCuspGaussianScaleJet n (m+1) x| := by
        simpa only [thetaCuspGaussianScaleJet, sub_zero, zero_sub, abs_neg] using
          (abs_sub_le ((2*(m : ℝ)+1/2)*thetaCuspGaussianScaleJet n m x) 0
            (2*thetaCuspGaussianScaleJet n (m+1) x))
      _ = (2*(m : ℝ)+1/2)*|thetaCuspGaussianScaleJet n m x| +
          2*|thetaCuspGaussianScaleJet n (m+1) x| := by
        simp only [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2*(m : ℝ)+1/2),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (2*(m : ℝ)+1/2)*((4*q)^n*(e*q^m)) +
          2*((4*q)^n*(e*q^(m+1))) :=
        add_le_add (mul_le_mul_of_nonneg_left h0 (by positivity))
          (mul_le_mul_of_nonneg_left h1 (by norm_num))
      _ = (2*(m : ℝ)+1/2+2*q)*((4*q)^n*(e*q^m)) := by rw [pow_succ]; ring
      _ ≤ (4*q)*((4*q)^n*(e*q^m)) := mul_le_mul_of_nonneg_right (by linarith) hb
      _ = (4*q)^(n+1)*(e*q^m) := by ring

/-- Every first-atom derivative has an explicit relative scale bound. -/
theorem abs_iteratedDeriv_firstAtom_le_effective (n : ℕ) {x : ℝ}
    (hq : (n : ℝ)+3 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n (fun y : ℝ => thetaCuspSourceTerm y 1) x| ≤
      3*(4*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspSourceTerm x 1 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let e := Real.exp (x/2-q)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hq3 : 3 ≤ q := by dsimp [q]; linarith
  have hq0 : 0 ≤ q := by linarith
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have h2 := abs_thetaCuspGaussianScaleJet_le n 2 (x := x) (by push_cast; linarith)
  have h1 := abs_thetaCuspGaussianScaleJet_le n 1 (x := x) (by push_cast; linarith)
  have hscalar : 4*q^(2 : ℕ)+6*q ≤ 3*(4*q^(2 : ℕ)-6*q) := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq3)]
  rw [iteratedDeriv_firstAtom_eq_gaussianScaleJets]
  calc
    |4*thetaCuspGaussianScaleJet n 2 x-6*thetaCuspGaussianScaleJet n 1 x| ≤
        4*|thetaCuspGaussianScaleJet n 2 x|+6*|thetaCuspGaussianScaleJet n 1 x| := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)] using
        (abs_sub_le (4*thetaCuspGaussianScaleJet n 2 x) 0 (6*thetaCuspGaussianScaleJet n 1 x))
    _ ≤ 4*((4*q)^n*(e*q^(2 : ℕ)))+6*((4*q)^n*(e*q^(1 : ℕ))) :=
      add_le_add (mul_le_mul_of_nonneg_left h2 (by norm_num))
        (mul_le_mul_of_nonneg_left h1 (by norm_num))
    _ = (4*q)^n*e*(4*q^(2 : ℕ)+6*q) := by ring
    _ ≤ (4*q)^n*e*(3*(4*q^(2 : ℕ)-6*q)) :=
      mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = 3*(4*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspSourceTerm x 1 := by
      rw [thetaCuspSourceTerm_one_eq_scale_profile]
      dsimp [q, e]
      ring

end
end RHTower
