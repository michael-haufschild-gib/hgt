import GaloisForLFunctions.HilbertMetric.SecondLevelConcavityFifthRootNoGo
import GaloisForLFunctions.HilbertMetric.ReflectionEighthJet

/-!
# Second-level concavity does not force reflected rank-three D1

Planat--Solé second-level concavity controls an ordinary consecutive-derivative Hankel
determinant of the squared-radius profile. TCD needs the different signed even-jet Hankel
determinant of the centered reflected product.

The positive even kernel `F(r) = exp (-r^4)` separates them exactly. Its squared-radius profile
`s(t) = exp (-t^2)` has positive first Laguerre expression and globally strict second-level
logarithmic concavity. Its centered reflected product is `P(t) = exp (-2t^4)`, whose even jets
through order eight are `1, 0, -48, 0, 80640`; hence its signed rank-three determinant is
`-3760128`.

Therefore the August 2026 second-level theorem cannot discharge finite TCD D1 without additional
theta-specific structure. The positive survivor is the exact ordinary-Hankel identity below.
-/

namespace HilbertMetric

noncomputable section

/-- Ordinary consecutive-derivative `3 × 3` Hankel determinant. -/
def derivativeHankelThreeDet (s0 s1 s2 s3 s4 : ℝ) : ℝ :=
  s0 * s2 * s4 - s0 * s3 ^ 2 - s1 ^ 2 * s4 +
    2 * s1 * s2 * s3 - s2 ^ 3

/-- Second-level Laguerre curvature is an ordinary derivative-Hankel determinant. -/
theorem secondLevelCurvature_eq_mul_derivativeHankelThreeDet
    (s0 s1 s2 s3 s4 : ℝ) :
    (s1 ^ 2 - s0 * s2) * (s2 ^ 2 - s0 * s4) -
        (s1 * s2 - s0 * s3) ^ 2 =
      s0 * derivativeHankelThreeDet s0 s1 s2 s3 s4 := by
  unfold derivativeHankelThreeDet
  ring

private def quarticGaussianReflectedPotentialPolynomial : Polynomial ℝ :=
  -Polynomial.C 24 * Polynomial.X ^ 2 +
    Polynomial.C 64 * Polynomial.X ^ 6

private def quarticGaussianReflectedPotential (x : ℝ) : ℝ :=
  quarticGaussianReflectedPotentialPolynomial.eval x

private theorem quarticGaussianReflectedPotential_eq (x : ℝ) :
    quarticGaussianReflectedPotential x = -24 * x ^ 2 + 64 * x ^ 6 := by
  simp [quarticGaussianReflectedPotential,
    quarticGaussianReflectedPotentialPolynomial]

private theorem iteratedDeriv_two_quarticGaussianReflectedProfile_eq_potential
    (x : ℝ) :
    iteratedDeriv 2 quarticGaussianReflectedProfile x =
      quarticGaussianReflectedPotential x * quarticGaussianReflectedProfile x := by
  rw [iteratedDeriv_two_quarticGaussianReflectedProfile,
    quarticGaussianReflectedPotential_eq]
  unfold quarticGaussianReflectedProfile
  ring

private theorem iteratedDeriv_iteratedDeriv_real
    (f : ℝ → ℝ) (m n : ℕ) :
    iteratedDeriv n (iteratedDeriv m f) = iteratedDeriv (m + n) f := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      rw [show m + (n + 1) = (m + n) + 1 by omega, iteratedDeriv_succ]

private theorem quarticGaussianReflectedProfile_jet_shift (n : ℕ) :
    iteratedDeriv (2 + n) quarticGaussianReflectedProfile 0 =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        iteratedDeriv i quarticGaussianReflectedPotential 0 *
          iteratedDeriv (n - i) quarticGaussianReflectedProfile 0 := by
  rw [← iteratedDeriv_iteratedDeriv_real quarticGaussianReflectedProfile 2 n]
  have heq : iteratedDeriv 2 quarticGaussianReflectedProfile =
      fun y => quarticGaussianReflectedPotential y *
        quarticGaussianReflectedProfile y := by
    funext y
    exact iteratedDeriv_two_quarticGaussianReflectedProfile_eq_potential y
  rw [heq]
  exact iteratedDeriv_fun_mul
    (by
      rw [show quarticGaussianReflectedPotential =
          fun x => -24 * x ^ 2 + 64 * x ^ 6 from
        funext quarticGaussianReflectedPotential_eq]
      fun_prop)
    (by
      unfold quarticGaussianReflectedProfile
      fun_prop)

private theorem iteratedDeriv_polynomial_eval_real
    (p : Polynomial ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => p.eval y) x =
      ((Polynomial.derivative^[n]) p).eval x := by
  induction n generalizing p x with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hderiv : deriv (fun y => p.eval y) =
          fun y => p.derivative.eval y := by
        funext y
        exact p.deriv
      rw [hderiv]
      simpa [Function.iterate_succ_apply] using
        (ih (x := x) (p := p.derivative))

private theorem iteratedDeriv_quarticGaussianReflectedPotential (n : ℕ) (x : ℝ) :
    iteratedDeriv n quarticGaussianReflectedPotential x =
      ((Polynomial.derivative^[n])
        quarticGaussianReflectedPotentialPolynomial).eval x := by
  have heq : quarticGaussianReflectedPotential =
      fun y => quarticGaussianReflectedPotentialPolynomial.eval y := by
    rfl
  rw [heq]
  exact iteratedDeriv_polynomial_eval_real
    quarticGaussianReflectedPotentialPolynomial n x

private theorem potential_jet_zero :
    iteratedDeriv 0 quarticGaussianReflectedPotential 0 = 0 := by
  rw [iteratedDeriv_quarticGaussianReflectedPotential]
  norm_num [quarticGaussianReflectedPotentialPolynomial]

private theorem potential_jet_one :
    iteratedDeriv 1 quarticGaussianReflectedPotential 0 = 0 := by
  rw [iteratedDeriv_quarticGaussianReflectedPotential]
  norm_num [quarticGaussianReflectedPotentialPolynomial]

private theorem potential_jet_two :
    iteratedDeriv 2 quarticGaussianReflectedPotential 0 = -48 := by
  rw [iteratedDeriv_quarticGaussianReflectedPotential]
  norm_num [quarticGaussianReflectedPotentialPolynomial,
    Function.iterate_succ_apply]

private theorem potential_jet_three :
    iteratedDeriv 3 quarticGaussianReflectedPotential 0 = 0 := by
  rw [iteratedDeriv_quarticGaussianReflectedPotential]
  norm_num [quarticGaussianReflectedPotentialPolynomial,
    Function.iterate_succ_apply]

private theorem potential_jet_four :
    iteratedDeriv 4 quarticGaussianReflectedPotential 0 = 0 := by
  rw [iteratedDeriv_quarticGaussianReflectedPotential]
  norm_num [quarticGaussianReflectedPotentialPolynomial,
    Function.iterate_succ_apply]

private theorem potential_jet_five :
    iteratedDeriv 5 quarticGaussianReflectedPotential 0 = 0 := by
  rw [iteratedDeriv_quarticGaussianReflectedPotential]
  norm_num [quarticGaussianReflectedPotentialPolynomial,
    Function.iterate_succ_apply]

private theorem potential_jet_six :
    iteratedDeriv 6 quarticGaussianReflectedPotential 0 = 46080 := by
  rw [iteratedDeriv_quarticGaussianReflectedPotential]
  norm_num [quarticGaussianReflectedPotentialPolynomial,
    Function.iterate_succ_apply]

private theorem quarticGaussianReflectedProfile_even :
    Function.Even quarticGaussianReflectedProfile := by
  intro x
  unfold quarticGaussianReflectedProfile
  congr 1
  ring

private theorem quarticGaussianReflectedProfile_odd_jet_zero
    {n : ℕ} (hn : Odd n) :
    iteratedDeriv n quarticGaussianReflectedProfile 0 = 0 := by
  have hfun : (fun x : ℝ => quarticGaussianReflectedProfile (-x)) =
      quarticGaussianReflectedProfile := funext quarticGaussianReflectedProfile_even
  have hcomp := iteratedDeriv_comp_neg n quarticGaussianReflectedProfile 0
  rw [hfun, neg_zero, hn.neg_one_pow] at hcomp
  simp only [neg_one_smul] at hcomp
  linarith

private theorem profile_jet_zero :
    iteratedDeriv 0 quarticGaussianReflectedProfile 0 = 1 := by
  norm_num [quarticGaussianReflectedProfile]

private theorem profile_jet_one :
    iteratedDeriv 1 quarticGaussianReflectedProfile 0 = 0 :=
  quarticGaussianReflectedProfile_odd_jet_zero (by decide)

private theorem profile_jet_two :
    iteratedDeriv 2 quarticGaussianReflectedProfile 0 = 0 := by
  rw [iteratedDeriv_two_quarticGaussianReflectedProfile]
  norm_num

private theorem profile_jet_three :
    iteratedDeriv 3 quarticGaussianReflectedProfile 0 = 0 :=
  quarticGaussianReflectedProfile_odd_jet_zero (by decide)

private theorem profile_jet_four :
    iteratedDeriv 4 quarticGaussianReflectedProfile 0 = -48 := by
  rw [show 4 = 2 + 2 by norm_num,
    quarticGaussianReflectedProfile_jet_shift]
  norm_num [Nat.choose, Finset.sum_range_succ, potential_jet_zero,
    potential_jet_one, potential_jet_two, profile_jet_zero,
    profile_jet_one, profile_jet_two]

private theorem profile_jet_five :
    iteratedDeriv 5 quarticGaussianReflectedProfile 0 = 0 :=
  quarticGaussianReflectedProfile_odd_jet_zero (by decide)

private theorem profile_jet_six :
    iteratedDeriv 6 quarticGaussianReflectedProfile 0 = 0 := by
  rw [show 6 = 2 + 4 by norm_num,
    quarticGaussianReflectedProfile_jet_shift]
  norm_num [Nat.choose, Finset.sum_range_succ, potential_jet_zero,
    potential_jet_one, potential_jet_two, potential_jet_three,
    potential_jet_four, profile_jet_zero, profile_jet_one,
    profile_jet_two, profile_jet_three, profile_jet_four]

private theorem profile_jet_seven :
    iteratedDeriv 7 quarticGaussianReflectedProfile 0 = 0 :=
  quarticGaussianReflectedProfile_odd_jet_zero (by decide)

private theorem profile_jet_eight :
    iteratedDeriv 8 quarticGaussianReflectedProfile 0 = 80640 := by
  rw [show 8 = 2 + 6 by norm_num,
    quarticGaussianReflectedProfile_jet_shift]
  norm_num [Nat.choose, Finset.sum_range_succ, potential_jet_zero,
    potential_jet_one, potential_jet_two, potential_jet_three,
    potential_jet_four, potential_jet_five, potential_jet_six,
    profile_jet_zero, profile_jet_one, profile_jet_two,
    profile_jet_three, profile_jet_four, profile_jet_five,
    profile_jet_six]

/-- Central signed rank-three determinant of the quartic-Gaussian reflected profile. -/
def quarticGaussianReflectedRankThreeD1 : ℝ :=
  signedEvenHankelThreeDet
    (iteratedDeriv 0 quarticGaussianReflectedProfile 0)
    (iteratedDeriv 2 quarticGaussianReflectedProfile 0)
    (iteratedDeriv 4 quarticGaussianReflectedProfile 0)
    (iteratedDeriv 6 quarticGaussianReflectedProfile 0)
    (iteratedDeriv 8 quarticGaussianReflectedProfile 0)

theorem quarticGaussianReflectedRankThreeD1_eq :
    quarticGaussianReflectedRankThreeD1 = -3760128 := by
  norm_num [quarticGaussianReflectedRankThreeD1, signedEvenHankelThreeDet,
    profile_jet_zero, profile_jet_two, profile_jet_four,
    profile_jet_six, profile_jet_eight]

theorem quarticGaussianReflectedRankThreeD1_neg :
    quarticGaussianReflectedRankThreeD1 < 0 := by
  rw [quarticGaussianReflectedRankThreeD1_eq]
  norm_num

/-- Strict radial second-level concavity does not force reflected rank-three D1. -/
theorem exists_secondLevelStrict_kernel_with_reflectedRankThreeD1Failure :
    ∃ (F s P : ℝ → ℝ),
      (∀ x, 0 < F x) ∧
      Function.Even F ∧
      (∀ x, 0 ≤ x → s x = F (Real.sqrt x)) ∧
      (∀ x, 0 < firstLaguerreExpression s x) ∧
      (∀ x, iteratedDeriv 2
        (fun y => Real.log (firstLaguerreExpression s y)) x < 0) ∧
      (∀ x, P x = F x * F (-x)) ∧
      signedEvenHankelThreeDet
        (iteratedDeriv 0 P 0) (iteratedDeriv 2 P 0)
        (iteratedDeriv 4 P 0) (iteratedDeriv 6 P 0)
        (iteratedDeriv 8 P 0) < 0 := by
  refine ⟨quarticGaussianKernel, quadraticGaussianRadialProfile,
    quarticGaussianReflectedProfile, quarticGaussianKernel_pos,
    quarticGaussianKernel_even, ?_, ?_, ?_,
    quarticGaussianReflectedProfile_eq_kernel_mul, ?_⟩
  · intro x hx
    exact quadraticGaussianRadialProfile_eq_quarticGaussianKernel_sqrt hx
  · exact firstLaguerreExpression_quadraticGaussianRadialProfile_pos
  · exact quadraticGaussianRadialProfile_secondLevel_strict
  · exact quarticGaussianReflectedRankThreeD1_neg

end

end HilbertMetric
