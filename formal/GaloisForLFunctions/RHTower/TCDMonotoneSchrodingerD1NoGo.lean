import GaloisForLFunctions.HilbertMetric.ReflectionEighthJet

/-!
# Monotone Schrödinger potential does not force rank-three TCD positivity

The positive even entire profile `exp (-z²-z⁴/6)` has a Schrödinger potential that starts
negative and is strictly increasing on the nonnegative real axis. Its central signed reflected
rank-three Hankel determinant is nevertheless negative. Thus the already-proved theta Riccati
monotonicity and central sign cannot, by themselves, discharge the missing TCD D1 gate.
-/

open Set

namespace RHTower

noncomputable section

namespace TCDMonotoneSchrodingerNoGo

def phasePolynomial : Polynomial ℝ :=
  -Polynomial.X ^ (2 : ℕ) - Polynomial.C (1/6) * Polynomial.X ^ (4 : ℕ)
def phase (x : ℝ) : ℝ := phasePolynomial.eval x
def profile (x : ℝ) : ℝ := Real.exp (phase x)
def slope (x : ℝ) : ℝ := phasePolynomial.derivative.eval x
def potentialPolynomial : Polynomial ℝ :=
  -Polynomial.C 2 + Polynomial.C 2 * Polynomial.X ^ (2 : ℕ) +
    Polynomial.C (8/3) * Polynomial.X ^ (4 : ℕ) +
    Polynomial.C (4/9) * Polynomial.X ^ (6 : ℕ)
def potential (x : ℝ) : ℝ := potentialPolynomial.eval x

theorem potential_eq (x : ℝ) :
    potential x = -2 + 2*x^(2 : ℕ) + (8/3)*x^(4 : ℕ) + (4/9)*x^(6 : ℕ) := by
  simp [potential, potentialPolynomial]

theorem hasDerivAt_phase (x : ℝ) : HasDerivAt phase (slope x) x := by
  exact phasePolynomial.hasDerivAt x

theorem hasDerivAt_profile (x : ℝ) :
    HasDerivAt profile (slope x * profile x) x := by
  unfold profile
  simpa [mul_comm] using (hasDerivAt_phase x).exp

theorem hasDerivAt_slope (x : ℝ) :
    HasDerivAt slope (phasePolynomial.derivative.derivative.eval x) x := by
  exact phasePolynomial.derivative.hasDerivAt x

theorem iteratedDeriv_two_profile (x : ℝ) :
    iteratedDeriv 2 profile x = potential x * profile x := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 1 profile = fun y => slope y * profile y := by
    funext y
    rw [iteratedDeriv_one]
    exact (hasDerivAt_profile y).deriv
  rw [heq]
  have hprod := (hasDerivAt_slope x).mul (hasDerivAt_profile x)
  change deriv (slope * profile) x = potential x * profile x
  rw [hprod.deriv, potential_eq]
  simp [slope, phasePolynomial]
  ring

theorem iteratedDeriv_iteratedDeriv_real
    (f : ℝ → ℝ) (m n : ℕ) :
    iteratedDeriv n (iteratedDeriv m f) = iteratedDeriv (m + n) f := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      rw [show m + (n + 1) = (m + n) + 1 by omega, iteratedDeriv_succ]

theorem profile_jet_shift (n : ℕ) :
    iteratedDeriv (2+n) profile 0 =
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        iteratedDeriv i potential 0 * iteratedDeriv (n-i) profile 0 := by
  rw [← iteratedDeriv_iteratedDeriv_real profile 2 n]
  have heq : iteratedDeriv 2 profile = fun y => potential y * profile y := by
    funext y
    exact iteratedDeriv_two_profile y
  rw [heq]
  exact iteratedDeriv_fun_mul
    (by
      rw [show potential = fun x => -2 + 2*x^(2 : ℕ) + (8/3)*x^(4 : ℕ) + (4/9)*x^(6 : ℕ)
        from funext potential_eq]
      fun_prop)
    (by
      have hphase : phase = fun x => -x^(2 : ℕ)-x^(4 : ℕ)/6 := by
        funext x
        simp [phase, phasePolynomial]
        ring
      unfold profile
      rw [hphase]
      fun_prop)

theorem profile_even : Function.Even profile := by
  intro x
  unfold profile phase
  congr 1
  simp [phasePolynomial]
  ring

theorem profile_odd_jet_zero {n : ℕ} (hn : Odd n) :
    iteratedDeriv n profile 0 = 0 := by
  have hfun : (fun x : ℝ => profile (-x)) = profile := funext profile_even
  have hcomp := iteratedDeriv_comp_neg n profile 0
  rw [hfun, neg_zero, hn.neg_one_pow] at hcomp
  simp only [neg_one_smul] at hcomp
  linarith

theorem iteratedDeriv_polynomial_eval_real (p : Polynomial ℝ) (n : ℕ) (x : ℝ) :
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

theorem iteratedDeriv_potential (n : ℕ) (x : ℝ) :
    iteratedDeriv n potential x =
      ((Polynomial.derivative^[n]) potentialPolynomial).eval x := by
  have heq : potential = fun y => potentialPolynomial.eval y := by
    funext y
    simp [potential, potentialPolynomial]
  rw [heq]
  exact iteratedDeriv_polynomial_eval_real potentialPolynomial n x

theorem potential_jet_zero : iteratedDeriv 0 potential 0 = -2 := by
  rw [iteratedDeriv_potential]
  norm_num [potentialPolynomial]
theorem potential_jet_one : iteratedDeriv 1 potential 0 = 0 := by
  rw [iteratedDeriv_potential]
  norm_num [potentialPolynomial]
theorem potential_jet_two : iteratedDeriv 2 potential 0 = 4 := by
  rw [iteratedDeriv_potential]
  norm_num [potentialPolynomial, Function.iterate_succ_apply]
theorem potential_jet_three : iteratedDeriv 3 potential 0 = 0 := by
  rw [iteratedDeriv_potential]
  norm_num [potentialPolynomial, Function.iterate_succ_apply]
theorem potential_jet_four : iteratedDeriv 4 potential 0 = 64 := by
  rw [iteratedDeriv_potential]
  norm_num [potentialPolynomial, Function.iterate_succ_apply]
theorem potential_jet_five : iteratedDeriv 5 potential 0 = 0 := by
  rw [iteratedDeriv_potential]
  norm_num [potentialPolynomial, Function.iterate_succ_apply]
theorem potential_jet_six : iteratedDeriv 6 potential 0 = 320 := by
  rw [iteratedDeriv_potential]
  norm_num [potentialPolynomial, Function.iterate_succ_apply]

theorem profile_jet_zero : iteratedDeriv 0 profile 0 = 1 := by
  norm_num [profile, phase, phasePolynomial]
theorem profile_jet_one : iteratedDeriv 1 profile 0 = 0 :=
  profile_odd_jet_zero (by decide)
theorem profile_jet_two : iteratedDeriv 2 profile 0 = -2 := by
  rw [iteratedDeriv_two_profile]
  norm_num [potential, potentialPolynomial, profile, phase, phasePolynomial]
theorem profile_jet_three : iteratedDeriv 3 profile 0 = 0 :=
  profile_odd_jet_zero (by decide)
theorem profile_jet_four : iteratedDeriv 4 profile 0 = 8 := by
  rw [show 4 = 2+2 by norm_num, profile_jet_shift]
  norm_num [Nat.choose, Finset.sum_range_succ, potential_jet_zero, potential_jet_one, potential_jet_two,
    profile_jet_zero, profile_jet_one, profile_jet_two]
theorem profile_jet_five : iteratedDeriv 5 profile 0 = 0 :=
  profile_odd_jet_zero (by decide)
theorem profile_jet_six : iteratedDeriv 6 profile 0 = 0 := by
  rw [show 6 = 2+4 by norm_num, profile_jet_shift]
  norm_num [Nat.choose, Finset.sum_range_succ, potential_jet_zero, potential_jet_one, potential_jet_two,
    potential_jet_three, potential_jet_four, profile_jet_zero,
    profile_jet_one, profile_jet_two, profile_jet_three, profile_jet_four]
theorem profile_jet_seven : iteratedDeriv 7 profile 0 = 0 :=
  profile_odd_jet_zero (by decide)
theorem profile_jet_eight : iteratedDeriv 8 profile 0 = -1120 := by
  rw [show 8 = 2+6 by norm_num, profile_jet_shift]
  norm_num [Nat.choose, Finset.sum_range_succ, potential_jet_zero, potential_jet_one, potential_jet_two,
    potential_jet_three, potential_jet_four, potential_jet_five,
    potential_jet_six, profile_jet_zero, profile_jet_one, profile_jet_two,
    profile_jet_three, profile_jet_four, profile_jet_five, profile_jet_six]

def entireSource (z : ℂ) : ℂ := Complex.exp (-z^(2 : ℕ)-z^(4 : ℕ)/6)

theorem analyticAt_entireSource (z : ℂ) : AnalyticAt ℂ entireSource z := by
  unfold entireSource
  fun_prop

theorem entireSource_ofReal (x : ℝ) : entireSource x = profile x := by
  simp [entireSource, profile, phase, phasePolynomial]
  congr 1
  ring

theorem profile_pos (x : ℝ) : 0 < profile x := by
  unfold profile
  positivity

theorem potential_zero_neg : potential 0 < 0 := by
  norm_num [potential, potentialPolynomial]

theorem hasDerivAt_potential (x : ℝ) :
    HasDerivAt potential (potentialPolynomial.derivative.eval x) x := by
  exact potentialPolynomial.hasDerivAt x

theorem potential_deriv_eq (x : ℝ) :
    deriv potential x = 4*x + (32/3)*x^(3 : ℕ) + (8/3)*x^(5 : ℕ) := by
  rw [(hasDerivAt_potential x).deriv]
  norm_num [potentialPolynomial]
  ring

theorem strictMonoOn_potential : StrictMonoOn potential (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
  · intro x hx
    exact (hasDerivAt_potential x).continuousAt.continuousWithinAt
  · intro x hx
    rw [potential_deriv_eq]
    have hx0 : 0 < x := by simpa using hx
    positivity

def centralReflectedRankThreeD1 : ℝ :=
  HilbertMetric.signedEvenHankelThreeDet
    ((iteratedDeriv 0 profile 0)^(2 : ℕ))
    (HilbertMetric.reflectedProductSecondJet
      (iteratedDeriv 0 profile 0) (iteratedDeriv 1 profile 0)
      (iteratedDeriv 2 profile 0))
    (HilbertMetric.reflectedProductFourthJet
      (iteratedDeriv 0 profile 0) (iteratedDeriv 1 profile 0)
      (iteratedDeriv 2 profile 0) (iteratedDeriv 3 profile 0)
      (iteratedDeriv 4 profile 0))
    (HilbertMetric.reflectedProductSixthJet
      (iteratedDeriv 0 profile 0) (iteratedDeriv 1 profile 0)
      (iteratedDeriv 2 profile 0) (iteratedDeriv 3 profile 0)
      (iteratedDeriv 4 profile 0) (iteratedDeriv 5 profile 0)
      (iteratedDeriv 6 profile 0))
    (HilbertMetric.reflectedProductEighthJet
      (iteratedDeriv 0 profile 0) (iteratedDeriv 1 profile 0)
      (iteratedDeriv 2 profile 0) (iteratedDeriv 3 profile 0)
      (iteratedDeriv 4 profile 0) (iteratedDeriv 5 profile 0)
      (iteratedDeriv 6 profile 0) (iteratedDeriv 7 profile 0)
      (iteratedDeriv 8 profile 0))

theorem centralReflectedRankThreeD1_eq :
    centralReflectedRankThreeD1 = -87040 := by
  simp [centralReflectedRankThreeD1, profile_jet_zero, profile_jet_one,
    profile_jet_two, profile_jet_three, profile_jet_four, profile_jet_five,
    profile_jet_six, profile_jet_seven, profile_jet_eight,
    HilbertMetric.signedEvenHankelThreeDet,
    HilbertMetric.reflectedProductSecondJet,
    HilbertMetric.reflectedProductFourthJet,
    HilbertMetric.reflectedProductSixthJet,
    HilbertMetric.reflectedProductEighthJet]
  norm_num

theorem centralReflectedRankThreeD1_neg :
    centralReflectedRankThreeD1 < 0 := by
  rw [centralReflectedRankThreeD1_eq]
  norm_num

theorem monotoneSchrodinger_rankThreeD1_noGo :
    (∀ z : ℂ, AnalyticAt ℂ entireSource z) ∧
    (∀ x : ℝ, entireSource x = profile x) ∧
    (∀ x : ℝ, 0 < profile x) ∧
    Function.Even profile ∧
    (∀ x : ℝ, iteratedDeriv 2 profile x = potential x * profile x) ∧
    potential 0 < 0 ∧
    StrictMonoOn potential (Ici 0) ∧
    centralReflectedRankThreeD1 < 0 := by
  exact ⟨analyticAt_entireSource, entireSource_ofReal, profile_pos, profile_even,
    iteratedDeriv_two_profile, potential_zero_neg, strictMonoOn_potential,
    centralReflectedRankThreeD1_neg⟩

end TCDMonotoneSchrodingerNoGo
end
end RHTower
