import GaloisForLFunctions.HTGeometry.ReciprocalGammaPoleBranch
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# Taylor coefficients of reciprocal-Gamma pole branches

This module closes the coefficient layer of the inverse-Gamma branch cocycle.  It computes the
second derivative of the entire reciprocal Gamma function at every negative integer, transfers that
value through the analytic inverse relation, and obtains the exact quadratic coefficient of every
normalized pole branch.  The factorial and digamma recurrences then become the first two Taylor
shadows of the nonlinear branch cocycle.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

/-- The entire reciprocal-Gamma function, including its canonical zero values at `-ℕ`. -/
noncomputable def reciprocalGammaEntire (z : ℂ) : ℂ := (Complex.Gamma z)⁻¹

theorem contDiff_reciprocalGammaEntire : ContDiff ℂ ⊤ reciprocalGammaEntire := by
  exact Complex.differentiable_one_div_Gamma.contDiff

/-- The twice-differentiated entire reciprocal-Gamma recurrence
`H''(s) = 2 H'(s+1) + s H''(s+1)`. -/
theorem iteratedDeriv_two_reciprocalGammaEntire_recurrence (s : ℂ) :
    iteratedDeriv 2 reciprocalGammaEntire s =
      2 * deriv reciprocalGammaEntire (s + 1) +
        s * iteratedDeriv 2 reciprocalGammaEntire (s + 1) := by
  have hfun : reciprocalGammaEntire =
      fun z : ℂ => z * reciprocalGammaEntire (z + 1) := by
    funext z
    exact Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one z
  have hder2 : iteratedDeriv 2 reciprocalGammaEntire s =
      iteratedDeriv 2 (fun z : ℂ => z * reciprocalGammaEntire (z + 1)) s := by
    exact congrFun (congrArg (iteratedDeriv 2) hfun) s
  calc
    iteratedDeriv 2 reciprocalGammaEntire s =
        iteratedDeriv 2 (fun z : ℂ => z * reciprocalGammaEntire (z + 1)) s := hder2
    _ = 2 * deriv reciprocalGammaEntire (s + 1) +
        s * iteratedDeriv 2 reciprocalGammaEntire (s + 1) := by
      have hshift : ContDiff ℂ ⊤ (fun z : ℂ => reciprocalGammaEntire (z + 1)) := by
        exact contDiff_reciprocalGammaEntire.comp
          (contDiff_id.add (contDiff_const : ContDiff ℂ ⊤ (fun _ : ℂ => (1 : ℂ))))
      change iteratedDeriv 2
        ((id : ℂ → ℂ) * (fun z : ℂ => reciprocalGammaEntire (z + 1))) s = _
      rw [iteratedDeriv_mul contDiffAt_id
        (hshift.contDiffAt.of_le (by norm_num))]
      have hid : iteratedDeriv 2 (id : ℂ → ℂ) s = 0 := by
        rw [show 2 = 0 + 1 + 1 by omega, iteratedDeriv_succ', iteratedDeriv_succ']
        simp
      norm_num [Finset.sum_range_succ, iteratedDeriv_comp_add_const,
        iteratedDeriv_fun_id, iteratedDeriv_zero, iteratedDeriv_one]
      rw [hid]
      ring

private theorem deriv_reciprocalGammaEntire_one :
    deriv reciprocalGammaEntire 1 = -Complex.digamma 1 := by
  have hpoles : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  change deriv (fun z : ℂ => (Complex.Gamma z)⁻¹) 1 = -Complex.digamma 1
  rw [oneDivGamma_deriv_eq 1 hpoles, Complex.digamma_def,
    logDeriv_apply, Complex.Gamma_one]
  ring

/-- Exact second derivative of reciprocal Gamma at its zero `-n`:
`H''(-n) = -2 (-1)^n n! ψ(n+1)`. -/
theorem iteratedDeriv_two_reciprocalGammaEntire_neg_nat (n : ℕ) :
    iteratedDeriv 2 reciprocalGammaEntire (-(n : ℂ)) =
      -2 * ((-1 : ℂ) ^ n * (n.factorial : ℂ)) *
        Complex.digamma ((n : ℂ) + 1) := by
  induction n with
  | zero =>
      rw [iteratedDeriv_two_reciprocalGammaEntire_recurrence]
      norm_num [deriv_reciprocalGammaEntire_one]
  | succ n ih =>
      have hder : deriv reciprocalGammaEntire (-(n : ℂ)) =
          (-1 : ℂ) ^ n * (n.factorial : ℂ) := by
        exact (hasDerivAt_oneDivGamma_neg_nat n).deriv
      have hpoles : ∀ m : ℕ, ((n : ℂ) + 1) ≠ -(m : ℂ) := by
        intro m h
        have hre := congrArg Complex.re h
        simp only [Complex.add_re, Complex.natCast_re, Complex.one_re,
          Complex.neg_re] at hre
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      have hpsi := Complex.digamma_apply_add_one ((n : ℂ) + 1) hpoles
      rw [iteratedDeriv_two_reciprocalGammaEntire_recurrence]
      simp only [Nat.cast_succ]
      rw [show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring, hder, ih]
      rw [hpsi, Nat.factorial_succ, pow_succ]
      push_cast
      have hn1 : (n : ℂ) + 1 ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      field_simp [hn1]
      ring

/-- The exact second derivative of a normalized inverse branch at its base point. -/
theorem ReciprocalGammaPoleBranch.iteratedDeriv_two_zero
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) :
    iteratedDeriv 2 zn 0 =
      2 * Complex.digamma ((n : ℂ) + 1) / (n.factorial : ℂ) ^ (2 : ℕ) := by
  have hEq : (fun x : ℂ => reciprocalGammaEntire (zn x)) =ᶠ[nhds 0]
      (fun x : ℂ => -x) := by
    simpa [reciprocalGammaEntire] using zn.right_inverse
  have hEq2 := hEq.iteratedDeriv_eq 2
  have hzero : iteratedDeriv 2 (fun x : ℂ => -x) 0 = 0 := by
    rw [show 2 = 0 + 1 + 1 by omega, iteratedDeriv_succ', iteratedDeriv_succ']
    simp
  have hH2 : ContDiffAt ℂ 2 reciprocalGammaEntire (zn 0) :=
    contDiff_reciprocalGammaEntire.contDiffAt.of_le le_top
  have hzn2 : ContDiffAt ℂ 2 zn 0 :=
    zn.analyticAt_zero.contDiffAt.of_le le_top
  have hcomp : iteratedDeriv 2 (reciprocalGammaEntire ∘ zn) 0 =
      iteratedDeriv 2 reciprocalGammaEntire (zn 0) * deriv zn 0 ^ (2 : ℕ) +
        deriv reciprocalGammaEntire (zn 0) * iteratedDeriv 2 zn 0 := by
    exact iteratedDeriv_comp_two hH2 hzn2
  have hcompeq : (reciprocalGammaEntire ∘ zn) =
      fun x : ℂ => reciprocalGammaEntire (zn x) := rfl
  have hmaster :
      iteratedDeriv 2 reciprocalGammaEntire (-(n : ℂ)) *
          (-((-1 : ℂ) ^ n / (n.factorial : ℂ))) ^ (2 : ℕ) +
        ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * iteratedDeriv 2 zn 0 = 0 := by
    have hderH : deriv reciprocalGammaEntire (-(n : ℂ)) =
        (-1 : ℂ) ^ n * (n.factorial : ℂ) := by
      change deriv (fun z : ℂ => (Complex.Gamma z)⁻¹) (-(n : ℂ)) = _
      exact (hasDerivAt_oneDivGamma_neg_nat n).deriv
    rw [hcompeq] at hcomp
    rw [zn.map_zero, zn.hasDerivAt_zero.deriv, hderH] at hcomp
    rw [hEq2, hzero] at hcomp
    exact hcomp.symm
  rw [iteratedDeriv_two_reciprocalGammaEntire_neg_nat] at hmaster
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hsign : (-1 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp [hfac] at hmaster ⊢
  have hsignsq : ((-1 : ℂ) ^ n) ^ (2 : ℕ) = 1 := by
    rw [← pow_mul]
    simp
  rw [hsignsq] at hmaster
  simp only [mul_zero] at hmaster
  have hcore : -(2 * Complex.digamma ((n : ℂ) + 1)) +
      (n.factorial : ℂ) ^ (2 : ℕ) * iteratedDeriv 2 zn 0 = 0 := by
    simpa using (mul_eq_zero.mp hmaster).resolve_left hsign
  linear_combination hcore

/-- The positive linear coefficient `r_n` in
`z_n(x) = -n - r_n x + O(x²)`. -/
noncomputable def reciprocalGammaBranchLinearCoeff (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n / (n.factorial : ℂ)

/-- The quadratic coefficient `A_n` in
`z_n(x) = -n - r_n x + A_n x² + O(x³)`. -/
noncomputable def reciprocalGammaBranchQuadraticCoeff (n : ℕ) : ℂ :=
  Complex.digamma ((n : ℂ) + 1) / (n.factorial : ℂ) ^ (2 : ℕ)

theorem ReciprocalGammaPoleBranch.deriv_zero_eq_neg_linearCoeff
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) :
    deriv zn 0 = -reciprocalGammaBranchLinearCoeff n := by
  rw [zn.hasDerivAt_zero.deriv]
  rfl

theorem ReciprocalGammaPoleBranch.quadratic_taylorCoeff
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) :
    iteratedDeriv 2 zn 0 / (2 : ℂ) = reciprocalGammaBranchQuadraticCoeff n := by
  rw [zn.iteratedDeriv_two_zero]
  simp [reciprocalGammaBranchQuadraticCoeff]
  ring

/-- The factorial recurrence `r_n = -(n+1) r_{n+1}`. -/
theorem reciprocalGammaBranchLinearCoeff_succ (n : ℕ) :
    reciprocalGammaBranchLinearCoeff n =
      -((n : ℂ) + 1) * reciprocalGammaBranchLinearCoeff (n + 1) := by
  simp only [reciprocalGammaBranchLinearCoeff, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  field_simp [hfac, hn1]

/-- The quadratic branch recurrence
`A_n = (n+1)² A_{n+1} - (n+1) r_{n+1}²`, equivalently the digamma recurrence. -/
theorem reciprocalGammaBranchQuadraticCoeff_succ (n : ℕ) :
    reciprocalGammaBranchQuadraticCoeff n =
      ((n : ℂ) + 1) ^ (2 : ℕ) * reciprocalGammaBranchQuadraticCoeff (n + 1) -
        ((n : ℂ) + 1) * reciprocalGammaBranchLinearCoeff (n + 1) ^ (2 : ℕ) := by
  have hpoles : ∀ m : ℕ, ((n : ℂ) + 1) ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.neg_re] at hre
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hpsi := Complex.digamma_apply_add_one ((n : ℂ) + 1) hpoles
  simp only [reciprocalGammaBranchQuadraticCoeff, reciprocalGammaBranchLinearCoeff,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [hpsi]
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hsignsq : ((-1 : ℂ) ^ n) ^ (2 : ℕ) = 1 := by
    rw [← pow_mul]
    norm_num
  field_simp [hfac, hn1]
  rw [hsignsq]
  ring

/-- The exact quadratic Taylor expansion of every normalized inverse branch, with an analytic
cubic remainder. -/
theorem ReciprocalGammaPoleBranch.taylor_two_with_cubic_remainder
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      (fun x : ℂ => zn x) =ᶠ[nhds 0]
        (fun x => -(n : ℂ) - reciprocalGammaBranchLinearCoeff n * x +
          reciprocalGammaBranchQuadraticCoeff n * x ^ (2 : ℕ) + x ^ (3 : ℕ) * R x) := by
  obtain ⟨R, hRan, hR⟩ := zn.analyticAt_zero.exists_eventuallyEq_sum_add_pow_mul 3
  refine ⟨R, hRan, ?_⟩
  filter_upwards [hR] with x hx
  rw [hx]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one]
  rw [zn.map_zero, zn.deriv_zero_eq_neg_linearCoeff,
    show iteratedDeriv 2 zn 0 = 2 * reciprocalGammaBranchQuadraticCoeff n by
      have h := zn.quadratic_taylorCoeff
      field_simp at h ⊢
      exact h]
  ring

end GaloisForLFunctions
