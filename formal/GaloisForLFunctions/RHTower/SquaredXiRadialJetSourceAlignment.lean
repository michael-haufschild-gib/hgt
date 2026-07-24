import GaloisForLFunctions.RHTower.XiCollapseDirichletLeg

/-!
# Sign alignment of the squared-Xi radial source jets

The squared-coordinate radial operator has positive reverse-Bessel magnitudes and alternating jet
signs.  This module packages those magnitudes recursively and proves the source identity needed by
the first unprotected squared-Xi derivative: after the formal Xi jet split is substituted, every
von Mangoldt jet occurs with the same negative sign.

The analytic theorem identifying this finite jet polynomial with the iterated radial derivative is
separate.  No RH assumption, zero location, or numerical input occurs here.
-/

noncomputable section

namespace RHTower

open Complex LSeries ArithmeticFunction
open scoped LSeries.notation

/-- Positive reverse-Bessel magnitudes forced by repeated application of
`(2*w)⁻¹ d/dw` to `L(1/2+w)/w`.

Inside the triangular range they satisfy
`b(n+1,j)=(2*n+1-j)*b(n,j)+b(n,j-1)`, with `b(0,0)=1`. -/
def squaredRadialJetWeight : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => (2 * n + 1) * squaredRadialJetWeight n 0
  | n + 1, j + 1 =>
      (2 * n - j) * squaredRadialJetWeight n (j + 1) +
        squaredRadialJetWeight n j

@[simp] theorem squaredRadialJetWeight_zero_zero :
    squaredRadialJetWeight 0 0 = 1 := rfl

@[simp] theorem squaredRadialJetWeight_zero_succ (j : ℕ) :
    squaredRadialJetWeight 0 (j + 1) = 0 := rfl

@[simp] theorem squaredRadialJetWeight_succ_zero (n : ℕ) :
    squaredRadialJetWeight (n + 1) 0 =
      (2 * n + 1) * squaredRadialJetWeight n 0 := rfl

@[simp] theorem squaredRadialJetWeight_succ_succ (n j : ℕ) :
    squaredRadialJetWeight (n + 1) (j + 1) =
      (2 * n - j) * squaredRadialJetWeight n (j + 1) +
        squaredRadialJetWeight n j := rfl

/-- The rational and half-argument digamma portions of the `j`th Xi logarithmic jet. -/
def xiRationalGammaJet (j : ℕ) (s : ℂ) : ℂ :=
  iteratedDeriv j
      (fun z : ℂ => 1 / z + 1 / (z - 1) - (Real.log Real.pi) / 2) s +
    (1 / 2 : ℂ) ^ (j + 1) * iteratedDeriv j Complex.digamma (s / 2)

/-- Alternating, positively rescaled squared-radial Xi jet polynomial. -/
def squaredXiAlternatingJetPolynomial (n : ℕ) (w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (squaredRadialJetWeight n j : ℂ) * w ^ j * (-1 : ℂ) ^ j *
      iteratedDeriv j xiLogDeriv (1 / 2 + w)

/-- Rational--Gamma part of the alternating squared-radial jet polynomial. -/
def squaredXiAlternatingRationalGammaJetPolynomial (n : ℕ) (w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (squaredRadialJetWeight n j : ℂ) * w ^ j * (-1 : ℂ) ^ j *
      xiRationalGammaJet j (1 / 2 + w)

/-- Positive-coefficient von Mangoldt part of the alternating squared-radial jet polynomial. -/
def squaredXiPrimeJetPolynomial (n : ℕ) (w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (squaredRadialJetWeight n j : ℂ) * w ^ j *
      LSeries (LSeries.logMul^[j] ↗Λ) (1 / 2 + w)

/-- **Exact source sign alignment.**  On the half-plane of absolute Euler convergence, the
alternating squared-radial Xi jet is its rational--Gamma jet minus a prime jet whose finite
reverse-Bessel coefficients carry no alternating signs. -/
theorem squaredXiAlternatingJetPolynomial_eq_rationalGamma_sub_prime
    (n : ℕ) {w : ℂ} (hw : 1 < (1 / 2 + w).re) :
    squaredXiAlternatingJetPolynomial n w =
      squaredXiAlternatingRationalGammaJetPolynomial n w -
        squaredXiPrimeJetPolynomial n w := by
  rw [squaredXiAlternatingJetPolynomial,
    squaredXiAlternatingRationalGammaJetPolynomial,
    squaredXiPrimeJetPolynomial, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDeriv_xiLogDeriv_split j hw]
  have hsign : (-1 : ℂ) ^ j * (-1 : ℂ) ^ (j + 1) = -1 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    norm_num
  rw [xiRationalGammaJet]
  calc
    (squaredRadialJetWeight n j : ℂ) * w ^ j * (-1 : ℂ) ^ j *
          (iteratedDeriv j
              (fun z : ℂ => 1 / z + 1 / (z - 1) - (Real.log Real.pi) / 2)
              (1 / 2 + w) +
            (1 / 2 : ℂ) ^ (j + 1) *
              iteratedDeriv j Complex.digamma ((1 / 2 + w) / 2) +
            (-1 : ℂ) ^ (j + 1) *
              LSeries (LSeries.logMul^[j] ↗Λ) (1 / 2 + w)) =
        (squaredRadialJetWeight n j : ℂ) * w ^ j * (-1 : ℂ) ^ j *
            xiRationalGammaJet j (1 / 2 + w) +
          (squaredRadialJetWeight n j : ℂ) * w ^ j *
            ((-1 : ℂ) ^ j * (-1 : ℂ) ^ (j + 1)) *
              LSeries (LSeries.logMul^[j] ↗Λ) (1 / 2 + w) := by
          rw [xiRationalGammaJet]
          ring
    _ = (squaredRadialJetWeight n j : ℂ) * w ^ j * (-1 : ℂ) ^ j *
            xiRationalGammaJet j (1 / 2 + w) -
          (squaredRadialJetWeight n j : ℂ) * w ^ j *
            LSeries (LSeries.logMul^[j] ↗Λ) (1 / 2 + w) := by
          rw [hsign]
          ring

/-- The exact reverse-Bessel closed form for the radial-jet magnitudes, equation (1):
`b(n,j) = (2n − j)! / (2^{n−j} (n−j)! j!)`. -/
def squaredRadialJetWeightClosedForm (n j : ℕ) : ℚ :=
  (Nat.factorial (2 * n - j) : ℚ) / (2 ^ (n - j) * Nat.factorial (n - j) * Nat.factorial j)

private theorem closedForm_diag (n : ℕ) : squaredRadialJetWeightClosedForm n n = 1 := by
  unfold squaredRadialJetWeightClosedForm
  rw [show 2 * n - n = n by omega, show n - n = 0 by omega, pow_zero, Nat.factorial_zero]
  have : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  push_cast
  field_simp

private theorem closedForm_zero_step (n : ℕ) :
    ((2 * n + 1 : ℕ) : ℚ) * squaredRadialJetWeightClosedForm n 0
      = squaredRadialJetWeightClosedForm (n + 1) 0 := by
  unfold squaredRadialJetWeightClosedForm
  rw [show 2 * n - 0 = 2 * n by omega, show n - 0 = n by omega,
      show 2 * (n + 1) - 0 = 2 * n + 2 by omega, show (n + 1) - 0 = n + 1 by omega,
      Nat.factorial_zero,
      show (2 * n + 2).factorial = (2 * n + 2) * ((2 * n + 1) * (2 * n).factorial) from by
        rw [show 2 * n + 2 = (2 * n + 1) + 1 from rfl, Nat.factorial_succ,
            show 2 * n + 1 = (2 * n) + 1 from rfl, Nat.factorial_succ],
      show (n + 1).factorial = (n + 1) * n.factorial from Nat.factorial_succ n]
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h2n : ((2 * n).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp
  ring

private theorem closedForm_interior_step (m k : ℕ) :
    ((2 * (m + k + 1) - k : ℕ) : ℚ) * squaredRadialJetWeightClosedForm (m + k + 1) (k + 1)
      + squaredRadialJetWeightClosedForm (m + k + 1) k
      = squaredRadialJetWeightClosedForm (m + k + 1 + 1) (k + 1) := by
  unfold squaredRadialJetWeightClosedForm
  have e1 : 2 * (m + k + 1) - (k + 1) = 2 * m + k + 1 := by omega
  have e2 : (m + k + 1) - (k + 1) = m := by omega
  have e3 : 2 * (m + k + 1) - k = 2 * m + k + 2 := by omega
  have e4 : (m + k + 1) - k = m + 1 := by omega
  have e5 : 2 * (m + k + 1 + 1) - (k + 1) = 2 * m + k + 3 := by omega
  have e6 : (m + k + 1 + 1) - (k + 1) = m + 1 := by omega
  rw [e1, e2, e3, e4, e5, e6]
  push_cast
  rw [show (2 * m + k + 2).factorial = (2 * m + k + 2) * (2 * m + k + 1).factorial from by
        rw [show 2 * m + k + 2 = (2 * m + k + 1) + 1 from rfl, Nat.factorial_succ],
      show (2 * m + k + 3).factorial
          = (2 * m + k + 3) * ((2 * m + k + 2) * (2 * m + k + 1).factorial) from by
        rw [show 2 * m + k + 3 = (2 * m + k + 2) + 1 from rfl, Nat.factorial_succ,
            show 2 * m + k + 2 = (2 * m + k + 1) + 1 from rfl, Nat.factorial_succ],
      show (m + 1).factorial = (m + 1) * m.factorial from Nat.factorial_succ m,
      show (k + 1).factorial = (k + 1) * k.factorial from Nat.factorial_succ k]
  have hm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hf : ((2 * m + k + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp
  ring

/-- Outside the triangular range the magnitudes vanish. -/
theorem squaredRadialJetWeight_eq_zero_of_lt : ∀ n j : ℕ, n < j → squaredRadialJetWeight n j = 0 := by
  intro n
  induction n with
  | zero =>
      intro j hj
      rcases j with _ | p
      · omega
      · simp
  | succ n ih =>
      intro j hj
      rcases j with _ | p
      · omega
      · rw [squaredRadialJetWeight_succ_succ, ih (p + 1) (by omega), ih p (by omega)]; simp

/-- **Exact reverse-Bessel closed form**, equation (1).  The recursively-defined radial-jet
magnitudes equal the factorial closed form on the triangular range. -/
theorem squaredRadialJetWeight_eq_closedForm (n : ℕ) :
    ∀ j, j ≤ n → (squaredRadialJetWeight n j : ℚ) = squaredRadialJetWeightClosedForm n j := by
  induction n with
  | zero =>
      intro j hj
      interval_cases j
      simp [squaredRadialJetWeightClosedForm]
  | succ n ih =>
      intro j hj
      rcases j with _ | k
      · rw [squaredRadialJetWeight_succ_zero, Nat.cast_mul, ih 0 (Nat.zero_le n)]
        exact closedForm_zero_step n
      · have hkn : k ≤ n := by omega
        rcases Nat.lt_or_ge k n with hlt | hge
        · rw [squaredRadialJetWeight_succ_succ, Nat.cast_add, Nat.cast_mul,
              ih (k + 1) hlt, ih k hkn]
          obtain ⟨m, rfl⟩ : ∃ m, n = m + k + 1 := ⟨n - k - 1, by omega⟩
          exact closedForm_interior_step m k
        · have hkeq : k = n := le_antisymm hkn hge
          rw [squaredRadialJetWeight_succ_succ, hkeq,
              squaredRadialJetWeight_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n)]
          rw [mul_zero, zero_add, ih n (le_refl n), closedForm_diag n, closedForm_diag (n + 1)]

/-- **Positivity**: every radial-jet magnitude on the triangular range is a positive integer. -/
theorem squaredRadialJetWeight_pos (n j : ℕ) (hj : j ≤ n) : 0 < squaredRadialJetWeight n j := by
  have h := squaredRadialJetWeight_eq_closedForm n j hj
  have hpos : 0 < squaredRadialJetWeightClosedForm n j := by
    unfold squaredRadialJetWeightClosedForm
    apply div_pos
    · exact_mod_cast Nat.factorial_pos _
    · have h1 : (0 : ℚ) < (Nat.factorial (n - j) : ℚ) := by exact_mod_cast Nat.factorial_pos _
      have h2 : (0 : ℚ) < (Nat.factorial j : ℚ) := by exact_mod_cast Nat.factorial_pos _
      positivity
  have hq : (0 : ℚ) < (squaredRadialJetWeight n j : ℚ) := by rw [h]; exact hpos
  exact_mod_cast hq

end RHTower
