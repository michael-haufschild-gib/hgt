import GaloisForLFunctions.RHTower.RiemannTower

/-!
# The prime-clock square-summability diagonal

For a real parameter `sigma`, attach to each prime the amplitude `p^(-sigma)`.  Functional-equation
reflection replaces `sigma` by `1-sigma`.  This file computes the total squared displacement between
those two prime-amplitude families.

The displacement is square-summable exactly at `sigma = 1/2`.  Off the diagonal, its square dominates
a positive multiple of the divergent prime harmonic series.  This is the elementary analytic core of
the statement that the reflected infinite prime sectors meet only on the critical line.

No zero set or Riemann-hypothesis assumption occurs in the result.
-/

noncomputable section

namespace RHTower

/-- Squared distance between the prime amplitudes at `sigma` and its reflection `1-sigma`. -/
def primeClockReflectionEnergy (sigma : ℝ) (p : Nat.Primes) : ℝ :=
  (((p : ℝ) ^ (-sigma)) - ((p : ℝ) ^ (-(1 - sigma)))) ^ 2

@[simp] theorem primeClockReflectionEnergy_half (p : Nat.Primes) :
    primeClockReflectionEnergy (1 / 2 : ℝ) p = 0 := by
  rw [primeClockReflectionEnergy,
    show -(1 - (1 / 2 : ℝ)) = -(1 / 2 : ℝ) by ring]
  simp

private theorem scaled_primeHarmonic_le_energy_of_lt_half
    {sigma : ℝ} (hsigma : sigma < 1 / 2) (p : Nat.Primes) :
    (1 - (2 : ℝ) ^ (-(1 - 2 * sigma))) ^ 2 * (1 / (p : ℝ)) ≤
      primeClockReflectionEnergy sigma p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast p.prop.two_le
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := one_le_two.trans hp2
  have hp0 : (0 : ℝ) < (p : ℝ) := zero_lt_one.trans_le hp1
  have hdelta : 0 < 1 - 2 * sigma := by linarith
  have hnegdelta : -(1 - 2 * sigma) < 0 := by linarith
  have hbase :
      (p : ℝ) ^ (-(1 - 2 * sigma)) ≤ (2 : ℝ) ^ (-(1 - 2 * sigma)) :=
    Real.rpow_le_rpow_of_nonpos zero_lt_two hp2 hnegdelta.le
  have hcpos : 0 < 1 - (2 : ℝ) ^ (-(1 - 2 * sigma)) := by
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two hnegdelta)
  have hfactorNonneg :
      0 ≤ 1 - (p : ℝ) ^ (-(1 - 2 * sigma)) := by
    exact sub_nonneg.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (one_lt_two.trans_le hp2) hnegdelta).le
  have hfactor :
      ((p : ℝ) ^ (-sigma)) - ((p : ℝ) ^ (-(1 - sigma))) =
        (p : ℝ) ^ (-sigma) * (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) := by
    rw [show -(1 - sigma) = -sigma + (-(1 - 2 * sigma)) by ring,
      Real.rpow_add hp0]
    ring
  have hpow : (1 / (p : ℝ)) ≤ ((p : ℝ) ^ (-sigma)) ^ 2 := by
    rw [one_div, ← Real.rpow_neg_one]
    rw [show ((p : ℝ) ^ (-sigma)) ^ 2 = (p : ℝ) ^ (-2 * sigma) by
      rw [pow_two, ← Real.rpow_add hp0]
      congr 1
      ring]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hfactorSq :
      (1 - (2 : ℝ) ^ (-(1 - 2 * sigma))) ^ 2 ≤
        (1 - (p : ℝ) ^ (-(1 - 2 * sigma))) ^ 2 := by
    exact (sq_le_sq₀ hcpos.le hfactorNonneg).2 (by linarith)
  rw [primeClockReflectionEnergy, hfactor, mul_pow]
  nlinarith [sq_nonneg ((p : ℝ) ^ (-sigma)),
    sq_nonneg (1 - (2 : ℝ) ^ (-(1 - 2 * sigma)))]

/-- Below the critical line, the reflected prime-clock displacement has divergent square energy. -/
theorem not_summable_primeClockReflectionEnergy_of_lt_half
    {sigma : ℝ} (hsigma : sigma < 1 / 2) :
    ¬ Summable (primeClockReflectionEnergy sigma) := by
  intro hsum
  let c : ℝ := 1 - (2 : ℝ) ^ (-(1 - 2 * sigma))
  have hcpos : 0 < c := by
    dsimp [c]
    apply sub_pos.mpr
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hscaled : Summable (fun p : Nat.Primes => c ^ 2 * (1 / (p : ℝ))) := by
    apply Summable.of_nonneg_of_le
    · intro p
      positivity
    · intro p
      simpa [c] using scaled_primeHarmonic_le_energy_of_lt_half hsigma p
    · exact hsum
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff (pow_ne_zero 2 hcpos.ne')).mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

/-- Reflection around `1/2` preserves the square energy pointwise. -/
theorem primeClockReflectionEnergy_one_sub (sigma : ℝ) (p : Nat.Primes) :
    primeClockReflectionEnergy (1 - sigma) p = primeClockReflectionEnergy sigma p := by
  rw [primeClockReflectionEnergy, primeClockReflectionEnergy,
    show -(1 - (1 - sigma)) = -sigma by ring]
  ring

/-- Above the critical line, the reflected prime-clock displacement has divergent square energy. -/
theorem not_summable_primeClockReflectionEnergy_of_half_lt
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    ¬ Summable (primeClockReflectionEnergy sigma) := by
  intro hsum
  apply not_summable_primeClockReflectionEnergy_of_lt_half
    (sigma := 1 - sigma) (by linarith)
  exact hsum.congr (fun p => (primeClockReflectionEnergy_one_sub sigma p).symm)

/-- The reflected prime-clock displacement has finite square energy exactly on the critical line. -/
theorem summable_primeClockReflectionEnergy_iff (sigma : ℝ) :
    Summable (primeClockReflectionEnergy sigma) ↔ sigma = 1 / 2 := by
  constructor
  · intro hsum
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact not_summable_primeClockReflectionEnergy_of_lt_half hlt hsum
    · exact not_summable_primeClockReflectionEnergy_of_half_lt hgt hsum
  · rintro rfl
    have hzero : primeClockReflectionEnergy (1 / 2 : ℝ) =
        (fun _ : Nat.Primes => (0 : ℝ)) := by
      funext p
      exact primeClockReflectionEnergy_half p
    rw [hzero]
    exact summable_zero

/-- RH says exactly that every `xi` zero lies in the square-summable reflected prime-clock sector. -/
theorem riemannHypothesis_iff_xiZero_primeClockShale :
    RiemannHypothesis ↔
      ∀ rho : ℂ, xi rho = 0 → Summable (primeClockReflectionEnergy rho.re) := by
  constructor
  · intro hRH rho hzero
    have hline : rho.re = 1 / 2 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hreflected : (1 : ℂ) - rho ∈ rightHalf := by
          rw [mem_rightHalf]
          simp only [Complex.sub_re, Complex.one_re]
          linarith
        exact (rh_iff_xi_ne_zero_right.mp hRH _ hreflected)
          (by rw [xi_one_sub]; exact hzero)
      · exact (rh_iff_xi_ne_zero_right.mp hRH rho (mem_rightHalf.mpr hgt)) hzero
    exact (summable_primeClockReflectionEnergy_iff rho.re).2 hline
  · intro hsector
    apply rh_iff_xi_ne_zero_right.mpr
    intro rho hrho hzero
    have hline := (summable_primeClockReflectionEnergy_iff rho.re).1 (hsector rho hzero)
    exact (ne_of_gt (mem_rightHalf.mp hrho)) hline

end RHTower
