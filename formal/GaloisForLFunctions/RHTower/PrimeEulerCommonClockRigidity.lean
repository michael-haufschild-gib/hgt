import GaloisForLFunctions.RHTower.PrimeEulerReflectedModulusNeutrality
import GaloisForLFunctions.RHTower.WindowBudget

/-!
# Common-clock rigidity of reflected prime Euler factors

One prime can choose a phase that makes two reflected Euler radii modulus-neutral.  The phases of
an actual vertical translate are not independent: they all have the form `tau * log p`.  Prime
recurrence in arbitrarily short logarithmic windows then forces cofinally many phases with cosine
bounded away from zero, while off-line neutrality would force those cosines to tend to zero.

Thus primewise neutrality under one common nonzero clock pins the horizontal displacement to zero.
The logarithmic-window input is isolated as `PrimeWindowSupply`; Bertrand discharges it in the
explicit low-clock range, while the prime number theorem supplies it for every positive window.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Equality of two reflected local-factor moduli determines the phase cosine exactly. -/
theorem cos_eq_radius_average_of_norm_one_sub_mul_eq
    {rminus rplus theta : ℝ} (hne : rminus ≠ rplus)
    (hmod :
      ‖(1 : ℂ) - (rplus : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)‖ =
        ‖(1 : ℂ) - (rminus : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)‖) :
    Real.cos theta = (rplus + rminus) / 2 := by
  have hsquares := congrArg (fun x : ℝ => x ^ 2) hmod
  change
    ‖(1 : ℂ) - (rplus : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)‖ ^ 2 =
      ‖(1 : ℂ) - (rminus : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)‖ ^ 2
    at hsquares
  rw [norm_one_sub_real_mul_exp_mul_I_sq,
    norm_one_sub_real_mul_exp_mul_I_sq] at hsquares
  have hsub : rplus - rminus ≠ 0 := sub_ne_zero.mpr hne.symm
  apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).mpr
  apply (mul_left_cancel₀ hsub)
  nlinarith

/-- At one prime, common-clock reflected neutrality forces the cosine to equal the average of the
two reflected Euler radii. -/
theorem cos_primeClock_eq_of_reflected_localFactor_modulus_neutral
    {p : ℕ} (hp : 1 < p) {epsilon tau : ℝ} (hepsilon : 0 < epsilon)
    (hmod :
      ‖(1 : ℂ) - (((p : ℝ) ^ (-1 / 2 + epsilon) : ℝ) : ℂ) *
          Complex.exp (((tau * Real.log p : ℝ) : ℂ) * Complex.I)‖ =
        ‖(1 : ℂ) - (((p : ℝ) ^ (-1 / 2 - epsilon) : ℝ) : ℂ) *
          Complex.exp (((tau * Real.log p : ℝ) : ℂ) * Complex.I)‖) :
    Real.cos (tau * Real.log p) =
      ((p : ℝ) ^ (-1 / 2 + epsilon) + (p : ℝ) ^ (-1 / 2 - epsilon)) / 2 := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hne : (p : ℝ) ^ (-1 / 2 - epsilon) ≠
      (p : ℝ) ^ (-1 / 2 + epsilon) := by
    exact ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt hpR (by linarith))
  exact cos_eq_radius_average_of_norm_one_sub_mul_eq hne hmod

/-- Logarithmic prime-window supply produces arbitrarily large primes whose common-clock cosine is
at least `sqrt 2 / 2`. -/
theorem exists_prime_cos_pos_of_supply {tau : ℝ} (htau : 0 < tau)
    (hsupply : PrimeWindowSupply (Real.pi / (2 * tau))) (Q : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ Q < q ∧
      Real.sqrt 2 / 2 ≤ Real.cos (tau * Real.log q) := by
  obtain ⟨X, hX⟩ := hsupply
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨k, hk⟩ := exists_nat_gt
    (max (tau * X / (2 * Real.pi))
      (tau * Real.log ((Q : ℝ) + 1) / (2 * Real.pi)) + 1)
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith
  set b := (2 * Real.pi * (k : ℝ) - Real.pi / 4) / tau with hbdef
  have hmax1 : tau * X / (2 * Real.pi) ≤
      max (tau * X / (2 * Real.pi))
        (tau * Real.log ((Q : ℝ) + 1) / (2 * Real.pi)) := le_max_left _ _
  have hmax2 : tau * Real.log ((Q : ℝ) + 1) / (2 * Real.pi) ≤
      max (tau * X / (2 * Real.pi))
        (tau * Real.log ((Q : ℝ) + 1) / (2 * Real.pi)) := le_max_right _ _
  have hk1 : tau * X / (2 * Real.pi) + 1 < (k : ℝ) := by linarith
  have hk2 : tau * Real.log ((Q : ℝ) + 1) / (2 * Real.pi) + 1 < (k : ℝ) := by
    linarith
  have hbX : X ≤ b := by
    have hk1mul := mul_lt_mul_of_pos_right hk1 h2pi
    rw [add_mul, div_mul_cancel₀ _ h2pi.ne'] at hk1mul
    rw [hbdef, le_div_iff₀ htau]
    nlinarith
  obtain ⟨q, hq, hmem⟩ := hX b hbX
  have hQq : Q < q := by
    have hlogQ : Real.log ((Q : ℝ) + 1) < Real.log q := by
      have hk2mul := mul_lt_mul_of_pos_right hk2 h2pi
      rw [add_mul, div_mul_cancel₀ _ h2pi.ne'] at hk2mul
      have hbQ : Real.log ((Q : ℝ) + 1) < b := by
        rw [hbdef, lt_div_iff₀ htau]
        nlinarith
      linarith [hmem.1]
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
    have h := (Real.log_lt_log_iff (by positivity) hqpos).mp hlogQ
    exact_mod_cast (by linarith : (Q : ℝ) < (q : ℝ))
  refine ⟨q, hq, hQq, ?_⟩
  have hhalf : tau * (Real.pi / (2 * tau)) = Real.pi / 2 := by
    rw [mul_comm (2 : ℝ) tau, ← div_div, ← mul_div_assoc, mul_comm tau (Real.pi / tau),
      div_mul_cancel₀ _ htau.ne']
  have htaub : tau * b = 2 * Real.pi * (k : ℝ) - Real.pi / 4 := by
    rw [hbdef, mul_comm, div_mul_cancel₀ _ htau.ne']
  have h1 : 2 * Real.pi * (k : ℝ) - Real.pi / 4 < tau * Real.log q := by
    have h := mul_lt_mul_of_pos_left hmem.1 htau
    linarith
  have h2 : tau * Real.log q < 2 * Real.pi * (k : ℝ) + Real.pi / 4 := by
    have h := mul_lt_mul_of_pos_left hmem.2 htau
    rw [mul_add, htaub, hhalf] at h
    linarith
  have hper : Real.cos (tau * Real.log q) =
      Real.cos (tau * Real.log q - (k : ℤ) * (2 * Real.pi)) :=
    (Real.cos_sub_int_mul_two_pi _ _).symm
  rw [hper, ← Real.sin_add_pi_div_two]
  apply sin_ge_sqrt_two_div_two
  · push_cast
    linarith
  · push_cast
    linarith

/-- **Common-clock primewise reflection rigidity.** If every prime Euler denominator is
reflected-modulus neutral under one nonzero common clock, then the strip displacement is zero. -/
theorem epsilon_eq_zero_of_cofinal_prime_reflected_modulus_neutral
    {epsilon tau : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (htau : 0 < tau) (hsupply : PrimeWindowSupply (Real.pi / (2 * tau)))
    (hneutral : ∀ p : ℕ, Nat.Prime p →
      ‖(1 : ℂ) - (((p : ℝ) ^ (-1 / 2 + epsilon) : ℝ) : ℂ) *
          Complex.exp (((tau * Real.log p : ℝ) : ℂ) * Complex.I)‖ =
        ‖(1 : ℂ) - (((p : ℝ) ^ (-1 / 2 - epsilon) : ℝ) : ℂ) *
          Complex.exp (((tau * Real.log p : ℝ) : ℂ) * Complex.I)‖) :
    epsilon = 0 := by
  by_contra hepsilon
  have hepsilonPos : 0 < epsilon := lt_of_le_of_ne hepsilon0 (Ne.symm hepsilon)
  have hyplus : 0 < 1 / 2 - epsilon := by linarith
  have hyminus : 0 < 1 / 2 + epsilon := by linarith
  have hplus : Tendsto (fun p : ℕ => (p : ℝ) ^ (-1 / 2 + epsilon)) atTop (nhds 0) := by
    convert (tendsto_rpow_neg_atTop hyplus).comp tendsto_natCast_atTop_atTop using 1
    funext p
    congr 1
    ring
  have hminus : Tendsto (fun p : ℕ => (p : ℝ) ^ (-1 / 2 - epsilon)) atTop (nhds 0) := by
    convert (tendsto_rpow_neg_atTop hyminus).comp tendsto_natCast_atTop_atTop using 1
    funext p
    congr 1
    ring
  have havg : Tendsto (fun p : ℕ =>
      ((p : ℝ) ^ (-1 / 2 + epsilon) + (p : ℝ) ^ (-1 / 2 - epsilon)) / 2)
      atTop (nhds 0) := by
    simpa using (hplus.add hminus).div_const 2
  have hevent : ∀ᶠ p : ℕ in atTop,
      ((p : ℝ) ^ (-1 / 2 + epsilon) + (p : ℝ) ^ (-1 / 2 - epsilon)) / 2 < 1 / 2 := by
    exact (tendsto_order.1 havg).2 (1 / 2) (by norm_num)
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 hevent
  obtain ⟨q, hq, hQq, hcos⟩ := exists_prime_cos_pos_of_supply htau hsupply Q
  have havgq := hQ q hQq.le
  have hcosEq := cos_primeClock_eq_of_reflected_localFactor_modulus_neutral
    hq.one_lt hepsilonPos (hneutral q hq)
  rw [hcosEq] at hcos
  have hsqrt : (1 / 2 : ℝ) < Real.sqrt 2 / 2 := by
    have hsqrt2 : 1 < Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    linarith
  linarith

/-- Bertrand's postulate removes the prime-window hypothesis in the explicit low-clock range. -/
theorem epsilon_eq_zero_of_cofinal_prime_reflected_modulus_neutral_of_log_two_lt_window
    {epsilon tau : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (htau : 0 < tau) (hwindow : Real.log 2 < Real.pi / (2 * tau))
    (hneutral : ∀ p : ℕ, Nat.Prime p →
      ‖(1 : ℂ) - (((p : ℝ) ^ (-1 / 2 + epsilon) : ℝ) : ℂ) *
          Complex.exp (((tau * Real.log p : ℝ) : ℂ) * Complex.I)‖ =
        ‖(1 : ℂ) - (((p : ℝ) ^ (-1 / 2 - epsilon) : ℝ) : ℂ) *
          Complex.exp (((tau * Real.log p : ℝ) : ℂ) * Complex.I)‖) :
    epsilon = 0 :=
  epsilon_eq_zero_of_cofinal_prime_reflected_modulus_neutral hepsilon0 hepsilonHalf htau
    (primeWindowSupply_of_log_two_lt hwindow) hneutral

end

end RHTower
