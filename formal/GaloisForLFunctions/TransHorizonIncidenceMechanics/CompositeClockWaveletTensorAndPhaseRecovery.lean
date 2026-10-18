import GaloisForLFunctions.TransHorizonIncidenceMechanics.ClockScheduleSynthesisAndPrimePowerPhaseRecovery

/-!
# Composite valuation-clock wavelets

Coprime moduli tensor both normalized lag multipliers and Ramanujan coefficients.
On a prime chain `p^b * u`, a transverse lag `L` contributes a common factor to
both clock samples. Choosing `L = lagVisibilityClock u` makes this factor
nonzero, so the difference detects exactly the valuation shells `a` and `a+1`.
These identities have no truncation-horizon restriction.

Normalized wavelets have transverse factor `sieveLagMultiplier u L`;
Ramanujan wavelets have transverse factor `ramanujanLagCoefficient u L`.
The distinction is essential for amplitudes and dipole conservation.
-/

open ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- At any fixed lag, coprime moduli have multiplicative normalized responses. -/
theorem sieveLagMultiplier_mul_of_coprime {q₁ q₂ : ℕ}
    (hc : q₁.Coprime q₂) (h : ℕ) :
    sieveLagMultiplier (q₁ * q₂) h =
      sieveLagMultiplier q₁ h * sieveLagMultiplier q₂ h := by
  have ht : (q₁ / Nat.gcd q₁ h).Coprime (q₂ / Nat.gcd q₂ h) :=
    hc.of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q₁ h))
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q₂ h))
  simp only [sieveLagMultiplier_eq_moebius_totient_quotient]
  rw [hc.mul_gcd, ← Nat.div_mul_div_comm (Nat.gcd_dvd_left q₁ h)
    (Nat.gcd_dvd_left q₂ h), Nat.totient_mul ht]
  simp only [moebiusReal, isMultiplicative_moebius.map_mul_of_coprime ht,
    Int.cast_mul, Nat.cast_mul, div_mul_div_comm]

/-- Multiplying the lag by a factor coprime to the modulus leaves its response unchanged. -/
theorem sieveLagMultiplier_mul_lag_of_coprime {q h k : ℕ} (hc : q.Coprime k) :
    sieveLagMultiplier q (h * k) = sieveLagMultiplier q h := by
  simp only [sieveLagMultiplier_eq_moebius_totient_quotient,
    hc.symm.gcd_mul_right_cancel_right]

/-- Cross-coprimality separates lag factors; the two lags need not be coprime. -/
theorem sieveLagMultiplier_mul_split {q₁ q₂ h₁ h₂ : ℕ}
    (hq : q₁.Coprime q₂) (h₁₂ : q₁.Coprime h₂) (h₂₁ : q₂.Coprime h₁) :
    sieveLagMultiplier (q₁ * q₂) (h₁ * h₂) =
      sieveLagMultiplier q₁ h₁ * sieveLagMultiplier q₂ h₂ := by
  rw [sieveLagMultiplier_mul_of_coprime hq,
    sieveLagMultiplier_mul_lag_of_coprime h₁₂]
  rw [Nat.mul_comm h₁ h₂, sieveLagMultiplier_mul_lag_of_coprime h₂₁]

/-- Ramanujan coefficients are multiplicative in coprime moduli at every lag. -/
theorem ramanujanLagCoefficient_mul_of_coprime {q₁ q₂ : ℕ}
    (hc : q₁.Coprime q₂) (h : ℕ) :
    ramanujanLagCoefficient (q₁ * q₂) h =
      ramanujanLagCoefficient q₁ h * ramanujanLagCoefficient q₂ h := by
  simp only [ramanujanLagCoefficient_eq_totient_mul,
    sieveLagMultiplier_mul_of_coprime hc, Nat.totient_mul hc, Nat.cast_mul]
  ring

/-- Cross-coprimality tensors the unnormalized lag coefficients as well. -/
theorem ramanujanLagCoefficient_mul_split {q₁ q₂ h₁ h₂ : ℕ}
    (hq : q₁.Coprime q₂) (h₁₂ : q₁.Coprime h₂) (h₂₁ : q₂.Coprime h₁) :
    ramanujanLagCoefficient (q₁ * q₂) (h₁ * h₂) =
      ramanujanLagCoefficient q₁ h₁ * ramanujanLagCoefficient q₂ h₂ := by
  simp only [ramanujanLagCoefficient_eq_totient_mul,
    sieveLagMultiplier_mul_split hq h₁₂ h₂₁, Nat.totient_mul hq, Nat.cast_mul]
  ring

/-- A four-lag mixed difference is exactly a tensor product of two lag differences. -/
theorem sieveLagMultiplier_mixed_difference {q₁ q₂ h₁ h₀ k₁ k₀ : ℕ}
    (hq : q₁.Coprime q₂)
    (hk₁ : q₁.Coprime k₁) (hk₀ : q₁.Coprime k₀)
    (hh₁ : q₂.Coprime h₁) (hh₀ : q₂.Coprime h₀) :
    sieveLagMultiplier (q₁ * q₂) (h₁ * k₁) -
        sieveLagMultiplier (q₁ * q₂) (h₁ * k₀) -
        sieveLagMultiplier (q₁ * q₂) (h₀ * k₁) +
        sieveLagMultiplier (q₁ * q₂) (h₀ * k₀) =
      (sieveLagMultiplier q₁ h₁ - sieveLagMultiplier q₁ h₀) *
        (sieveLagMultiplier q₂ k₁ - sieveLagMultiplier q₂ k₀) := by
  rw [sieveLagMultiplier_mul_split hq hk₁ hh₁,
    sieveLagMultiplier_mul_split hq hk₀ hh₁,
    sieveLagMultiplier_mul_split hq hk₁ hh₀,
    sieveLagMultiplier_mul_split hq hk₀ hh₀]
  ring

/-- A normalized clock difference sampled at a fixed transverse lag. -/
def compositeClockWaveletMultiplier (p a q L : ℕ) : ℝ :=
  sieveLagMultiplier q (p ^ a * L) - sieveLagMultiplier q (p ^ (a - 1) * L)

/-- An unnormalized clock difference sampled at a fixed transverse lag. -/
def compositeClockWaveletRamanujan (p a q L : ℕ) : ℝ :=
  ramanujanLagCoefficient q (p ^ a * L) -
    ramanujanLagCoefficient q (p ^ (a - 1) * L)

/-- A composite prime-chain wavelet factors into longitudinal and transverse responses. -/
theorem compositeClockWaveletMultiplier_factor {p a b u L : ℕ}
    (hu : p.Coprime u) (hL : p.Coprime L) :
    compositeClockWaveletMultiplier p a (p ^ b * u) L =
      clockWaveletMultiplier p a (p ^ b) * sieveLagMultiplier u L := by
  unfold compositeClockWaveletMultiplier clockWaveletMultiplier
  rw [sieveLagMultiplier_mul_split (hu.pow_left b) (hL.pow_left b)
      (hu.symm.pow_right a),
    sieveLagMultiplier_mul_split (hu.pow_left b) (hL.pow_left b)
      (hu.symm.pow_right (a - 1))]
  ring

/-- The Ramanujan tensor factor is the transverse Ramanujan coefficient. -/
theorem compositeClockWaveletRamanujan_factor {p a b u L : ℕ}
    (hu : p.Coprime u) (hL : p.Coprime L) :
    compositeClockWaveletRamanujan p a (p ^ b * u) L =
      clockWaveletRamanujan p a (p ^ b) * ramanujanLagCoefficient u L := by
  unfold compositeClockWaveletRamanujan clockWaveletRamanujan
  rw [ramanujanLagCoefficient_mul_split (hu.pow_left b) (hL.pow_left b)
      (hu.symm.pow_right a),
    ramanujanLagCoefficient_mul_split (hu.pow_left b) (hL.pow_left b)
      (hu.symm.pow_right (a - 1))]
  ring

/-- Every visibility clock divides its own modulus. -/
theorem lagVisibilityClock_dvd_self (u : ℕ) : lagVisibilityClock u ∣ u :=
  Nat.div_dvd_of_dvd (Nat.prod_primeFactors_dvd u)

/-- Taking a transverse visibility clock preserves coprimality with the chain prime. -/
theorem coprime_lagVisibilityClock {p u : ℕ} (hu : p.Coprime u) :
    p.Coprime (lagVisibilityClock u) := hu.of_dvd_right (lagVisibilityClock_dvd_self u)

/-- The canonical transverse multiplier is nonzero exactly away from the zero mode. -/
theorem sieveLagMultiplier_at_visibilityClock_ne_zero_iff (u : ℕ) :
    sieveLagMultiplier u (lagVisibilityClock u) ≠ 0 ↔ u ≠ 0 := by
  rw [sieveLagMultiplier_ne_zero_iff, and_iff_left (dvd_refl _)]

/-- The canonical transverse Ramanujan coefficient has the same nonvanishing boundary. -/
theorem ramanujanLagCoefficient_at_visibilityClock_ne_zero_iff (u : ℕ) :
    ramanujanLagCoefficient u (lagVisibilityClock u) ≠ 0 ↔ u ≠ 0 := by
  rw [ramanujanLagCoefficient_ne_zero_iff, and_iff_left (dvd_refl _)]

/-- Exact two-shell support of the prime-power normalized wavelet. -/
theorem clockWaveletMultiplier_prime_pow_ne_zero_iff {p a b : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) :
    clockWaveletMultiplier p a (p ^ b) ≠ 0 ↔ b = a ∨ b = a + 1 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
  by_cases hb : b = a
  · subst b
    rw [clockWaveletMultiplier_prime_pow_self hp ha]
    simp [div_ne_zero hpR hd]
  by_cases hb' : b = a + 1
  · subst b
    rw [clockWaveletMultiplier_prime_pow_succ hp ha]
    simp [div_ne_zero (neg_ne_zero.mpr one_ne_zero) hd]
  have hz : clockWaveletMultiplier p a (p ^ b) = 0 := by
    by_cases hba : b < a
    · exact clockWaveletMultiplier_prime_pow_of_lt hp hba
    · exact clockWaveletMultiplier_prime_pow_of_gt hp (by omega)
  simp [hz, hb, hb']

/-- Exact two-shell support of the prime-power Ramanujan dipole. -/
theorem clockWaveletRamanujan_prime_pow_ne_zero_iff {p a b : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) :
    clockWaveletRamanujan p a (p ^ b) ≠ 0 ↔ b = a ∨ b = a + 1 := by
  have hpa : ((p ^ a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero a hp.ne_zero
  by_cases hb : b = a
  · subst b
    rw [clockWaveletRamanujan_prime_pow_self hp ha]
    exact iff_of_true hpa (Or.inl rfl)
  by_cases hb' : b = a + 1
  · subst b
    rw [clockWaveletRamanujan_prime_pow_succ hp ha]
    exact iff_of_true (neg_ne_zero.mpr hpa) (Or.inr rfl)
  have hz : clockWaveletRamanujan p a (p ^ b) = 0 := by
    by_cases hba : b < a
    · exact clockWaveletRamanujan_prime_pow_of_lt hp hba
    · exact clockWaveletRamanujan_prime_pow_of_gt hp (by omega)
  simp [hz, hb, hb']

/-- At any coprime transverse lag, visibility and longitudinal shell membership
are the two independent conditions for a nonzero normalized response. -/
theorem compositeClockWaveletMultiplier_ne_zero_iff {p a b u L : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (hu : p.Coprime u) (hL : p.Coprime L) :
    compositeClockWaveletMultiplier p a (p ^ b * u) L ≠ 0 ↔
      (b = a ∨ b = a + 1) ∧ u ≠ 0 ∧ lagVisibilityClock u ∣ L := by
  rw [compositeClockWaveletMultiplier_factor hu hL, mul_ne_zero_iff,
    clockWaveletMultiplier_prime_pow_ne_zero_iff hp ha, sieveLagMultiplier_ne_zero_iff]

/-- The same exact support law holds for the unnormalized wavelet. -/
theorem compositeClockWaveletRamanujan_ne_zero_iff {p a b u L : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (hu : p.Coprime u) (hL : p.Coprime L) :
    compositeClockWaveletRamanujan p a (p ^ b * u) L ≠ 0 ↔
      (b = a ∨ b = a + 1) ∧ u ≠ 0 ∧ lagVisibilityClock u ∣ L := by
  rw [compositeClockWaveletRamanujan_factor hu hL, mul_ne_zero_iff,
    clockWaveletRamanujan_prime_pow_ne_zero_iff hp ha, ramanujanLagCoefficient_ne_zero_iff]

/-- At the canonical transverse clock the only remaining support condition is the shell. -/
theorem compositeClockWaveletMultiplier_at_clock_ne_zero_iff {p a b u : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (hu : p.Coprime u) (hu0 : u ≠ 0) :
    compositeClockWaveletMultiplier p a (p ^ b * u) (lagVisibilityClock u) ≠ 0 ↔
      b = a ∨ b = a + 1 := by
  rw [compositeClockWaveletMultiplier_ne_zero_iff hp ha hu (coprime_lagVisibilityClock hu)]
  simp [hu0]

/-- Ramanujan shell detection at the canonical transverse clock. -/
theorem compositeClockWaveletRamanujan_at_clock_ne_zero_iff {p a b u : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (hu : p.Coprime u) (hu0 : u ≠ 0) :
    compositeClockWaveletRamanujan p a (p ^ b * u) (lagVisibilityClock u) ≠ 0 ↔
      b = a ∨ b = a + 1 := by
  rw [compositeClockWaveletRamanujan_ne_zero_iff hp ha hu (coprime_lagVisibilityClock hu)]
  simp [hu0]

/-- The canonical normalized wavelet detects the exact two adjacent valuations
of every nonzero integer, including moduli with arbitrarily many prime factors. -/
theorem compositeClockWaveletMultiplier_valuation_recovery {p a q : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (hq : q ≠ 0) :
    compositeClockWaveletMultiplier p a q (lagVisibilityClock (ordCompl[p] q)) ≠ 0 ↔
      q.factorization p = a ∨ q.factorization p = a + 1 := by
  have h := compositeClockWaveletMultiplier_at_clock_ne_zero_iff
    (b := q.factorization p) hp ha (Nat.coprime_ordCompl hp hq) (Nat.ordCompl_pos p hq).ne'
  rwa [Nat.ordProj_mul_ordCompl_eq_self] at h

/-- Canonical valuation recovery for the Ramanujan wavelet. -/
theorem compositeClockWaveletRamanujan_valuation_recovery {p a q : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (hq : q ≠ 0) :
    compositeClockWaveletRamanujan p a q (lagVisibilityClock (ordCompl[p] q)) ≠ 0 ↔
      q.factorization p = a ∨ q.factorization p = a + 1 := by
  have h := compositeClockWaveletRamanujan_at_clock_ne_zero_iff
    (b := q.factorization p) hp ha (Nat.coprime_ordCompl hp hq) (Nat.ordCompl_pos p hq).ne'
  rwa [Nat.ordProj_mul_ordCompl_eq_self] at h

/-- The equal and opposite Ramanujan poles remain a dipole on every composite chain. -/
theorem compositeClockWaveletRamanujan_dipole_cancel {p a u L : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (hu : p.Coprime u) (hL : p.Coprime L) :
    compositeClockWaveletRamanujan p a (p ^ a * u) L +
      compositeClockWaveletRamanujan p a (p ^ (a + 1) * u) L = 0 := by
  rw [compositeClockWaveletRamanujan_factor hu hL,
    compositeClockWaveletRamanujan_factor hu hL, ← add_mul,
    clockWaveletRamanujan_prime_pow_dipole_cancel hp ha, zero_mul]

/-- Calibrating by the nonzero transverse coefficient recovers the signed
prime-power response, including its exact amplitude and its zero region. -/
theorem compositeClockWaveletRamanujan_calibrated {p a b u : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (hu : p.Coprime u) (hu0 : u ≠ 0) :
    compositeClockWaveletRamanujan p a (p ^ b * u) (lagVisibilityClock u) /
        ramanujanLagCoefficient u (lagVisibilityClock u) =
      if b = a then ((p ^ a : ℕ) : ℝ)
      else if b = a + 1 then -((p ^ a : ℕ) : ℝ) else 0 := by
  rw [compositeClockWaveletRamanujan_factor hu (coprime_lagVisibilityClock hu),
    mul_div_cancel_right₀ _
      ((ramanujanLagCoefficient_at_visibilityClock_ne_zero_iff u).mpr hu0)]
  split_ifs with hb hb'
  · subst b
    exact clockWaveletRamanujan_prime_pow_self hp ha
  · subst b
    exact clockWaveletRamanujan_prime_pow_succ hp ha
  · by_cases hba : b < a
    · exact clockWaveletRamanujan_prime_pow_of_lt hp hba
    · exact clockWaveletRamanujan_prime_pow_of_gt hp (by omega)

/-- The calibrated canonical response distinguishes the two adjacent valuation
shells by their signs, for every nonzero composite or prime-power modulus. -/
theorem compositeClockWaveletRamanujan_valuation_phase_recovery {p a q : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (hq : q ≠ 0) :
    compositeClockWaveletRamanujan p a q (lagVisibilityClock (ordCompl[p] q)) /
        ramanujanLagCoefficient (ordCompl[p] q) (lagVisibilityClock (ordCompl[p] q)) =
      if q.factorization p = a then ((p ^ a : ℕ) : ℝ)
      else if q.factorization p = a + 1 then -((p ^ a : ℕ) : ℝ) else 0 := by
  have h := compositeClockWaveletRamanujan_calibrated (b := q.factorization p)
    hp ha (Nat.coprime_ordCompl hp hq) (Nat.ordCompl_pos p hq).ne'
  rwa [Nat.ordProj_mul_ordCompl_eq_self] at h

/-- Mixed clock difference along two multiplicative lag directions. -/
def clockTensorMultiplier (p r a c q : ℕ) : ℝ :=
  sieveLagMultiplier q (p ^ a * r ^ c) -
    sieveLagMultiplier q (p ^ a * r ^ (c - 1)) -
    sieveLagMultiplier q (p ^ (a - 1) * r ^ c) +
    sieveLagMultiplier q (p ^ (a - 1) * r ^ (c - 1))

/-- Independent prime-power directions produce an exact product of wavelets. -/
theorem clockTensorMultiplier_prime_powers {p r a b c d : ℕ} (hpr : p.Coprime r) :
    clockTensorMultiplier p r a c (p ^ b * r ^ d) =
      clockWaveletMultiplier p a (p ^ b) * clockWaveletMultiplier r c (r ^ d) := by
  unfold clockTensorMultiplier clockWaveletMultiplier
  exact sieveLagMultiplier_mixed_difference ((hpr.pow_left b).pow_right d)
    ((hpr.pow_left b).pow_right c) ((hpr.pow_left b).pow_right (c - 1))
    ((hpr.symm.pow_left d).pow_right a) ((hpr.symm.pow_left d).pow_right (a - 1))

/-- Two independent clocks isolate the four corners of an adjacent valuation rectangle. -/
theorem clockTensorMultiplier_prime_powers_ne_zero_iff {p r a b c d : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    clockTensorMultiplier p r a c (p ^ b * r ^ d) ≠ 0 ↔
      (b = a ∨ b = a + 1) ∧ (d = c ∨ d = c + 1) := by
  rw [clockTensorMultiplier_prime_powers ((Nat.coprime_primes hp hr).mpr hpr),
    mul_ne_zero_iff, clockWaveletMultiplier_prime_pow_ne_zero_iff hp ha,
    clockWaveletMultiplier_prime_pow_ne_zero_iff hr hc]

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
