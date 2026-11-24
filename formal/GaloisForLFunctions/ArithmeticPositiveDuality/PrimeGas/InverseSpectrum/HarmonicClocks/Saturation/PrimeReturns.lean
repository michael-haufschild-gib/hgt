import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.PrimeClock

/-! # Arithmetic classification of exact phase returns -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open _root_.RHTower.PrimeCoShift

/-- Denominator of the clock rotation in units of the elementary prime. -/
def clockDenominator (r : ℕ+) (j : ℕ) : ℕ := r.val*(j+1)

theorem clockDenominator_pos (r : ℕ+) (j : ℕ) : 0 < clockDenominator r j :=
  Nat.mul_pos r.pos (Nat.succ_pos j)

theorem cyclicTime_eq_pi_div (r : ℕ+) (p : Nat.Primes) (j : ℕ) :
    cyclicTime r p j = Real.pi/((clockDenominator r j:ℝ)*energy (primePNat p)) := by
  simp only [cyclicTime,resonantTime,primeZeroSpacing,clockDenominator,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp [(prime_energy_pos p).ne',show (j:ℝ)+1 ≠ 0 by positivity,
    show (r.val:ℝ) ≠ 0 by exact_mod_cast r.ne_zero]

private theorem full_turn_iff (x : ℝ) :
    Complex.exp ((x:ℂ)*(2*(Real.pi:ℂ)*Complex.I)) = 1 ↔ ∃ a : ℤ, x = a := by
  rw [Complex.exp_eq_one_iff]
  have hn : (2*(Real.pi:ℂ)*Complex.I) ≠ 0 := mul_ne_zero
    (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  constructor
  · rintro ⟨a,h⟩
    refine ⟨a,Complex.ofReal_injective ?_⟩
    simpa only [Complex.ofReal_intCast] using mul_right_cancel₀ hn h
  · rintro ⟨a,rfl⟩
    exact ⟨a,by simp only [Complex.ofReal_intCast]⟩

private theorem clock_return_energy (r : ℕ+) (p : Nat.Primes) (j : ℕ) (n : ℕ+) (k : ℕ) :
    splitPhase (cyclicTime r p j) n^k = 1 ↔
      ∃ a : ℕ, (k:ℝ)*energy n = a*((clockDenominator r j:ℝ)*energy (primePNat p)) := by
  let D := clockDenominator r j
  let L := energy (primePNat p)
  have hL : 0 < (D:ℝ)*L := mul_pos (Nat.cast_pos.mpr (clockDenominator_pos r j)) (prime_energy_pos p)
  let x := (k:ℝ)*energy n/((D:ℝ)*L)
  have he : splitPhase (cyclicTime r p j) n^k = (Complex.exp ((x:ℂ)*(2*(Real.pi:ℂ)*Complex.I)))⁻¹ := by
    rw [splitPhase_eq_exp,← Complex.exp_nat_mul,← Complex.exp_neg,cyclicTime_eq_pi_div]
    congr 1
    dsimp only [x,D,L]
    push_cast
    ring
  rw [he,inv_eq_one,full_turn_iff]
  constructor
  · rintro ⟨z,hz⟩
    have hpos : 0 ≤ x := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast n.pos))) hL.le
    have hzr : (0:ℝ) ≤ z := hz ▸ hpos
    have hz₀ : (0:ℤ) ≤ z := by exact_mod_cast hzr
    refine ⟨z.toNat,?_⟩
    have hz' : (z.toNat:ℝ) = z := by exact_mod_cast Int.toNat_of_nonneg hz₀
    rw [hz']
    exact (div_eq_iff hL.ne').mp hz
  · rintro ⟨a,ha⟩
    exact ⟨(a:ℤ),by exact_mod_cast (div_eq_iff hL.ne').mpr ha⟩

/-- A periodic phase belongs to a pure prime occupation. Its harmonic returns record the divisors of its exponent. -/
theorem prime_clock_return_iff (r : ℕ+) (p : Nat.Primes) (j : ℕ) (n : ℕ+) {k : ℕ} (hk : 0 < k) :
    splitPhase (cyclicTime r p j) n^k = 1 ↔
      ∃ h : ℕ, n = primeRayLabel p h ∧ clockDenominator r j ∣ k*h := by
  let D := clockDenominator r j
  have hp := prime_energy_pos p
  rw [clock_return_energy]
  constructor
  · rintro ⟨a,ha⟩
    have he : Real.log (((n.val^k:ℕ):ℝ)) = Real.log ((((p.val)^(D*a):ℕ):ℝ)) := by
      simp only [Nat.cast_pow,Real.log_pow,Nat.cast_mul]
      change (k:ℝ)*energy n = ((D:ℝ)*a)*energy (primePNat p)
      linear_combination ha
    have hn₀ : (0:ℝ) < ((n.val^k:ℕ):ℝ) := Nat.cast_pos.mpr (pow_pos n.pos k)
    have hp₀ : (0:ℝ) < ((p.val^(D*a):ℕ):ℝ) := Nat.cast_pos.mpr (pow_pos p.property.pos (D*a))
    have he' := congrArg Real.exp he
    rw [Real.exp_log hn₀,Real.exp_log hp₀] at he'
    have hn : n.val^k = p.val^(D*a) := Nat.cast_injective (R := ℝ) he'
    have hd : n.val ∣ p.val^(D*a) := hn ▸ dvd_pow_self n.val hk.ne'
    obtain ⟨h,_,hh⟩ := (Nat.dvd_prime_pow p.property).mp hd
    have hname : n = primeRayLabel p h := PNat.coe_injective hh
    refine ⟨h,hname,a,?_⟩
    rw [hname,energy_primeRayLabel] at ha
    have ht : (((k*h:ℕ):ℝ))*energy (primePNat p) = (((D*a:ℕ):ℝ))*energy (primePNat p) := by
      push_cast
      linear_combination ha
    exact_mod_cast mul_right_cancel₀ hp.ne' ht
  · rintro ⟨h,rfl,a,ha⟩
    refine ⟨a,?_⟩
    rw [energy_primeRayLabel,← mul_assoc,← Nat.cast_mul,ha,Nat.cast_mul]
    ring

#print axioms clockDenominator_pos
#print axioms cyclicTime_eq_pi_div
#print axioms prime_clock_return_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
