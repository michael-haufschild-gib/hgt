import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Saturation.PrimeReturns
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Saturation.PhaseLaw

/-! # Exact fibers of an elementary prime clock -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open _root_.RHTower.PrimeCoShift

/-- One full turn of the block of D quanta of p. -/
def primeClockTime (p : Nat.Primes) (D : ℕ+) := cyclicTime D p 0

theorem primeClock_phase_one (p : Nat.Primes) (D n : ℕ+) :
    occupationPhase (primeClockTime p D) n = 1 ↔
      ∃ e : ℕ, n = primeRayLabel p e ∧ D.val ∣ e := by
  change (⟨_,_⟩ : Circle) = 1 ↔ _
  rw [Subtype.ext_iff]
  change splitPhase (cyclicTime D p 0) n = 1 ↔ _
  simpa only [pow_one,clockDenominator,zero_add,mul_one,one_mul] using
    (prime_clock_return_iff D p 0 n (k := 1) Nat.zero_lt_one)

private theorem positive_phase (p : Nat.Primes) (D n : ℕ+) :
    (occupationPhase (primeClockTime p D) n : ℂ) =
      (Complex.exp (((energy n/((D.val:ℝ)*energy (primePNat p)):ℝ):ℂ)*
        (2*(Real.pi:ℂ)*Complex.I)))⁻¹ := by
  change splitPhase (cyclicTime D p 0) n = _
  rw [splitPhase_eq_exp,← Complex.exp_neg,cyclicTime_eq_pi_div]
  congr 1
  simp only [clockDenominator,zero_add,mul_one]
  push_cast
  ring

private theorem exp_turn_eq (x y : ℝ) :
    Complex.exp ((x:ℂ)*(2*(Real.pi:ℂ)*Complex.I)) =
      Complex.exp ((y:ℂ)*(2*(Real.pi:ℂ)*Complex.I)) ↔ ∃ z : ℤ, x = y+z := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  have hc : (2*(Real.pi:ℂ)*Complex.I) ≠ 0 := mul_ne_zero
    (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  apply exists_congr
  intro z
  rw [← add_mul]
  constructor
  · intro h
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_add,Complex.ofReal_intCast] using mul_right_cancel₀ hc h
  · intro h
    rw [h,Complex.ofReal_add,Complex.ofReal_intCast]

private theorem exponent_energy_injective : Function.Injective energy := by
  intro a b hab
  apply PNat.coe_injective
  apply Nat.cast_injective (R := ℝ)
  have he := congrArg Real.exp hab
  change Real.exp (Real.log (a.val:ℝ)) = Real.exp (Real.log (b.val:ℝ)) at he
  rwa [Real.exp_log (Nat.cast_pos.mpr a.pos),Real.exp_log (Nat.cast_pos.mpr b.pos)] at he

/-- Equal phases above a given label are precisely its translates by whole clock blocks. -/
theorem primeClock_alias_iff (p : Nat.Primes) (D a b : ℕ+) (hab : a ≤ b) :
    occupationPhase (primeClockTime p D) a = occupationPhase (primeClockTime p D) b ↔
      ∃ k : ℕ, b = a*primeRayLabel p (D.val*k) := by
  let L := (D.val:ℝ)*energy (primePNat p)
  have hL : 0 < L := mul_pos (Nat.cast_pos.mpr D.pos) (prime_energy_pos p)
  have hm : energy a ≤ energy b := Real.log_le_log (Nat.cast_pos.mpr a.pos)
    (by exact_mod_cast (show a.val ≤ b.val from hab))
  have coe_iff (x y : Circle) : x = y ↔ (x:ℂ) = (y:ℂ) :=
    ⟨fun h => congrArg (fun u : Circle => (u:ℂ)) h,Subtype.ext⟩
  rw [eq_comm,coe_iff]
  rw [positive_phase,positive_phase,inv_inj,exp_turn_eq]
  change (∃ z : ℤ, energy b/L = energy a/L+z) ↔ _
  constructor
  · rintro ⟨z,hz⟩
    have hzr : (0:ℝ) ≤ z := by linarith only [div_le_div_of_nonneg_right hm hL.le,hz]
    have hz₀ : (0:ℤ) ≤ z := by exact_mod_cast hzr
    refine ⟨z.toNat,exponent_energy_injective ?_⟩
    have hz' : (z.toNat:ℝ) = z := by exact_mod_cast Int.toNat_of_nonneg hz₀
    have he := (div_eq_iff hL.ne').mp hz
    rw [add_mul,div_mul_cancel₀ _ hL.ne'] at he
    rw [energy_mul,energy_primeRayLabel,Nat.cast_mul,hz',he]
    dsimp only [L]
    ring
  · rintro ⟨k,rfl⟩
    refine ⟨(k:ℤ),?_⟩
    rw [energy_mul,energy_primeRayLabel,Nat.cast_mul,Int.cast_natCast,add_div]
    congr 1
    apply (div_eq_iff hL.ne').mpr
    dsimp only [L]
    ring

/-- Distinct labels in one fiber cannot both lie below the first whole clock block. -/
theorem primeClock_separates_below (p : Nat.Primes) (D a b : ℕ+)
    (ha : a.val < p.val^D.val) (hb : b.val < p.val^D.val) :
    occupationPhase (primeClockTime p D) a = occupationPhase (primeClockTime p D) b ↔ a = b := by
  have ordered (x y : ℕ+) (hxy : x ≤ y) (hy : y.val < p.val^D.val)
      (he : occupationPhase (primeClockTime p D) x = occupationPhase (primeClockTime p D) y) : x = y := by
    obtain ⟨k,hk⟩ := (primeClock_alias_iff p D x y hxy).mp he
    cases k with
    | zero => simpa [primeRayLabel] using hk.symm
    | succ k =>
      have hd : p.val^D.val ∣ y.val := by
        rw [hk]
        change p.val^D.val ∣ x.val*p.val^(D.val*(k+1))
        rw [Nat.mul_succ,pow_add]
        exact dvd_mul_left _ _ |>.trans (dvd_mul_left _ _)
      exact False.elim ((not_le.mpr hy) (Nat.le_of_dvd y.pos hd))
  constructor
  · intro h
    rcases le_total a b with hab | hba
    · exact ordered a b hab hb h
    · exact (ordered b a hba ha h.symm).symm
  · rintro rfl
    rfl

#print axioms primeClock_phase_one
#print axioms primeClock_alias_iff
#print axioms primeClock_separates_below

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
