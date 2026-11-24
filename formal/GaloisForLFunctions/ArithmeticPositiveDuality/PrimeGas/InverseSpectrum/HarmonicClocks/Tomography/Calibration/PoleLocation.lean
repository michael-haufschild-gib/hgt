import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Calibration.LaurentReadout
import GaloisForLFunctions.RHTower.HeatMixedMomentDeterminacy

/-! # Complex localization by two Laurent-coefficient readings -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- The excess of two measured leading coefficients at a regular or singular point. -/
def coefficientCoordinate (p : Nat.Primes) (D : ℕ+) (z : ℂ) : ℂ :=
  meromorphicTrailingCoeffAt (continuedClockReturn p D) z /
    meromorphicTrailingCoeffAt (continuedClockReturn p (D+D)) z - 1

private theorem clock_power (p : Nat.Primes) (D E : ℕ+) (z : ℂ) :
    (heat z (primeRayLabel p D.val))^E.val =
      Complex.exp (-(Real.log p.val:ℂ) * ((D.val:ℂ)*(E.val:ℂ)*z)) := by
  rw [heat,energy_primeRayLabel,← Complex.exp_nat_mul]
  congr 1
  simp only [energy,_root_.RHTower.PrimeCoShift.primePNat_coe,Complex.ofReal_mul,Complex.ofReal_natCast]
  ring

/-- Ratios at two distinct primes locate any common pole, without entering its multiplicity
or knowing its real part in advance. -/
theorem coefficientCoordinate_pair_injective (p q : Nat.Primes) (hpq : p ≠ q) (D E : ℕ+) :
    Function.Injective (fun z : {s : ℂ // 0 < s.re} =>
      (coefficientCoordinate p D z.val,coefficientCoordinate q E z.val)) := by
  intro z w he
  have hp := congrArg Prod.fst he
  have hq := congrArg Prod.snd he
  change coefficientCoordinate p D z.val = coefficientCoordinate p D w.val at hp
  change coefficientCoordinate q E z.val = coefficientCoordinate q E w.val at hq
  rw [coefficientCoordinate,coefficientCoordinate,returnCoefficient_excess p D z.property,
    returnCoefficient_excess p D w.property] at hp
  rw [coefficientCoordinate,coefficientCoordinate,returnCoefficient_excess q E z.property,
    returnCoefficient_excess q E w.property] at hq
  apply Subtype.ext
  apply mul_left_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.mpr D.ne_zero) (Nat.cast_ne_zero.mpr E.ne_zero)
    : (D.val:ℂ)*(E.val:ℂ) ≠ 0)
  apply _root_.RHTower.prime_heat_coordinate_pair_injective p.property q.property (fun h => hpq (Subtype.ext h))
  apply Prod.ext
  · change Complex.exp _ = Complex.exp _
    simpa only [clock_power] using congrArg (fun x : ℂ => x^E.val) hp
  · change Complex.exp _ = Complex.exp _
    simpa only [clock_power,mul_comm (E.val:ℂ) (D.val:ℂ)] using congrArg (fun x : ℂ => x^D.val) hq

#print axioms coefficientCoordinate_pair_injective

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
