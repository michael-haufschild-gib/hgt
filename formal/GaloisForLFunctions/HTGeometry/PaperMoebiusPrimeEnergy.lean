import GaloisForLFunctions.HTGeometry.PaperMoebiusPrimeTransport
import GaloisForLFunctions.HTGeometry.PaperGammaHankelPolarization

/-!
# Native Gamma--Hankel energy of the actual Möbius prime action

Real coefficients are read from the proved arithmetic transport itself.
Its finite Laplace source and full energy retain the literal p-free mixed
term. The exact minimizing time is algebraic source data; no assertion of
analytic admissibility or asymptotic cancellation is built into it.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

noncomputable section

/-- The actual p-free projection, with native energy indexing n ↦ n+1. -/
def paperPrimeFreeRealCoefficient (p : Nat.Primes) (n : ℕ) : ℝ :=
  ((paperPrimeConstantProjection p
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) (n + 1)).re

/-- Real coefficients are extracted from the actual scalar action on Möbius. -/
def paperMoebiusPrimeRealTransport (p : Nat.Primes) (t : ℝ) (n : ℕ) : ℝ :=
  (paperMoebiusPrimeTransport p (t : ℂ) (n + 1)).re

theorem paperPrimeFreeRealCoefficient_apply (p : Nat.Primes) (n : ℕ) :
    paperPrimeFreeRealCoefficient p n =
      if (p : ℕ) ∣ n + 1 then 0 else shiftedMobiusRealCoefficient n := by
  rw [paperPrimeFreeRealCoefficient, paperPrimeConstantProjection_apply]
  split_ifs <;> simp [shiftedMobiusRealCoefficient, ArithmeticFunction.intCoe_apply]

/-- Literal arithmetic specialization has the exact real source decomposition. -/
theorem paperMoebiusPrimeRealTransport_eq (p : Nat.Primes) (t : ℝ) :
    paperMoebiusPrimeRealTransport p t =
      fun n => shiftedMobiusRealCoefficient n - t * paperPrimeFreeRealCoefficient p n := by
  funext n
  rw [paperMoebiusPrimeRealTransport, paperMoebiusPrimeTransport_apply,
    paperPrimeFreeRealCoefficient_apply]
  by_cases hn : (p : ℕ) ∣ n + 1
  · simp [hn, shiftedMobiusRealCoefficient]
  · simp [hn, shiftedMobiusRealCoefficient, Complex.mul_re]
    ring

/-- The finite Laplace source retains every original signed coefficient. -/
theorem paperMoebiusPrimeRealTransport_laplace (p : Nat.Primes) (t : ℝ) (N : ℕ) (x : ℝ) :
    finiteRealLaplacePencil (paperMoebiusPrimeRealTransport p t) N x =
      finiteMobiusLaplacePencil N x -
        t * finiteRealLaplacePencil (paperPrimeFreeRealCoefficient p) N x := by
  rw [paperMoebiusPrimeRealTransport_eq]
  simp only [finiteRealLaplacePencil, finiteMobiusLaplacePencil, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

/-- Native Gamma--Hankel energy of the actual transported prefix. -/
def paperMoebiusPrimeEnergy (p : Nat.Primes) (t : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  finiteGammaHankelEnergy (paperMoebiusPrimeRealTransport p t) N r

/-- Full signed mixed energy with the p-free projection. -/
def paperMoebiusPrimeEnergyCross (p : Nat.Primes) (N : ℕ) (r : ℝ) : ℝ :=
  paperGammaHankelPairing shiftedMobiusRealCoefficient (paperPrimeFreeRealCoefficient p) N r

/-- No off-diagonal term is discarded in the exact transport law. -/
theorem paperMoebiusPrimeEnergy_eq (p : Nat.Primes) (t : ℝ) (N : ℕ) (r : ℝ) :
    paperMoebiusPrimeEnergy p t N r = finiteMobiusGammaHankelEnergy N r -
      2 * t * paperMoebiusPrimeEnergyCross p N r +
        t ^ 2 * finiteGammaHankelEnergy (paperPrimeFreeRealCoefficient p) N r := by
  rw [paperMoebiusPrimeEnergy, paperMoebiusPrimeRealTransport_eq]
  exact paperGammaHankelEnergy_sub _ _ _ _ _

/-- Exact time-zero recovery of the original native Möbius energy. -/
@[simp] theorem paperMoebiusPrimeEnergy_zero (p : Nat.Primes) (N : ℕ) (r : ℝ) :
    paperMoebiusPrimeEnergy p 0 N r = finiteMobiusGammaHankelEnergy N r := by
  simp [paperMoebiusPrimeEnergy_eq]

/-- Signed source data determine the unconstrained minimizing time. -/
def paperMoebiusPrimeEnergyOptimalTime (p : Nat.Primes) (N : ℕ) (r : ℝ) : ℝ :=
  paperMoebiusPrimeEnergyCross p N r /
    finiteGammaHankelEnergy (paperPrimeFreeRealCoefficient p) N r

/-- Minimization is proved for the literal transported source, including zero cutoffs. -/
theorem paperMoebiusPrimeEnergy_minimizer (p : Nat.Primes) (N : ℕ)
    (r : {r : ℝ // 0 < r}) (t : ℝ) :
    paperMoebiusPrimeEnergy p (paperMoebiusPrimeEnergyOptimalTime p N r) N r ≤
      paperMoebiusPrimeEnergy p t N r := by
  simp only [paperMoebiusPrimeEnergy, paperMoebiusPrimeRealTransport_eq]
  exact paperGammaHankelEnergy_minimizer _ _ _ _ _

/-- Exact minimum value, with the native zero-energy case already paid. -/
theorem paperMoebiusPrimeEnergy_minimum_value (p : Nat.Primes) (N : ℕ)
    (r : {r : ℝ // 0 < r}) :
    paperMoebiusPrimeEnergy p (paperMoebiusPrimeEnergyOptimalTime p N r) N r =
      finiteMobiusGammaHankelEnergy N r - paperMoebiusPrimeEnergyCross p N r ^ 2 /
        finiteGammaHankelEnergy (paperPrimeFreeRealCoefficient p) N r := by
  rw [paperMoebiusPrimeEnergy, paperMoebiusPrimeRealTransport_eq,
    paperGammaHankelEnergy_complete_square]
  simp only [paperMoebiusPrimeEnergyOptimalTime, paperMoebiusPrimeEnergyCross,
    finiteMobiusGammaHankelEnergy, sub_self, zero_pow (NeZero.ne _), mul_zero, add_zero]

/-- Improvement is precisely a signed mixed-term comparison. -/
theorem paperMoebiusPrimeEnergy_improves_iff (p : Nat.Primes) (t : ℝ) (N : ℕ) (r : ℝ) :
    paperMoebiusPrimeEnergy p t N r ≤ finiteMobiusGammaHankelEnergy N r ↔
      t ^ 2 * finiteGammaHankelEnergy (paperPrimeFreeRealCoefficient p) N r ≤
        2 * t * paperMoebiusPrimeEnergyCross p N r := by
  rw [paperMoebiusPrimeEnergy_eq]
  constructor <;> intro h <;> linarith

/-- Opposite source times retain the exact nonnegative quadratic cost. -/
theorem paperMoebiusPrimeEnergy_opposite (p : Nat.Primes) (t : ℝ) (N : ℕ) (r : ℝ) :
    paperMoebiusPrimeEnergy p t N r + paperMoebiusPrimeEnergy p (-t) N r =
      2 * finiteMobiusGammaHankelEnergy N r +
        2 * t ^ 2 * finiteGammaHankelEnergy (paperPrimeFreeRealCoefficient p) N r := by
  rw [paperMoebiusPrimeEnergy_eq, paperMoebiusPrimeEnergy_eq]
  ring

/-- At least one of the times ±1 keeps at least the original source energy. -/
theorem paperMoebiusPrimeEnergy_one_or_neg_one (p : Nat.Primes) (N : ℕ)
    (r : {r : ℝ // 0 < r}) :
    finiteMobiusGammaHankelEnergy N r ≤ paperMoebiusPrimeEnergy p 1 N r ∨
      finiteMobiusGammaHankelEnergy N r ≤ paperMoebiusPrimeEnergy p (-1) N r := by
  have he := paperMoebiusPrimeEnergy_opposite p 1 N r
  have hp := finiteGammaHankelEnergy_nonneg (paperPrimeFreeRealCoefficient p) N r.property
  by_contra h
  push Not at h
  norm_num only [one_pow, mul_one] at he
  linarith

end

end GaloisForLFunctions.HTGeometry
