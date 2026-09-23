import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz
import GaloisForLFunctions.RHTower.SoninSemilocalTwoPlaceAssociation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Gamma-damped prime incidence in the even-factorial jet metric

The usual factorial Fock norm makes a prime raw-jet column grow like
`exp ((log p)^(2 : ℕ))`.  The even-factorial metric instead has the exact column identity

`sum_j (log p)^(2j) / (2j)! = cosh (log p)`.

The canonical doubled-frequency Gamma diagonal is at most `sqrt 2 / p`, so the complete
prime-to-jet incidence energy is bounded by `sqrt 2 * p^(-2x)`.  It is therefore summable for
every source point `x > 1/2`.

This is an unconditional all-prime Hilbert--Schmidt energy theorem.  It does not assert that the
even-factorial completion transports the Gamma clock, makes the completed Weil form positive, or
proves RH.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Squared matrix coefficient of the Gamma-damped prime raw-jet incidence after normalizing the
`j`-th raw derivative by `sqrt ((2j)!)`. -/
def primeLaplaceEvenFactorialJetEnergy
    (x : ℝ) (p : Nat.Primes) (j : ℕ) : ℝ :=
  semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
    (p : ℝ) ^ (-2 * x) *
      primeLogSupport p ^ (2 * j) / ((2 * j).factorial : ℝ)

lemma primeLaplaceEvenFactorialJetEnergy_nonneg
    (x : ℝ) (p : Nat.Primes) (j : ℕ) :
    0 ≤ primeLaplaceEvenFactorialJetEnergy x p j := by
  unfold primeLaplaceEvenFactorialJetEnergy
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg
        (Real.rpow_nonneg (Real.cosh_pos _).le _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (pow_nonneg (primeLogSupport_pos p).le _))
    (Nat.cast_nonneg _)

/-- The even-factorial energy of one prime column sums exactly to the Gamma diagonal times
`p^(-2x) cosh (log p)`. -/
theorem hasSum_primeLaplaceEvenFactorialJetEnergy
    (x : ℝ) (p : Nat.Primes) :
    HasSum (primeLaplaceEvenFactorialJetEnergy x p)
      (semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        (p : ℝ) ^ (-2 * x) * Real.cosh (primeLogSupport p)) := by
  have h := (Real.hasSum_cosh (primeLogSupport p)).mul_left
    (semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
      (p : ℝ) ^ (-2 * x))
  refine h.congr ?_
  intro j
  unfold primeLaplaceEvenFactorialJetEnergy
  ring

theorem tsum_primeLaplaceEvenFactorialJetEnergy
    (x : ℝ) (p : Nat.Primes) :
    ∑' j, primeLaplaceEvenFactorialJetEnergy x p j =
      semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        (p : ℝ) ^ (-2 * x) * Real.cosh (primeLogSupport p) :=
  (hasSum_primeLaplaceEvenFactorialJetEnergy x p).tsum_eq

lemma cosh_primeLogSupport_le (p : Nat.Primes) :
    Real.cosh (primeLogSupport p) ≤ (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.one_le
  have hinv_le_one : ((p : ℝ) : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hp0).2 hp1
  rw [primeLogSupport, Real.cosh_log hp0]
  linarith

/-- Gamma decay cancels the linear growth of the even-factorial coherent-column energy. -/
lemma semilocalArchimedeanCharacteristic_mul_cosh_primeLogSupport_le
    (p : Nat.Primes) :
    semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        Real.cosh (primeLogSupport p) ≤ Real.sqrt 2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hchar :=
    semilocalArchimedeanCharacteristic_two_mul_le_sqrtTwo_mul_exp_neg
      (primeLogSupport p)
  have hexp : Real.exp (-primeLogSupport p) = ((p : ℝ))⁻¹ := by
    rw [primeLogSupport, Real.exp_neg, Real.exp_log hp0]
  rw [hexp] at hchar
  calc
    semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        Real.cosh (primeLogSupport p) ≤
      (Real.sqrt 2 * (p : ℝ)⁻¹) * Real.cosh (primeLogSupport p) := by
        gcongr
    _ ≤ (Real.sqrt 2 * (p : ℝ)⁻¹) * (p : ℝ) := by
      gcongr
      exact cosh_primeLogSupport_le p
    _ = Real.sqrt 2 := by field_simp

theorem primeLaplaceEvenFactorialJetTotalEnergy_le
    (x : ℝ) (p : Nat.Primes) :
    semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        (p : ℝ) ^ (-2 * x) * Real.cosh (primeLogSupport p) ≤
      Real.sqrt 2 * (p : ℝ) ^ (-2 * x) := by
  calc
    semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        (p : ℝ) ^ (-2 * x) * Real.cosh (primeLogSupport p) =
      (p : ℝ) ^ (-2 * x) *
        (semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
          Real.cosh (primeLogSupport p)) := by ring
    _ ≤ (p : ℝ) ^ (-2 * x) * Real.sqrt 2 := by
      gcongr
      exact semilocalArchimedeanCharacteristic_mul_cosh_primeLogSupport_le p
    _ = Real.sqrt 2 * (p : ℝ) ^ (-2 * x) := by ring

theorem summable_primeLaplaceEvenFactorialJetTotalEnergy
    {x : ℝ} (hx : 1 / 2 < x) :
    Summable (fun p : Nat.Primes ↦
      semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        (p : ℝ) ^ (-2 * x) * Real.cosh (primeLogSupport p)) := by
  have hpow : Summable (fun p : Nat.Primes ↦
      Real.sqrt 2 * (p : ℝ) ^ (-2 * x)) :=
    (Nat.Primes.summable_rpow.mpr (by linarith)).mul_left (Real.sqrt 2)
  exact hpow.of_nonneg_of_le
    (fun p ↦ mul_nonneg
      (mul_nonneg
        (Real.rpow_nonneg (Real.cosh_pos _).le _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.cosh_pos _).le)
    (fun p ↦ primeLaplaceEvenFactorialJetTotalEnergy_le x p)

/-- **All-prime even-factorial incidence theorem.**  The complete Gamma-damped prime-to-jet
matrix has summable squared coefficients at every source point strictly right of `1/2`. -/
theorem summable_primeLaplaceEvenFactorialJetEnergy
    {x : ℝ} (hx : 1 / 2 < x) :
    Summable (fun pj : Nat.Primes × ℕ ↦
      primeLaplaceEvenFactorialJetEnergy x pj.1 pj.2) := by
  rw [summable_prod_of_nonneg (fun pj ↦
    primeLaplaceEvenFactorialJetEnergy_nonneg x pj.1 pj.2)]
  refine ⟨fun p ↦ (hasSum_primeLaplaceEvenFactorialJetEnergy x p).summable, ?_⟩
  simpa only [tsum_primeLaplaceEvenFactorialJetEnergy] using
    summable_primeLaplaceEvenFactorialJetTotalEnergy hx

end

end RHTower
