import GaloisForLFunctions.RHTower.JuliaCriticalFactorialDefectMeasureCompletion

/-!
# Prime--Gamma factorial fugacity boundary

The complete factorial jet tower has a real fugacity parameter `lambda`.
Positive Julia aperture makes every fugacity prime-summable.  At the critical
boundary, summability holds exactly for `lambda < 1`; the identity character
is the sharp prime-harmonic wall.

The even and odd factorial columns both contain that identity sector.  Their
difference is the negative fugacity character and is summable.  Thus scalar
parity supertrace cancels the critical singularity rather than proving RH.
No Xi-divisor landing or RH implication is asserted here.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Critical Gamma-damped prime weight at real factorial fugacity `lambda`. -/
def primeGammaFactorialFugacityBoundaryWeight
    (lambda : ℝ) (p : Nat.Primes) : ℝ :=
  semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
    (p : ℝ) ^ (lambda - 1)

lemma primeGammaFactorialFugacityBoundaryWeight_nonneg
    (lambda : ℝ) (p : Nat.Primes) :
    0 ≤ primeGammaFactorialFugacityBoundaryWeight lambda p := by
  exact mul_nonneg
    (Real.rpow_nonneg (Real.cosh_pos _).le _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Gamma damping compares the fugacity weight with the sharp prime power
`sqrt 2 * p^(lambda - 2)`. -/
lemma primeGammaFactorialFugacityBoundaryWeight_le
    (lambda : ℝ) (p : Nat.Primes) :
    primeGammaFactorialFugacityBoundaryWeight lambda p ≤
      Real.sqrt 2 * (p : ℝ) ^ (lambda - 2) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hchar :=
    semilocalArchimedeanCharacteristic_two_mul_le_sqrtTwo_mul_exp_neg
      (primeLogSupport p)
  have hexp : Real.exp (-primeLogSupport p) = ((p : ℝ))⁻¹ := by
    rw [primeLogSupport, Real.exp_neg, Real.exp_log hp0]
  rw [hexp] at hchar
  calc
    primeGammaFactorialFugacityBoundaryWeight lambda p ≤
        (Real.sqrt 2 * (p : ℝ)⁻¹) *
          (p : ℝ) ^ (lambda - 1) := by
      unfold primeGammaFactorialFugacityBoundaryWeight
      gcongr
    _ = Real.sqrt 2 * (p : ℝ) ^ (lambda - 2) := by
      rw [show (p : ℝ)⁻¹ = (p : ℝ) ^ (-1 : ℝ) by
        exact (Real.rpow_neg_one (p : ℝ)).symm]
      calc
        (Real.sqrt 2 * (p : ℝ) ^ (-1 : ℝ)) *
              (p : ℝ) ^ (lambda - 1) =
            Real.sqrt 2 *
              ((p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (lambda - 1)) := by
          ring
        _ = Real.sqrt 2 *
              (p : ℝ) ^ ((-1 : ℝ) + (lambda - 1)) := by
          rw [Real.rpow_add hp0]
        _ = Real.sqrt 2 * (p : ℝ) ^ (lambda - 2) := by
          congr 2
          ring

theorem summable_primeGammaFactorialFugacityBoundaryWeight_of_lt
    {lambda : ℝ} (hlambda : lambda < 1) :
    Summable (primeGammaFactorialFugacityBoundaryWeight lambda) := by
  have hpow : Summable (fun p : Nat.Primes =>
      Real.sqrt 2 * (p : ℝ) ^ (lambda - 2)) :=
    (Nat.Primes.summable_rpow.mpr (by linarith)).mul_left (Real.sqrt 2)
  exact hpow.of_nonneg_of_le
    (fun p => primeGammaFactorialFugacityBoundaryWeight_nonneg lambda p)
    (fun p => primeGammaFactorialFugacityBoundaryWeight_le lambda p)

theorem not_summable_primeGammaFactorialFugacityBoundaryWeight_of_one_le
    {lambda : ℝ} (hlambda : 1 ≤ lambda) :
    ¬ Summable (primeGammaFactorialFugacityBoundaryWeight lambda) := by
  intro h
  have hrecip : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) := by
    apply h.of_nonneg_of_le
    · intro p
      positivity
    · intro p
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.one_le
      have hpow : 1 ≤ (p : ℝ) ^ (lambda - 1) :=
        Real.one_le_rpow hp1 (by linarith)
      calc
        1 / (p : ℝ) = (p : ℝ)⁻¹ := by rw [one_div]
        _ ≤ semilocalArchimedeanCharacteristic
              (2 * primeLogSupport p) :=
          invPrime_le_semilocalArchimedeanCharacteristic_two_primeLogSupport p
        _ ≤ primeGammaFactorialFugacityBoundaryWeight lambda p := by
          unfold primeGammaFactorialFugacityBoundaryWeight
          have hchar0 :
              0 ≤ semilocalArchimedeanCharacteristic
                (2 * primeLogSupport p) :=
            Real.rpow_nonneg (Real.cosh_pos _).le _
          nlinarith
  exact Nat.Primes.not_summable_one_div hrecip

/-- The identity fugacity `lambda = 1` is the exact critical
prime-harmonic abscissa. -/
theorem summable_primeGammaFactorialFugacityBoundaryWeight_iff
    (lambda : ℝ) :
    Summable (primeGammaFactorialFugacityBoundaryWeight lambda) ↔
      lambda < 1 := by
  constructor
  · intro h
    by_contra hn
    exact not_summable_primeGammaFactorialFugacityBoundaryWeight_of_one_le
      (le_of_not_gt hn) h
  · exact summable_primeGammaFactorialFugacityBoundaryWeight_of_lt

/-- A dagger which preserves summability of the two reciprocal fugacity
rates can exist only at zero horizontal character rate. -/
theorem reflectedFugacitySummability_equiv_iff
    (q : ℝ) :
    (Summable
        (primeGammaFactorialFugacityBoundaryWeight (1 + 2 * q)) ↔
      Summable
        (primeGammaFactorialFugacityBoundaryWeight (1 - 2 * q))) ↔
      q = 0 := by
  rw [summable_primeGammaFactorialFugacityBoundaryWeight_iff,
    summable_primeGammaFactorialFugacityBoundaryWeight_iff]
  constructor
  · intro h
    by_contra hq
    rcases lt_or_gt_of_ne hq with hqneg | hqpos
    · have hleft : 1 + 2 * q < 1 := by linarith
      have hright := h.mp hleft
      linarith
    · have hright : 1 - 2 * q < 1 := by linarith
      have hleft := h.mpr hright
      linarith
  · intro hq
    subst q
    norm_num

/-- Positive-aperture Gamma--Julia fugacity column. -/
def juliaFactorialFugacityWeight
    (x lambda : ℝ) (p : Nat.Primes) : ℝ :=
  semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
    (p : ℝ)⁻¹ *
      Real.exp
        (lambda * gammaSewnMobiusJuliaNormalizedPrimeLog x p)

lemma juliaFactorialFugacityWeight_nonneg
    (x lambda : ℝ) (p : Nat.Primes) :
    0 ≤ juliaFactorialFugacityWeight x lambda p := by
  unfold juliaFactorialFugacityWeight
  exact mul_nonneg
    (mul_nonneg
      (Real.rpow_nonneg (Real.cosh_pos _).le _)
      (inv_nonneg.mpr (Nat.cast_nonneg _)))
    (Real.exp_pos _).le

lemma juliaFactorialFugacityWeight_le
    {x : ℝ} (hx : 0 < x) (lambda : ℝ) (p : Nat.Primes) :
    juliaFactorialFugacityWeight x lambda p ≤
      (Real.sqrt 2 *
        Real.exp (|lambda| * ((Real.sqrt (3 / 4))⁻¹ / x))) *
          (p : ℝ) ^ (-2 : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hell0 :=
    gammaSewnMobiusJuliaNormalizedPrimeLog_nonneg hx p
  have hell :=
    gammaSewnMobiusJuliaNormalizedPrimeLog_le hx p
  have hexponent :
      lambda * gammaSewnMobiusJuliaNormalizedPrimeLog x p ≤
        |lambda| * ((Real.sqrt (3 / 4))⁻¹ / x) := by
    calc
      lambda * gammaSewnMobiusJuliaNormalizedPrimeLog x p ≤
          |lambda| * gammaSewnMobiusJuliaNormalizedPrimeLog x p :=
        mul_le_mul_of_nonneg_right (le_abs_self lambda) hell0
      _ ≤ |lambda| * ((Real.sqrt (3 / 4))⁻¹ / x) :=
        mul_le_mul_of_nonneg_left hell (abs_nonneg lambda)
  have hexp := Real.exp_le_exp.mpr hexponent
  have hchar :=
    semilocalArchimedeanCharacteristic_two_mul_le_sqrtTwo_mul_exp_neg
      (primeLogSupport p)
  have hprimeExp :
      Real.exp (-primeLogSupport p) = ((p : ℝ))⁻¹ := by
    rw [primeLogSupport, Real.exp_neg, Real.exp_log hp0]
  rw [hprimeExp] at hchar
  calc
    juliaFactorialFugacityWeight x lambda p ≤
        (Real.sqrt 2 * (p : ℝ)⁻¹) * (p : ℝ)⁻¹ *
          Real.exp
            (lambda * gammaSewnMobiusJuliaNormalizedPrimeLog x p) := by
      unfold juliaFactorialFugacityWeight
      gcongr
    _ ≤ (Real.sqrt 2 * (p : ℝ)⁻¹) * (p : ℝ)⁻¹ *
          Real.exp (|lambda| * ((Real.sqrt (3 / 4))⁻¹ / x)) := by
      gcongr
    _ = (Real.sqrt 2 *
          Real.exp (|lambda| * ((Real.sqrt (3 / 4))⁻¹ / x))) *
          (p : ℝ) ^ (-2 : ℝ) := by
      rw [show (p : ℝ)⁻¹ = (p : ℝ) ^ (-1 : ℝ) by
        exact (Real.rpow_neg_one (p : ℝ)).symm]
      calc
        Real.sqrt 2 * (p : ℝ) ^ (-1 : ℝ) *
              (p : ℝ) ^ (-1 : ℝ) *
              Real.exp (|lambda| * ((Real.sqrt (3 / 4))⁻¹ / x)) =
            (Real.sqrt 2 *
              Real.exp (|lambda| * ((Real.sqrt (3 / 4))⁻¹ / x))) *
              ((p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (-1 : ℝ)) := by
          ring
        _ = (Real.sqrt 2 *
              Real.exp (|lambda| * ((Real.sqrt (3 / 4))⁻¹ / x))) *
              (p : ℝ) ^ ((-1 : ℝ) + (-1 : ℝ)) := by
          rw [Real.rpow_add hp0]
        _ = (Real.sqrt 2 *
              Real.exp (|lambda| * ((Real.sqrt (3 / 4))⁻¹ / x))) *
              (p : ℝ) ^ (-2 : ℝ) := by norm_num

/-- Every real factorial fugacity is prime-summable at every positive Julia
aperture. -/
theorem summable_juliaFactorialFugacityWeight
    {x : ℝ} (hx : 0 < x) (lambda : ℝ) :
    Summable (juliaFactorialFugacityWeight x lambda) := by
  have hpow : Summable (fun p : Nat.Primes =>
      (Real.sqrt 2 *
        Real.exp (|lambda| * ((Real.sqrt (3 / 4))⁻¹ / x))) *
          (p : ℝ) ^ (-2 : ℝ)) :=
    (Nat.Primes.summable_rpow.mpr (by norm_num)).mul_left
      (Real.sqrt 2 *
        Real.exp (|lambda| * ((Real.sqrt (3 / 4))⁻¹ / x)))
  exact hpow.of_nonneg_of_le
    (fun p => juliaFactorialFugacityWeight_nonneg x lambda p)
    (fun p => juliaFactorialFugacityWeight_le hx lambda p)

/-- Critical even factorial column. -/
def primeGammaCriticalEvenFugacityColumn (p : Nat.Primes) : ℝ :=
  semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
    (p : ℝ)⁻¹ * Real.cosh (primeLogSupport p)

/-- Critical odd factorial column. -/
def primeGammaCriticalOddFugacityColumn (p : Nat.Primes) : ℝ :=
  semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
    (p : ℝ)⁻¹ * Real.sinh (primeLogSupport p)

/-- Even minus odd cancels the identity fugacity and leaves exactly the
trace-class negative character. -/
theorem primeGammaCriticalEven_sub_odd_eq_negativeFugacity
    (p : Nat.Primes) :
    primeGammaCriticalEvenFugacityColumn p -
        primeGammaCriticalOddFugacityColumn p =
      primeGammaFactorialFugacityBoundaryWeight (-1) p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  unfold primeGammaCriticalEvenFugacityColumn
    primeGammaCriticalOddFugacityColumn
    primeGammaFactorialFugacityBoundaryWeight
  rw [← mul_sub, Real.cosh_sub_sinh]
  have hexp :
      Real.exp (-primeLogSupport p) = ((p : ℝ))⁻¹ := by
    rw [primeLogSupport, Real.exp_neg, Real.exp_log hp0]
  rw [hexp]
  rw [show (p : ℝ)⁻¹ = (p : ℝ) ^ (-1 : ℝ) by
    exact (Real.rpow_neg_one (p : ℝ)).symm]
  calc
    semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
          (p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (-1 : ℝ) =
        semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
          ((p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (-1 : ℝ)) := by ring
    _ = semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
          (p : ℝ) ^ ((-1 : ℝ) + (-1 : ℝ)) := by
      rw [Real.rpow_add hp0]
    _ = semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
          (p : ℝ) ^ ((-1 : ℝ) - 1) := by norm_num

/-- The critical parity supertrace is summable even though both parity
sectors contain the nonsummable identity character. -/
theorem summable_primeGammaCriticalEven_sub_odd :
    Summable (fun p : Nat.Primes =>
      primeGammaCriticalEvenFugacityColumn p -
        primeGammaCriticalOddFugacityColumn p) := by
  exact
    (summable_primeGammaFactorialFugacityBoundaryWeight_of_lt
      (by norm_num : (-1 : ℝ) < 1)).congr
      (fun p => (primeGammaCriticalEven_sub_odd_eq_negativeFugacity p).symm)

end

end RHTower
