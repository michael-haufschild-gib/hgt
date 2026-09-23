import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect

/-!
# Prime--Hodge cubic orbit birth

The pre-divisor prime--history defect already exists as a literal, normalized, prime-mixed
Schatten-one kernel.  This module proves its missing cubic Lyapunov source law on that exact
coordinate core: the third prime-clock action is one rank-one source vector with every prime
label retained.  The same formula is rigid entrywise, so no other coordinate kernel can satisfy
this literal source equation.

No Xi zero, divisor, cutoff, fitted normalization, or bounded endpoint extension enters.
-/

open Complex Matrix Filter Topology Set
open scoped Kronecker ComplexOrder BigOperators

namespace RHTower

noncomputable section

/-- Literal PCOB prime source vector, normalized by the formed Stokes current. -/
def primeHodgeCubicBirthVector (d : ℝ) (p : Nat.Primes) : ℂ :=
  ((1 / 2 : ℝ) *
    (Real.sqrt (routePPrimitiveGammaJuliaStokesApertureScaleSq d p) *
      Real.log (p : ℝ) *
        Real.sqrt (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, 0)) /
          xiGammaEulerValuationNat (p, 0)) /
      Real.sqrt (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)) : ℝ)

/-- Exact prime-coordinate PCOB cubic birth law for the normalized cofinal Stokes kernel. -/
theorem primeHodgeCubicClock_normalizedStokesKernel
    {d : ℝ} (hd : 0 < d) (p q : Nat.Primes) :
    ((Real.log (p : ℝ) + Real.log (q : ℝ) : ℝ) : ℂ) ^ (3 : ℕ) *
        normalizedStokesPrimeKernel d (p, q) =
      8 * primeHodgeCubicBirthVector d p * star (primeHodgeCubicBirthVector d q) := by
  have hp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast q.property.one_lt)
  have hJ : 0 < gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d :=
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd
  have hsum : Real.log (p : ℝ) + Real.log (q : ℝ) ≠ 0 :=
    (add_pos hp hq).ne'
  have hrootJ : Real.sqrt (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) ≠ 0 :=
    (Real.sqrt_pos.2 hJ).ne'
  rw [normalizedStokesPrimeKernel,
    routePPrimitiveGammaJuliaStokesCofinalChildKernel,
    xiGammaEulerPrimitiveLogFrequency_prime_zero,
    xiGammaEulerPrimitiveLogFrequency_prime_zero]
  simp only [primeHodgeCubicBirthVector, Complex.star_def, Complex.conj_ofReal]
  rw [finiteVonMangoldtDepthOneAmplitude,
    finiteVonMangoldtDepthOneAmplitude]
  simp only [Complex.conj_ofReal]
  rw [show routePBaseCauchyCubicKernel 1 (Real.log (p : ℝ))
      (Real.log (q : ℝ)) 0 =
      2 / (((Real.log (p : ℝ) + Real.log (q : ℝ) : ℝ) : ℂ) ^ (3 : ℕ)) by
    rw [routePBaseCauchyCubicKernel, routePCollisionPairFrequency]
    push_cast
    ring]
  field_simp [hsum, hrootJ]
  norm_cast
  field_simp [hrootJ]
  rw [Real.sq_sqrt hJ.le]
  norm_num
  ring

/-- The normalized Stokes kernel has its literal normalized prime density on the diagonal. -/
theorem normalizedStokesPrimeKernel_diagonal
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    normalizedStokesPrimeKernel d (p, p) =
      ((routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℝ) : ℂ) := by
  rw [normalizedStokesPrimeKernel,
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal hd]
  norm_cast

/-- The birth-vector diagonal is the normalized Stokes density times the cubic prime clock. -/
theorem primeHodgeCubicBirthVector_diagonal
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    primeHodgeCubicBirthVector d p * star (primeHodgeCubicBirthVector d p) =
      ((routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d *
          Real.log (p : ℝ) ^ (3 : ℕ) : ℝ) : ℂ) := by
  have h := primeHodgeCubicClock_normalizedStokesKernel hd p p
  rw [normalizedStokesPrimeKernel_diagonal hd p] at h
  apply (mul_left_cancel₀ (show (8 : ℂ) ≠ 0 by norm_num))
  calc
    8 * (primeHodgeCubicBirthVector d p * star (primeHodgeCubicBirthVector d p)) =
        8 * primeHodgeCubicBirthVector d p * star (primeHodgeCubicBirthVector d p) := by ring
    _ = ((Real.log (p : ℝ) + Real.log (p : ℝ) : ℝ) : ℂ) ^ (3 : ℕ) *
        ((routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℝ) : ℂ) := h.symm
    _ = 8 * ((routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d *
            Real.log (p : ℝ) ^ (3 : ℕ) : ℝ) : ℂ) := by
      push_cast
      ring

/-- Literal cubic clock applied to a prime--history coordinate kernel. -/
def primeHodgeHistoryCubicClock
    (X : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex → ℂ)
    (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) : ℂ :=
  ((Real.log (ab.1.2 : ℝ) + Real.log (ab.2.2 : ℝ) : ℝ) : ℂ) ^ (3 : ℕ) *
    X ab

/-- Cubic clock on the actual finite prime--history source core. -/
def primeHodgeHistoryCubicClockCore
    (d : ℝ) (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) : ℂ :=
  primeHodgeHistoryCubicClock (primeHodgeHistoryDefectKernel d) ab

/-- Prime--history rank-one source born by the literal cubic clock. -/
def primeHodgeHistoryCubicBirthKernel
    (d : ℝ) (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) : ℂ :=
  if _ : ab.1.1 = ab.2.1 then
    (PrimeHodgeHistory.w ab.1.1 : ℂ) *
      primeHodgeCubicBirthVector d ab.1.2 * star (primeHodgeCubicBirthVector d ab.2.2)
  else 0

/-- Exact PCOB source birth on every prime--history coordinate. -/
theorem primeHodgeHistoryCubicClockCore_eq_birth
    {d : ℝ} (hd : 0 < d) (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) :
    primeHodgeHistoryCubicClockCore d ab =
      8 * primeHodgeHistoryCubicBirthKernel d ab := by
  by_cases hhistory : ab.1.1 = ab.2.1
  · rw [primeHodgeHistoryCubicClockCore, primeHodgeHistoryCubicClock,
      primeHodgeHistoryDefectKernel,
      if_pos hhistory, primeHodgeHistoryCubicBirthKernel, dif_pos hhistory]
    calc
      ((Real.log (ab.1.2 : ℝ) + Real.log (ab.2.2 : ℝ) : ℝ) : ℂ) ^ (3 : ℕ) *
          ((PrimeHodgeHistory.w ab.1.1 : ℂ) *
            normalizedStokesPrimeKernel d (ab.1.2, ab.2.2)) =
          (PrimeHodgeHistory.w ab.1.1 : ℂ) *
            (((Real.log (ab.1.2 : ℝ) + Real.log (ab.2.2 : ℝ) : ℝ) : ℂ) ^ (3 : ℕ) *
              normalizedStokesPrimeKernel d (ab.1.2, ab.2.2)) := by ring
      _ = (PrimeHodgeHistory.w ab.1.1 : ℂ) *
          (8 * primeHodgeCubicBirthVector d ab.1.2 *
            star (primeHodgeCubicBirthVector d ab.2.2)) := by
        rw [primeHodgeCubicClock_normalizedStokesKernel hd]
      _ = 8 * ((PrimeHodgeHistory.w ab.1.1 : ℂ) *
        primeHodgeCubicBirthVector d ab.1.2 *
          star (primeHodgeCubicBirthVector d ab.2.2)) := by ring
  · rw [primeHodgeHistoryCubicClockCore, primeHodgeHistoryCubicClock,
      primeHodgeHistoryDefectKernel,
      if_neg hhistory, primeHodgeHistoryCubicBirthKernel, dif_neg hhistory]
    ring

/-- The PCOB cubic boundary equation determines the actual source kernel on every coordinate. -/
theorem primeHodgeHistoryDefectKernel_unique_of_cubicClock
    {d : ℝ} (hd : 0 < d)
    (X : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex → ℂ)
    (hX : ∀ ab, primeHodgeHistoryCubicClock X ab =
      8 * primeHodgeHistoryCubicBirthKernel d ab) :
    X = primeHodgeHistoryDefectKernel d := by
  funext ab
  have hrate : 0 < Real.log (ab.1.2 : ℝ) + Real.log (ab.2.2 : ℝ) :=
    add_pos
      (Real.log_pos (by exact_mod_cast ab.1.2.property.one_lt))
      (Real.log_pos (by exact_mod_cast ab.2.2.property.one_lt))
  have hclockNe :
      ((Real.log (ab.1.2 : ℝ) + Real.log (ab.2.2 : ℝ) : ℝ) : ℂ) ^ (3 : ℕ) ≠ 0 := by
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hrate.ne')
  apply (mul_left_cancel₀ hclockNe)
  calc
    ((Real.log (ab.1.2 : ℝ) + Real.log (ab.2.2 : ℝ) : ℝ) : ℂ) ^ (3 : ℕ) * X ab =
        primeHodgeHistoryCubicClock X ab := rfl
    _ = 8 * primeHodgeHistoryCubicBirthKernel d ab := hX ab
    _ = primeHodgeHistoryCubicClockCore d ab :=
      (primeHodgeHistoryCubicClockCore_eq_birth hd ab).symm
    _ = ((Real.log (ab.1.2 : ℝ) + Real.log (ab.2.2 : ℝ) : ℝ) : ℂ) ^ (3 : ℕ) *
        primeHodgeHistoryDefectKernel d ab := rfl

/-- Every literal prime label survives in the cubic birth vector. -/
theorem primeHodgeCubicBirthVector_ne_zero
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    primeHodgeCubicBirthVector d p ≠ 0 := by
  have hJ : 0 < gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d :=
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd
  have hw : 0 < routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p :=
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd p
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hmass : 0 <
      routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d *
          Real.log (p : ℝ) ^ (3 : ℕ) :=
    mul_pos (div_pos hw hJ) (pow_pos hlog _)
  intro hzero
  have hdiag := primeHodgeCubicBirthVector_diagonal hd p
  have hcontra : (0 : ℂ) =
      ((routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d *
          Real.log (p : ℝ) ^ (3 : ℕ) : ℝ) : ℂ) := by
    simpa [hzero] using hdiag
  exact (Complex.ofReal_ne_zero.mpr hmass.ne') hcontra.symm

/-- Every same-history prime pair survives in the cubic rank-one birth kernel. -/
theorem primeHodgeHistoryCubicBirthKernel_sameHistory_ne_zero
    {d : ℝ} (hd : 0 < d) (n : ℕ) (p q : Nat.Primes) :
    primeHodgeHistoryCubicBirthKernel d ((n, p), (n, q)) ≠ 0 := by
  rw [primeHodgeHistoryCubicBirthKernel, dif_pos rfl]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (PrimeHodgeHistory.w_pos n).ne'
    · exact primeHodgeCubicBirthVector_ne_zero hd p
  · exact star_ne_zero.mpr (primeHodgeCubicBirthVector_ne_zero hd q)

end

end RHTower
