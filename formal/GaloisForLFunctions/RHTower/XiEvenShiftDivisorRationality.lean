import GaloisForLFunctions.RHTower.XiEvenShiftPrimeDefectTelescope
import GaloisForLFunctions.RHTower.XiShiftPrimeExposure
import GaloisForLFunctions.RHTower.XiShiftDivisorFaithful

/-!
# Rationality of the archimedean correction on even shifts

The Gamma recurrence makes the archimedean logarithmic-derivative difference across a shift by two
an explicit rational function.  Iterating gives the closed form for every even shift: the
archimedean correction at shift `2m` is the rational telescope

  `∑_{j<m} (1/(s+2j+2) + 1/(s+2j+1) - 1/(s+2j-1))`

pointwise on the Euler half-plane, not merely as an upper-end germ.  Consequently the even-shift
prime defect and the general corrected transverse defect agree pointwise there.

At divisor level this says: a family of even shifts whose coefficients sum to zero has an
archimedean correction that is a rational function, because the common digamma mode is carried
entirely by the total mass.
-/

namespace RHTower

open Complex

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- **Closed form of the even-shift archimedean correction.** For every even shift the correction is
the explicit rational telescope, pointwise on the Euler half-plane. -/
theorem xiTransverseShiftArchimedeanCorrection_even {s : ℂ} (hs : 1 < s.re) (m : ℕ) :
    xiTransverseShiftArchimedeanCorrection (2 * m) s = xiEvenShiftPrimeCorrection m s := by
  have hre : ∀ k : ℕ, 1 < (s + (k : ℂ)).re := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [Complex.add_re, Complex.natCast_re]
    linarith
  induction m with
  | zero => simp [xiTransverseShiftArchimedeanCorrection, xiEvenShiftPrimeCorrection]
  | succ m ih =>
      have hstep := logDeriv_archFactor_shift_two (hre (2 * m))
      have hcast : ((2 * (m + 1) : ℕ) : ℂ) = ((2 * m : ℕ) : ℂ) + 2 := by push_cast; ring
      have hcorr : xiEvenShiftPrimeCorrection (m + 1) s =
          xiEvenShiftPrimeCorrection m s +
            (1 / (s + ((2 * m : ℕ) : ℂ) + 2) + 1 / (s + ((2 * m : ℕ) : ℂ) + 1) -
              1 / (s + ((2 * m : ℕ) : ℂ) - 1)) := by
        rw [xiEvenShiftPrimeCorrection, xiEvenShiftPrimeCorrection, Finset.sum_range_succ]
      rw [xiTransverseShiftArchimedeanCorrection] at ih ⊢
      rw [hcast, hcorr, show s + (((2 * m : ℕ) : ℂ) + 2) = s + ((2 * m : ℕ) : ℂ) + 2 by ring]
      linear_combination hstep + ih

/-- **Pointwise even-shift defect identification.** On the Euler half-plane the explicitly corrected
even-shift defect is the general corrected transverse defect. -/
theorem xiEvenShiftPrimeDefect_eq_xiTransverseShiftPrimeDefect {s : ℂ} (hs : 1 < s.re) (m : ℕ) :
    xiEvenShiftPrimeDefect m s = xiTransverseShiftPrimeDefect (2 * m) s := by
  rw [xiEvenShiftPrimeDefect, xiTransverseShiftPrimeDefect,
    xiTransverseShiftRawLogDerivDefect,
    xiTransverseShiftArchimedeanCorrection_even hs m]

/-- **Mass-zero even families have rational archimedean corrections.** The common digamma mode of the
archimedean factor is carried entirely by the total mass, so it cancels exactly when the coefficients
sum to zero. -/
theorem archimedeanCorrection_evenFamily_of_mass_zero {d : ℕ} (k : Fin d → ℕ) (c : Fin d → ℂ)
    (hmass : ∑ i, c i = 0) {s : ℂ} (hs : 1 < s.re) :
    ∑ i, c i * logDeriv archFactor (s + ((2 * k i : ℕ) : ℂ)) =
      ∑ i, c i * xiEvenShiftPrimeCorrection (k i) s := by
  have h : ∀ i, logDeriv archFactor (s + ((2 * k i : ℕ) : ℂ)) =
      logDeriv archFactor s + xiEvenShiftPrimeCorrection (k i) s := by
    intro i
    have hcorr := xiTransverseShiftArchimedeanCorrection_even hs (k i)
    rw [xiTransverseShiftArchimedeanCorrection] at hcorr
    linear_combination hcorr
  calc ∑ i, c i * logDeriv archFactor (s + ((2 * k i : ℕ) : ℂ))
      = ∑ i, (c i * logDeriv archFactor s + c i * xiEvenShiftPrimeCorrection (k i) s) :=
        Finset.sum_congr rfl fun i _ => by rw [h i]; ring
    _ = (∑ i, c i) * logDeriv archFactor s +
          ∑ i, c i * xiEvenShiftPrimeCorrection (k i) s := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ = ∑ i, c i * xiEvenShiftPrimeCorrection (k i) s := by rw [hmass]; ring

/-- **Even-shift divisor rationality.** The archimedean correction of a mass-zero even-shift divisor
is the divisor-weighted rational telescope. -/
theorem xiShiftDivisorArchimedeanCorrection_evenFamily {d : ℕ} (k : Fin d → ℕ) (c : Fin d → ℂ)
    (hmass : ∑ i, c i = 0) {s : ℂ} (hs : 1 < s.re) :
    xiShiftDivisorArchimedeanCorrection
        (familyShiftDivisor (fun i => ((2 * k i : ℕ) : ℂ)) c) s =
      ∑ i, c i * xiEvenShiftPrimeCorrection (k i) s := by
  rw [xiShiftDivisorArchimedeanCorrection, shiftDivisorValue_familyShiftDivisor]
  exact archimedeanCorrection_evenFamily_of_mass_zero k c hmass hs

/-- **Even-shift divisor prime value.** For a mass-zero even-shift family the corrected completed-Xi
value is the raw weighted logarithmic derivative minus an explicit rational function. -/
theorem xiShiftDivisorPrimeValue_evenFamily {d : ℕ} (k : Fin d → ℕ) (c : Fin d → ℂ)
    (hmass : ∑ i, c i = 0) {s : ℂ} (hs : 1 < s.re) :
    xiShiftDivisorPrimeValue (familyShiftDivisor (fun i => ((2 * k i : ℕ) : ℂ)) c) s =
      (∑ i, c i * logDeriv xi (s + ((2 * k i : ℕ) : ℂ))) -
        ∑ i, c i * xiEvenShiftPrimeCorrection (k i) s := by
  rw [xiShiftDivisorPrimeValue, xiShiftDivisorLogDeriv, shiftDivisorValue_familyShiftDivisor,
    xiShiftDivisorArchimedeanCorrection_evenFamily k c hmass hs]

end

end RHTower
