import GaloisForLFunctions.RHTower.EulerHedenmalmGammaStokesTransgression
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect
import GaloisForLFunctions.RHTower.ArchimedeanGamma

/-!
# Theta Mellin-six formation of the integral--nuclear history

The Mellin transform of the literal first theta atom is the completed archimedean factor.
Removing its forced Euler pole polynomial leaves `Gamma_R`.  The normalized six-step holonomy of
that response is exactly every survival tail of the prime--Hodge history, and its adjacent boundary
loss is exactly the emitted nuclear flux.  Hence the history marginal of the pre-divisor
prime-mixed operator is formed by the literal theta atom rather than added as an auxiliary law.

No zero, divisor copy, ordinate, or RH hypothesis enters any statement.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- Mellin response of the literal first theta atom after removing the Euler pole polynomial. -/
def thetaCuspPoleStrippedMellinResponse (s : ℂ) : ℂ :=
  2 * mellin (fun t : ℝ => (thetaCuspSeed t : ℂ)) s / (s * (s - 1))

/-- Pole stripping leaves exactly Deligne's real archimedean Gamma factor. -/
theorem thetaCuspPoleStrippedMellinResponse_eq_GammaR
    {s : ℂ} (hs : 1 < s.re) :
    thetaCuspPoleStrippedMellinResponse s = Complex.Gammaℝ s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := sub_eq_zero.mp h
    rw [this] at hs
    norm_num at hs
  rw [thetaCuspPoleStrippedMellinResponse,
    mellin_thetaCuspSeed_eq_archFactor (by linarith), archFactor]
  field_simp [hs0, hs1]

/-- Three `Gamma_R` cofaces compose to the exact six-step multiplier. -/
theorem gammaReal_shift_six
    {s : ℂ} (hs0 : s ≠ 0) (hs2 : s + 2 ≠ 0) (hs4 : s + 4 ≠ 0) :
    Complex.Gammaℝ (s + 6) =
      (s * (s + 2) * (s + 4) / (8 * (Real.pi : ℂ) ^ 3)) *
        Complex.Gammaℝ s := by
  calc
    Complex.Gammaℝ (s + 6) = Complex.Gammaℝ ((s + 4) + 2) := by
      congr 1
      ring
    _ = ((s + 4) / (2 * (Real.pi : ℂ))) * Complex.Gammaℝ (s + 4) :=
      GaloisForLFunctions.gammaReal_shift_two hs4
    _ = ((s + 4) / (2 * (Real.pi : ℂ))) *
        (((s + 2) / (2 * (Real.pi : ℂ))) * Complex.Gammaℝ (s + 2)) := by
      rw [show s + 4 = (s + 2) + 2 by ring,
        GaloisForLFunctions.gammaReal_shift_two hs2]
    _ = ((s + 4) / (2 * (Real.pi : ℂ))) *
        (((s + 2) / (2 * (Real.pi : ℂ))) *
          ((s / (2 * (Real.pi : ℂ))) * Complex.Gammaℝ s)) := by
      rw [GaloisForLFunctions.gammaReal_shift_two hs0]
    _ = (s * (s + 2) * (s + 4) / (8 * (Real.pi : ℂ) ^ 3)) *
        Complex.Gammaℝ s := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp [hpi]
      ring

/-- Ratio form of the six-step archimedean holonomy. -/
theorem gammaReal_div_shift_six
    {s : ℂ} (hs0 : s ≠ 0) (hs2 : s + 2 ≠ 0) (hs4 : s + 4 ≠ 0)
    (hG : Complex.Gammaℝ s ≠ 0) :
    Complex.Gammaℝ s / Complex.Gammaℝ (s + 6) =
      8 * (Real.pi : ℂ) ^ 3 / (s * (s + 2) * (s + 4)) := by
  rw [gammaReal_shift_six hs0 hs2 hs4]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hs0, hs2, hs4, hG, hpi]

/-- Normalized six-step theta Mellin holonomy on the natural Hodge history grades. -/
def thetaCuspMellinSixHolonomy (n : ℕ) : ℂ :=
  (thetaCuspPoleStrippedMellinResponse ((2 * n + 3 : ℕ) : ℂ) /
      thetaCuspPoleStrippedMellinResponse ((2 * n + 9 : ℕ) : ℂ)) /
    (thetaCuspPoleStrippedMellinResponse 3 /
      thetaCuspPoleStrippedMellinResponse 9)

/-- The literal theta atom reconstructs every history tail of the prime-mixed nuclear defect. -/
theorem thetaCuspMellinSixHolonomy_eq_primeHodgeHistory_m (n : ℕ) :
    thetaCuspMellinSixHolonomy n = (PrimeHodgeHistory.m n : ℂ) := by
  have hleft : 1 < (((2 * n + 3 : ℕ) : ℂ)).re := by
    exact_mod_cast (by omega : 1 < 2 * n + 3)
  have hright : 1 < (((2 * n + 9 : ℕ) : ℂ)).re := by
    exact_mod_cast (by omega : 1 < 2 * n + 9)
  rw [thetaCuspMellinSixHolonomy,
    thetaCuspPoleStrippedMellinResponse_eq_GammaR hleft,
    thetaCuspPoleStrippedMellinResponse_eq_GammaR hright,
    thetaCuspPoleStrippedMellinResponse_eq_GammaR (s := (3 : ℂ)) (by norm_num),
    thetaCuspPoleStrippedMellinResponse_eq_GammaR (s := (9 : ℂ)) (by norm_num)]
  have hn0 : (((2 * n + 3 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : (2 * n + 3 : ℕ) ≠ 0)
  have hn2 : (((2 * n + 3 : ℕ) : ℂ)) + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Nat.cast_add, Nat.cast_mul] at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hn4 : (((2 * n + 3 : ℕ) : ℂ)) + 4 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Nat.cast_add, Nat.cast_mul] at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hnG : Complex.Gammaℝ (((2 * n + 3 : ℕ) : ℂ)) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by positivity)
  have hn := gammaReal_div_shift_six hn0 hn2 hn4 hnG
  have hn' :
      Complex.Gammaℝ ((2 * n + 3 : ℕ) : ℂ) /
          Complex.Gammaℝ ((2 * n + 9 : ℕ) : ℂ) =
        8 * (Real.pi : ℂ) ^ 3 /
          (((2 * n + 3 : ℕ) : ℂ) * ((2 * n + 5 : ℕ) : ℂ) *
            ((2 * n + 7 : ℕ) : ℂ)) := by
    convert hn using 1 <;> push_cast <;> ring
  have hbase := gammaReal_div_shift_six
    (s := (3 : ℂ)) (by norm_num) (by norm_num) (by norm_num)
    (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
  have hbase' :
      Complex.Gammaℝ 3 / Complex.Gammaℝ 9 =
        8 * (Real.pi : ℂ) ^ 3 / (3 * 5 * 7) := by
    convert hbase using 1 <;> norm_num
  rw [hn', hbase', PrimeHodgeHistory.m]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp [hpi]
  ring

/-- Adjacent theta holonomy loss is exactly the emitted nuclear history flux. -/
theorem thetaCuspMellinSixHolonomy_sub_succ_eq_primeHodgeHistory_w (n : ℕ) :
    thetaCuspMellinSixHolonomy n - thetaCuspMellinSixHolonomy (n + 1) =
      (PrimeHodgeHistory.w n : ℂ) := by
  rw [thetaCuspMellinSixHolonomy_eq_primeHodgeHistory_m,
    thetaCuspMellinSixHolonomy_eq_primeHodgeHistory_m]
  simp [PrimeHodgeHistory.w]

/-- Real adjacent boundary loss of the normalized theta Mellin-six holonomy. -/
def thetaCuspMellinSixFlux (n : ℕ) : ℝ :=
  (thetaCuspMellinSixHolonomy n - thetaCuspMellinSixHolonomy (n + 1)).re

theorem thetaCuspMellinSixFlux_eq_primeHodgeHistory_w (n : ℕ) :
    thetaCuspMellinSixFlux n = PrimeHodgeHistory.w n := by
  rw [thetaCuspMellinSixFlux,
    thetaCuspMellinSixHolonomy_sub_succ_eq_primeHodgeHistory_w]
  simp

/-- Every theta-formed flux tail reconstructs the unspent Mellin-six holonomy. -/
theorem thetaCuspMellinSixFlux_tail_hasSum (n : ℕ) :
    HasSum (fun k => thetaCuspMellinSixFlux (k + n))
      (thetaCuspMellinSixHolonomy n).re := by
  simp_rw [thetaCuspMellinSixFlux_eq_primeHodgeHistory_w,
    thetaCuspMellinSixHolonomy_eq_primeHodgeHistory_m]
  simpa using PrimeHodgeHistory.tail_hasSum_w n

/-- The diagonal density of the prime-mixed defect is the theta Mellin-six boundary flux tensored
with the coefficient-faithful prime density. -/
theorem primeHodgeHistoryDiagonalWeight_eq_thetaCuspMellinSixFlux
    (d : ℝ) (np : PrimeHodgeHistoryIndex) :
    primeHodgeHistoryDiagonalWeight d np =
      thetaCuspMellinSixFlux np.1 *
          routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d np.2 /
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d := by
  rw [primeHodgeHistoryDiagonalWeight,
    thetaCuspMellinSixFlux_eq_primeHodgeHistory_w]

end

end RHTower
