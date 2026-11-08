import GaloisForLFunctions.ArithmeticProduction.LongMollifiersImplyCriticalClustering
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeThreshold

/-!
# An Euler mollifier needs the primes up to `log² T`

The Euler mollifier over the primes `p ≤ y`, `M_y(s) = Π_{p≤y} (1 − p^{−s})`, is the real Dirichlet
polynomial with coefficients `μ(d)` on the divisors `d` of the primorial `y#`, of length `y# ≤ 4^y`
(`edPoly_eulerMollifierCoeff`).

**Theorem** (`eulerMollifier_needs_primes`). For `K₀ > 0` and all large `T`, if
`∫_T^{2T} |ζ M_y(½ + it)|² dt ≤ (1 + K₀/log T) T` then
`y ≥ min(1/24, 1/(14K₀)) log² T / log 4`.

So a near-unit mollified second moment (rate `K₀/log T`) reached by an Euler mollifier uses every
prime up to a constant times `log² T`: the necessary length `log N ≳ log² T` of the corpus, read in
Euler coordinates, is the range of primes from `log T` to `log² T`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticProduction

open _root_.RHTower

/-- The primes up to `y`. -/
abbrev primesUpTo (y : ℕ) : Finset ℕ := (Finset.range (y + 1)).filter Nat.Prime

/-- The coefficients `μ(d) · [d | y#]` of the Euler mollifier over the primes `p ≤ y`. -/
def eulerMollifierCoeff (y : ℕ) : ℕ → ℂ := finitePrimeApertureMobiusCoefficient (primesUpTo y)

theorem prod_primesUpTo (y : ℕ) : ∏ p ∈ primesUpTo y, p = primorial y := rfl

/-- **The Euler mollifier is a Dirichlet polynomial of length `y#`.** -/
theorem edPoly_eulerMollifierCoeff (y : ℕ) (s : ℂ) :
    edPoly (eulerMollifierCoeff y) (Finset.Icc 1 (primorial y)) s =
      ∏ p ∈ primesUpTo y, (1 - (p : ℂ) ^ (-s)) := by
  have h := pm_finitePrime_coefficient_cpow_sum (primesUpTo y)
    (fun p hp => (Finset.mem_filter.mp hp).2) s
  rw [prod_primesUpTo] at h
  rw [edPoly, eulerMollifierCoeff]
  simp only [Complex.ofReal_natCast]
  exact h

theorem eulerMollifierCoeff_one (y : ℕ) : eulerMollifierCoeff y 1 = 1 := by
  simp [eulerMollifierCoeff, finitePrimeApertureMobiusCoefficient, mobiusComplexCoefficient]

theorem norm_eulerMollifierCoeff_le_one (y n : ℕ) : ‖eulerMollifierCoeff y n‖ ≤ 1 := by
  unfold eulerMollifierCoeff finitePrimeApertureMobiusCoefficient mobiusComplexCoefficient
  split_ifs
  · have h := ArithmeticFunction.abs_moebius_le_one (n := n)
    rw [show ((ArithmeticFunction.moebius n : ℤ) : ℂ) = (((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℂ)
      by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast h
  · simp

theorem conj_eulerMollifierCoeff (y n : ℕ) :
    (starRingEnd ℂ) (eulerMollifierCoeff y n) = eulerMollifierCoeff y n := by
  unfold eulerMollifierCoeff finitePrimeApertureMobiusCoefficient mobiusComplexCoefficient
  split_ifs <;> simp

/-- The length of the Euler mollifier: `log y# ≤ y log 4`. -/
theorem log_primorial_le (y : ℕ) : Real.log (primorial y) ≤ y * Real.log 4 := by
  have h := primorial_le_4_pow y
  have hpos : (0 : ℝ) < primorial y := by exact_mod_cast primorial_pos y
  calc Real.log (primorial y) ≤ Real.log ((4 : ℝ) ^ y) :=
        Real.log_le_log hpos (by exact_mod_cast h)
    _ = y * Real.log 4 := Real.log_pow y 4

/-- **An Euler mollifier with a near-unit second moment uses the primes up to `log² T`.** -/
theorem eulerMollifier_needs_primes {K₀ : ℝ} (hK₀ : 0 < K₀) :
    ∀ᶠ T : ℝ in atTop, ∀ y : ℕ,
      (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          ∏ p ∈ primesUpTo y, (1 - (p : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)))‖ ^ 2) ≤
          (1 + K₀ / Real.log T) * T →
        min (1 / 24) (1 / (14 * K₀)) * Real.log T ^ 2 / Real.log 4 ≤ y := by
  filter_upwards [log_length_ge_of_secondMomentRate hK₀] with T hT y hmom
  have hlen := hT (eulerMollifierCoeff y) (primorial y) (primorial_pos y)
    (eulerMollifierCoeff_one y) (fun n _ => norm_eulerMollifierCoeff_le_one y n)
    (fun n _ => conj_eulerMollifierCoeff y n)
    (by simpa only [edPoly_eulerMollifierCoeff] using hmom)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ hlog4]
  exact hlen.trans (log_primorial_le y)

end GaloisForLFunctions.ArithmeticProduction
