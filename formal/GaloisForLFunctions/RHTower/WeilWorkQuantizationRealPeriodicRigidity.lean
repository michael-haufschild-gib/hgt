import GaloisForLFunctions.RHTower.WeilWorkQuantizationPeriodicRigidity
import GaloisForLFunctions.RHTower.WeilWorkQuantizationBilateralRigidity
import GaloisForLFunctions.RHTower.WeilWorkQuantizationRationalPeriodReindex

/-!
# Rigidity for every weighted real-periodic canonical Weil phase

The rational-exponent subgroup reduces an arbitrary real base to a rational
base. Integer and signed noninteger rational rigidity then cover every case.
The final source-only alternative does not assert existence of a representation.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open GaloisForLFunctions.HTGeometry

/-- Reduced rational bases unify the integer and noninteger receivers. -/
theorem quantization_rigidity_of_rat_periodic_phase {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {q : ℚ} (hq : 1 < (q : ℝ)) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log (q : ℝ)| / 2))
    (hphase : ∀ t : ℝ, 0 < t →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW t : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log (q : ℝ) * t : ℝ) : ℂ) * I)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast (show (0 : ℝ) ≤ q by linarith)
  have hnum : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ))
      (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq0))
  have hcast : (q.num.natAbs : ℝ) / q.den = q := by rw [hnum, ← Rat.cast_def]
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hdu : q.den < q.num.natAbs := by
    have hh : (1 : ℝ) < (q.num.natAbs : ℝ) / q.den := by rwa [hcast]
    have hh' := (lt_div_iff₀ hd).mp hh
    simpa only [one_mul, Nat.cast_lt] using hh'
  by_cases hv : q.den = 1
  · have hu : 2 ≤ q.num.natAbs := by omega
    have he : (q.num.natAbs : ℝ) = q := by simpa only [hv, Nat.cast_one, div_one] using hcast
    rw [← he] at hp hphase
    apply quantization_rigidity_of_periodic_phase hW hu ?_ hphase
    simpa only [quantization_qfrequency_weight hu] using hp
  · apply quantization_rigidity_of_bilateral_rational_phase hW (by have := q.den_pos; omega)
      hdu q.reduced
    · simpa only [hcast] using hp
    · simpa only [hcast] using hphase

/-- Every weighted periodic representation of the actual phase is rigid,
with no arithmetic restriction on the real base. -/
theorem quantization_rigidity_of_real_periodic_phase {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {r : ℝ} (hr : 1 < r) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log r| / 2))
    (hphase : ∀ t : ℝ, 0 < t →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW t : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log r * t : ℝ) : ℂ) * I)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  rcases quantization_rigidity_or_rational_period_power hW with hR | hpower
  · exact hR
  rcases quantization_rigidity_or_rational_harmonics hW with hR | hrat
  · exact hR
  obtain ⟨N, m, n, hN, _, _, he⟩ := hpower r hr p hp hphase
  have he' : r ^ N = ((m : ℚ) / n : ℚ) := by simpa only [Rat.cast_div, Rat.cast_natCast] using he
  obtain ⟨a, ha, ⟨q, hq⟩, hgen⟩ :=
    quantization_rational_exponent_generator (by omega : 0 < N) he' (by linarith : 0 < r)
  have hq1 : 1 < (q : ℝ) := by
    rw [hq, Real.one_lt_exp_iff]
    exact mul_pos (by exact_mod_cast ha) (Real.log_pos hr)
  obtain ⟨hp', hseries⟩ := quantization_periodic_reindex ha hq hp
    (fun k hk => (hgen k).mp (hrat r hr p hp hphase k hk))
  exact quantization_rigidity_of_rat_periodic_phase hW hq1 hp'
    (fun t ht => (hphase t ht).trans (hseries t))

/-- Source-only alternative: nonrigidity excludes every weighted real-periodic phase. -/
theorem quantization_rigidity_or_no_real_periodic_phase {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∀ r : ℝ, 1 < r → ∀ p : ℤ → ℂ,
        (Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log r| / 2)) →
        ¬(∀ t : ℝ, 0 < t →
          cexp (((2 * Real.pi * quantizationResidualCumulative hW t : ℝ) : ℂ) * I) =
            ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log r * t : ℝ) : ℂ) * I)) := by
  classical
  by_cases hR : (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis
  · exact Or.inl hR
  · exact Or.inr fun r hr p hp hphase =>
      hR (quantization_rigidity_of_real_periodic_phase hW hr hp hphase)

end RHTower.WeilSpectral
