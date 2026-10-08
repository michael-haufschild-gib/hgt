import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadicalTranslation
import GaloisForLFunctions.RHTower.WeilWorkQuantizationArithmeticSpectrum
import GaloisForLFunctions.RHTower.WeilWorkQuantizationPeriodicResidues

/-!
# Actual residues vanish at irrational radical heights

Unit translation sends a positive irrational radical outside every positive
radical resonance. The actual period-one residue law therefore annihilates
all such heights, without isolating a single harmonic or dropping an infinite
resonance chain.
-/

open Complex Set
noncomputable section
namespace RHTower.WeilSpectral

theorem quantization_radical_real_sum_add_one {ι : Type} {lam : ℕ → ℝ}
    (p : ι → ℂ) (ω : ι → ℝ)
    (hrad : ∀ j, ∃ N : ℕ, 0 < N ∧ ∃ q : ℚ, (Real.exp (ω j / 2)) ^ N = q)
    {x : ℝ} (hx : 0 < x)
    (hxr : ∃ N : ℕ, 0 < N ∧ ∃ q : ℚ, x ^ N = q)
    (hxi : ¬∃ q : ℚ, (q : ℝ) = x) :
    quantizationRealFrequencySum lam p ω (x + 1) = 0 := by
  have hzero (j : ι) : quantizationFrequencyResidue lam (ω j - 2 * Real.log (x + 1)) 1 = 0 := by
    have hn : ¬∃ n, quantizationFrequencyResonates (ω j - 2 * Real.log (x + 1)) 1 n := by
      rintro ⟨n, hn, he⟩
      have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      rw [Nat.cast_one, Real.log_one] at he
      have hs : (n : ℝ) * Real.exp (ω j / 2) = x + 1 := by
        rw [← Real.exp_log hnR, ← Real.exp_add,
          show Real.log n + ω j / 2 = Real.log (x + 1) by linarith,
          Real.exp_log (by linarith)]
      obtain ⟨N, hN, q, hq⟩ := hxr
      obtain ⟨M, hM, a, ha⟩ := hrad j
      have hpow : (x + 1) ^ M = (((n : ℚ) ^ M * a : ℚ) : ℝ) := by
        rw [← hs, mul_pow, ha]
        push_cast
        rfl
      exact hxi (quantization_radical_translate_rational hx hN hM hq hpow)
    simp only [quantizationFrequencyResidue, dif_neg hn]
  simp only [quantizationRealFrequencySum, hzero, mul_zero, tsum_zero]

/-- Full source coupling forces zero at every positive irrational radical,
even when that height has infinitely many represented resonances. -/
theorem quantization_phase_radical_residue_zero {ι : Type} [Countable ι]
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2))
    (hphase : ∀ t : ℝ, 0 < t →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW t : ℝ) : ℂ) * I) =
        ∑' j, p j * cexp (((ω j * t : ℝ) : ℂ) * I))
    (hrad : ∀ j, ∃ N : ℕ, 0 < N ∧ ∃ q : ℚ, (Real.exp (ω j / 2)) ^ N = q)
    {x : ℝ} (hx : 0 < x)
    (hxr : ∃ N : ℕ, 0 < N ∧ ∃ q : ℚ, x ^ N = q)
    (hxi : ¬∃ q : ℚ, (q : ℝ) = x) :
    quantizationRealFrequencySum lam p ω x = 0 := by
  rw [← quantization_phase_resonance_periodic hW hp hphase hx]
  exact quantization_radical_real_sum_add_one p ω hrad hx hxr hxi

theorem quantization_exp_int_mul (a : ℝ) (k : ℤ) :
    Real.exp ((k : ℝ) * a) = (Real.exp a) ^ k := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp [Real.exp_nat_mul]
  · simp [Real.exp_nat_mul, Real.exp_neg, neg_mul]

theorem quantization_periodic_frequency_radical {r : ℝ} (hr : 0 < r)
    {N : ℕ} (hN : 0 < N) {q : ℚ} (hq : r ^ N = q) (k : ℤ) :
    ∃ M : ℕ, 0 < M ∧ ∃ a : ℚ,
      (Real.exp ((2 * (k : ℝ) * Real.log r) / 2)) ^ M = a := by
  refine ⟨N, hN, q ^ k, ?_⟩
  rw [← Real.exp_nat_mul]
  have he : (N : ℝ) * (2 * (k : ℝ) * Real.log r / 2) =
      (k : ℝ) * ((N : ℝ) * Real.log r) := by ring
  rw [he, quantization_exp_int_mul, Real.exp_nat_mul, Real.exp_log hr, hq]
  push_cast
  rfl

/-- Source-only residue obstruction for every real periodic base. L3p pays
the rational-power condition in the nonrigid branch. -/
theorem quantization_rigidity_or_radical_residue_zero {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∀ r : ℝ, 1 < r → ∀ p : ℤ → ℂ,
        (Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log r| / 2)) →
        (∀ t : ℝ, 0 < t →
          cexp (((2 * Real.pi * quantizationResidualCumulative hW t : ℝ) : ℂ) * I) =
            ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log r * t : ℝ) : ℂ) * I)) →
        ∀ x : ℝ, 0 < x →
          (∃ N : ℕ, 0 < N ∧ ∃ q : ℚ, x ^ N = q) →
          (¬∃ q : ℚ, (q : ℝ) = x) →
          quantizationRealFrequencySum lam p (fun k => 2 * (k : ℝ) * Real.log r) x = 0 := by
  rcases quantization_rigidity_or_rational_period_power hW with hR | hpower
  · exact Or.inl hR
  · right
    intro r hr p hp hphase x hx hxr hxi
    obtain ⟨N, m, n, hN, hm, hn, he⟩ := hpower r hr p hp hphase
    have hq : r ^ N = (((m : ℚ) / n : ℚ) : ℝ) := by push_cast; exact he
    exact quantization_phase_radical_residue_zero hW hp hphase
      (quantization_periodic_frequency_radical (by linarith) (by omega) hq) hx hxr hxi

end RHTower.WeilSpectral
