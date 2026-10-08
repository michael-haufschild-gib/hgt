import GaloisForLFunctions.RHTower.WeilWorkQuantizationFrequencyMass
import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadicalResidues

/-!
# Elimination of irrational radical frequency mass

The actual inverse convolution turns residue vanishing on every integer
dilation of an irrational radical into vanishing of its frequency mass.
For a periodic representation, distinct harmonics have distinct scales.
-/

open Complex Set
noncomputable section
namespace RHTower.WeilSpectral

theorem quantization_radical_div_nat {x : ℝ} {n : ℕ}
    (hxr : ∃ N : ℕ, 0 < N ∧ ∃ q : ℚ, x ^ N = q) :
    ∃ N : ℕ, 0 < N ∧ ∃ q : ℚ, (x / n) ^ N = q := by
  obtain ⟨N, hN, q, hq⟩ := hxr
  refine ⟨N, hN, q / (n : ℚ) ^ N, ?_⟩
  rw [div_pow, hq]
  push_cast
  rfl

theorem quantization_irrational_div_nat {x : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hxi : ¬∃ q : ℚ, (q : ℝ) = x) : ¬∃ q : ℚ, (q : ℝ) = x / n := by
  rintro ⟨q, hq⟩
  apply hxi ⟨q * n, ?_⟩
  push_cast
  rw [hq, div_mul_cancel₀ x (by exact_mod_cast hn)]

theorem quantization_phase_radical_mass_zero {ι : Type} [Countable ι]
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2))
    (hphase : ∀ t : ℝ, 0 < t →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW t : ℝ) : ℂ) * I) =
        ∑' j, p j * cexp (((ω j * t : ℝ) : ℂ) * I))
    (hrad : ∀ j, ∃ N : ℕ, 0 < N ∧ ∃ q : ℚ, (Real.exp (ω j / 2)) ^ N = q)
    {x : ℝ} (hx : 0 < x)
    (hxi : ¬∃ q : ℚ, (q : ℝ) = x) :
    quantizationFrequencyMass p ω x = 0 := by
  classical
  by_cases hxr : ∃ N : ℕ, 0 < N ∧ ∃ q : ℚ, x ^ N = q
  swap
  · have hz (j : ι) : quantizationFrequencyMassTerm p ω x j = 0 := by
      have he : Real.exp (ω j / 2) ≠ x := by
        intro he
        exact hxr (he ▸ hrad j)
      simp only [quantizationFrequencyMassTerm, if_neg he]
    simp only [quantizationFrequencyMass, hz, tsum_zero]
  rw [quantization_frequencyMass_inverse hW hp hx]
  have hz (n : ℕ) :
      LSeries.term (quantizationInverseCoeff lam) (((3 / 2 : ℝ) : ℂ)) n *
        ((Real.exp (-(3 * Real.log (x / n) / 2)) : ℂ) *
          quantizationRealFrequencySum lam p ω (x / n)) = 0 := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [quantization_phase_radical_residue_zero hW hp hphase hrad
        (div_pos hx (by exact_mod_cast Nat.pos_of_ne_zero hn))
        (quantization_radical_div_nat hxr) (quantization_irrational_div_nat hn hxi),
        mul_zero, mul_zero]
  simp only [hz, tsum_zero]

theorem quantization_periodic_frequencyMass {r : ℝ} (hr : 1 < r)
    (p : ℤ → ℂ) (k : ℤ) :
    quantizationFrequencyMass p (fun j => 2 * (j : ℝ) * Real.log r)
        (Real.exp ((k : ℝ) * Real.log r)) =
      p k * (Real.exp (-((k : ℝ) * Real.log r)) : ℂ) := by
  classical
  have he (j : ℤ) : 2 * (j : ℝ) * Real.log r / 2 = (j : ℝ) * Real.log r := by ring
  unfold quantizationFrequencyMass
  rw [tsum_eq_single k]
  · simp [quantizationFrequencyMassTerm, he]
  · intro j hj
    have hne : Real.exp ((j : ℝ) * Real.log r) ≠ Real.exp ((k : ℝ) * Real.log r) := by
      intro h
      have hc := mul_right_cancel₀ (Real.log_pos hr).ne' (Real.exp_injective h)
      exact hj (by exact_mod_cast hc)
    simp [quantizationFrequencyMassTerm, he, hne]

theorem quantization_periodic_irrational_harmonic_zero {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {r : ℝ} (hr : 1 < r) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log r| / 2))
    (hphase : ∀ t : ℝ, 0 < t →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW t : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log r * t : ℝ) : ℂ) * I))
    {N : ℕ} (hN : 0 < N) {q : ℚ} (hq : r ^ N = q) {k : ℤ}
    (hki : ¬∃ q : ℚ, (q : ℝ) = Real.exp ((k : ℝ) * Real.log r)) : p k = 0 := by
  have hrad := quantization_periodic_frequency_radical (by linarith : 0 < r) hN hq
  have hz := quantization_phase_radical_mass_zero hW hp hphase hrad (Real.exp_pos _) hki
  rw [quantization_periodic_frequencyMass hr p k] at hz
  exact (mul_eq_zero.mp hz).resolve_right (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

/-- Source-only support classification: every active harmonic of every
weighted periodic representation of a nonrigid source has rational scale. -/
theorem quantization_rigidity_or_rational_harmonics {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∀ r : ℝ, 1 < r → ∀ p : ℤ → ℂ,
        (Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log r| / 2)) →
        (∀ t : ℝ, 0 < t →
          cexp (((2 * Real.pi * quantizationResidualCumulative hW t : ℝ) : ℂ) * I) =
            ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log r * t : ℝ) : ℂ) * I)) →
        ∀ k : ℤ, p k ≠ 0 → ∃ q : ℚ, (q : ℝ) = Real.exp ((k : ℝ) * Real.log r) := by
  classical
  rcases quantization_rigidity_or_rational_period_power hW with hR | hpower
  · exact Or.inl hR
  · right
    intro r hr p hp hphase k hk
    obtain ⟨N, m, n, hN, hm, hn, he⟩ := hpower r hr p hp hphase
    have hq : r ^ N = (((m : ℚ) / n : ℚ) : ℝ) := by push_cast; exact he
    by_contra hki
    exact hk (quantization_periodic_irrational_harmonic_zero hW hr hp hphase
      (by omega) hq hki)

end RHTower.WeilSpectral
