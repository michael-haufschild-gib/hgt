import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Saturation.Harmonics

/-! # Harmonic revivals forced by extremal retention -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- At maximal retained mass each running block of r responses converges to one. -/
theorem extremal_block_limit {r : ℕ+} {t : ℕ → ℝ} {v : ℕ → MissingWave} {m : ℕ+ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (hc : ∀ j, harmonicTest r 0 (v j) (t j))
    (hm : ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n)))
    (hs : HasSum m (1/(r.val:ℝ))) (k : ℕ) :
    Tendsto (fun j => blockReading (v j) (t j) k r.val) atTop (𝓝 1) := by
  have he : ((r.val:ℂ)*(retentionCeiling r 0:ℝ)) = 1 := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_mul,order_mul_retention]
    simp
  have hl : HasSum m (retentionCeiling r 0) := by simpa [retentionCeiling] using hs
  simpa only [he] using saturated_block_limit ht tendsto_const_nhds hc hm hl k

/-- Saturating the escape bound determines every harmonic, including the untested multiples of r. -/
theorem extremal_harmonic_revival {r : ℕ+} {t : ℕ → ℝ} {v : ℕ → MissingWave} {m : ℕ+ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (hc : ∀ j, harmonicTest r 0 (v j) (t j))
    (hm : ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n)))
    (hs : HasSum m (1/(r.val:ℝ))) (k : ℕ) :
    Tendsto (fun j => harmonicReading (v j) (t j) k) atTop (𝓝 (if r.val ∣ k then (1:ℂ) else 0)) := by
  have hl : HasSum m (retentionCeiling r 0) := by simpa [retentionCeiling] using hs
  simpa only [Complex.ofReal_zero] using saturated_harmonic_limit ht tendsto_const_nhds hc hm hl k

#print axioms extremal_block_limit
#print axioms extremal_harmonic_revival

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
