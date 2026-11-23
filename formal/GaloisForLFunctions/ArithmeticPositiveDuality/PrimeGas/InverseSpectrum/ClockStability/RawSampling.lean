import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.NoisyData

/-! # Sampling the surviving partition itself on the composition line -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

/-- Trusted entries of a finite readout of the continued surviving partition at a known clock height. -/
def fitsSurviving {r : ℕ} (b : OrderedSpectrum r) (t : ℝ) (y : ℕ → ℂ)
    (start last : ℕ) (bad : Finset ℕ) (η : ℝ) : Prop :=
  ∀ n, start ≤ n → n ≤ last → n ∉ bad → ‖survivingPartition b.val (compositionSample t n) - y n‖ ≤ η

private theorem fits_relative_of_surviving {l u : ℝ} {r : ℕ} (t : Icc l u) (b : OrderedSpectrum r)
    {y : ℕ → ℂ} {start last : ℕ} {bad : Finset ℕ} {η : ℝ} (hη : 0 ≤ η) (h : fitsSurviving b t.val y start last bad η) :
    fitsReadings (t,b) t.val (fun n => riemannZeta (compositionSample t.val n) - y n) start last bad η := by
  refine ⟨by simpa only [sub_self,abs_zero] using hη,?_⟩
  intro n hn hl hb
  have e : clockReading t.val b n - (riemannZeta (compositionSample t.val n)-y n) =
      y n - survivingPartition b.val (compositionSample t.val n) := by
    unfold clockReading survivingPartition
    abel
  rw [e,norm_sub_rev]
  exact h n hn hl hb

/-- With a common clock, noisy raw partition values suffice and can have k independent outliers per candidate. -/
theorem finite_surviving_partition_sampling (r : ℕ) (l u : ℝ) (f : SpectralResponse) {ε : ℝ} (hε : 0 < ε)
    (start k : ℕ) :
    ∃ N : ℕ, ∀ (t : Icc l u) (b c : OrderedSpectrum r) (y : ℕ → ℂ) (B C : Finset ℕ),
      B.card ≤ k → C.card ≤ k →
      fitsSurviving b t.val y start (start+N+2*k) B (occupationWeight N/2) →
      fitsSurviving c t.val y start (start+N+2*k) C (occupationWeight N/2) →
      detectorError f b.val c.val < ε := by
  obtain ⟨N,hN⟩ := noisy_clock_stability r l u f hε start k
  refine ⟨N,fun t b c y B C hB hC hb hc => ?_⟩
  have hη := (half_pos (occupationWeight_pos N)).le
  exact hN (t,b) (t,c) t.val _ B C hB hC (fits_relative_of_surviving t b hη hb)
    (fits_relative_of_surviving t c hη hc)

#print axioms finite_surviving_partition_sampling

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
