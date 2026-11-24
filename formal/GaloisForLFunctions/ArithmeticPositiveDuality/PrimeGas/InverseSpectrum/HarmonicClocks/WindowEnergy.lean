import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Retention
import GaloisForLFunctions.HTGeometry.MontgomeryVaughanBandPerturbation

/-! # Second-moment control of missing harmonic amplitudes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- Contribution of finitely many occupations to a running block of responses. -/
def windowBlock (v : MissingWave) (t : ℝ) (F : Finset ℕ+) (k d : ℕ) :=
  ∑ n ∈ F, (occupationProbability v n:ℂ)*(splitPhase t n^k*clockPolynomial d (splitPhase t n))

private theorem weighted_amplitude_sq {ι : Type*} (F : Finset ι) (w : ι → ℝ) (z : ι → ℂ)
    (hw : ∀ i, 0 ≤ w i) :
    ‖∑ i ∈ F, (w i:ℂ)*z i‖^2 ≤ (∑ i ∈ F, w i)*∑ i ∈ F, w i*‖z i‖^2 := by
  have h := norm_sum_le F (fun i => (w i:ℂ)*z i)
  simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw _)] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (GaloisForLFunctions.HTGeometry.sq_sum_weighted_le F w (fun i => ‖z i‖) (fun i _ => hw i))

private theorem tail_hasSum {A : Type*} [NormedAddCommGroup A] [CompleteSpace A] {f : ℕ+ → A}
    {b : A} (hs : HasSum f b) (F : Finset ℕ+) :
    HasSum (fun n : (Fᶜ : Set ℕ+) => f n) (b-∑ n ∈ F, f n) := by
  have h := hs.summable.subtype (fun n => n ∈ (Fᶜ : Set ℕ+))
  apply h.hasSum_iff.mpr
  exact eq_sub_iff_add_eq'.mpr ((hs.summable.sum_add_tsum_compl (s := F)).trans hs.tsum_eq)

/-- Missing block amplitude is bounded by the geometric mean of missing mass and missing Fejér energy. -/
theorem windowBlock_tail_sq (v : MissingWave) (t : ℝ) (F : Finset ℕ+) (k d : ℕ) :
    ‖blockReading v t k d-windowBlock v t F k d‖^2 ≤
      (1-windowMass v F)*(fejerReading v t d-windowFejer v t F d) := by
  let μ (n : ℕ+) := occupationProbability v n
  let z (n : ℕ+) := splitPhase t n^k*clockPolynomial d (splitPhase t n)
  have hf := tail_hasSum (blockReading_hasSum v t k d) F
  have hp := tail_hasSum (occupationLaw_hasSum v) F
  have hq := tail_hasSum (fejer_hasSum v t d) F
  have hn (n : ℕ+) : ‖z n‖ = ‖clockPolynomial d (splitPhase t n)‖ := by
    simp only [z,norm_mul,norm_pow,splitPhase_norm,one_pow,one_mul]
  apply le_of_tendsto_of_tendsto' (hf.norm.pow 2) (Filter.Tendsto.mul hp hq)
  intro G
  simpa only [hn] using weighted_amplitude_sq G (fun n : (Fᶜ : Set ℕ+) => μ n)
    (fun n => z n) (fun n => occupationLaw_nonneg v n)

theorem windowBlock_limit {t : ℕ → ℝ} {v : ℕ → MissingWave} {m : ℕ+ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (hm : ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n)))
    (F : Finset ℕ+) (k d : ℕ) :
    Tendsto (fun j => windowBlock (v j) (t j) F k d) atTop (𝓝 ((d:ℂ)*(∑ n ∈ F, m n:ℝ))) := by
  have h := tendsto_finsetSum F (fun n _ =>
    (hm n).ofReal.mul (((clockPhase_limit ht n).pow k).mul (clockPolynomial_limit ht n d)))
  simpa only [windowBlock,one_pow,one_mul,← Finset.sum_mul,← Complex.ofReal_sum,mul_comm (d:ℂ)] using h

theorem windowFejer_limit {t : ℕ → ℝ} {v : ℕ → MissingWave} {m : ℕ+ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (hm : ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n)))
    (F : Finset ℕ+) (d : ℕ) :
    Tendsto (fun j => windowFejer (v j) (t j) F d) atTop (𝓝 ((d:ℝ)^2*∑ n ∈ F, m n)) := by
  have h := tendsto_finsetSum F (fun n _ => (hm n).mul ((clockPolynomial_limit ht n d).norm.pow 2))
  simpa only [windowFejer,Complex.norm_natCast,← Finset.sum_mul,mul_comm ((d:ℝ)^2)] using h

#print axioms windowBlock_tail_sq
#print axioms windowBlock_limit
#print axioms windowFejer_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
