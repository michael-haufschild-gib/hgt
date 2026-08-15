import GaloisForLFunctions.RHTower.BakerGeneralProof.GapFreeGrowthBound

/-!
# Growth bound for a repeated-frequency modulus

This module specializes the gap-free contour/Cauchy estimate to the canonical modulus
`Q(w) = ∏ᵢ (w - μᵢ)^K`. Its interpolation dimension is exactly `card(I) * K`; all constants
depend on an upper frequency radius and never on pairwise frequency separation.
-/

open scoped Classical
open Complex Metric
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

noncomputable def frequencyContourRadius (Omega : ℝ) : ℝ :=
  2 * (Omega + 1)

theorem one_le_frequencyContourRadius {Omega : ℝ} (hOmega : 0 ≤ Omega) :
    1 ≤ frequencyContourRadius Omega := by
  unfold frequencyContourRadius
  linarith

theorem frequency_lt_frequencyContourRadius {Omega : ℝ} (hOmega : 0 ≤ Omega) :
    Omega < frequencyContourRadius Omega := by
  unfold frequencyContourRadius
  linarith

theorem frequencyContourRadius_sub_pos {Omega : ℝ} (hOmega : 0 ≤ Omega) :
    0 < frequencyContourRadius Omega - Omega := by
  linarith [frequency_lt_frequencyContourRadius hOmega]

/-- The generic contour/Cauchy estimate specialized to the canonical repeated-frequency modulus. -/
theorem norm_exponentialPolynomial_le_repeatedFrequency
    {I : Type*} [Fintype I]
    (P : I → Polynomial ℂ) (mu : I → ℂ) (K : ℕ)
    (hP : ∀ i, (P i).natDegree < K)
    {Omega R M : ℝ} (hOmega : 0 ≤ Omega)
    (hmu : ∀ i, ‖mu i‖ ≤ Omega)
    (hR : 0 < R)
    (hboundary : ∀ w ∈ sphere (0 : ℂ) R,
      ‖exponentialPolynomial P mu w‖ ≤ M)
    (z : ℂ) :
    ‖exponentialPolynomial P mu z‖ ≤
      (frequencyContourRadius Omega *
        (Real.exp (‖z‖ * frequencyContourRadius Omega) *
          (frequencyContourRadius Omega ^ (Fintype.card I * K) *
            (1 + Omega) ^ (Fintype.card I * K)) /
          (frequencyContourRadius Omega - Omega) ^ (Fintype.card I * K))) *
        ∑ m ∈ Finset.range (Fintype.card I * K + 1),
          (m.factorial : ℝ) * M / R ^ m := by
  let Q : Polynomial ℂ := repeatedFrequencyModulus mu K
  let rho : ℝ := frequencyContourRadius Omega
  let delta : ℝ := (rho - Omega) ^ (Fintype.card I * K)
  let C : ℝ := (1 + Omega) ^ (Fintype.card I * K)
  have hrho : 1 ≤ rho := one_le_frequencyContourRadius hOmega
  have hOmegaRho : Omega < rho := frequency_lt_frequencyContourRadius hOmega
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact pow_pos (sub_pos.mpr hOmegaRho) _
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hcoeff : coeffNormSum Q ≤ C := by
    dsimp [Q, C]
    exact coeffNormSum_repeatedFrequencyModulus_le_uniform mu K hmu
  have hden : ∀ zeta ∈ sphere (0 : ℂ) rho, delta ≤ ‖Q.eval zeta‖ := by
    intro zeta hzeta
    dsimp [delta, Q]
    exact norm_eval_repeatedFrequencyModulus_ge mu K hOmegaRho hmu hzeta
  have hdvd : ∀ i, (Polynomial.X - Polynomial.C (mu i)) ^ K ∣ Q := by
    intro i
    exact power_dvd_repeatedFrequencyModulus mu K i
  have hmuball : ∀ i, mu i ∈ ball (0 : ℂ) rho := by
    intro i
    rw [mem_ball, dist_zero_right]
    exact (hmu i).trans_lt hOmegaRho
  have hmain := norm_exponentialPolynomial_le_contourHermite
    P mu K hP Q hrho hC hdelta hcoeff hden hdvd hmuball hR hboundary z
  simpa [Q, rho, delta, C, natDegree_repeatedFrequencyModulus] using hmain

end GaloisForLFunctions.RHTower.BakerGeneralProof
