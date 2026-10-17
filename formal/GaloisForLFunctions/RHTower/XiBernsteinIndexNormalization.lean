import GaloisForLFunctions.RHTower.XiBernsteinIndexAsymptotic
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor

/-!
# Normalization and amplitude recovery of the actual index profile

The actual source has positive energy in every degree. Its normalized index tests converge,
and its energy growth determines the amplitude used in the index measure.
-/

open Filter Topology
open scoped BigOperators Real unitInterval

namespace RHTower

noncomputable section

theorem primeArchEndpointBernsteinIndexEnergy_one_eq_purity (n : ℕ) :
    primeArchEndpointBernsteinIndexEnergy (fun _ => 1) n = primeArchEndpointBernsteinPurity n := by
  rw [primeArchEndpointBernsteinIndexEnergy, primeArchEndpointBernsteinPurity,
    bernsteinCoefficientPurity]
  simp only [one_mul]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ‖primeArchEndpointBernsteinPacket n k‖ ^ 2) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [primeArchEndpointBernsteinPacket, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem primeArchEndpointBernsteinIndexEnergy_one_pos (n : ℕ) :
    0 < primeArchEndpointBernsteinIndexEnergy (fun _ => 1) n := by
  rw [primeArchEndpointBernsteinIndexEnergy_one_eq_purity]
  have h := mass_sq_le_card_mul_primeArchEndpointBernsteinPurity n
  have hmass := sq_pos_of_pos normalizedPrimeArchMoment_zero_pos
  have hn : 0 < (n + 1 : ℝ) := by positivity
  nlinarith

def xiEndpointBernsteinOccupationMass (D : Finset XiZeroCopy) : ℝ :=
  ∑ u ∈ xiEndpointCoordinateSet D,
    ‖xiEndpointCoordinateWeight D u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u

theorem xiEndpointBernsteinOccupationMass_pos (D : Finset XiZeroCopy) {B : ℝ}
    (hDne : D.Nonempty) (hB : 1 < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B) :
    0 < xiEndpointBernsteinOccupationMass D := by
  apply Finset.sum_pos _ (xiEndpointCoordinateSet_nonempty hDne)
  intro u hu
  have hc : 0 < ‖xiEndpointCoordinateWeight D u‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (xiEndpointCoordinateWeight_ne_zero hu))
  obtain ⟨q, hq, hqu⟩ := Finset.mem_image.mp hu
  have him : u.im ≠ 0 := by
    rw [← hqu]
    exact (xiEndpoint_offLine_and_normalized_im_ne_zero_of_one_lt_amplitude q
      (by rw [hD q hq]; exact hB)).2
  exact mul_pos hc (bernsteinAffineRowHalfOrderConstant_pos
    (fun heq => him (by rw [heq]; rfl)) (fun heq => him (by rw [heq]; rfl)))

/-- The source packet defines a probability profile in every degree, with the exact limiting
test law obtained by normalizing the maximal divisor weights. -/
theorem tendsto_primeArchEndpointBernstein_normalized_index_test
    (D : Finset XiZeroCopy) {B beta : ℝ} (hDne : D.Nonempty) (hB : 1 < B)
    (hbeta0 : 0 ≤ beta) (hbeta : beta < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    (htail : ∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta)
    {g : I → ℝ} {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, |g x| ≤ M)
    (hg : ∀ u ∈ xiEndpointCoordinateSet D, ContinuousAt g (bernsteinAffineOccupation u)) :
    Tendsto (fun n : ℕ => primeArchEndpointBernsteinIndexEnergy g n /
      primeArchEndpointBernsteinIndexEnergy (fun _ => 1) n) atTop
      (nhds ((∑ u ∈ xiEndpointCoordinateSet D, ‖xiEndpointCoordinateWeight D u‖ ^ 2 *
        bernsteinAffineRowHalfOrderConstant u * g (bernsteinAffineOccupation u)) /
          xiEndpointBernsteinOccupationMass D)) := by
  have hnum := tendsto_primeArchEndpointBernsteinIndexEnergy_of_maximalPacket D hB hbeta0 hbeta
    hD htail hM hbound hg
  have hden := tendsto_primeArchEndpointBernsteinIndexEnergy_of_maximalPacket D hB hbeta0 hbeta
    hD htail (g := fun _ => 1) (M := 1) (by norm_num) (by intro p; norm_num)
    (fun u hu => continuous_const.continuousAt)
  simp only [mul_one] at hden
  have hmass := xiEndpointBernsteinOccupationMass_pos D hDne hB hD
  have h := hnum.div hden hmass.ne'
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hB0 : 0 < B := lt_trans zero_lt_one hB
  have hscale : Real.sqrt n / (B ^ 2) ^ n ≠ 0 := by positivity
  exact mul_div_mul_left _ _ hscale

theorem primeArchEndpointBernsteinIndexEnergy_one_eq_rpow (n : ℕ) :
    primeArchEndpointBernsteinIndexEnergy (fun _ => 1) n =
      primeArchEndpointBernsteinRpowEnergy 2 n := by
  rw [primeArchEndpointBernsteinIndexEnergy, primeArchEndpointBernsteinRpowEnergy,
    finitePacketRpowEnergy]
  simp only [one_mul, Real.rpow_two]
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ => ‖primeArchEndpointBernsteinPacket n k‖ ^ 2) (n + 1)

/-- The normalization amplitude is itself observed from the same source packet's energy. -/
theorem tendsto_primeArchEndpointBernstein_index_mass_root_of_maximalPacket
    (hRH : ¬ RiemannHypothesis) (D : Finset XiZeroCopy) {B beta : ℝ}
    (hDne : D.Nonempty) (hbeta : beta < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    (htail : ∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) :
    Tendsto (fun n : ℕ =>
      primeArchEndpointBernsteinIndexEnergy (fun _ => 1) n ^ ((n : ℝ)⁻¹))
      atTop (nhds (B ^ 2)) := by
  obtain ⟨B', hB', hsector, ⟨q', hq'⟩, hmax, hlim⟩ :=
    exists_attained_tendsto_primeArchEndpointBernsteinRpowEnergy_of_not_rh
      (p := 2) (by norm_num) hRH
  obtain ⟨q, hq⟩ := hDne
  have hBB' : B ≤ B' := by simpa only [hD q hq] using hmax q
  have hB'B : B' ≤ B := by
    rw [← hq']
    by_cases hq'D : q' ∈ D
    · exact (hD q' hq'D).le
    · exact (htail q' hq'D).trans hbeta.le
  have heq : B' = B := le_antisymm hB'B hBB'
  rw [heq] at hlim
  simpa only [← primeArchEndpointBernsteinIndexEnergy_one_eq_rpow, Real.rpow_two] using hlim

end
end RHTower
