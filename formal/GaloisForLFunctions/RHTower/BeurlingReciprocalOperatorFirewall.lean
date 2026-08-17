import GaloisForLFunctions.HTGeometry.EntireDet2HilbertSchmidtContinuity
import GaloisForLFunctions.RHTower.BeurlingRHSensitivityThreshold

/-!
# Beurling reciprocal-mass operator firewall

The Beurling sensitivity family has off-critical zeros while its reciprocal prime mass tends to zero.
This module tests a genuinely operator-valued response: a source assignment may replace scalar
renormalization by a Hilbert--Schmidt kernel whose entire Hilbert--Carleman determinant records the
selected divisor.

Continuity is stated in the exact reciprocal-mass topology.  If source perturbations of reciprocal
mass below `δ` force Hilbert--Schmidt distance below `ε`, and every selected off-line Beurling zero is
encoded as a determinant zero at the normalized spectral coordinate `1`, then the base determinant
must vanish at `1`.  Hence no such assignment exists when the base determinant is nonzero there.

This does not retire arithmetic-discontinuous or non-Hilbert--Schmidt operator assignments.
-/

namespace RHTower.BeurlingSensitivity

open Filter Topology GaloisForLFunctions.HTGeometry HilbertSchmidt

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- Continuity at the unperturbed source from Beurling reciprocal mass to Hilbert--Schmidt norm. -/
def ReciprocalMassToHSContinuousAtBase
    (β : ℝ) (K : ℝ → ι × ι → ℂ) (K₀ : ι × ι → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ γ : ℝ,
    Real.log (1 + γ ^ 2 / (1 - β) ^ 2) < δ →
      hsNorm (K γ - K₀) < ε

/-- **Reciprocal-topology divisor firewall.** There is no Hilbert--Schmidt kernel assignment which
is continuous at the rational source for reciprocal generalized-prime mass and sends every selected
off-critical Beurling zero to a fixed normalized zero of its entire regularized determinant, provided
the base determinant is nonzero there. -/
theorem not_exists_beurling_reciprocalContinuous_divisorFaithful_entireDet2
    {β : ℝ} (hβ1 : 1 / 2 < β) (hβ2 : β < 1)
    (K₀ : ι × ι → ℂ) (hK₀ : IsHS K₀)
    (hbase : entireDet2 K₀ 1 ≠ 0) :
    ¬ ∃ K : ℝ → ι × ι → ℂ,
      (∀ γ, IsHS (K γ)) ∧
      ReciprocalMassToHSContinuousAtBase β K K₀ ∧
      (∀ γ : ℝ, γ ≠ 0 →
        perturbedZeta β γ ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 →
          1 / 2 < ((β : ℂ) + (γ : ℂ) * Complex.I).re →
          entireDet2 (K γ) 1 = 0) := by
  rintro ⟨K, hK, hcont, hfaith⟩
  let γseq : ℕ → ℝ := fun n => 1 / (n + 1)
  have hγlim : Tendsto γseq atTop (nhds 0) := by
    simpa only [γseq] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hmasslim : Tendsto
      (fun n => Real.log (1 + γseq n ^ 2 / (1 - β) ^ 2)) atTop (nhds 0) :=
    (tendsto_reciprocalMass β hβ2).comp hγlim
  have hmass_nonneg : ∀ γ : ℝ,
      0 ≤ Real.log (1 + γ ^ 2 / (1 - β) ^ 2) := by
    intro γ
    apply Real.log_nonneg
    have hb : 0 < (1 - β) ^ 2 := by positivity
    have hq : 0 ≤ γ ^ 2 / (1 - β) ^ 2 := div_nonneg (sq_nonneg γ) hb.le
    linarith
  have hKlim : Tendsto (fun n => hsNorm (K (γseq n) - K₀)) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hcontrol⟩ := hcont ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmasslim δ hδ
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNorm_nonneg _)]
    apply hcontrol
    have hnear := hN n hn
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (hmass_nonneg (γseq n))] at hnear
    exact hnear
  have hzero : ∀ n, entireDet2 (K (γseq n)) 1 = 0 := by
    intro n
    have hγpos : 0 < γseq n := by
      simp only [γseq]
      positivity
    exact hfaith (γseq n) (ne_of_gt hγpos)
      (perturbedZeta_eq_zero β (ne_of_gt hγpos)) (by simpa [re_of_zero] using hβ1)
  exact not_persistent_entireDet2_zero_of_hsNorm_tendsto
    (fun n => K (γseq n)) K₀ (fun n => hK (γseq n)) hK₀ hKlim 1 hbase hzero

end

end RHTower.BeurlingSensitivity
