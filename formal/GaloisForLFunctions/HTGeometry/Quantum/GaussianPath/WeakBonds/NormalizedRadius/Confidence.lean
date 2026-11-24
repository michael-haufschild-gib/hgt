import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NormalizedRadius.Survival
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NormalizedRadius.ClockComparison
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.DerivativeBounds.ConfidenceBits

/-! # Joint confidence bounds after fixing every prefix's total interaction strength -/
open Set Filter MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NormalizedRadius
open PrescribedTimes PassageMoments PassageMoments.DerivativeBounds
noncomputable section

/-- Every size and confidence share a deadline for normalized first
excursions. Weak cut directions still force a T⁻¹⁸ joint survival floor. -/
theorem gaussian_fixed_radius_first_passage_confidence :
    ∃ b : ℕ, ∃ c > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let D : ℕ := 2^(k+3)
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let r := sqrt (Fintype.card (PrefixIndex n):ℝ)
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let σ := fun x => crossingOrigin n P (9/80) (atRadius r x)
      let Δ := fun s x => crossingWait n P s (atRadius r x)
      (∀ u : ℕ, let G := (2:ℝ)^(D^b+u*marginOrder k)
        μ.real {x | 2*G<σ x ∨ ∃ s, 2*G<Δ s x} ≤ (32/9)*(1/2:ℝ)^(D+u)) ∧
      ∀ T ≥ (1:ℝ), c ≤ T^18*μ.real {x | T<σ x ∧ ∀ s≤P/2, T<Δ s x} := by
  obtain ⟨b,hb⟩ := gaussian_first_passage_confidence_bits
  obtain ⟨c,hc,hl⟩ := gaussian_normalized_joint_survival
  refine ⟨b,c,hc,?_⟩
  filter_upwards [hb,hl] with k hu hlow
  intro n D P r μ σ Δ
  refine ⟨fun u => ?_,hlow⟩
  intro G
  have h := fixed_radius_clock_comparison n (passageMax k 0) (measurable_passageMax k 0)
    (fun _ ha => passageMax_smul k 0 ha) (G:=G) (by dsimp only [G]; positivity)
  have h' := h.trans (hu u)
  have hs : {x | 2*G<σ x ∨ ∃ s, 2*G<Δ s x} ⊆
      {x | 2*G<passageMax k 0 (atRadius r x)} := by
    rintro x (hx | ⟨s,hx⟩)
    · exact hx.trans_le (le_max_left ..)
    · exact hx.trans_le ((crossingWait_antitone (n:=n) (j:=P) (Nat.zero_le s) _).trans (le_max_right ..))
  apply (measureReal_mono (μ:=μ) hs).trans
  change (3/4:ℝ)*μ.real {x | 2*G<passageMax k 0 (atRadius r x)} ≤ (8/3)*(1/2:ℝ)^(D+u) at h'
  linarith only [h']

#print axioms gaussian_fixed_radius_first_passage_confidence
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NormalizedRadius
