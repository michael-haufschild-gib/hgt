import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.TailBlock
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.Cutoff

/-! # Common physical probes and the simultaneous moment envelope -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

/-- A single physical omission satisfies a whole bounded continuum of trace resolutions, with amplitude independent of its largest order. -/
theorem physical_moment_family_probe (Q : GibbsExponent) {σ t R : ℝ} (hs : 0 < σ) (ht : 1 ≤ t) (hR : t ≤ R) :
    ∃ b ∈ physicalSpectra 1, (highWindowFactor σ/5)*(t/R^σ) < ‖relativePartition b (⟨σ,t⟩:ℂ)‖ ∧
      ∀ q : GibbsExponent, q ≤ Q → momentLoss q b ≤ (1/R)^q.val := by
  have hRp := (zero_lt_one.trans_le ht).trans_le hR
  obtain ⟨b,hL,hD⟩ := common_tail_profile hs ht hR
  obtain ⟨c,hphys,hc,hd⟩ := physical_moment_probe Q (z := ⟨σ,t⟩) hs b hL (hD Q)
  have hw : momentLoss Q c ≤ (1/R)^Q.val := hd.le.trans_eq (by rw [one_div R,Real.inv_rpow hRp.le,one_div])
  have hroot := Real.rpow_le_rpow (momentLoss_nonneg Q c) hw (inv_nonneg.mpr (show 0 < Q.val from Q.property).le)
  rw [Real.rpow_rpow_inv (one_div_pos.mpr hRp).le (show 0 < Q.val from Q.property).ne'] at hroot
  refine ⟨c,hphys,hc,?_⟩
  intro q hq
  have he := Real.rpow_le_rpow (Real.rpow_nonneg (momentLoss_nonneg q c) _) ((moment_root_monotone c hq).trans hroot) q.property.le
  rwa [Real.rpow_inv_rpow (momentLoss_nonneg q c) (show 0 < q.val from q.property).ne'] at he

/-- Controlling the order equal to the real temperature supplies a uniform cap for every joint measurement containing it. -/
theorem own_moment_amplitude_cap {σ t R : ℝ} (hs : 0 < σ) (ht : 1 ≤ t) (hR : t ≤ R) (b : SpectralBand 1)
    (h : momentLoss ⟨σ,hs⟩ b ≤ (1/R)^σ) :
    ‖relativePartition b (⟨σ,t⟩:ℂ)‖ ≤ ((σ+1)/σ)*(t/R^σ) := by
  have ht' := zero_lt_one.trans_le ht
  have hRp := ht'.trans_le hR
  rw [one_div R,Real.inv_rpow hRp.le] at h
  have he := relativePartition_norm_le b ⟨σ,hs⟩ (z := ⟨σ,t⟩) le_rfl
  have hh := mul_le_mul (div_le_div_of_nonneg_right (clock_height_norm_bounds hs ht).2 hs.le) h (momentLoss_nonneg _ b)
    (div_nonneg (mul_pos (add_pos hs zero_lt_one) ht').le hs.le)
  exact (he.trans hh).trans_eq (by ring)

/-- Taking the cutoff in the full interlacing band permits all moment orders at once. -/
theorem simultaneous_band_envelope {σ t R : ℝ} (hs : 0 < σ) (ht : 1 ≤ t) (hR : t ≤ R) :
    let A := {x : ℝ | ∃ b : SpectralBand 1, (∀ q : GibbsExponent, momentLoss q b ≤ (1/R)^q.val) ∧
      ‖relativePartition b (⟨σ,t⟩:ℂ)‖ = x}
    (highWindowFactor σ/5)*(t/R^σ) < sSup A ∧ sSup A ≤ ((σ+1)/σ)*(t/R^σ) := by
  dsimp only
  obtain ⟨b,hL,hD⟩ := common_tail_profile hs ht hR
  have hRp := (zero_lt_one.trans_le ht).trans_le hR
  have hb (q : GibbsExponent) : momentLoss q b ≤ (1/R)^q.val :=
    (hD q).le.trans_eq (by rw [one_div R,Real.inv_rpow hRp.le,one_div])
  let A := {x : ℝ | ∃ d : SpectralBand 1, (∀ q : GibbsExponent, momentLoss q d ≤ (1/R)^q.val) ∧
    ‖relativePartition d (⟨σ,t⟩:ℂ)‖ = x}
  have hmem : ‖relativePartition b (⟨σ,t⟩:ℂ)‖ ∈ A := ⟨b,hb,rfl⟩
  have hu (x : ℝ) (hx : x ∈ A) : x ≤ ((σ+1)/σ)*(t/R^σ) := by
    obtain ⟨d,hd,rfl⟩ := hx
    exact own_moment_amplitude_cap hs ht hR d (hd ⟨σ,hs⟩)
  exact ⟨hL.trans_le (le_csSup ⟨_,hu⟩ hmem),csSup_le ⟨_,hmem⟩ hu⟩

/-- The same sharp band envelope holds when the constraint is exact preservation of the large occupation levels. -/
theorem pinned_band_envelope {σ t R : ℝ} (hs : 0 < σ) (ht : 1 ≤ t) (hR : t ≤ R) :
    let A := {x : ℝ | ∃ b : SpectralBand 1, (∀ k, 1/R < occupationWeight k → (b k).val = occupationWeight k) ∧
      ‖relativePartition b (⟨σ,t⟩:ℂ)‖ = x}
    (highWindowFactor σ/5)*(t/R^σ) < sSup A ∧ sSup A ≤ ((σ+1)/σ)*(t/R^σ) := by
  have hRp := (zero_lt_one.trans_le ht).trans_le hR
  simpa only [all_moment_ceilings_iff _ (one_div_pos.mpr hRp).le] using simultaneous_band_envelope hs ht hR

#print axioms pinned_band_envelope
#print axioms physical_moment_family_probe
#print axioms own_moment_amplitude_cap
#print axioms simultaneous_band_envelope

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
