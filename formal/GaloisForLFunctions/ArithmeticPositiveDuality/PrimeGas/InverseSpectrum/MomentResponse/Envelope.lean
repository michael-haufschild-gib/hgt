import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.TailBlock

/-! # Sharp envelope at arbitrary positive real moment -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

/-- Partition amplitudes attained by conserving rank-one omissions at the prescribed relative moment tolerance. -/
def momentAmplitudes (q : GibbsExponent) (σ t D : ℝ) : Set ℝ :=
  {x | ∃ b ∈ physicalSpectra 1, momentLoss q b ≤ D ∧ ‖relativePartition b (⟨σ,t⟩:ℂ)‖ = x}

private theorem envelope_upper (q : GibbsExponent) {σ : ℝ} (hs : 0 < σ) :
    ∃ C > (0:ℝ), ∀ t ≥ (1:ℝ), ∀ R ≥ t, ∀ x ∈ momentAmplitudes q σ t (2/R^q.val), x ≤ C*(t/R^(min σ q.val)) := by
  let a : GibbsExponent := ⟨min σ q.val,lt_min hs q.property⟩
  let p := q.val/a.val
  have hp : 0 < p := div_pos q.property a.property
  have hq' : 0 < q.val := q.property
  have ha' : 0 < a.val := a.property
  have he : q.val*p⁻¹ = a.val := by dsimp only [p]; field_simp [hq'.ne',ha'.ne']
  refine ⟨((σ+1)/a.val)*(2:ℝ)^p⁻¹,mul_pos (div_pos (add_pos hs zero_lt_one) a.property) (Real.rpow_pos_of_pos (by norm_num) _),?_⟩
  rintro t ht R hR x ⟨b,_,hd,rfl⟩
  let z : ℂ := ⟨σ,t⟩
  have ht' := zero_lt_one.trans_le ht
  have hRp := ht'.trans_le hR
  have haq : a ≤ q := show min σ q.val ≤ q.val from min_le_right _ _
  have h := (momentLoss_transfer a q haq b).trans hd
  have hb := Real.rpow_le_rpow (Real.rpow_nonneg (momentLoss_nonneg a b) p) h (inv_nonneg.mpr hp.le)
  change (momentLoss a b^p)^p⁻¹ ≤ (2/R^q.val)^p⁻¹ at hb
  rw [Real.rpow_rpow_inv (momentLoss_nonneg a b) hp.ne',Real.div_rpow (by norm_num : (0:ℝ)≤2)
    (Real.rpow_nonneg hRp.le _),← Real.rpow_mul hRp.le,he] at hb
  have hnorm := relativePartition_norm_le b a (z := z) (min_le_left _ _)
  have hfac := div_le_div_of_nonneg_right (clock_height_norm_bounds hs ht).2 a.property.le
  have hu := mul_le_mul hfac hb (momentLoss_nonneg a b) (div_nonneg (mul_pos (add_pos hs zero_lt_one) ht').le a.property.le)
  exact (hnorm.trans hu).trans_eq (by change _ = _*(t/R^a.val); ring)

private theorem envelope_lower (q : GibbsExponent) {σ : ℝ} (hs : 0 < σ) :
    ∃ c > (0:ℝ), ∀ t ≥ (1:ℝ), ∀ R ≥ t, t ≤ R^q.val →
      ∃ x ∈ momentAmplitudes q σ t (2/R^q.val), c*(t/R^(min σ q.val)) < x := by
  have groundPos := div_pos (shortChordFactor_pos σ) (mul_pos (by norm_num : (0:ℝ)<2) (add_pos zero_lt_one (show 0 < q.val from q.property)))
  rcases le_total σ q.val with h | h
  · refine ⟨highWindowFactor σ/5,div_pos (highWindowFactor_pos σ) (by norm_num),?_⟩
    intro t ht R hR _
    obtain ⟨b,ha,hb⟩ := common_tail_profile hs ht hR
    obtain ⟨c,hphys,hL,hD⟩ := physical_moment_probe q (z := ⟨σ,t⟩) hs b ha (hb q)
    have hcost := div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤2) (Real.rpow_nonneg (zero_le_one.trans (ht.trans hR)) q.val)
    rw [min_eq_left h]
    exact ⟨_,⟨c,hphys,hD.le.trans hcost,rfl⟩,hL⟩
  · refine ⟨_,groundPos,?_⟩
    intro t ht R hR htime
    obtain ⟨c,hphys,hL,hD⟩ := ground_moment_probe q hs ht htime
    have hcost := div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤2) (Real.rpow_nonneg (zero_le_one.trans (ht.trans hR)) q.val)
    rw [min_eq_right h]
    exact ⟨_,⟨c,hphys,hD.le.trans hcost,rfl⟩,hL⟩

/-- In the simultaneous short-angle window the supremum of actual amplitudes has order t/R^min(σ,q). -/
theorem moment_amplitude_envelope (q : GibbsExponent) {σ : ℝ} (hs : 0 < σ) :
    ∃ c > (0:ℝ), ∃ C > (0:ℝ), ∀ t ≥ (1:ℝ), ∀ R ≥ t, t ≤ R^q.val →
      c*(t/R^(min σ q.val)) < sSup (momentAmplitudes q σ t (2/R^q.val)) ∧
      sSup (momentAmplitudes q σ t (2/R^q.val)) ≤ C*(t/R^(min σ q.val)) := by
  obtain ⟨c,hc,hl⟩ := envelope_lower q hs
  obtain ⟨C,hC,hu⟩ := envelope_upper q hs
  refine ⟨c,hc,C,hC,?_⟩
  intro t ht R hR htime
  obtain ⟨x,hx,hL⟩ := hl t ht R hR htime
  exact ⟨hL.trans_le (le_csSup ⟨_,hu t ht R hR⟩ hx),csSup_le ⟨_,hx⟩ (hu t ht R hR)⟩

#print axioms moment_amplitude_envelope

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
