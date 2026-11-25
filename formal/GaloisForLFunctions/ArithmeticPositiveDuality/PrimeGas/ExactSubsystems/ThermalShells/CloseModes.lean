import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints.Geometry
import GaloisForLFunctions.RHTower.STCPrimeWindowPackets

/-! # Distinct prime energies with arbitrarily small separation in every moving band -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells

open Set Filter Topology _root_.RHTower
open BinaryOrientation.LargestPrime.Bands BinaryOrientation.LargestPrime.Bands.Marks

/-- Relative prime windows provide two actual modes with an arbitrarily small unscaled energy gap. -/
theorem eventually_close_modes {c d ε : ℝ} (hc : 0 < c) (hcd : c < d) (hε : 0 < ε) :
    ∀ᶠ h in criticalApproach, ∃ p q : ↥(added c d h),
      0 < squarefreePrimeEnergy q.val-squarefreePrimeEnergy p.val ∧
      squarefreePrimeEnergy q.val-squarefreePrimeEnergy p.val < ε := by
  have hr := sub_pos.mpr (Real.one_lt_exp_iff.mpr hε)
  obtain ⟨X,hX⟩ := exists_prime_ratio_window (c := 1) le_rfl hr
  have step (m : ℝ) (hm : X ≤ m) : ∃ p : Nat.Primes, m < (p:ℝ) ∧ (p:ℝ) < Real.exp ε*m := by
    obtain ⟨p,hp,hlo,hhi⟩ := hX m hm
    refine ⟨⟨p,hp⟩,by simpa only [one_mul] using hlo,?_⟩
    simpa only [one_mul,show 1+(Real.exp ε-1) = Real.exp ε by ring] using hhi
  have hv : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  have hZ : Tendsto (fun h : Ioi (0:ℝ) => Real.exp (c/h.val)) criticalApproach atTop := by
    simpa only [Function.comp_def,div_eq_mul_inv] using
      Real.tendsto_exp_atTop.comp ((tendsto_inv_nhdsGT_zero.comp hv).const_mul_atTop hc)
  have hsmall := (hv.mono_right nhdsWithin_le_nhds).mul_const (2*ε)
  rw [zero_mul] at hsmall
  filter_upwards [hZ.eventually_ge_atTop X,hsmall.eventually_lt_const (sub_pos.mpr hcd)] with h hz hw
  obtain ⟨p,hp,hp'⟩ := step _ hz
  obtain ⟨q,hq,hq'⟩ := step _ (hz.trans hp.le)
  have hp0 : 0 < (p:ℝ) := Nat.cast_pos.mpr p.property.pos
  have hq0 : 0 < (q:ℝ) := Nat.cast_pos.mpr q.property.pos
  have hlo := Real.log_lt_log (Real.exp_pos _) hp
  rw [Real.log_exp] at hlo
  have hhi := Real.log_lt_log hp0 hp'
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp] at hhi
  have hsep := Real.log_lt_log hp0 hq
  have hgap := Real.log_lt_log hq0 hq'
  rw [Real.log_mul (Real.exp_pos _).ne' hp0.ne',Real.log_exp] at hgap
  have hh : 0 < h.val := h.property
  have hpL : c < h.val*Real.log (p:ℝ) := ((div_lt_iff₀ hh).mp hlo).trans_eq (mul_comm _ _)
  have hqL := hpL.trans (mul_lt_mul_of_pos_left hsep hh)
  have hU : Real.log (q:ℝ) < c/h.val+2*ε := by linarith only [hhi,hgap]
  have hscale : h.val*(c/h.val) = c := by field_simp [hh.ne']
  have hqU : h.val*Real.log (q:ℝ) ≤ d := by
    have H := mul_lt_mul_of_pos_left hU hh
    rw [mul_add,hscale] at H
    linarith only [H,hw]
  have hpU := (mul_le_mul_of_nonneg_left hsep.le hh.le).trans hqU
  refine ⟨⟨p,(mem_added c d h p).mpr ⟨hpL,hpU⟩⟩,⟨q,(mem_added c d h q).mpr ⟨hqL,hqU⟩⟩,
    sub_pos.mpr hsep,?_⟩
  change Real.log (q:ℝ)-Real.log (p:ℝ) < ε
  linarith only [hgap]

#print axioms eventually_close_modes

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells
