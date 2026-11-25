import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns.PhysicalWaits
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Failure probabilities before exponential-in-dimension winding -/

open Set Filter MeasureTheory Real Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns
open AntipodalHorizons
noncomputable section

/-- The sum of the block dimensions at a middle cut is negligible
compared to the full Hilbert dimension. -/
private theorem block_ratio :
    Tendsto (fun k : ℕ => (blockDimension (k+1):ℝ)/(2:ℝ)^(k+3)) atTop (𝓝 0) := by
  let h (k : ℕ) := (k+3)/2
  have hh : Tendsto h atTop atTop := tendsto_atTop.mpr fun a =>
    (eventually_ge_atTop (2*a)).mono fun k hk => by dsimp only [h]; omega
  have hlim := ((tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)).comp hh).const_mul 2
  simp only [Function.comp_apply,pow_zero,mul_zero,mul_one_div] at hlim
  apply squeeze_zero (fun _ => by positivity) _ hlim
  intro k
  let N := k+3
  have hl : h k≤N-h k := by dsimp only [h,N]; omega
  have hsum : (N-h k)+h k=N := Nat.sub_add_cancel (hl.trans (Nat.sub_le _ _))
  have hp := Nat.pow_le_pow_right (Nat.zero_lt_two) hl
  have hd : blockDimension (k+1) ≤ 2*2^(N-h k) := by
    change 2^(h k)+2^(N-h k)≤_
    omega
  change (blockDimension (k+1):ℝ)/(2:ℝ)^N≤2/(2:ℝ)^(h k)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ ≤ (2*(2:ℝ)^(N-h k))*(2:ℝ)^(h k) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (by positivity)
    _ = _ := by rw [mul_assoc,←pow_add,hsum]

private theorem constant_ratio (c : ℝ) :
    Tendsto (fun k : ℕ => c/(2:ℝ)^(k+3)) atTop (𝓝 0) := by
  have h := ((tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)).comp
    (tendsto_add_atTop_nat 3)).const_mul c
  simpa only [Function.comp_apply,pow_zero,mul_one_div,mul_zero] using h

/-- For every prescribed winding with log(m+1)=o(D), a first scalar
return within b⁻ᴰ has probability larger than ρᴰ, for every fixed
0<b,ρ<1. Both the origin and the elapsed time belong to the uncut,
frozen path. -/
theorem gaussian_early_antipode_failures {ε b ρ : ℝ} (hε : 0<ε)
    (hb : b∈Ioo (0:ℝ) 1) (hρ : ρ∈Ioo (0:ℝ) 1) (m : ℕ→ℕ)
    (hm : Tendsto (fun k => log ((m k:ℝ)+1)/(2:ℝ)^(k+3)) atTop (𝓝 0)) :
    ∀ᶠ k : ℕ in atTop, let D : ℕ := 2^(k+3)
      ρ^D < pathPauliDisorderLaw.real {ω | elapsed k (m k) ε ω ≤ (1/b)^D} := by
  obtain ⟨B,hB,c,hc,h⟩ := gaussian_two_prescribed_wait_floors hε
  have hM := block_ratio.mul_const (log B)
  have hdate := ((constant_ratio (log π)).add hm).add hM
  have hmass := ((hm.const_mul 9).add (hM.const_mul 10)).sub (constant_ratio (log c))
  simp only [mul_zero,zero_mul,add_zero,sub_zero] at hdate hmass
  have hlog := log_pos ((one_lt_div hb.1).mpr hb.2)
  have hneg := neg_pos.mpr (log_neg hρ.1 hρ.2)
  filter_upwards [hdate.eventually_lt_const hlog,hmass.eventually_lt_const hneg] with k ht hp
  intro D
  let M := B^(blockDimension (k+1))
  have hMpos : 0<(M:ℝ) := Nat.cast_pos.mpr (pow_pos (Nat.zero_lt_one.trans_le hB) _)
  have hD : 0<(D:ℝ) := Nat.cast_pos.mpr (Nat.two_pow_pos _)
  have hmpos : 0<(m k:ℝ)+1 := by positivity
  have hlogM : log (M:ℝ)=(blockDimension (k+1):ℝ)*log B := by
    dsimp only [M]
    rw [Nat.cast_pow,log_pow]
  have hd : (D:ℝ)=(2:ℝ)^(k+3) := by simp only [D,Nat.cast_pow,Nat.cast_ofNat]
  obtain ⟨w,hw,hh⟩ := h k (m k)
  let E := {ω | ∀ j : ℕ, j<w → elapsed k j ε ω≤π*((w:ℝ)-((j:ℝ)+1/2))}
  let p := pathPauliDisorderLaw.real E
  change c≤((m k:ℝ)+1)^9*(M:ℝ)^10*p at hh
  have hp₀ : 0<p := pos_of_mul_pos_right (hc.trans_le hh) (by positivity)
  have hplog := log_le_log hc hh
  rw [log_mul (by positivity) hp₀.ne',log_mul (by positivity) (by positivity),
    log_pow,log_pow,hlogM] at hplog
  have hdate' : log π+log ((m k:ℝ)+1)+(blockDimension (k+1):ℝ)*log B < log (1/b)*(D:ℝ) := by
    apply (div_lt_iff₀ hD).mp
    calc
      _ = log π/(2:ℝ)^(k+3)+log ((m k:ℝ)+1)/(2:ℝ)^(k+3)+
          ((blockDimension (k+1):ℝ)/(2:ℝ)^(k+3))*log B := by rw [hd]; ring
      _ < _ := ht
  have hmass' : 9*log ((m k:ℝ)+1)+10*((blockDimension (k+1):ℝ)*log B)-log c < -log ρ*(D:ℝ) := by
    apply (div_lt_iff₀ hD).mp
    calc
      _ = 9*(log ((m k:ℝ)+1)/(2:ℝ)^(k+3))+
          10*(((blockDimension (k+1):ℝ)/(2:ℝ)^(k+3))*log B)-log c/(2:ℝ)^(k+3) := by rw [hd]; ring
      _ < _ := hp
  have htime : π*((m k:ℝ)+1)*(M:ℝ) < (1/b)^D := by
    apply (log_lt_log_iff (by positivity) (pow_pos (one_div_pos.mpr hb.1) _)).mp
    rw [log_mul (by positivity) hMpos.ne',log_mul pi_ne_zero hmpos.ne',hlogM,log_pow]
    linarith only [hdate']
  have hresult : ρ^D<p := by
    apply (log_lt_log_iff (pow_pos hρ.1 _) hp₀).mp
    rw [log_pow]
    push_cast at hplog
    linarith only [hmass',hplog]
  apply hresult.trans_le
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  have hs := hω (m k) hw.1
  have hw' : (w:ℝ)≤((m k:ℝ)+1)*(M:ℝ) := by exact_mod_cast hw.2
  have hnon : 0≤(m k:ℝ)+1/2 := by positivity
  exact hs.trans ((mul_le_mul_of_nonneg_left ((sub_le_self _ hnon).trans hw') pi_pos.le).trans
    (by simpa only [mul_assoc] using htime.le))

#print axioms gaussian_early_antipode_failures
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns
