import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Spacing.PhysicalRecords
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.HalfOrder
import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw

/-! # A deterministic record length for the physical near-Hilbert floor -/
open Real Filter Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open SharpOccupation
noncomputable section

/-- The half-dimension replica moment dephases over this explicit duration. -/
def windowLength (k : ℕ) : ℝ := (effectiveGap k (2*2^(k+1)))⁻¹

/-- The observed spacings can shorten the deterministic record length. -/
def sampleLength (k : ℕ) (E : Level k → ℝ) : ℝ := (recordGap k E (2*2^(k+1)))⁻¹

theorem sampleLength_le (k : ℕ) (E : Level k → ℝ) : sampleLength k E ≤ windowLength k :=
  inv_anti₀ (effectiveGap_pos k _) (le_max_left ..)

/-- All origins, including the original robust crossing, obey the same
occupation estimate as soon as the record reaches the displayed length. -/
theorem gaussian_nearHilbert_window :
    ∃ b ∈ Ioo (0:ℝ) 1, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D : ℕ := 2^K
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
      ∀ ε : ℝ, ε ≤ 39/80 → ∀ o : ℝ, ∀ T ≥ sampleLength k E, ∀ j ≤ nearHilbertContinuousCircuitBudget K,
        visitFraction H j ε o (o+T) < b^D := by
  let y := (7/10:ℝ)
  let L := log y+log 2/2
  have hy : 0 < y := by norm_num [y]
  have hsign := log_neg (by norm_num : (0:ℝ) < (7/10)^2*2) (by norm_num : (7/10:ℝ)^2*2 < 1)
  rw [log_mul (pow_ne_zero _ hy.ne') (by norm_num),log_pow] at hsign
  have hL : L < 0 := by dsimp only [L,y]; norm_num only [Nat.cast_ofNat] at hsign; linarith only [hsign]
  let b := exp (L/2)
  have hb : b ∈ Ioo (0:ℝ) 1 := ⟨exp_pos _,exp_lt_one_iff.mpr (show L/2 < 0 by linarith only [hL])⟩
  have hlog : log y+32*log 2/(64:ℕ) < log b := by
    rw [show log b=L/2 from log_exp _]
    dsimp only [L] at hL ⊢
    norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  have hprice := positive_budget_exponent 64 (by decide) (1/80) y b (by norm_num) hy hb.1 hlog
  refine ⟨b,hb,?_⟩
  filter_upwards [gaussian_spaced_gate_window] with ω hw
  filter_upwards [hw,(tendsto_add_atTop_nat 3).eventually hprice,eventually_ge_atTop 4] with k hk hnet hk₁
  intro K D u H E ε hε o T hT j hj
  let s := nearHilbertContinuousCircuitBudget K
  let h : ℕ := 2^(k+1)
  let q := 2*h
  have hh : 24 ≤ h := (by decide : 24 ≤ 2^5).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 5 ≤ k+1))
  have hd : D=4*h := by
    change 2^(k+1+2)=4*2^(k+1)
    rw [pow_add]; exact Nat.mul_comm _ _
  change (recordGap k E q)⁻¹ ≤ T at hT
  have ht : 0 < T := (inv_pos.mpr (recordGap_pos k E q)).trans_le hT
  have hdephase : 1 ≤ T*recordGap k E q := (div_le_iff₀ (recordGap_pos k E q)).mp
    (by simpa only [one_div] using hT : 1/recordGap k E q ≤ T)
  have hf := hk ε (1/80) (1/2) (by norm_num) (by linarith only [hε]) (by norm_num) (by norm_num)
    s q (by dsimp only [q]; omega) o T ht
  rw [show (1:ℝ)-(1/2)^2/2=7/8 by norm_num] at hf
  rw [max_eq_left (inv_le_one_of_one_le₀ hdephase),mul_one] at hf
  have hp := half_order_price h hh
  rw [←hd] at hp
  apply (visitFraction_mono H hj ε o (o+T) (le_add_of_nonneg_right ht.le)).trans_lt
  exact (hf.trans (mul_le_mul_of_nonneg_left hp (by positivity))).trans_lt hnet

/-- The same inverse-spacing bound controls affordable duration even
when the record stops before the half-dimension moment dephases. -/
theorem gaussian_nearHilbert_duration :
    ∃ b ∈ Ioo (0:ℝ) 1, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D : ℕ := 2^K
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
      ∀ ε : ℝ, ε ≤ 39/80 → ∀ o : ℝ, ∀ T ≥ (0:ℝ), ∀ j ≤ nearHilbertContinuousCircuitBudget K,
        volume.real (visitSet H j ε ∩ Icc o (o+T)) < b^D*max T (sampleLength k E) := by
  obtain ⟨b,hb,h⟩ := gaussian_nearHilbert_window
  refine ⟨b,hb,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with k hk
  intro K D u H E ε hε o T _ j hj
  let L := max T (sampleLength k E)
  have hL : 0 < L := (inv_pos.mpr (recordGap_pos k E _)).trans_le (le_max_right ..)
  have hh := hk ε hε o L (le_max_right ..) j hj
  rw [visitFraction,add_sub_cancel_left] at hh
  apply lt_of_le_of_lt _ ((div_lt_iff₀ hL).mp hh)
  have hend : o+T ≤ o+L := by linarith only [show T ≤ L from le_max_left ..]
  exact measureReal_mono (inter_subset_inter_right _ (Icc_subset_Icc le_rfl hend))
    (ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono inter_subset_right))

#print axioms gaussian_nearHilbert_duration
#print axioms gaussian_nearHilbert_window
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
