import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.FiniteCircuitWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.HalfOrder
import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw

/-! # A deterministic record length for the physical near-Hilbert floor -/
open Real Filter Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open SharpOccupation
noncomputable section

/-- The half-dimension replica moment dephases over this explicit duration. -/
def windowLength (k : ℕ) : ℝ := 4*√((2^(k+1):ℕ):ℝ)/effectiveGap k (2*2^(k+1))

/-- All origins, including the original robust crossing, obey the same
occupation estimate as soon as the record reaches the displayed length. -/
theorem gaussian_nearHilbert_window :
    ∃ b ∈ Ioo (0:ℝ) 1, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D : ℕ := 2^K
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∀ ε : ℝ, ε ≤ 39/80 → ∀ o : ℝ, ∀ T ≥ windowLength k, ∀ j ≤ nearHilbertContinuousCircuitBudget K,
        visitFraction H j ε o (o+T) < b^D := by
  let y := (7/10:ℝ)
  let L := log y+log 2/2
  have hy : 0 < y := by norm_num [y]
  have hsign := log_neg (by norm_num : (0:ℝ) < (7/10)^2*2) (by norm_num : (7/10:ℝ)^2*2 < 1)
  rw [log_mul (pow_ne_zero _ hy.ne') (by norm_num),log_pow] at hsign
  have hL : L < 0 := by dsimp only [L,y]; norm_num only [Nat.cast_ofNat] at hsign; linarith only [hsign]
  let b := exp (L/2)
  have hb : b ∈ Ioo (0:ℝ) 1 := ⟨exp_pos _,exp_lt_one_iff.mpr (half_neg hL)⟩
  have hlog : log y+32*log 2/(64:ℕ) < log b := by
    rw [show log b=L/2 from log_exp _]
    dsimp only [L] at hL ⊢
    norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  have hprice := positive_budget_exponent 64 (by decide) (1/80) y b (by norm_num) hy hb.1 hlog
  refine ⟨b,hb,?_⟩
  filter_upwards [gaussian_finite_gate_window] with ω hw
  filter_upwards [hw,(tendsto_add_atTop_nat 3).eventually hprice,eventually_ge_atTop 1] with k hk hnet hk₁
  intro K D u H ε hε o T hT j hj
  let s := nearHilbertContinuousCircuitBudget K
  let h : ℕ := 2^(k+1)
  let q := 2*h
  have hh : 4 ≤ h := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ k+1)
  have hpos : 0 < (h:ℝ) := by exact_mod_cast (by omega : 0 < h)
  have hd : D=4*h := by
    change 2^(k+1+2)=4*2^(k+1)
    rw [pow_add]; exact Nat.mul_comm _ _
  have ht : 0 < T := (div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hpos)) (effectiveGap_pos k q)).trans_le hT
  have hf := hk ε (1/80) (1/2) (by norm_num) (by linarith only [hε]) (by norm_num) (by norm_num)
    s q (by dsimp only [q]; omega) o T ht
  rw [show (1:ℝ)-(1/2)^2/2=7/8 by norm_num] at hf
  have hG := half_order_price h hh (effectiveGap_pos k q) hT
  rw [←hd] at hG
  have hp : momentPrice ((q.factorial:ℝ)/(D:ℝ)^q) (T*effectiveGap k q)/(7/8:ℝ)^(2*q) ≤
      zeroGateArcDensity D (7/10) := (div_le_div_of_nonneg_right (min_le_right _ _)
    (by positivity : 0 ≤ (7/8:ℝ)^(2*q))).trans hG
  apply (visitFraction_mono H hj ε o (o+T) (le_add_of_nonneg_right ht.le)).trans_lt
  exact (hf.trans (mul_le_mul_of_nonneg_left hp (by positivity))).trans_lt hnet

#print axioms gaussian_nearHilbert_window
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
