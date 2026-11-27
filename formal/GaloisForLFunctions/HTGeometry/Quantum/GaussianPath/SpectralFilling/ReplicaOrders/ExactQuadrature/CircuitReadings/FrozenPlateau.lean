import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.CircuitReadings.GateOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.NearHilbertWindow

/-! # Hard circuit readings on an explicit clock of the frozen chain -/
open Real Filter MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
open SharpOccupation ReplicaOrders
noncomputable section

/-- From any origin, fewer than b^D of the half-period choices yield
a near-Hilbert gate fit on a typical sufficiently long frozen prefix.
The dates themselves are sums of measured half-periods. -/
theorem gaussian_hard_clock_readings :
    ∃ b∈Ioo (0:ℝ) 1, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D : ℕ := 2^K
      let H : selfAdjoint (Register K) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
      let q := 2*2^(k+1)
      let P := nearHilbertContinuousCircuitBudget K
      ∀ a ε : ℝ, ε≤39/80 → ∀ s≤P,
        reading (frequencies E q).toList (gateIndicator H s ε) a<b^D := by
  let y := (7/10:ℝ)
  let L := log y+log 2/2
  have hy : 0<y := by norm_num [y]
  have hsign := log_neg (by norm_num : (0:ℝ)<(7/10)^2*2) (by norm_num : (7/10:ℝ)^2*2<1)
  rw [log_mul (pow_ne_zero _ hy.ne') (by norm_num),log_pow] at hsign
  have hL : L<0 := by dsimp only [L,y]; norm_num only [Nat.cast_ofNat] at hsign; linarith only [hsign]
  let b := exp (L/2)
  have hb : b∈Ioo (0:ℝ) 1 := ⟨exp_pos _,exp_lt_one_iff.mpr (show L/2<0 by linarith only [hL])⟩
  have hlog : log y+32*log 2/(64:ℕ)<log b := by
    rw [show log b=L/2 from log_exp _]
    dsimp only [L] at hL ⊢
    norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  have hprice := positive_budget_exponent 64 (by decide) (1/80) y b (by norm_num) hy hb.1 hlog
  refine ⟨b,hb,?_⟩
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hw
  filter_upwards [(tendsto_add_atTop_nat 3).eventually hprice,eventually_ge_atTop 4] with k hnet hk
  intro K D H E q P a ε he s hs
  let h : ℕ := 2^(k+1)
  have hh : 24≤h := (by decide : 24≤2^5).trans
    (Nat.pow_le_pow_right (by decide : 0<2) (by omega : 5≤k+1))
  have hd : D=4*h := by change 2^(k+1+2)=4*2^(k+1); rw [pow_add]; exact Nat.mul_comm _ _
  let M := (q.factorial:ℝ)/(D:ℝ)^q
  have hM : 0≤M := div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hp := half_order_price h hh
  rw [←hd] at hp
  have hsmall : M/(7/8:ℝ)^(2*q)≤zeroGateArcDensity D (7/10) :=
    (div_le_div_of_nonneg_right (le_mul_of_one_le_left hM (by norm_num : (1:ℝ)≤96))
      (pow_nonneg (by norm_num) _)).trans hp
  have h := sampled_gate_occupation H (hw k) P q a ε (1/80) (1/2) (by norm_num)
    (by linarith only [he]) (by norm_num) (by norm_num)
  rw [show (1:ℝ)-(1/2)^2/2=7/8 by norm_num] at h
  have hmono (t : ℝ) : gateIndicator H s ε t≤gateIndicator H P ε t := by
    classical
    unfold gateIndicator
    split_ifs with hx hy' hy' <;> try norm_num
    obtain ⟨z,hz,C,hC,he⟩ := hx
    exact (hy' ⟨z,hz,C,hC.trans hs,he⟩).elim
  exact ((reading_mono _ hmono a).trans (h.trans
    (mul_le_mul_of_nonneg_left hsmall (by positivity)))).trans_lt hnet

#print axioms gaussian_hard_clock_readings
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
