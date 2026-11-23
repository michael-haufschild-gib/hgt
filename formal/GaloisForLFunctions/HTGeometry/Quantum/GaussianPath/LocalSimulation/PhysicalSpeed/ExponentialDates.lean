import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.PhysicalSpeed.EarlyTail
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncrementClocks.CertificateScale

/-! # Doubly exponential disorder suppression at single-exponential deadlines -/
open Filter MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.LocalPatches.PhysicalSpeed
open PrescribedTimes ShortWindows IncrementClocks
noncomputable section

private theorem width_le_travel_product {N : ℕ} (hs : 64 ≤ N.sqrt) :
    crossingWidth N ≤ travelProduct N := by
  let s := N.sqrt
  have hpoly := ReturnExcursions.dimension_dominates_speed hs
  have hN : N+1 ≤ (s+1)^2 := by rw [pow_two]; exact Nat.lt_succ_sqrt N
  have hscale : N+1 ≤ 2^s := hN.trans (le_trans (by omega) hpoly)
  have hsq : 26*s ≤ N := by
    have h := Nat.mul_le_mul_right s (show 26 ≤ s from by omega)
    exact h.trans (Nat.sqrt_le N)
  have he : (N-26*s)+(5*s+26)+2*s ≤ N := by omega
  have hbound : 2^(N-26*s)*(2^(5*s+26)*(N+1)^2) ≤ 2^N := calc
    _ ≤ 2^(N-26*s)*(2^(5*s+26)*(2^s)^2) := by gcongr
    _ = 2^((N-26*s)+(5*s+26)+2*s) := by
      rw [←pow_mul,←mul_assoc,←pow_add,←pow_add,Nat.mul_comm s 2]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he
  have hW : crossingWidth N ≤ localCrossingWidth N := by
    unfold localCrossingWidth
    apply (le_div_iff₀ (by positivity)).mpr
    exact_mod_cast hbound
  apply hW.trans
  exact le_mul_of_one_le_left (by dsimp [localCrossingWidth]; positivity)
    (by have hpos : 1 ≤ N := by omega
        have h' : (1:ℝ) ≤ N := by exact_mod_cast hpos
        linarith only [h'] : 1 ≤ 2*(N:ℝ))

/-- For every exponent below the Hilbert dimension exponent, the chance
that either physical first passage occurs before that exponential date is
doubly exponentially small in the qubit count. -/
theorem gaussian_early_exponential_onset_or_return {γ β : ℝ} (h : γ+β < 1) :
    ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let t := (2:ℝ)^(γ*(N:ℝ))
      let m := Fintype.card (ChainLabel N)
      pathPauliDisorderLaw.real {ω | crossingOrigin (k+1) P (9/80) (prefixPoint k ω) ≤ t ∨
        ∃ s ≤ P/2, crossingWait (k+1) P s (prefixPoint k ω) ≤ t} ≤
          2*(m:ℝ)*exp (-((2:ℝ)^(β*(N:ℝ)))^2/2) := by
  have hl := (tendsto_add_atTop_nat 3).eventually (crossingWidth_exponent_ratio.eventually_const_lt h)
  filter_upwards [gaussian_early_first_passage_tail,hl,eventually_ge_atTop (64*64)] with k hp hx hk
  intro N P t m
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  change γ+β < logb 2 (crossingWidth N)/(N:ℝ) at hx
  have hex := (lt_div_iff₀ hN).mp hx
  simp only [crossingWidth,logb_pow,logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] at hex
  have hpow := rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hex.le
  rw [rpow_natCast] at hpow
  have hw := hpow.trans (width_le_travel_product (N:=N) (Nat.le_sqrt.mpr (by dsimp [N]; omega)))
  have ht : 0 < t := rpow_pos_of_pos (by norm_num) _
  have hr : (2:ℝ)^(β*(N:ℝ)) ≤ travelProduct N/t := by
    apply (le_div_iff₀ ht).mpr
    change (2:ℝ)^_*(2:ℝ)^_ ≤ _
    rw [←rpow_add (by norm_num : (0:ℝ)<2),←add_mul,add_comm β γ]
    exact hw
  apply (hp t ht).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply exp_le_exp.mpr
  linarith only [pow_le_pow_left₀ (rpow_nonneg (by norm_num : (0:ℝ)≤2) _) hr 2]

#print axioms gaussian_early_exponential_onset_or_return
end
end GaloisForLFunctions.HTGeometry.LocalPatches.PhysicalSpeed
