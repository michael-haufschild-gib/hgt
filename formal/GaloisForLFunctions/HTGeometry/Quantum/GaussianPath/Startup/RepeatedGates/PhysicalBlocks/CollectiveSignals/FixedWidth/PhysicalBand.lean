import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.Sampling.PhysicalDensity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.PhysicalGateCharge

/-! # An eighth-power physical gate excess on every compact startup band -/
open Filter MeasureTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal Feedback
noncomputable section

/-- A single constant works on every fixed compact subinterval of
(0,1], even as the left endpoint is taken arbitrarily close to zero.
Every quarter-error circuit pays the eighth-power excess. -/
theorem gaussian_fixed_band_eighth_power :
    ∃ b>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a : ℝ, 0<a → ∀ᶠ n : ℕ in atTop,
      ∀ t∈Icc a 1, ∀ k : ℕ, HasProjectiveCircuitApproximation (n+2) (1/4) k
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
        (1+b*t^8)*((n+1:ℕ):ℝ)<(k:ℝ) := by
  obtain ⟨c,hc,hcharge⟩ := gaussian_eighth_power_repeats
  let u (j : ℕ) := 1/((j:ℝ)+1)
  have hu (j : ℕ) : 0<u j := by dsimp only [u]; positivity
  let η j := c/4*(u j)^8
  have hη (j : ℕ) : 0<η j := mul_pos (by positivity) (pow_pos (hu j) _)
  have hs (j : ℕ) := gaussian_uniform_repeat_floor (T:=1) (hu j) (hη j)
    (by norm_num : (0:ℝ)≤1/4) (by have h := one_le_sqrt.mpr (by norm_num : (1:ℝ)≤2); linarith only [h])
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [hcharge,ae_all_iff.mpr hs] with ω hrep hfloor
  intro a ha
  obtain ⟨j,hj⟩ := exists_nat_ge (1/a)
  have hja : u j≤a := by
    apply (div_le_iff₀ (show 0<(j:ℝ)+1 by positivity)).mpr
    have h := (div_le_iff₀ ha).mp hj
    linarith only [h,ha]
  obtain ⟨N,hN⟩ := exists_nat_ge (1/η j)
  filter_upwards [hrep,hfloor j,eventually_ge_atTop N] with n hn hf hlarge
  intro t ht k hk
  obtain ⟨z,hz,C,hC,he⟩ := hk
  let K : ℝ := (n+1:ℕ)
  have hK : 0≤K := Nat.cast_nonneg _
  have hN' : 1/η j≤K := hN.trans (Nat.cast_le.mpr (hlarge.trans (Nat.le_succ _)))
  have h₁ : 1≤η j*K := by
    have h := (div_le_iff₀ (hη j)).mp hN'
    rwa [mul_comm] at h
  have hc₁ := hn t ⟨ha.trans_le ht.1,ht.2⟩ C z hz he
  have hc₂ := hf t ⟨hja.trans ht.1,ht.2⟩ C z hz he
  have hcost : (C.gateCount:ℝ)≤k := Nat.cast_le.mpr hC
  have hηt := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (hu j).le (hja.trans ht.1) 8) (show 0≤c/4 by positivity)) hK
  change c*K*t^8≤_ at hc₁
  change (1-η j)*K+_<_ at hc₂
  change (1+c/2*t^8)*K<(k:ℝ)
  dsimp only [η] at h₁ hc₂
  linarith only [h₁,hc₁,hc₂,hcost,hηt]

#print axioms gaussian_fixed_band_eighth_power
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
