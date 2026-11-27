import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.GateBand
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Sampling.CalibrationGrid

import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstExcess

/-! # Uniform physical gate excess at moving times on the frozen chain -/
open Filter MeasureTheory Set Real
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
noncomputable section

/-- Almost surely on all large prefixes, every fitting circuit pays at
least a constant times K t⁵⁶ above the bond sweep, simultaneously from
the reciprocal date of order K⁻¹⁄²⁵⁶ through the logarithmic cutoff. -/
theorem gaussian_uniform_sweep_excess :
    ∃ a>0, ∃ B>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let s := 1/(prefixIndex n:ℝ)
      let T := 1/(3348*coordinateCap B n)
      0<s ∧ s≤T ∧ ∀ t∈Icc s T, ∀ k : ℕ, HasProjectiveCircuitApproximation (n+2) (1/4) k
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
        ((n+1:ℕ):ℝ)+a*K*t^56<(k:ℝ) := by
  obtain ⟨c,hc,hgrid⟩ := gaussian_calibration_grid
  obtain ⟨b,hb,B,hB,hfit⟩ := gaussian_moving_gate_price hc
  let M : ℝ := 4*2^256
  have hM : 0<M := by dsimp only [M]; positivity
  refine ⟨b/M,div_pos hb hM,B,hB,?_⟩
  filter_upwards [hgrid,hfit] with ω hbox hw
  filter_upwards [prefixIndex_tendsto.eventually hbox,hw,eventually_ge_atTop (3:ℕ)] with n hn hprice hsize
  intro K s T
  let j := prefixIndex n
  obtain ⟨hs,hT,hl,_,hcount⟩ := hprice
  have hcap : 1≤coordinateCap B n := by
    unfold coordinateCap
    linarith only [sqrt_nonneg (log (B*((n+2:ℕ):ℝ)))]
  have hden : 0<3348*coordinateCap B n := by linarith only [hcap]
  have h₁ : T≤1 := (div_le_one hden).mpr (by linarith only [hcap])
  refine ⟨hs,hT,?_⟩
  intro t ht k hk
  have hj : (0:ℝ)<j := Nat.cast_pos.mpr (prefixIndex_bounds n hsize).1
  obtain ⟨δ,hδ,hδt,hboxes⟩ := hn ((n+1)/4) (by omega) t ⟨ht.1,ht.2.trans h₁⟩
  have hweight : (j:ℝ)^208≤(j:ℝ)^256*t^48 := calc
    _ = (j:ℝ)^256*(1/(j:ℝ))^48 := by field_simp [show (j:ℝ)≠0 from hj.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le ht.1 48) (pow_nonneg hj.le 256)
  have he := hcount t ht δ _ hδ hδt hweight hboxes k hk
  have hK : K≤M*(j:ℝ)^256 := (real_prefix_size n hsize).2
  have hscale : b/M*K≤b*(j:ℝ)^256 := calc
    _ ≤ b/M*(M*(j:ℝ)^256) := mul_le_mul_of_nonneg_left hK (div_nonneg hb.le hM.le)
    _ = _ := by rw [←mul_assoc,div_mul_cancel₀ _ hM.ne']
  exact (add_le_add (le_refl ((n+1:ℕ):ℝ)) ((mul_le_mul_of_nonneg_right hscale (pow_nonneg (hs.le.trans ht.1) 56)).trans_eq
    (show b*(j:ℝ)^256*t^56=b*((j:ℝ)^256*t^48)*t^8 by ring))).trans_lt he

open RepeatedGates.PhysicalBlocks
open scoped Matrix.Norms.L2Operator
private abbrev chain (ω : PathPauliDisorder) (n : ℕ) : selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) :=
  ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩

/-- On both sides of the original first low return, the gate budget in
excess of one sweep has a growing lower bound at physical error 3/20.
The budget of the circuit at the low return enters as an additive loss. -/
theorem gaussian_first_dip_excess_band :
    ∃ a>0, ∃ B>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let s := 1/(prefixIndex n:ℝ)
      let T := 1/(3348*coordinateCap B n)
      0<s ∧ s≤T ∧ ∀ r : ℕ,
        let v := firstLowAfterCrossing ω n r
        ∀ h : ℝ, |h|∈Icc s T → ∀ k : ℕ,
          HasProjectiveCircuitApproximation (n+2) (3/20) k (unitaryEvolution (chain ω n).val (v+h)) →
          ((n+1:ℕ):ℝ)+a*K* |h|^56<((r+k:ℕ):ℝ) := by
  obtain ⟨a,ha,B,hB,hband⟩ := gaussian_uniform_sweep_excess
  refine ⟨a,ha,B,hB,?_⟩
  filter_upwards [hband] with ω hω
  filter_upwards [hω] with n hn
  intro K s T
  obtain ⟨hs,hT,hfit⟩ := hn
  refine ⟨hs,hT,?_⟩
  intro r v h hh k hk
  let H := chain ω n
  have hv : HasProjectiveCircuitApproximation (n+2) (1/10) r (unitaryEvolution H.val v) :=
    (PrecisionReturns.firstVisit_isLeast H _ r (by norm_num : (0:ℝ)<1/10)).1.2
  have he := affordable_add_time H (x := -v) (y := v+h) (hv.neg_time H) hk
  rw [neg_add_cancel_left,show (1/10:ℝ)+3/20=1/4 by norm_num] at he
  apply hfit |h| hh (r+k)
  rcases le_total 0 h with hpos|hneg
  · rwa [abs_of_nonneg hpos]
  · rw [abs_of_nonpos hneg]
    exact he.neg_time H

/-- A date within the band is a deadline for every first crossing with
2r+q ≤ a K t⁵⁶, starting from any physical tenth-error r-gate visit. -/
theorem gaussian_excess_crossing_deadlines :
    ∃ a>0, ∃ B>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let s := 1/(prefixIndex n:ℝ)
      let T := 1/(3348*coordinateCap B n)
      0<s ∧ s≤T ∧ ∀ t∈Icc s T, ∀ (r q : ℕ) (v : ℝ),
        ((2*r+q:ℕ):ℝ)≤a*K*t^56 →
        HasProjectiveCircuitApproximation (n+2) (1/10) r (unitaryEvolution (chain ω n).val v) →
        ∀ ρ∈Icc (9/80:ℝ) (1/8),
          let τ := firstExcessAfter ω n (r+q) v ρ
          let f (x : ℝ) := orbitCircuitDistance (chain ω n) (n+1+(r+q)) (v+x)
          0≤τ ∧ τ≤t ∧ f τ=ρ ∧ ∀ x∈Ico 0 τ, f x<ρ := by
  obtain ⟨a,ha,B,hB,hband⟩ := gaussian_uniform_sweep_excess
  refine ⟨a,ha,B,hB,?_⟩
  filter_upwards [hband] with ω hω
  filter_upwards [hω] with n hn
  intro K s T
  obtain ⟨hs,hT,hfit⟩ := hn
  refine ⟨hs,hT,?_⟩
  intro t ht r q v hbudget hv ρ hρ
  apply firstExcessAfter_le_of_increment ω n r q (hs.le.trans ht.1)
    (show 1/10<ρ by linarith only [hρ.1]) hv
  rintro ⟨z,hz,C,hC,he⟩
  have hh := hfit t ht (r+(n+1+(r+q))) ⟨z,hz,C,hC,he.trans (by linarith only [hρ.2])⟩
  change ((n+1:ℕ):ℝ)+a*K*t^56<((r+(n+1+(r+q)):ℕ):ℝ) at hh
  push_cast at hh hbudget
  linarith only [hh,hbudget]

#print axioms gaussian_excess_crossing_deadlines
#print axioms gaussian_first_dip_excess_band
#print axioms gaussian_uniform_sweep_excess
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
