import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Scales.GatePrice
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Scales.CoordinateCap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Sampling.MarkedPrefixes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Sampling.WeakStrips
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.PhysicalBonds

/-! # A polynomial date for excess gates on the frozen Gaussian chain -/

open MeasureTheory Filter Real Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit RepeatedGates.PhysicalBlocks
noncomputable section

/-- All boundary and spanning losses are paid uniformly on one Gaussian
draw. Any calibration count above the minimum size yields its own
eighth-power gate charge. -/
theorem gaussian_moving_gate_price {c : ℝ} (hc : 0<c) :
    ∃ b>0, ∃ B>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let j := prefixIndex n
      let s := 1/(j:ℝ)
      let T := 1/(3348*coordinateCap B n)
      0<s ∧ s≤T ∧ 4*j^256≤n+1 ∧ n+2≤4*(2*j)^256 ∧
      ∀ t∈Icc s T, ∀ δ w : ℝ, 0≤δ → δ≤t/10000 → (j:ℝ)^208≤w →
        c*w≤((goodBoxes (1/sqrt 2) δ ω ((n+1)/4)).card:ℝ) →
        ∀ k : ℕ, HasProjectiveCircuitApproximation (n+2) (1/4) k
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
          ((n+1:ℕ):ℝ)+b*w*t^8<(k:ℝ) := by
  obtain ⟨_,_,C,hC,hw⟩ := gaussian_weak_edge_counts
  obtain ⟨B,hB,hcap⟩ := gaussian_coordinate_window
  let A := C*(4*2^256)
  have hA : 0≤A := by dsimp only [A]; positivity
  obtain ⟨b,hb,hprice⟩ := moving_gate_price hc hA
  refine ⟨b,hb,B,hB,?_⟩
  filter_upwards [hw,gaussian_moving_seams,hcap] with ω hweak hseam hsup
  filter_upwards [hweak,prefixIndex_tendsto.eventually hseam,hsup,
    prefixIndex_tendsto.eventually hprice,prefixIndex_tendsto.eventually_ge_atTop 2,eventually_ge_atTop 3]
    with n hw' hs' hcap' hp hj₂ hn
  intro j s T
  obtain ⟨hj,hl,hu⟩ := prefixIndex_bounds n hn
  have hjp : 0<(j:ℝ) := by exact_mod_cast hj
  have hj1 : 1≤(j:ℝ) := by exact_mod_cast hj
  have hs : 0<s := one_div_pos.mpr hjp
  have hs1 : s≤1 := (div_le_one hjp).mpr hj1
  have hB' : 1≤coordinateCap B n := by unfold coordinateCap; linarith only [sqrt_nonneg (log (B*((n+2:ℕ):ℝ)))]
  have hcap₀ : 0<3348*coordinateCap B n := by linarith only [hB']
  have hT : s≤T := one_div_le_one_div_of_le hcap₀ hcap'.2
  refine ⟨hs,hT,hl,hu,?_⟩
  intro t ht δ w hδ hδt hwbox hmark k hk
  obtain ⟨hK,hK'⟩ := real_prefix_size n hn
  change 4*(j:ℝ)^256≤((n+2:ℕ):ℝ) at hK
  change ((n+2:ℕ):ℝ)≤(4*2^256)*(j:ℝ)^256 at hK'
  have hgrid : 4*2^20≤((n+2:ℕ):ℝ)*(s^7)^20 := calc
    _ ≤ 4*(j:ℝ)^20 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le_two (by exact_mod_cast hj₂) 20) (by norm_num)
    _ ≤ 4*(j:ℝ)^116 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hj1 (by decide : 20≤116)) (by norm_num)
    _ = (4*(j:ℝ)^256)*(s^7)^20 := by dsimp only [s]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hK (pow_nonneg (pow_nonneg hs.le 7) _)
  have hw₀ := (hw' (s^7) (pow_pos hs _) (pow_le_one₀ hs.le hs1) hgrid).2
  have hw₁ : ((weakEdges (pathPauliDisorderShell ω n) (s^7)).card:ℝ)≤A*(j:ℝ)^193 := calc
    _ ≤ _ := hw₀
    _ ≤ C*((4*2^256)*(j:ℝ)^256)*(s^7)^9 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK' hC.le) (pow_nonneg (pow_nonneg hs.le _) _)
    _ = _ := by dsimp only [s,A]; field_simp
  have hsmall := (le_div_iff₀ hcap₀).mp ht.2
  have hT1 : T≤1 := (div_le_one hcap₀).mpr (by linarith only [hB'])
  exact hp n ω (coordinateCap B n) t δ w (zero_le_one.trans hB') hcap'.1
    (by linarith only [hsmall]) ht.1 (ht.2.trans hT1) hw₁
    (hs' n (by omega)) hδ hδt hwbox hmark k hk

/-- At the reciprocal date the excess reaches order K²⁵⁄³². The
same marked triples give an eighth-power lower bound on the rest
of the window. -/
theorem gaussian_moving_gate_band :
    ∃ b>0, ∃ B>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let j := prefixIndex n
      let s := 1/(j:ℝ)
      let T := 1/(3348*coordinateCap B n)
      0<s ∧ s≤T ∧ 4*j^256≤n+1 ∧ n+2≤4*(2*j)^256 ∧
      ∀ t∈Icc s T, ∀ k : ℕ, HasProjectiveCircuitApproximation (n+2) (1/4) k
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
        ((n+1:ℕ):ℝ)+b*(j:ℝ)^208*t^8<(k:ℝ) := by
  obtain ⟨c,hc,hmark⟩ := gaussian_moving_triples
  obtain ⟨b,hb,B,hB,hfit⟩ := gaussian_moving_gate_price hc
  refine ⟨b,hb,B,hB,?_⟩
  filter_upwards [hmark,hfit] with ω hm hw
  filter_upwards [prefixIndex_tendsto.eventually hm,hw] with n hn hprice
  intro j s T
  obtain ⟨hs,hT,hl,hu,hp⟩ := hprice
  refine ⟨hs,hT,hl,hu,?_⟩
  intro t ht
  exact hp t ht (s/10000) ((j:ℝ)^208) (div_nonneg hs.le (by norm_num))
    (div_le_div_of_nonneg_right ht.1 (by norm_num)) le_rfl (hn _ (by omega))

#print axioms gaussian_moving_gate_price
#print axioms gaussian_moving_gate_band
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
