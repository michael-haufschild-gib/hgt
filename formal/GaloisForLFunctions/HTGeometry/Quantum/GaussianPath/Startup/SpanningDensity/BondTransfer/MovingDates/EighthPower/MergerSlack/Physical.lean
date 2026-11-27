import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.EighthPower.MergerSlack.Finite
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.Outliers.ThresholdMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Sampling.GuardScales
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Scales.CoordinateCap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.PhysicalBonds

/-! # Component mergers above a polynomial startup date -/
open Filter MeasureTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit FixedHorizon RepeatedGates RepeatedGates.Temporal RepeatedGates.Temporal.Feedback
noncomputable section

/-- For any deterministic c>0, up to a deterministic T>0 every fitting
circuit loses less than c(K−1)t⁸/2 component mergers, uniformly after
the polynomial onset. -/
theorem gaussian_eighth_merger_slack {c : ℝ} (hc : 0<c) :
    ∃ T>0, T≤1 ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let j := prefixIndex n
      let s := (1/(j:ℝ))^12
      0<s ∧ s≤1 ∧ 4*j^256≤n+1 ∧ n+2≤4*(2*j)^256 ∧
        ∀ t∈Icc s T, ∀ (C : TwoQubitCircuit (n+2)) (z : ℂ), ‖z‖=1 →
          ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤1/4 →
          ((n+1:ℕ):ℝ)+(redundant (circuitWord C):ℝ)+1<(C.gateCount:ℝ)+c/2*((n+1:ℕ):ℝ)*t^8 := by
  obtain ⟨_,_,C,hC,hweak⟩ := gaussian_weak_edge_counts
  obtain ⟨D,hD,hbad⟩ := gaussian_tenth_power_outliers
  let A := C*(4*2^256)
  obtain ⟨T,hT,hT₁,hprice⟩ := eventual_eighth_merger_slack (A:=A) hc hD.le
  refine ⟨T,hT,hT₁,?_⟩
  filter_upwards [hweak,hbad,gaussian_eighth_power_seams] with ω hw hx hseam
  filter_upwards [hw,hx,prefixIndex_tendsto.eventually hseam,prefixIndex_tendsto.eventually hprice,
    prefixIndex_tendsto.eventually_ge_atTop 2,eventually_ge_atTop (3:ℕ)] with n hw' hx' hs' hp hj₂ hn
  intro j s
  obtain ⟨hj,hl,hu⟩ := prefixIndex_bounds n hn
  have hJ : (0:ℝ)<j := Nat.cast_pos.mpr hj
  have hj₁ : 1≤(j:ℝ) := by exact_mod_cast hj
  let h := (1/(j:ℝ))^11
  have h₀ : 0<h := pow_pos (one_div_pos.mpr hJ) _
  have hi : 1/(j:ℝ)≤1 := (div_le_one hJ).mpr hj₁
  have h₁ : h≤1 := pow_le_one₀ (one_div_pos.mpr hJ).le hi
  have hs : 0<s := pow_pos (one_div_pos.mpr hJ) _
  refine ⟨hs,pow_le_one₀ (one_div_pos.mpr hJ).le hi,hl,hu,?_⟩
  intro t ht F z hz he
  let N : ℝ := (n+1:ℕ)
  let K : ℝ := (n+2:ℕ)
  have htp := hs.trans_le ht.1
  have hN := (Nat.cast_le (α:=ℝ)).mpr hl
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hN
  change 4*(j:ℝ)^256≤N at hN
  obtain ⟨hK,hK'⟩ := real_prefix_size n hn
  change 4*(j:ℝ)^256≤K at hK
  change K≤(4*2^256)*(j:ℝ)^256 at hK'
  have hgrid : 4*2^20≤K*h^20 := calc
    _ ≤ 4*(j:ℝ)^20 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le_two (by exact_mod_cast hj₂) 20) (by norm_num)
    _ ≤ 4*(j:ℝ)^36 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hj₁ (by decide : 20≤36)) (by norm_num)
    _ = (4*(j:ℝ)^256)*h^20 := by dsimp only [h]; field_simp [hJ.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right hK (pow_nonneg h₀.le _)
  have hweak' : ((weakEdges (pathPauliDisorderShell ω n) h).card:ℝ)≤A*(j:ℝ)^157 := calc
    _ ≤ C*K*h^9 := (hw' h h₀ h₁ hgrid).2
    _ ≤ C*((4*2^256)*(j:ℝ)^256)*h^9 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hK' hC.le) (pow_nonneg h₀.le _)
    _ = _ := by dsimp only [h,A]; field_simp [hJ.ne']
  exact hp n ω t hN ht.1 ht.2 hweak' (hx' t htp) (hs' n (by omega)) F z hz he

#print axioms gaussian_eighth_merger_slack
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
