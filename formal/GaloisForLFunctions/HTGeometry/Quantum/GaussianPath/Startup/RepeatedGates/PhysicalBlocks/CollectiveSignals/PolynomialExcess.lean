import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.BoxCount
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.PhysicalGateCharge
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.Calibration.SmallAngles

/-! # A polynomial short-time excess over one physical bond sweep -/
open Filter MeasureTheory Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal Feedback
noncomputable section

/-- Every date from a prescribed positive onset to one time unit has
excess gate density at least a fixed power of that onset. -/
theorem gaussian_polynomial_gate_band :
    ∃ c>0, ∀ t∈Ioc (0:ℝ) 1, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ v∈Icc t 1, ∀ s : ℕ,
      HasProjectiveCircuitApproximation (n+2) (1/4) s
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) v) →
      (1+c*t^56)*(n+1:ℕ)<(s:ℝ) := by
  obtain ⟨c,hc,hprice⟩ := calibrated_small_time_mass
  let c₀ := c/(2^8*21840)
  have hc₀ : 0<c₀ := by dsimp only [c₀]; positivity
  refine ⟨c₀,hc₀,?_⟩
  intro t ht
  let δ := t/10000
  let gain := c₀*t^56
  have hgain : 0<gain := mul_pos hc₀ (pow_pos ht.1 _)
  have herr : (1/4:ℝ)<sqrt 2 := (by norm_num : (1/4:ℝ)<1).trans_le (one_le_sqrt.mpr (by norm_num))
  filter_upwards [(good_boxes_half_mass (1/sqrt 2) (div_pos ht.1 (by norm_num : (0:ℝ)<10000))).2,
    gaussian_uniform_repeat_floor (T:=1) ht.1 hgain (by norm_num : (0:ℝ)≤1/4) herr] with ω hfreq hfloor
  obtain ⟨K,hK⟩ := eventually_atTop.mp hfreq
  obtain ⟨J,hJ⟩ := exists_nat_gt (1/gain)
  filter_upwards [hfloor,eventually_ge_atTop (4*K+20),eventually_ge_atTop J] with n hf hn hn'
  intro v hv s hsfit
  have hv₀ := ht.1.trans_le hv.1
  have hsin := short_sine (show v∈Ioc (0:ℝ) 1 from ⟨hv₀,hv.2⟩)
  have hsin' : t/2 ≤ sin v := (div_le_div_of_nonneg_right hv.1 two_pos.le).trans hsin
  have ht₂ := sq_le_sq' (by linarith only [hsin,hv₀] : -(sin v)≤v/2) hsin
  have hs : 0 < (sin v)^2 := sq_pos_of_pos ((half_pos hv₀).trans_le hsin)
  have hroom : 252* |v| * δ≤(sin v)^2/4 := by
    rw [abs_of_pos hv₀]
    dsimp only [δ]
    linarith only [ht₂,mul_le_mul_of_nonneg_left hv.1 hv₀.le,sq_nonneg v]
  have hprice' : 21840*gain≤boxProbability (1/sqrt 2) δ*(sin v)^8 := by
    have hpow := pow_le_pow_left₀ (half_pos ht.1).le hsin' 8
    exact (show 21840*gain=c*t^48*(t/2)^8 by dsimp only [gain,c₀]; ring).trans_le
      (mul_le_mul (hprice t ht) hpow (pow_nonneg (half_pos ht.1).le _)
        ((mul_nonneg hc.le (pow_nonneg ht.1.le _)).trans (hprice t ht)))
  obtain ⟨z,hz,C,hC,he⟩ := hsfit
  let m := (n+1)/4
  have hmass := hK m (by dsimp only [m]; omega)
  have hN : ((n+1:ℕ):ℝ)≤5*(m:ℝ) := by exact_mod_cast (show n+1≤5*m by dsimp only [m]; omega)
  have hB := boxes_force_repeated_calls ω C (show 0≤δ from div_nonneg ht.1.le (by norm_num))
    hs hroom z hz he
  have hcost := hf v hv C z hz he
  let N : ℝ := n+1
  have hn₀ : 0≤N := by dsimp only [N]; positivity
  have hunit : 1≤gain*N := by
    have hh : 1/gain≤N := hJ.le.trans (by dsimp only [N]; exact_mod_cast (show J≤n+1 by omega))
    linarith only [(div_le_iff₀ hgain).mp hh]
  let p := boxProbability (1/sqrt 2) δ
  have hp : 0≤p := (mul_nonneg hc.le (pow_nonneg ht.1.le _)).trans (hprice t ht)
  have hpre : p*N≤10*((goodBoxes (1/sqrt 2) δ ω m).card:ℝ) := by
    change p/2*(m:ℝ)≤_ at hmass
    push_cast at hN
    linarith only [mul_le_mul_of_nonneg_left hN hp,hmass]
  have hrep : 4*gain*N≤(redundant (circuitWord C):ℝ)+1 := by
    linarith only [mul_le_mul_of_nonneg_right hprice' hn₀,
      mul_le_mul_of_nonneg_right hpre (pow_nonneg ((half_pos hv₀).le.trans hsin) 8),hB]
  have hcirc : (C.gateCount:ℝ) ≤ s := Nat.cast_le.mpr hC
  push_cast at hcost ⊢
  change (1+gain)*N<(s:ℝ)
  change (1-gain)*N+_ < _ at hcost
  linarith only [hcost,hrep,hunit,hcirc]

/-- At the prescribed date itself the excess is at least c times its
fifty-sixth power, with c independent of the choice of date. -/
theorem gaussian_polynomial_gate_excess :
    ∃ c>0, ∀ t∈Ioc (0:ℝ) 1, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ s : ℕ,
      HasProjectiveCircuitApproximation (n+2) (1/4) s
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
      (1+c*t^56)*(n+1:ℕ)<(s:ℝ) := by
  obtain ⟨c,hc,hh⟩ := gaussian_polynomial_gate_band
  exact ⟨c,hc,fun t ht => (hh t ht).mono fun _ hw => hw.mono fun _ hn => hn t ⟨le_rfl,ht.2⟩⟩

#print axioms gaussian_polynomial_gate_band
#print axioms gaussian_polynomial_gate_excess
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
