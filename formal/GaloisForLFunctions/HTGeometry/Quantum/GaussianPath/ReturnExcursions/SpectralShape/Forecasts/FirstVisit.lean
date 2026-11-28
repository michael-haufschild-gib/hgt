import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Forecasts.ExponentialScale
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Forecasts.PhysicalWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.Reflection

/-! # The integer spectral shape at the original first return escapes exterior forecasts -/

open Filter MeasureTheory Set Real
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open PrescribedTimes ShortWindows SharpOccupation AngularWindings.PhysicalTubes
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- Even an exponential number of measurable shape forecasts from all the other
couplings eventually miss every winding after the original plateau crossing. -/
theorem post_crossing_forecasts {a : ℝ} (ha : 1<a) (h₆ : a^6<2)
    (e : (k : ℕ) → Fin (k+2))
    (f : (k : ℕ) → Fin ⌊a^(k+3)⌋₊ → (Exterior (n:=k+1) (e k)→ℝ) → ℝ)
    (hf : ∀ k j, Measurable (f k j)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let σ := crossingOrigin (k+1) (nearHilbertContinuousCircuitBudget (k+3)) (9/80) (prefixPoint k ω)
      ¬forecastHit (e k) (f k) σ (1/10) (pathPauliDisorderShell ω (k+1)) := by
  obtain ⟨b,τ,hab,hτ,hτ'⟩ := forecast_bases h₆
  let K (k : ℕ) := k+3
  let x := π*(1+physicalArc (1/10))
  let μ := pathPauliDisorderLaw
  let S (k : ℕ) := {ω : PathPauliDisorder | let h := pathPauliDisorderShell ω (k+1)
    ‖h‖^2∈Icc (K k:ℝ) (13*(K k:ℝ)) ∧ forecastHit (e k) (f k) (τ^(K k)) (1/10) h}
  have hb := ha.trans hab
  have hb₀ := zero_lt_one.trans hb
  have hτ₀ := (pow_pos hb₀ 6).trans hτ
  have he : (1/10:ℝ)∈Ioo 0 (sqrt 2) := ⟨by norm_num,(by norm_num : (1/10:ℝ)<1).trans_le
    (one_le_sqrt.mpr (by norm_num))⟩
  have hx : 0≤x := mul_nonneg pi_pos.le (by linarith only [(physicalArc_spec he.1 he.2).1.1])
  have hscale := (tendsto_add_atTop_nat 3).eventually (forecast_scales hb hτ x hx)
  have hratio : a/b<1 := (div_lt_one hb₀).mpr hab
  have hsum := (summable_nat_add_iff 3).mpr
    (summable_geometric_of_lt_one (div_nonneg (zero_lt_one.trans ha).le hb₀.le) hratio)
  have hseries : Summable (fun k => μ.real (S k)) := by
    apply (hsum.mul_left 12).of_norm_bounded_eventually_nat
    filter_upwards [hscale] with k hk
    let N := K k
    let r := b⁻¹^N
    have hr : 0<r := pow_pos (inv_pos.mpr hb₀) _
    have hp := gaussian_forecast_window (e k) (f k) (hf k) univ MeasurableSet.univ (τ^N) (1/10) r
      he (pow_pos hτ₀ _) hr hk.1 hk.2
    simp only [preimage_univ,inter_univ,probReal_univ,mul_one] at hp
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    apply hp.trans
    have hcard : (⌊a^N⌋₊:ℝ)≤a^N := Nat.floor_le (pow_nonneg (zero_lt_one.trans ha).le _)
    calc
      _ ≤ a^N*(12*r) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 12*(a/b)^N := by simp only [r,div_eq_mul_inv,mul_pow]; ring
  have hmiss : ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ω∉S k := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top μ _)] using hseries.tsum_ofReal_ne_top
  filter_upwards [hmiss,regular_shells,date_before_crossing hτ₀ hτ'] with ω hm hv hd
  filter_upwards [hm,(tendsto_add_atTop_nat 1).eventually hv,hd] with k hmiss hV hdate
  rintro σ ⟨t,ht,C,w,hw,hm⟩
  exact hmiss ⟨hV,t,hdate.trans ht,C,w,hw,hm⟩

/-- At every budget's true first return there exists an implementing circuit and
a winding. Every such winding at the return escapes the prescribed forecasts,
even though the forecasts may observe all but three physical couplings. -/
theorem gaussian_first_winding_forecasts {a : ℝ} (ha : 1<a) (h₆ : a^6<2)
    (e : (k : ℕ) → Fin (k+2))
    (f : (k : ℕ) → Fin ⌊a^(k+3)⌋₊ → (Exterior (n:=k+1) (e k)→ℝ) → ℝ)
    (hf : ∀ k j, Measurable (f k j)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let h := pathPauliDisorderShell ω (k+1)
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let X := prefixPoint k ω
      let σ := crossingOrigin (k+1) P (9/80) X
      ∀ s : ℕ, let v := σ+crossingWait (k+1) P s X
        (∃ C : TwoQubitCircuit (k+3), C.gateCount ≤ s ∧ ∃ w, windingFit h C.eval w v (1/10)) ∧
        ∀ (C : TwoQubitCircuit (k+3)) w, windingFit h C.eval w v (1/10) →
          ∀ j, windingShape w≠f k j (outside (e k) h) := by
  filter_upwards [post_crossing_forecasts ha h₆ e f hf] with ω hw
  filter_upwards [hw] with k hk
  intro h P X σ s v
  have hh := ElapsedWindow.first_wait_fit (k+1) P s X
  have he : (1/10:ℝ)∈Ioo 0 (sqrt 2) := ⟨by norm_num,(by norm_num : (1/10:ℝ)<1).trans_le
    (one_le_sqrt.mpr (by norm_num))⟩
  constructor
  · obtain ⟨z,hz,C,hC,hfit⟩ := (hasProjectiveCircuitApproximation_iff_infDist ..).mpr hh.2
    refine ⟨C,hC,(laboratory_iff_winding h C.eval v he).mp ⟨z,hz,?_⟩⟩
    have hmat : numberedGenerator (k+1) X=pathHamiltonian h := numberedGenerator_shell _
    rwa [hmat] at hfit
  · intro C w hfit j hj
    exact hk ⟨v,le_add_of_nonneg_right hh.1,C,w,hfit,j,hj⟩

#print axioms gaussian_first_winding_forecasts
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
