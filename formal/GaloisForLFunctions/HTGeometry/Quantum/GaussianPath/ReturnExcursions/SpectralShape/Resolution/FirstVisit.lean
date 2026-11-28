import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Resolution.PhysicalWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Resolution.Scales
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.Reflection

/-! # Two onsite fields obstruct winding forecasts at the first return -/

open Filter MeasureTheory Set Real
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open PrescribedTimes ShortWindows SharpOccupation
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- For every exponential base below two, all forecasts from the remaining
physical couplings eventually miss every winding beyond the first crossing.
The observations include the bond joining the two withheld onsite fields. -/
theorem resolved_post_crossing {a : ℝ} (ha : 1<a) (ha₂ : a<2)
    (e : (k : ℕ) → Fin (k+2))
    (f : (k : ℕ) → Fin ⌊a^(k+3)⌋₊ → (PairExterior (n:=k+1) (e k)→ℝ) → ℝ)
    (hf : ∀ k j, Measurable (f k j)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let σ := crossingOrigin (k+1) (nearHilbertContinuousCircuitBudget (k+3)) (9/80) (prefixPoint k ω)
      ¬pairHit (e k) (f k) σ (1/10) (pathPauliDisorderShell ω (k+1)) := by
  obtain ⟨b,hab,hb₂⟩ := exists_between ha₂
  obtain ⟨τ,hbτ,hτ₂⟩ := exists_between hb₂
  let K (k : ℕ) := k+3
  let x := π*(1+physicalArc (1/10))
  let r (k : ℕ) := 1/(K k:ℝ)^2
  let μ := pathPauliDisorderLaw
  let S (k : ℕ) := {ω : PathPauliDisorder | let h := pathPauliDisorderShell ω (k+1)
    ‖h‖^2∈Icc (K k:ℝ) (13*(K k:ℝ)) ∧ resolvedEdge h.ofLp (e k) (r k) ∧
      pairHit (e k) (f k) (τ^(K k)) (1/10) h}
  have hb := ha.trans hab
  have hb₀ := zero_lt_one.trans hb
  have hτ₀ := hb₀.trans hbτ
  have he : (1/10:ℝ)∈Ioo 0 (sqrt 2) := ⟨by norm_num,(by norm_num : (1/10:ℝ)<1).trans_le
    (one_le_sqrt.mpr (by norm_num))⟩
  have hx : 0≤x := mul_nonneg pi_pos.le (by linarith only [(physicalArc_spec he.1 he.2).1.1])
  have hscale := (tendsto_add_atTop_nat 3).eventually (resolved_scales hb hbτ x hx)
  have hratio : a/b<1 := (div_lt_one hb₀).mpr hab
  have hsum := (summable_nat_add_iff 3).mpr
    (summable_geometric_of_lt_one (div_nonneg (zero_lt_one.trans ha).le hb₀.le) hratio)
  have hseries : Summable (fun k => μ.real (S k)) := by
    apply (hsum.mul_left 24).of_norm_bounded_eventually_nat
    filter_upwards [hscale] with k hk
    let N := K k
    let ρ := b⁻¹^N
    have hρ : 0<ρ := pow_pos (inv_pos.mpr hb₀) _
    have hr : 0<r k := by dsimp only [r,K]; positivity
    have hp := resolved_forecast_window (e k) (f k) (hf k) univ MeasurableSet.univ (τ^N) (1/10) (r k) ρ
      he (pow_pos hτ₀ _) hr hρ hk.1 hk.2
    simp only [preimage_univ,inter_univ,probReal_univ,mul_one] at hp
    rw [Real.norm_of_nonneg measureReal_nonneg]
    apply hp.trans
    have hcard : (⌊a^N⌋₊:ℝ)≤a^N := Nat.floor_le (pow_nonneg (zero_lt_one.trans ha).le _)
    calc
      _ ≤ a^N*(24*ρ) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 24*(a/b)^N := by simp only [ρ,div_eq_mul_inv,mul_pow]; ring
  have hmiss : ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ω∉S k := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top μ _)] using hseries.tsum_ofReal_ne_top
  filter_upwards [hmiss,regular_shells,resolved_prefixes e,date_before_crossing hτ₀ hτ₂] with ω hm hv hg hd
  filter_upwards [hm,(tendsto_add_atTop_nat 1).eventually hv,hg,hd] with k hmiss hV hreg hdate
  rintro σ ⟨t,ht,C,w,hw,hm⟩
  exact hmiss ⟨hV,hreg,t,hdate.trans ht,C,w,hw,hm⟩

/-- At the true first visit for every budget, a fitting circuit exists, and
every fitting circuit's integer word avoids all the two-field forecasts. -/
theorem gaussian_resolved_first_winding {a : ℝ} (ha : 1<a) (ha₂ : a<2)
    (e : (k : ℕ) → Fin (k+2))
    (f : (k : ℕ) → Fin ⌊a^(k+3)⌋₊ → (PairExterior (n:=k+1) (e k)→ℝ) → ℝ)
    (hf : ∀ k j, Measurable (f k j)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let h := pathPauliDisorderShell ω (k+1)
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let X := prefixPoint k ω
      let σ := crossingOrigin (k+1) P (9/80) X
      ∀ s : ℕ, let v := σ+crossingWait (k+1) P s X
        (∃ C : TwoQubitCircuit (k+3), C.gateCount ≤ s ∧ ∃ w, windingFit h C.eval w v (1/10)) ∧
        ∀ (C : TwoQubitCircuit (k+3)) w, windingFit h C.eval w v (1/10) →
          ∀ j, windingShape w≠f k j (pairReadings (e k) h.ofLp) := by
  filter_upwards [resolved_post_crossing ha ha₂ e f hf] with ω hw
  filter_upwards [hw] with k hk
  intro h P X σ s v
  have hh := ElapsedWindow.first_wait_fit (k+1) P s X
  have he : (1/10:ℝ)∈Ioo (0:ℝ) (sqrt 2) := ⟨by norm_num,(by norm_num : (1/10:ℝ)<1).trans_le
    (one_le_sqrt.mpr (by norm_num))⟩
  constructor
  · obtain ⟨z,hz,C,hC,hfit⟩ := (hasProjectiveCircuitApproximation_iff_infDist ..).mpr hh.2
    refine ⟨C,hC,(laboratory_iff_winding h C.eval v he).mp ⟨z,hz,?_⟩⟩
    rwa [show numberedGenerator (k+1) X=pathHamiltonian h from numberedGenerator_shell _] at hfit
  · intro C w hfit j hj
    exact hk ⟨v,le_add_of_nonneg_right hh.1,C,w,hfit,j,hj⟩

#print axioms gaussian_resolved_first_winding
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
