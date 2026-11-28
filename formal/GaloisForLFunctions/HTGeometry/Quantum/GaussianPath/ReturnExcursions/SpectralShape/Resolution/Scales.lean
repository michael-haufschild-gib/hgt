import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Resolution.AngularSlope
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Forecasts.ExponentialScale
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.DateTail

/-! # Resolving physical winding shapes at every exponential rate below two -/

open MeasureTheory Filter Real Set WithLp
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open Dephasing.PairedFields Dephasing.PairedFields.ClockAdjustment
open private continuous_edgeResponse from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.GaussianPair
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- The two physical traces on any prescribed sequence of bonds eventually
resolve their derivatives on the original frozen prefixes. -/
theorem resolved_prefixes (e : (k : ℕ) → Fin (k+2)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      resolvedEdge (pathPauliDisorderShell ω (k+1)).ofLp (e k) (1/((k+3:ℕ):ℝ)^2) := by
  let μ := pathPauliDisorderLaw
  let r (k : ℕ) : ℝ := 1/((k+3:ℕ):ℝ)^2
  let Z (k : ℕ) (ω : PathPauliDisorder) : Coeff (k+1) := (pathPauliDisorderShell ω (k+1)).ofLp
  let B (k : ℕ) := {h : Coeff (k+1) | ¬resolvedEdge h (e k) (r k)}
  have hM (n : ℕ) : Continuous (thirdMoment (n:=n)) := by
    have hH := (pathHamiltonianLM n).continuous_of_finiteDimensional
    change Continuous (fun h : PathShell n => pathHamiltonian h) at hH
    unfold thirdMoment Matrix.trace
    fun_prop
  have hB (k) : MeasurableSet (B k) := by
    have h₁ := (hM (k+1)).measurable.comp (MeasurableEquiv.toLp 2 (Coeff (k+1))).measurable
    exact ((measurableSet_le measurable_const h₁.abs).inter (measurableSet_le measurable_const
      (continuous_edgeResponse (e k) 0 0).abs.measurable)).compl
  have hs : Summable (fun k : ℕ => μ.real (Z k ⁻¹' B k)) := by
    have hh : Summable (fun k : ℕ => (1:ℝ)/(k:ℝ)^2) := summable_one_div_nat_pow.mpr (by norm_num)
    apply (((summable_nat_add_iff 3).mpr hh).mul_left 18).of_norm_bounded
    intro k
    rw [Real.norm_of_nonneg measureReal_nonneg,(BlockDilations.prefix_measure _).measureReal_preimage
      (hB k).nullMeasurableSet]
    exact gaussian_resolved_edge (e k) (by dsimp only [r]; positivity)
  have hh : ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ω∉Z k ⁻¹' B k := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top μ _)] using hs.tsum_ofReal_ne_top
  filter_upwards [hh] with ω hw
  exact hw.mono fun k hk => not_not.mp hk

/-- The polynomial price of resolving a typical onsite derivative is absorbed
by any gap between the exponential date base and the forecast resolution base. -/
theorem resolved_scales {b τ : ℝ} (hb : 1<b) (hbτ : b<τ) (x : ℝ) (hx : 0≤x) :
    ∀ᶠ K : ℕ in atTop, 16*x≤τ^K*sqrt (K:ℝ) ∧
      6*(16000*x*(sqrt (13*(K:ℝ)))^5/τ^K)<b⁻¹^K*((1/(K:ℝ)^2)^6/(1+13*(K:ℝ))) := by
  let C := 6*(16000*x*13^5)*14
  let q := τ/b
  have hb₀ := zero_lt_one.trans hb
  have hτ := hb.trans hbτ
  have hq : 1<q := (one_lt_div hb₀).mpr hbτ
  have he := ((tendsto_pow_const_div_const_pow_of_one_lt 18 hq).const_mul C).eventually_lt_const
    (by simp : C*0<1)
  filter_upwards [he,(tendsto_pow_atTop_atTop_of_one_lt hτ).eventually_ge_atTop (16*x),
    eventually_ge_atTop 1] with K hh hdate hK
  have hn : 1≤(K:ℝ) := by exact_mod_cast hK
  have hK₀ := zero_lt_one.trans_le hn
  have hτ₀ := pow_pos (zero_lt_one.trans hτ) K
  have hden : 0<1+13*(K:ℝ) := by positivity
  have hs : sqrt (13*(K:ℝ))≤13*(K:ℝ) := sqrt_le_iff.mpr
    ⟨by positivity,by nlinarith only [hn,sq_nonneg ((K:ℝ)-1)]⟩
  constructor
  · exact hdate.trans (le_mul_of_one_le_right hτ₀.le (one_le_sqrt.mpr hn))
  · change C*((K:ℝ)^18/q^K)<1 at hh
    rw [←mul_div_assoc,div_lt_one (pow_pos (zero_lt_one.trans hq) _)] at hh
    have hbound : 6*(16000*x*(sqrt (13*(K:ℝ)))^5)*(1+13*(K:ℝ))*((K:ℝ)^2)^6<q^K := by
      apply lt_of_le_of_lt _ hh
      calc
        _ ≤ 6*(16000*x*(13*(K:ℝ))^5)*(14*(K:ℝ))*((K:ℝ)^2)^6 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul _ (by linarith only [hn]) hden.le (by positivity)
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sqrt_nonneg _) hs _) (by positivity)) (by norm_num)
        _ = _ := by dsimp only [C]; ring
    change _ < (τ/b)^K at hbound
    rw [div_pow,lt_div_iff₀ (pow_pos hb₀ _)] at hbound
    rw [one_div_pow,inv_pow,←one_div]
    field_simp [hτ₀.ne',hden.ne',hK₀.ne',hb₀.ne']
    nlinarith only [hbound]

#print axioms resolved_prefixes
#print axioms resolved_scales
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
