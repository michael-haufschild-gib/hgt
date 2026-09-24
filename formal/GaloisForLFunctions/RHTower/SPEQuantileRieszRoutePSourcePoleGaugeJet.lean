import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourcePoleResidue

/-!
# Route P source-pole gauge jets

At a positive-height zeta zero, the literal source has a nonzero simple
residue. Its patched reciprocal has a simple zero. Any differentiable gauge
that regularizes the source through a separately patched product has an
assigned center value fixed by gauge derivative times residue; continuity
of the unpatched totalized product forces its first jet to vanish.
These are local graph constraints, not a cofinal intertwiner or debt payment.
-/

open Complex Filter Topology

namespace RHTower

/-- Local reciprocal of the literal source, patched at its selected pole. -/
noncomputable def routePSourceInversePoleGauge (z0 z : ℂ) : ℂ :=
  if z = z0 then 0 else (routePSourceLaplaceContinuation z)⁻¹

theorem routePSourceInversePoleGauge_derivative_of_zero
    {rho : ℂ} (hzeta : riemannZeta rho = 0) (him : 0 < rho.im) :
    ∃ m : ℕ, 1 ≤ m ∧
      HasDerivAt
        (routePSourceInversePoleGauge (rho - 1 / 2))
        (-(m : ℂ) / (rho * (rho + 1 / 2)))⁻¹
        (rho - 1 / 2) ∧
      (-(m : ℂ) / (rho * (rho + 1 / 2)))⁻¹ ≠ 0 := by
  obtain ⟨m, hm, hres⟩ :=
    routePSourceLaplaceContinuation_residue_of_zero hzeta him
  let z0 : ℂ := rho - 1 / 2
  let c : ℂ := -(m : ℂ) / (rho * (rho + 1 / 2))
  have hrho : rho ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hrhohalf : rho + 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hc : c ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
      (mul_ne_zero hrho hrhohalf)
  have hres' : Tendsto
      (fun z : ℂ => (z - z0) * routePSourceLaplaceContinuation z)
      (𝓝[≠] z0) (𝓝 c) := by
    simpa only [z0, c] using hres
  have hinv : Tendsto
      (fun z : ℂ => (routePSourceLaplaceContinuation z)⁻¹ / (z - z0))
      (𝓝[≠] z0) (𝓝 c⁻¹) := by
    convert hres'.inv₀ hc using 1
    funext z
    simp only [mul_inv_rev, div_eq_mul_inv]
  have hslope : slope (routePSourceInversePoleGauge z0) z0 =
      (fun z : ℂ => (routePSourceLaplaceContinuation z)⁻¹ / (z - z0)) := by
    funext z
    by_cases hz : z = z0
    · subst z
      simp
    · simp [slope_fun_def_field, routePSourceInversePoleGauge, hz]
  refine ⟨m, hm, ?_, ?_⟩
  · rw [hasDerivAt_iff_tendsto_slope]
    simpa only [z0, c, hslope] using hinv
  · exact inv_ne_zero hc

theorem exists_routePSourceInversePoleGauge_quantized_critical_zero :
    ∃ (rho : ℂ) (m : ℕ),
      0 < rho.im ∧ riemannZeta rho = 0 ∧ 1 ≤ m ∧
      HasDerivAt
        (routePSourceInversePoleGauge (rho - 1 / 2))
        (-(m : ℂ) / (rho * (rho + 1 / 2)))⁻¹
        (rho - 1 / 2) ∧
      (-(m : ℂ) / (rho * (rho + 1 / 2)))⁻¹ ≠ 0 := by
  obtain ⟨rho, _, him, hzeta, _, _, _⟩ :=
    exists_routePSourceLaplaceContinuation_quantized_critical_pole
  obtain ⟨m, hm, hderiv, hne⟩ :=
    routePSourceInversePoleGauge_derivative_of_zero hzeta him
  exact ⟨rho, m, him, hzeta, hm, hderiv, hne⟩

/-- The value assigned at a removable product singularity is forced by the
gauge derivative and the source residue. -/
theorem routePSourceGauge_patched_value_of_zero
    {rho : ℂ} (hzeta : riemannZeta rho = 0) (him : 0 < rho.im)
    (g h : ℂ → ℂ) (d : ℂ)
    (hgzero : g (rho - 1 / 2) = 0)
    (hg : HasDerivAt g d (rho - 1 / 2))
    (hh : ContinuousAt h (rho - 1 / 2))
    (heq : (fun z => h z) =ᶠ[𝓝[≠] (rho - 1 / 2)]
      (fun z => g z * routePSourceLaplaceContinuation z)) :
    ∃ m : ℕ, 1 ≤ m ∧
      h (rho - 1 / 2) = d * (-(m : ℂ) / (rho * (rho + 1 / 2))) := by
  obtain ⟨m, hm, hres⟩ :=
    routePSourceLaplaceContinuation_residue_of_zero hzeta him
  let z0 : ℂ := rho - 1 / 2
  let c : ℂ := -(m : ℂ) / (rho * (rho + 1 / 2))
  have hgzero' : g z0 = 0 := by simpa only [z0] using hgzero
  have hres' : Tendsto
      (fun z : ℂ => (z - z0) * routePSourceLaplaceContinuation z)
      (𝓝[≠] z0) (𝓝 c) := by
    simpa only [z0, c] using hres
  have hquot : Tendsto (fun z : ℂ => g z / (z - z0))
      (𝓝[≠] z0) (𝓝 d) := by
    have hslope : Tendsto (slope g z0) (𝓝[≠] z0) (𝓝 d) :=
      (hasDerivAt_iff_tendsto_slope).mp hg
    apply hslope.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z - z0 ≠ 0 := sub_ne_zero.mpr hz
    simp [slope_fun_def_field, hgzero', div_eq_mul_inv]
  have hprod := hquot.mul hres'
  have hprod' : Tendsto h (𝓝[≠] z0) (𝓝 (d * c)) := by
    apply hprod.congr'
    filter_upwards [heq, self_mem_nhdsWithin] with z hEq hz
    have hz' : z - z0 ≠ 0 := sub_ne_zero.mpr hz
    rw [hEq]
    field_simp
  have hh' : Tendsto h (𝓝[≠] z0) (𝓝 (h z0)) :=
    hh.tendsto.mono_left nhdsWithin_le_nhds
  have hv := tendsto_nhds_unique hh' hprod'
  exact ⟨m, hm, by simpa only [z0, c] using hv⟩

/-- Continuity of the unpatched literal product forces a vanishing first jet. -/
theorem routePSourceGauge_unpatched_derivative_zero
    {rho : ℂ} (hzeta : riemannZeta rho = 0) (him : 0 < rho.im)
    (g : ℂ → ℂ) (d : ℂ)
    (hg : HasDerivAt g d (rho - 1 / 2))
    (hprod : ContinuousAt
      (fun z => g z * routePSourceLaplaceContinuation z) (rho - 1 / 2)) :
    d = 0 := by
  have hgzero := routePSourceLaplaceContinuation_regularizing_gauge_vanishes
    hzeta him g hg.continuousAt hprod
  obtain ⟨m, hm, hv⟩ :=
    routePSourceGauge_patched_value_of_zero hzeta him g
      (fun z => g z * routePSourceLaplaceContinuation z) d
      hgzero hg hprod (Filter.Eventually.of_forall fun _ => rfl)
  have hrho : rho ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hrhohalf : rho + 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hc : -(m : ℂ) / (rho * (rho + 1 / 2)) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
      (mul_ne_zero hrho hrhohalf)
  rw [hgzero, zero_mul] at hv
  exact (mul_eq_zero.mp hv.symm).resolve_right hc

/-- Hardy's zero makes the first-jet obstruction unconditional. -/
theorem exists_routePSourceGauge_unpatched_firstJet_zero :
    ∃ rho : ℂ, 0 < rho.im ∧ riemannZeta rho = 0 ∧
      ∀ (g : ℂ → ℂ) (d : ℂ),
        HasDerivAt g d (rho - 1 / 2) →
        ContinuousAt
          (fun z => g z * routePSourceLaplaceContinuation z)
          (rho - 1 / 2) →
        d = 0 := by
  obtain ⟨rho, _, him, hzeta, _, _, _⟩ :=
    exists_routePSourceLaplaceContinuation_quantized_critical_pole
  exact ⟨rho, him, hzeta,
    fun g d hg hprod =>
      routePSourceGauge_unpatched_derivative_zero hzeta him g d hg hprod⟩

end RHTower
