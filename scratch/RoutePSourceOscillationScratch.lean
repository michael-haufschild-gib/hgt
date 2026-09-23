import GaloisForLFunctions.RHTower.CriticalChebyshevBoostChargeInjection
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem
import GaloisForLFunctions.RHTower.CCMUnitRieszCausalLaplaceBridge

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- Meromorphic continuation candidate for the literal unit-Riesz source transform. -/
def routePSourceLaplaceContinuation (z : ℂ) : ℂ :=
  (criticalNormalizedChebyshevErrorContinuation z - 2 / 3) / (z + 1)

private theorem boost_eq_sourceContinuation
    {z : ℂ} (hzhalf : z + 1 / 2 ≠ 0) (hzone : z + 1 ≠ 0) :
    criticalChebyshevBoostCurrent z =
      z * ((z + 1 / 2) *
        ((z + 1) * routePSourceLaplaceContinuation z + 2 / 3) + 1) := by
  rw [routePSourceLaplaceContinuation,
    criticalChebyshevBoostCurrent_eq_continuationAffine hzhalf]
  field_simp [hzone]
  ring

/-- A literal critical-line zero is a non-removable singularity of the source transform. -/
private theorem not_continuousAt_routePSourceLaplaceContinuation_of_zero
    {rho : ℂ} (hzeta : riemannZeta rho = 0) (him : 0 < rho.im) :
    ¬ ContinuousAt routePSourceLaplaceContinuation (rho - 1 / 2) := by
  intro hcont
  let z0 : ℂ := rho - 1 / 2
  obtain ⟨m, hm, hres⟩ :=
    criticalChebyshevBoostCurrent_residue_of_riemannZeta_zero hzeta
  have hz0im : 0 < z0.im := by simpa [z0] using him
  have hz0ne : z0 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hzhalf : z0 + 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [z0] at this
    linarith
  have hzone : z0 + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [z0] at this
    linarith
  have hopen : IsOpen {z : ℂ | z + 1 / 2 ≠ 0 ∧ z + 1 ≠ 0} := by
    exact (isOpen_ne_fun (continuous_id.add continuous_const) continuous_const).inter
      (isOpen_ne_fun (continuous_id.add continuous_const) continuous_const)
  have hev0 : ∀ᶠ z in 𝓝 z0, z + 1 / 2 ≠ 0 ∧ z + 1 ≠ 0 :=
    hopen.mem_nhds ⟨hzhalf, hzone⟩
  have hev : ∀ᶠ z in 𝓝[≠] z0, z + 1 / 2 ≠ 0 ∧ z + 1 ≠ 0 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hev0
  have hGcont : ContinuousAt
      (fun z : ℂ => z * ((z + 1 / 2) *
        ((z + 1) * routePSourceLaplaceContinuation z + 2 / 3) + 1)) z0 := by
    fun_prop
  have hBfinite : Tendsto criticalChebyshevBoostCurrent (𝓝[≠] z0)
      (𝓝 (z0 * ((z0 + 1 / 2) *
        ((z0 + 1) * routePSourceLaplaceContinuation z0 + 2 / 3) + 1))) := by
    apply (hGcont.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [hev] with z hz
    exact (boost_eq_sourceContinuation hz.1 hz.2).symm
  have hsub : Tendsto (fun z : ℂ => z - z0) (𝓝[≠] z0) (𝓝 0) := by
    have hid : Tendsto (fun z : ℂ => z) (𝓝[≠] z0) (𝓝 z0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hc : Tendsto (fun _ : ℂ => z0) (𝓝[≠] z0) (𝓝 z0) :=
      tendsto_const_nhds
    simpa using hid.sub hc
  have hzero : Tendsto
      (fun z : ℂ => (z - z0) * criticalChebyshevBoostCurrent z)
      (𝓝[≠] z0) (𝓝 0) := by
    simpa using hsub.mul hBfinite
  have hlim := tendsto_nhds_unique hres hzero
  have hresne : -(z0) * (m : ℂ) ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr hz0ne) (Nat.cast_ne_zero.mpr (by omega))
  exact hresne (by simpa only [z0] using hlim)

/-- On the honest real Laplace ray this continuation is the literal source transform. -/
theorem routePSourceLaplaceContinuation_eq_laplace_on_real
    {r : ℝ} (hr : 1 / 2 < r) :
    routePSourceLaplaceContinuation (r : ℂ) =
      GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventLaplace (r : ℂ) := by
  have hzone : (r : ℂ) + 1 ≠ 0 := by
    apply ne_zero_of_re_pos
    norm_num
    linarith
  rw [routePSourceLaplaceContinuation,
    criticalNormalizedChebyshevErrorContinuation_eq_laplace (by simpa using hr),
    GaloisForLFunctions.RHTower.criticalNormalizedChebyshevErrorLaplace_eq_resolvent_on_real hr]
  field_simp [hzone]
  ring

/-- The meromorphic candidate agrees with the literal transform throughout its honest half-plane. -/
theorem routePSourceLaplaceContinuation_eq_laplace
    {z : ℂ} (hz : 1 / 2 < z.re) :
    routePSourceLaplaceContinuation z =
      GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventLaplace z := by
  have hu : 0 < (z - 1 / 2).re := by
    norm_num [Complex.sub_re] at hz ⊢
    linarith
  have h :=
    GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventDefectExtension_eq_regularized_rightHalfPlane hu
  have hfun : zetaResidueUnit = regularizedRiemannZeta := by
    funext s
    rfl
  rw [GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventDefectExtension,
    regularizedCriticalMellinDefect, ← hfun] at h
  have hcoord1 : z - 1 / 2 + 1 = z + 1 / 2 := by ring
  have hcoord2 : z - 1 / 2 + 3 / 2 = z + 1 := by ring
  have hcoord3 : z - 1 / 2 + 1 / 2 = z := by ring
  rw [hcoord1, hcoord2, hcoord3] at h
  have hden : z + 1 / 2 ≠ 0 := by
    apply ne_zero_of_re_pos
    norm_num
    linarith
  have hzone : z + 1 ≠ 0 := by
    apply ne_zero_of_re_pos
    norm_num
    linarith
  have hcore :
      (z + 1 / 2) *
          ((z + 1) * GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventLaplace z + 2 / 3) =
        -(logDeriv zetaResidueUnit (z + 1 / 2) + 1) := by
    linear_combination -h
  have hsolve :
      -(logDeriv zetaResidueUnit (z + 1 / 2) + 1) / (z + 1 / 2) =
        (z + 1) * GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventLaplace z + 2 / 3 := by
    apply (div_eq_iff hden).2
    linear_combination -hcore
  rw [routePSourceLaplaceContinuation, criticalNormalizedChebyshevErrorContinuation]
  rw [hsolve]
  field_simp [hzone]
  ring

/-- Hardy zeros force a singularity of the literal P/SP-E source continuation. -/
theorem exists_routePSourceLaplaceContinuation_critical_singularity :
    ∃ τ : ℝ, 0 < τ ∧ riemannZeta (linePt τ) = 0 ∧
      ¬ ContinuousAt routePSourceLaplaceContinuation (linePt τ - 1 / 2) := by
  obtain ⟨T0, hT0, hT⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨τ, hτ, hzero⟩ := hT T0 le_rfl
  have hτ0 : 0 < τ := lt_of_lt_of_le hT0 hτ.1
  exact ⟨τ, hτ0, hzero,
    not_continuousAt_routePSourceLaplaceContinuation_of_zero hzero
      (by simpa only [linePt_im] using hτ0)⟩

end RHTower
