import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceSpectralPole

/-!
# Quantized poles of the literal Route P source

The finite-order Laplace continuation carries a nonzero residue at every
positive-height zeta zero. Its value records the exact zero multiplicity.
Consequently a continuous scalar graph gauge can regularize this source only
by vanishing at that zero. This is a meromorphic graph constraint, not a
signed-debt estimate or a proof of RH.
-/

open Complex Filter Topology

namespace RHTower

/-- The literal Route P source has residue `-m / (rho * (rho + 1/2))` at a
positive-height zeta zero `rho` of multiplicity `m`. -/
theorem routePSourceLaplaceContinuation_residue_of_zero
    {rho : ℂ} (hzeta : riemannZeta rho = 0) (him : 0 < rho.im) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto
        (fun z : ℂ => (z - (rho - 1 / 2)) * routePSourceLaplaceContinuation z)
        (𝓝[≠] (rho - 1 / 2))
        (𝓝 (-(m : ℂ) / (rho * (rho + 1 / 2)))) := by
  obtain ⟨m, hm, hboost⟩ :=
    criticalChebyshevBoostCurrent_residue_of_riemannZeta_zero hzeta
  refine ⟨m, hm, ?_⟩
  let z0 : ℂ := rho - 1 / 2
  have hz0im : 0 < z0.im := by simpa [z0] using him
  have hz0 : z0 ≠ 0 := by
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
  have hA : z0 * (z0 + 1 / 2) * (z0 + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hz0 hzhalf) hzone
  have hpoly : Tendsto
      (fun z : ℂ => z * ((z + 1 / 2) * (2 / 3) + 1))
      (𝓝[≠] z0)
      (𝓝 (z0 * ((z0 + 1 / 2) * (2 / 3) + 1))) := by
    exact (by fun_prop : ContinuousAt
      (fun z : ℂ => z * ((z + 1 / 2) * (2 / 3) + 1)) z0).tendsto.mono_left
        nhdsWithin_le_nhds
  have hden : Tendsto
      (fun z : ℂ => z * (z + 1 / 2) * (z + 1))
      (𝓝[≠] z0)
      (𝓝 (z0 * (z0 + 1 / 2) * (z0 + 1))) := by
    exact (by fun_prop : ContinuousAt
      (fun z : ℂ => z * (z + 1 / 2) * (z + 1)) z0).tendsto.mono_left
        nhdsWithin_le_nhds
  have hsub : Tendsto (fun z : ℂ => z - z0) (𝓝[≠] z0) (𝓝 0) := by
    simpa using (by fun_prop : ContinuousAt (fun z : ℂ => z - z0) z0).tendsto.mono_left
      nhdsWithin_le_nhds
  have hboost' : Tendsto
      (fun z : ℂ => (z - z0) * criticalChebyshevBoostCurrent z)
      (𝓝[≠] z0) (𝓝 (-(z0) * (m : ℂ))) := by
    simpa only [z0] using hboost
  have hratio := (hboost'.sub (hsub.mul hpoly)).div hden hA
  have hev : ∀ᶠ z in 𝓝[≠] z0,
      z ≠ 0 ∧ z + 1 / 2 ≠ 0 ∧ z + 1 ≠ 0 := by
    have hopen : IsOpen {z : ℂ | z ≠ 0 ∧ z + 1 / 2 ≠ 0 ∧ z + 1 ≠ 0} := by
      have h1 : IsOpen {z : ℂ | z ≠ 0} :=
        isOpen_ne_fun continuous_id continuous_const
      have h2 : IsOpen {z : ℂ | z + 1 / 2 ≠ 0} :=
        isOpen_ne_fun (continuous_id.add continuous_const) continuous_const
      have h3 : IsOpen {z : ℂ | z + 1 ≠ 0} :=
        isOpen_ne_fun (continuous_id.add continuous_const) continuous_const
      simpa [Set.setOf_and, Set.inter_assoc] using (h1.inter h2).inter h3
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hopen.mem_nhds ⟨hz0, hzhalf, hzone⟩)
  have heq :
      (fun z : ℂ => (z - z0) * routePSourceLaplaceContinuation z) =ᶠ[𝓝[≠] z0]
      (fun z : ℂ =>
        ((z - z0) * criticalChebyshevBoostCurrent z -
          (z - z0) * (z * ((z + 1 / 2) * (2 / 3) + 1))) /
          (z * (z + 1 / 2) * (z + 1))) := by
    filter_upwards [hev] with z hz
    have hsrc : (z + 1) * routePSourceLaplaceContinuation z =
        criticalNormalizedChebyshevErrorContinuation z - 2 / 3 := by
      unfold routePSourceLaplaceContinuation
      exact mul_div_cancel₀ _ hz.2.2
    have hnorm : criticalNormalizedChebyshevErrorContinuation z =
        (z + 1) * routePSourceLaplaceContinuation z + 2 / 3 := by
      linear_combination -hsrc
    have hcore : criticalChebyshevBoostCurrent z =
        (z * (z + 1 / 2) * (z + 1)) * routePSourceLaplaceContinuation z +
          z * ((z + 1 / 2) * (2 / 3) + 1) := by
      rw [criticalChebyshevBoostCurrent_eq_continuationAffine hz.2.1, hnorm]
      ring
    apply (eq_div_iff (mul_ne_zero
      (mul_ne_zero hz.1 hz.2.1) hz.2.2)).2
    calc
      (z - z0) * routePSourceLaplaceContinuation z *
          (z * (z + 1 / 2) * (z + 1)) =
          (z - z0) * ((z * (z + 1 / 2) * (z + 1)) *
            routePSourceLaplaceContinuation z) := by ring
      _ = (z - z0) *
          (criticalChebyshevBoostCurrent z -
            z * ((z + 1 / 2) * (2 / 3) + 1)) := by rw [hcore]; ring
      _ = _ := by ring
  have hlim : Tendsto
      (fun z : ℂ => (z - z0) * routePSourceLaplaceContinuation z)
      (𝓝[≠] z0)
      (𝓝 ((-(z0) * (m : ℂ) -
        0 * (z0 * ((z0 + 1 / 2) * (2 / 3) + 1))) /
        (z0 * (z0 + 1 / 2) * (z0 + 1)))) :=
    hratio.congr' heq.symm
  have hcenter : z0 + 1 / 2 = rho := by dsimp [z0]; ring
  have hplus : z0 + 1 = rho + 1 / 2 := by dsimp [z0]; ring
  have hvalue : (-(z0) * (m : ℂ)) /
      (z0 * (z0 + 1 / 2) * (z0 + 1)) =
      -(m : ℂ) / (rho * (rho + 1 / 2)) := by
    rw [hcenter, hplus]
    have hleft : z0 * rho * (rho + 1 / 2) ≠ 0 := by
      simpa only [hcenter, hplus] using hA
    have hrho : rho ≠ 0 := by rw [← hcenter]; exact hzhalf
    have hrhohalf : rho + 1 / 2 ≠ 0 := by rw [← hplus]; exact hzone
    have hright : rho * (rho + 1 / 2) ≠ 0 :=
      mul_ne_zero hrho hrhohalf
    apply (div_eq_div_iff hleft hright).2
    ring
  simpa only [zero_mul, sub_zero, hvalue] using hlim

/-- Any continuous scalar gauge whose product with the Route P source is
continuous through a positive-height zeta zero must vanish there. -/
theorem routePSourceLaplaceContinuation_regularizing_gauge_vanishes
    {rho : ℂ} (hzeta : riemannZeta rho = 0) (him : 0 < rho.im)
    (g : ℂ → ℂ)
    (hg : ContinuousAt g (rho - 1 / 2))
    (hprod : ContinuousAt
      (fun z => g z * routePSourceLaplaceContinuation z) (rho - 1 / 2)) :
    g (rho - 1 / 2) = 0 := by
  obtain ⟨m, hm, hres⟩ :=
    routePSourceLaplaceContinuation_residue_of_zero hzeta him
  let z0 : ℂ := rho - 1 / 2
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
  have hsub : Tendsto (fun z : ℂ => z - z0) (𝓝[≠] z0) (𝓝 0) := by
    simpa using (by fun_prop : ContinuousAt (fun z : ℂ => z - z0) z0).tendsto.mono_left
      nhdsWithin_le_nhds
  have hg' : Tendsto g (𝓝[≠] z0) (𝓝 (g z0)) :=
    hg.tendsto.mono_left nhdsWithin_le_nhds
  have hprod' : Tendsto (fun z => g z * routePSourceLaplaceContinuation z)
      (𝓝[≠] z0) (𝓝 (g z0 * routePSourceLaplaceContinuation z0)) :=
    hprod.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : Tendsto
      (fun z : ℂ => ((z - z0) * routePSourceLaplaceContinuation z) * g z)
      (𝓝[≠] z0) (𝓝 0) := by
    simpa only [zero_mul] using (hsub.mul hprod').congr'
      (Eventually.of_forall (fun z => by ring))
  have hres' : Tendsto
      (fun z : ℂ => ((z - z0) * routePSourceLaplaceContinuation z) * g z)
      (𝓝[≠] z0)
      (𝓝 ((-(m : ℂ) / (rho * (rho + 1 / 2))) * g z0)) := by
    simpa only [z0] using hres.mul hg'
  have hEq := tendsto_nhds_unique hres' hzero
  exact (mul_eq_zero.mp hEq).resolve_left hc

/-- Unconditionally, a positive-height zeta zero supplies a quantized literal
Route P source pole; every continuous scalar regularizer vanishes there. -/
theorem exists_routePSourceLaplaceContinuation_quantized_critical_pole :
    ∃ (rho : ℂ) (m : ℕ),
      0 < rho.im ∧ riemannZeta rho = 0 ∧ 1 ≤ m ∧
      Tendsto
        (fun z : ℂ => (z - (rho - 1 / 2)) * routePSourceLaplaceContinuation z)
        (𝓝[≠] (rho - 1 / 2))
        (𝓝 (-(m : ℂ) / (rho * (rho + 1 / 2)))) ∧
      ∀ g : ℂ → ℂ,
        ContinuousAt g (rho - 1 / 2) →
        ContinuousAt (fun z => g z * routePSourceLaplaceContinuation z)
          (rho - 1 / 2) →
        g (rho - 1 / 2) = 0 := by
  obtain ⟨T0, hT0, hT⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨τ, hτ, hzero⟩ := hT T0 le_rfl
  have hτ0 : 0 < τ := lt_of_lt_of_le hT0 hτ.1
  let rho : ℂ := linePt τ
  have him : 0 < rho.im := by simpa only [rho, linePt_im] using hτ0
  obtain ⟨m, hm, hres⟩ :=
    routePSourceLaplaceContinuation_residue_of_zero hzero him
  exact ⟨rho, m, him, hzero, hm, hres,
    fun g hg hprod =>
      routePSourceLaplaceContinuation_regularizing_gauge_vanishes
        hzero him g hg hprod⟩

end RHTower
