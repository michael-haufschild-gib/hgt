import GaloisForLFunctions.RHTower.DeningerMeyerXiGaussianGammaResidue

/-!
# Route R local relative anomaly-cancellation no-go

This module formalizes C23 of the Route R prepolar audit.  Any local Meyer lift whose Poisson
image differs from the coefficient-faithful Gaussian Green germ only by a holomorphic correction
retains completed meromorphic order `-1`.  Thus no holomorphic correction, lower principal jet,
or locally invisible source-exact term changes the universal Gamma/Green pole.

Conversely, if a local correction makes completed Xi transport holomorphic, then its Poisson image
also has nonnegative order: cancellation necessarily erases the retained Green principal
coefficient.  Local relative anomaly cancellation and coefficient faithfulness are therefore
mutually exclusive.  Any surviving Route R producer must be nonlocal across divisor fibres or
prime places.

No RH, critical-line placement, Xi-zero simplicity, same-fibre norm identity, or source-dagger
identity is assumed.
-/

open Complex Filter Topology Set Metric
open scoped Real

namespace RHTower.DeningerMeyerGaussianGreen

noncomputable section

private theorem eventually_xi_eq_archFactor_mul_zeta_of_mem_strip
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    ∀ᶠ s in nhdsWithin rho {rho}ᶜ, xi s = archFactor s * riemannZeta s := by
  let U : Set ℂ := {s | 0 < s.re ∧ s.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hstripEventually : ∀ᶠ s in nhdsWithin rho {rho}ᶜ, s ∈ U :=
    Filter.Eventually.filter_mono inf_le_left (hUopen.mem_nhds hstrip)
  filter_upwards [hstripEventually] with s hs
  exact xi_eq_archFactor_mul_zeta
    (by intro h; subst s; dsimp [U] at hs; norm_num at hs)
    (by intro h; subst s; dsimp [U] at hs; norm_num at hs)
    (Gammaℝ_ne_zero_of_re_pos hs.1)

private theorem meromorphicOrderAt_archFactor_eq_zero
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    meromorphicOrderAt archFactor rho = 0 := by
  have harch : AnalyticAt ℂ archFactor rho :=
    archFactor_analyticOnNhd_re_pos rho hstrip.1
  rw [harch.meromorphicOrderAt_eq,
    harch.analyticOrderAt_eq_zero.mpr (archFactor_ne_zero_strip hstrip)]
  norm_num

theorem meromorphicOrderAt_xi_mul_coefficientFaithfulGaussianCorrection_eq_neg_one
    {c rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (hcr : rho ≠ c)
    (P H : ℂ → ℂ) (hH : AnalyticAt ℂ H rho)
    (himage : ∀ᶠ s in nhdsWithin rho {rho}ᶜ,
      riemannZeta s * P s =
        (gaussianResolventDenominator c rho s)⁻¹ + H s) :
    meromorphicOrderAt (fun s => xi s * P s) rho = -1 := by
  have harch : AnalyticAt ℂ archFactor rho :=
    archFactor_analyticOnNhd_re_pos rho hstrip.1
  have hden : AnalyticAt ℂ (gaussianResolventDenominator c rho) rho := by
    unfold gaussianResolventDenominator gaussianMellinCharacter
    fun_prop
  have heq : (fun s => xi s * P s) =ᶠ[nhdsWithin rho {rho}ᶜ]
      (fun s => archFactor s * (gaussianResolventDenominator c rho s)⁻¹ +
        archFactor s * H s) := by
    filter_upwards [eventually_xi_eq_archFactor_mul_zeta_of_mem_strip hstrip,
      himage] with s hxi hP
    rw [hxi, mul_assoc, hP]
    ring
  rw [meromorphicOrderAt_congr heq]
  have hprincipal : meromorphicOrderAt
      (fun s => archFactor s * (gaussianResolventDenominator c rho s)⁻¹) rho = -1 := by
    change meromorphicOrderAt
      (archFactor * (gaussianResolventDenominator c rho)⁻¹) rho = -1
    rw [meromorphicOrderAt_mul harch.meromorphicAt hden.meromorphicAt.inv,
      meromorphicOrderAt_archFactor_eq_zero hstrip,
      meromorphicOrderAt_inv, hden.meromorphicOrderAt_eq,
      analyticOrderAt_gaussianResolventDenominator_eq_one hcr]
    norm_num
  have hcorr : AnalyticAt ℂ (fun s => archFactor s * H s) rho := harch.mul hH
  have hlt : meromorphicOrderAt
      (fun s => archFactor s * (gaussianResolventDenominator c rho s)⁻¹) rho <
      meromorphicOrderAt (fun s => archFactor s * H s) rho := by
    rw [hprincipal]
    exact lt_of_lt_of_le
      (by
        change (((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ))
        exact WithTop.coe_lt_coe.mpr (by omega))
      hcorr.meromorphicOrderAt_nonneg
  change meromorphicOrderAt
    ((fun s => archFactor s * (gaussianResolventDenominator c rho s)⁻¹) +
      (fun s => archFactor s * H s)) rho = -1
  rw [meromorphicOrderAt_add_eq_left_of_lt hcorr.meromorphicAt hlt, hprincipal]

theorem completedCancellation_forces_poissonPrincipal_erasure
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (Q : ℂ → ℂ) (hQ : MeromorphicAt Q rho)
    (hcancel : 0 ≤ meromorphicOrderAt (fun s => xi s * Q s) rho) :
    0 ≤ meromorphicOrderAt (fun s => riemannZeta s * Q s) rho := by
  have harch : AnalyticAt ℂ archFactor rho :=
    archFactor_analyticOnNhd_re_pos rho hstrip.1
  have hzeta : AnalyticAt ℂ riemannZeta rho :=
    analyticOn_riemannZeta rho (by
      intro h
      subst rho
      norm_num at hstrip)
  have hpoisson : MeromorphicAt (fun s => riemannZeta s * Q s) rho :=
    hzeta.meromorphicAt.mul hQ
  have heq : (fun s => xi s * Q s) =ᶠ[nhdsWithin rho {rho}ᶜ]
      (fun s => archFactor s * (riemannZeta s * Q s)) := by
    filter_upwards [eventually_xi_eq_archFactor_mul_zeta_of_mem_strip hstrip] with s hxi
    rw [hxi]
    ring
  rw [meromorphicOrderAt_congr heq] at hcancel
  change 0 ≤ meromorphicOrderAt
    (archFactor * (fun s => riemannZeta s * Q s)) rho at hcancel
  rw [meromorphicOrderAt_mul harch.meromorphicAt hpoisson,
    meromorphicOrderAt_archFactor_eq_zero hstrip, zero_add] at hcancel
  exact hcancel

end
end RHTower.DeningerMeyerGaussianGreen
