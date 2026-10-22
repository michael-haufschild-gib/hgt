import GaloisForLFunctions.RHTower.CriticalContinuousChebyshevDivisorLaplaceWeld
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmQuantileDivisorCharge
import GaloisForLFunctions.RHTower.PrimePolarResidueCancellation

/-!
# Chebyshev-source injection of the Route N boost charge

The logarithmic Laplace transform of normalized continuous Chebyshev error supplies more than the
unweighted divisor current.  Multiplying its finite-order continuation by centered spectral
coordinate `z = s - 1/2` gives exactly

`-z * logDeriv ((s - 1) * zeta(s))`.

Thus every zeta zero receives its Route N modular boost charge directly from pre-divisor Chebyshev
source.  No positive scalarization, entire exponential gauge, or floor correction intervenes.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Finite-order continuation of the normalized continuous-Chebyshev Laplace transform. -/
def criticalNormalizedChebyshevErrorContinuation (z : ℂ) : ℂ :=
  -(logDeriv zetaResidueUnit (z + 1 / 2) + 1) / (z + 1 / 2)

/-- The honest Laplace transform and finite-order continuation agree on the convergence half-plane. -/
theorem criticalNormalizedChebyshevErrorContinuation_eq_laplace
    {z : ℂ} (hz : 1 / 2 < z.re) :
    criticalNormalizedChebyshevErrorContinuation z =
      criticalNormalizedChebyshevErrorLaplace z := by
  rw [criticalNormalizedChebyshevErrorContinuation,
    criticalNormalizedChebyshevErrorLaplace_eq_logDeriv hz]

/-- Centered boost current extracted from the finite-order zeta residue unit. -/
def criticalChebyshevBoostCurrent (z : ℂ) : ℂ :=
  -z * logDeriv zetaResidueUnit (z + 1 / 2)

/-- **C51 source injection.** On the honest convergence half-plane, Route N's centered boost
current is exactly the first affine expression in the Route T Chebyshev-source Laplace transform. -/
theorem criticalChebyshevBoostCurrent_eq_laplaceAffine
    {z : ℂ} (hz : 1 / 2 < z.re) :
    criticalChebyshevBoostCurrent z =
      z * ((z + 1 / 2) * criticalNormalizedChebyshevErrorLaplace z + 1) := by
  have hz0 : z + 1 / 2 ≠ 0 := by
    apply ne_zero_of_re_pos
    rw [Complex.add_re]
    norm_num
    linarith
  have hden : z * 2 + 1 ≠ 0 := by
    intro h
    apply hz0
    linear_combination h / 2
  rw [criticalChebyshevBoostCurrent,
    criticalNormalizedChebyshevErrorLaplace_eq_logDeriv hz]
  have hcancel :
      (z + 1 / 2) *
          (-(logDeriv zetaResidueUnit (z + 1 / 2) + 1) / (z + 1 / 2)) =
        -(logDeriv zetaResidueUnit (z + 1 / 2) + 1) := by
    field_simp [hz0, hden]
  rw [hcancel]
  ring

/-- The same injection stated entirely through the finite-order continuation. -/
theorem criticalChebyshevBoostCurrent_eq_continuationAffine
    {z : ℂ} (hz0 : z + 1 / 2 ≠ 0) :
    criticalChebyshevBoostCurrent z =
      z * ((z + 1 / 2) * criticalNormalizedChebyshevErrorContinuation z + 1) := by
  rw [criticalChebyshevBoostCurrent, criticalNormalizedChebyshevErrorContinuation]
  have hden : z * 2 + 1 ≠ 0 := by
    intro h
    apply hz0
    linear_combination h / 2
  have hcancel :
      (z + 1 / 2) *
          (-(logDeriv zetaResidueUnit (z + 1 / 2) + 1) / (z + 1 / 2)) =
        -(logDeriv zetaResidueUnit (z + 1 / 2) + 1) := by
    field_simp [hz0, hden]
  rw [hcancel]
  ring

/-- Every zeta zero is a zero of the entire residue unit. -/
theorem zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero
    {rho : ℂ} (hzeta : riemannZeta rho = 0) :
    zetaResidueUnit rho = 0 := by
  have hrho : rho ≠ 1 := riemannZeta_zero_ne_one hzeta
  rw [zetaResidueUnit, Function.update_of_ne hrho, hzeta, mul_zero]

/-- The entire residue unit is not locally identically zero at any point. -/
theorem not_eventually_zetaResidueUnit_eq_zero (rho : ℂ) :
    ¬ ∀ᶠ z in 𝓝 rho, zetaResidueUnit z = 0 := by
  intro hevent
  let U : Set ℂ := Set.univ
  have hana : AnalyticOnNhd ℂ zetaResidueUnit U :=
    fun z _ => analyticAt_zetaResidueUnit z
  have heq : Set.EqOn zetaResidueUnit 0 U :=
    hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ rho) hevent
  have hone := heq (Set.mem_univ (1 : ℂ))
  rw [zetaResidueUnit_one] at hone
  norm_num at hone

/-- **C51 quantized source residue.** At every zeta zero `rho`, the Chebyshev boost current has
residue `-(rho-1/2)m`, where `m>=1` is the zero multiplicity of the entire residue unit. -/
theorem criticalChebyshevBoostCurrent_residue_of_riemannZeta_zero
    {rho : ℂ} (hzeta : riemannZeta rho = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto
        (fun z : ℂ =>
          (z - (rho - 1 / 2)) * criticalChebyshevBoostCurrent z)
        (𝓝[≠] (rho - 1 / 2))
        (𝓝 (-(rho - 1 / 2) * (m : ℂ))) := by
  have hana : AnalyticAt ℂ zetaResidueUnit rho := analyticAt_zetaResidueUnit rho
  have hnontrivial := not_eventually_zetaResidueUnit_eq_zero rho
  obtain ⟨m, g, hg, hg0, hfactor⟩ :=
    hana.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnontrivial
  have hfactor' : zetaResidueUnit =ᶠ[𝓝 rho]
      (fun z => (z - rho) ^ m • g z) := hfactor
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exfalso
      apply hg0
      have hvalue := hfactor'.eq_of_nhds
      rw [hm] at hvalue
      simpa [zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero hzeta] using hvalue.symm
    · exact hm
  have hresidue := logDeriv_residue_of_factorization hg hg0 hfactor'
  let z0 : ℂ := rho - 1 / 2
  have hshift : Tendsto (fun z : ℂ => z + 1 / 2) (𝓝[≠] z0) (𝓝[≠] rho) := by
    have h := sub_const_punctured_tendsto z0 (-1 / 2)
    have hcenter : z0 - (-1 / 2) = rho := by
      simp only [z0]
      ring
    rw [hcenter] at h
    convert h using 1
    funext z
    ring
  have hshifted : Tendsto
      (fun z : ℂ => (z - z0) * logDeriv zetaResidueUnit (z + 1 / 2))
      (𝓝[≠] z0) (𝓝 (m : ℂ)) := by
    refine (hresidue.comp hshift).congr (fun z => ?_)
    simp only [Function.comp_apply, z0]
    ring
  have hcenter : Tendsto (fun z : ℂ => -z) (𝓝[≠] z0) (𝓝 (-z0)) :=
    continuous_neg.tendsto z0 |>.mono_left nhdsWithin_le_nhds
  refine ⟨m, hm1, ?_⟩
  have hproduct := hcenter.mul hshifted
  convert hproduct using 1
  · funext z
    rw [criticalChebyshevBoostCurrent]
    simp only [z0]
    ring

/-- The real residue is exactly Route N's modular divisor charge. -/
theorem re_criticalChebyshevBoostCurrent_residue_eq_divisorCharge
    (m : ℕ) (rho : ℂ) :
    (-(rho - 1 / 2) * (m : ℂ)).re =
      HedenmalmQuantile.divisorCharge m rho :=
  HedenmalmQuantile.re_centeredLogDeriv_residue m rho

end

end RHTower
