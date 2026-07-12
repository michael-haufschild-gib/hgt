import GaloisForLFunctions.RHTower.XiRelativeResolventFlux

/-!
# Removable prime--archimedean polar seam

The source-built difference `-ζ'/ζ - (archFactor)'/archFactor` is represented by two singular
terms at `s = 1`, although their completed sum has a removable singularity.  This file proves the
missing punctured-germ statement: away from the centre of a sufficiently small punctured
neighbourhood, the source difference is the completed seam flux `-ξ'/ξ`; that flux is analytic at
`1` and is the unique analytic completion of the source germ.

No positivity, zero-location statement, or Riemann-hypothesis premise is used.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- The completed seam flux is analytic at the removable polar seam `s = 1`. -/
theorem analyticAt_seamFluxCochain_one :
    AnalyticAt ℂ seamFluxCochain 1 := by
  have hxi : AnalyticAt ℂ xi 1 :=
    (xi_analyticOnNhd Set.univ) 1 (Set.mem_univ 1)
  have hxi0 : xi (1 : ℂ) ≠ 0 := xi_ne_zero_of_one_le_re (by norm_num)
  unfold seamFluxCochain logDeriv
  change AnalyticAt ℂ (fun s => -(deriv xi s / xi s)) 1
  exact (hxi.deriv.div hxi hxi0).neg

/-- On a punctured neighbourhood of `s = 1`, the continued prime--archimedean source difference
is exactly the completed seam flux.  Thus the cancellation of the two apparent polar terms is a
germ identity, not a value assigned only at the centre. -/
theorem primeArchPolarFlux_eventuallyEq_seamFluxCochain_one :
    (fun s : ℂ => infinitePrimeFlux s - logDeriv archFactor s) =ᶠ[𝓝[≠] (1 : ℂ)]
      seamFluxCochain := by
  have hre : ∀ᶠ s : ℂ in 𝓝 (1 : ℂ), 0 < s.re := by
    change ∀ᶠ s : ℂ in 𝓝 (1 : ℂ), s.re ∈ Set.Ioi 0
    exact Complex.continuous_re.continuousAt
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < (1 : ℂ).re))
  have hxiAt : AnalyticAt ℂ xi 1 :=
    (xi_analyticOnNhd Set.univ) 1 (Set.mem_univ 1)
  have hxi0 : xi (1 : ℂ) ≠ 0 := xi_ne_zero_of_one_le_re (by norm_num)
  have hxine : ∀ᶠ s : ℂ in 𝓝 (1 : ℂ), xi s ≠ 0 :=
    hxiAt.continuousAt.eventually_ne hxi0
  filter_upwards [hre.filter_mono inf_le_left, hxine.filter_mono inf_le_left,
    self_mem_nhdsWithin] with s hspos hxis hs1mem
  have hs1 : s ≠ 1 := by simpa using hs1mem
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hspos
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hspos
  have hzeta : riemannZeta s ≠ 0 := by
    intro hz
    apply hxis
    rw [xi_eq_archFactor_mul_zeta hs0 hs1 hG, hz, mul_zero]
  exact (seamFluxCochain_eq_continuedPrime_add_archimedean hspos hs1 hzeta).symm

/-- The punctured prime--archimedean source difference has an analytic completion at `s = 1`. -/
theorem exists_primeArchPolarFlux_analyticCompletion_one :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧
      (fun s : ℂ => infinitePrimeFlux s - logDeriv archFactor s) =ᶠ[𝓝[≠] (1 : ℂ)] g := by
  exact ⟨seamFluxCochain, analyticAt_seamFluxCochain_one,
    primeArchPolarFlux_eventuallyEq_seamFluxCochain_one⟩

/-- **Uniqueness of polar-seam removal.** Every analytic completion of the punctured
prime--archimedean source germ agrees locally with the completed seam flux. -/
theorem primeArchPolarFlux_analyticCompletion_unique_one
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 1)
    (hsource :
      (fun s : ℂ => infinitePrimeFlux s - logDeriv archFactor s) =ᶠ[𝓝[≠] (1 : ℂ)] g) :
    g =ᶠ[𝓝 (1 : ℂ)] seamFluxCochain := by
  have hpunct : g =ᶠ[𝓝[≠] (1 : ℂ)] seamFluxCochain :=
    hsource.symm.trans primeArchPolarFlux_eventuallyEq_seamFluxCochain_one
  have hfreq : ∃ᶠ s : ℂ in 𝓝[≠] (1 : ℂ), g s = seamFluxCochain s :=
    hpunct.frequently
  exact (hg.frequently_eq_iff_eventually_eq analyticAt_seamFluxCochain_one).mp hfreq

end

end RHTower
