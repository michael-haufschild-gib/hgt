import GaloisForLFunctions.RHTower.CompletedFluxIncidencePower
import GaloisForLFunctions.RHTower.PrimeArchPolarSeamRemoval

/-!
# Prime--arch polar all-order incidence-completion universality

The punctured prime--archimedean source at `s = 1` is the completed Xi seam flux.  Translating to
the local coordinate and multiplying its `m`th power by `x^m` gives exactly the existing completed
flux incidence-power germ.  Thus every positive incidence order has a canonical analytic fill,
vanishes at the polar center, and is the unique analytic completion of its source-built punctured
germ.

This is an all-order connector between polar-seam removal and the completed incidence hierarchy.
No zero-location hypothesis or numerical computation is used.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- The order-`m` prime--arch polar incidence source in the local coordinate at `s = 1`. -/
def primeArchPolarIncidenceSource (m : ℕ) (x : ℂ) : ℂ :=
  x ^ m *
    (infinitePrimeFlux (1 + x) - logDeriv archFactor (1 + x)) ^ m

/-- Every completed incidence power at the polar seam is the corresponding source-built
punctured germ. -/
theorem completedFluxIncidencePowerGermAt_one_eq_primeArchPolar_eventually
    (m : ℕ) :
    completedFluxIncidencePowerGermAt m 1 =ᶠ[𝓝[≠] (0 : ℂ)]
      primeArchPolarIncidenceSource m := by
  have hshift :
      Tendsto (fun x : ℂ => 1 + x) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h0 : Tendsto (fun x : ℂ => 1 + x) (𝓝 (0 : ℂ)) (𝓝 (1 + 0)) :=
        (continuous_const.add continuous_id).continuousAt
      simpa using h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
      intro h
      apply hx
      linear_combination h
  have hsource :=
    primeArchPolarFlux_eventuallyEq_seamFluxCochain_one.comp_tendsto hshift
  filter_upwards [self_mem_nhdsWithin, hsource] with x hx hsourcex
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [Function.comp_apply] at hsourcex
  rw [completedFluxIncidencePowerGermAt, completedFluxGermAt, if_neg hx0,
    primeArchPolarIncidenceSource, hsourcex, mul_pow]

/-- Every positive incidence order vanishes at the filled polar center. -/
theorem completedFluxIncidencePowerGermAt_one_zero
    {m : ℕ} (hm : m ≠ 0) :
    completedFluxIncidencePowerGermAt m 1 0 = 0 := by
  rw [completedFluxIncidencePowerGermAt_zero,
    analyticOrderAt_eq_zero.mpr
      (Or.inr (xi_ne_zero_of_one_le_re (by norm_num : (1 : ℝ) ≤ (1 : ℂ).re)))]
  simp [hm]

/-- The completed incidence germ is the unique analytic completion of the order-`m` punctured
prime--arch source. -/
theorem primeArchPolarIncidencePower_analyticCompletion_unique
    (m : ℕ) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0)
    (hsource :
      primeArchPolarIncidenceSource m =ᶠ[𝓝[≠] (0 : ℂ)] g) :
    g =ᶠ[𝓝 (0 : ℂ)] completedFluxIncidencePowerGermAt m 1 := by
  have hpunct :
      g =ᶠ[𝓝[≠] (0 : ℂ)] completedFluxIncidencePowerGermAt m 1 :=
    hsource.symm.trans
      (completedFluxIncidencePowerGermAt_one_eq_primeArchPolar_eventually m).symm
  exact
    (hg.frequently_eq_iff_eventually_eq
      (completedFluxIncidencePowerGermAt_analyticAt_zero m 1)).mp hpunct.frequently

/-- Complete all-order polar-incidence completion certificate. -/
structure PrimeArchPolarIncidencePowerCertificate (m : ℕ) : Prop where
  analytic :
    AnalyticAt ℂ (completedFluxIncidencePowerGermAt m 1) 0
  centerZero :
    completedFluxIncidencePowerGermAt m 1 0 = 0
  sourceGerm :
    completedFluxIncidencePowerGermAt m 1 =ᶠ[𝓝[≠] (0 : ℂ)]
      primeArchPolarIncidenceSource m
  unique :
    ∀ g : ℂ → ℂ, AnalyticAt ℂ g 0 →
      primeArchPolarIncidenceSource m =ᶠ[𝓝[≠] (0 : ℂ)] g →
        g =ᶠ[𝓝 (0 : ℂ)] completedFluxIncidencePowerGermAt m 1

/-- **Prime--arch polar all-order incidence-completion universality law.**  At every positive
incidence order, the translated prime--arch source has one canonical analytic completion: the
completed Xi incidence-power germ.  Its filled polar-center value is forced to zero. -/
theorem primeArchPolar_allOrderIncidenceCompletionUniversality
    {m : ℕ} (hm : m ≠ 0) :
    PrimeArchPolarIncidencePowerCertificate m where
  analytic :=
    completedFluxIncidencePowerGermAt_analyticAt_zero m 1
  centerZero :=
    completedFluxIncidencePowerGermAt_one_zero hm
  sourceGerm :=
    completedFluxIncidencePowerGermAt_one_eq_primeArchPolar_eventually m
  unique :=
    fun _ hg hsource =>
      primeArchPolarIncidencePower_analyticCompletion_unique m hg hsource

end

end RHTower
