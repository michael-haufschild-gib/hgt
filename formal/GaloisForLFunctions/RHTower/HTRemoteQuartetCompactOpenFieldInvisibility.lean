import GaloisForLFunctions.RHTower.RemotePassportSurgery
import GaloisForLFunctions.RHTower.HTWeilCompactDetectorNearRadicalAlternative

/-!
# HT remote-quartet compact-open field invisibility

Closed card package: an arbitrary finite Hermite passport survives symmetry-complete off-critical
quartet insertion inside one exact order-one hypertranscendental differential-translation field.
Every compact-open derivative, finite strict continuous probe, finite Li prefix, and finite
continuous decaying inverse-root test survives cofinally.  The pure-quartet Weil package is
re-exported at the end.
-/

open Complex Set Polynomial Filter Topology
open scoped Differential

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complete arbitrary-passport package proved by the remote surgery construction. -/
structure HTRemoteQuartetPackage {ι : Type*} [Fintype ι]
    (alpha a : ℝ) (M : ι → ℕ) (nodes : ι → ℂ) : Prop where
  base_zero_re : ∀ s : ℂ, liReflectedGammaCarrier alpha s = 0 → s.re = 1 / 2
  quartet_mem_criticalStrip : ∀ T : ℝ,
    (0 < (remotePassportTarget a T).re ∧ (remotePassportTarget a T).re < 1) ∧
      (0 < (1 - remotePassportTarget a T).re ∧
        (1 - remotePassportTarget a T).re < 1) ∧
      (0 < ((starRingEnd ℂ) (remotePassportTarget a T)).re ∧
        ((starRingEnd ℂ) (remotePassportTarget a T)).re < 1) ∧
      (0 < (1 - (starRingEnd ℂ) (remotePassportTarget a T)).re ∧
        (1 - (starRingEnd ℂ) (remotePassportTarget a T)).re < 1)
  exact_order_one : ∀ T : ℝ,
    HasExactEntireOrderOne (remotePassportGaugedCarrier alpha M nodes a T)
  hypertranscendental : ∀ T : ℝ,
    Hypertranscendental (remotePassportGaugedCarrier alpha M nodes a T)
  scalar_symmetries : ∀ (T : ℝ) (s : ℂ),
    remotePassportGaugedCarrier alpha M nodes a T (1 - s) =
        remotePassportGaugedCarrier alpha M nodes a T s ∧
      remotePassportGaugedCarrier alpha M nodes a T ((starRingEnd ℂ) s) =
        (starRingEnd ℂ) (remotePassportGaugedCarrier alpha M nodes a T s)
  passport_jets : ∀ (T : ℝ) (i : ι) (n : ℕ), n < M i →
    iteratedDeriv n (remotePassportGaugedCarrier alpha M nodes a T)
        ((1 / 2 : ℂ) + nodes i) =
      iteratedDeriv n (liReflectedGammaCarrier alpha) ((1 / 2 : ℂ) + nodes i)
  same_complete_translated_differential_field : ∀ T : ℝ,
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    letI : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncDifferentialAlgebra
    IntermediateField.adjoin (RatFunc ℂ)
        (Set.range fun p : ℂ × ℕ => differentialJet p.2
          (remotePassportGaugedCarrierTranslateFamily alpha M nodes a T p.1)) =
      IntermediateField.adjoin (RatFunc ℂ)
        (Set.range fun p : ℂ × ℕ => differentialJet p.2
          (liReflectedGammaCarrierTranslateFamily alpha p.1))
  compact_open_convergence :
    TendstoLocallyUniformly (remotePassportGaugedCarrier alpha M nodes a)
      (liReflectedGammaCarrier alpha) atTop
  every_derivative_compact_open_convergence : ∀ j : ℕ,
    TendstoLocallyUniformly
      (fun T => iteratedDeriv j (remotePassportGaugedCarrier alpha M nodes a T))
      (iteratedDeriv j (liReflectedGammaCarrier alpha)) atTop
  quartet_inserted_cofinally :
    ∀ᶠ T : ℝ in atTop,
      0 < T ∧
      remotePassportGaugedCarrier alpha M nodes a T (remotePassportTarget a T) = 0 ∧
      remotePassportGaugedCarrier alpha M nodes a T (1 - remotePassportTarget a T) = 0 ∧
      remotePassportGaugedCarrier alpha M nodes a T
        ((starRingEnd ℂ) (remotePassportTarget a T)) = 0 ∧
      remotePassportGaugedCarrier alpha M nodes a T
        (1 - (starRingEnd ℂ) (remotePassportTarget a T)) = 0
  gauge_zeros_escape_compacts : ∀ (K : Set ℂ), IsCompact K →
    ∀ᶠ T : ℝ in atTop, ∀ s ∈ K, remotePassportGauge M nodes a T s ≠ 0
  finite_continuous_selectors : ∀ (κ : Type*) [Finite κ]
      (Phi : κ → DeningerCompactOpenEntire → ℝ),
    (∀ k, Continuous (Phi k)) →
    (∀ k, 0 < Phi k (liReflectedGammaCarrierCompactOpen alpha)) →
    ∀ᶠ T : ℝ in atTop, ∀ k,
      0 < Phi k (remotePassportGaugedCarrierCompactOpen alpha M nodes a T)
  finite_Li_prefixes : ∀ N : ℕ,
    ∀ᶠ T : ℝ in atTop, ∀ n : Fin N,
      0 < remotePassportGaugedCarrierLiCoefficient alpha (n + 1) M nodes a T
  finite_decaying_inverse_root_tests : ∀ (g : ℂ → ℂ),
    ContinuousAt g 0 → g 0 = 0 →
    Tendsto (fun T => polynomialInverseRootSum g
      (remotePassportGaugePolynomial M nodes a T)) atTop (nhds 0)

/-- Closed arbitrary-passport theorem, with every mathematical side condition explicit and proved
from the reflected-Gamma carrier plus the real-even two-coefficient surgery. -/
theorem htRemoteQuartetCompactOpenFieldInvisibility :
    ∀ {ι : Type*} [Fintype ι]
      (alpha a : ℝ) (M : ι → ℕ) (nodes : ι → ℂ),
      0 < alpha → 0 < |a| → |a| < 1 / 2 →
      (∀ k : ℤ, (2 * alpha - 1 : ℂ) ≠ (k : ℂ)) →
      HTRemoteQuartetPackage alpha a M nodes := by
  intro ι _ alpha a M nodes halpha haPos haStrip hsep
  have ha : a ≠ 0 := (abs_pos.mp haPos)
  refine
    { base_zero_re := ?_
      quartet_mem_criticalStrip := ?_
      exact_order_one := ?_
      hypertranscendental := ?_
      scalar_symmetries := ?_
      passport_jets := ?_
      same_complete_translated_differential_field := ?_
      compact_open_convergence := ?_
      every_derivative_compact_open_convergence := ?_
      quartet_inserted_cofinally := ?_
      gauge_zeros_escape_compacts := ?_
      finite_continuous_selectors := ?_
      finite_Li_prefixes := ?_
      finite_decaying_inverse_root_tests := ?_ }
  · intro s hs
    exact liReflectedGammaCarrier_zero_re_eq_half hs
  · intro T
    exact remotePassportTarget_quartet_mem_criticalStrip haStrip
  · intro T
    exact remotePassportGaugedCarrier_hasExactEntireOrderOne halpha M nodes a T
  · intro T
    exact remotePassportGaugedCarrier_hypertranscendental_of_two_mul_sub_one
      M nodes a T hsep
  · intro T s
    exact ⟨remotePassportGaugedCarrier_one_sub alpha M nodes a T s,
      remotePassportGaugedCarrier_conj alpha M nodes a T s⟩
  · intro T i n hn
    exact remotePassportGaugedCarrier_iteratedDeriv_eq_of_lt alpha M nodes a T i hn
  · intro T
    exact remotePassportGaugedCarrierTranslateFamily_allJets_adjoin_eq
      alpha M nodes a T
  · exact remotePassportGaugedCarrier_tendstoLocallyUniformly alpha M nodes ha
  · intro j
    exact remotePassportGaugedCarrier_iteratedDeriv_tendstoLocallyUniformly
      alpha M nodes ha j
  · exact eventually_remotePassportGaugedCarrier_quartet_zero alpha M nodes ha
  · intro K hK
    exact eventually_remotePassportGauge_ne_zero_on_compact M nodes ha K hK
  · intro κ _ Phi hPhi hpos
    exact eventually_remotePassportGaugedCarrier_finite_continuous_probes_pos
      alpha M nodes ha Phi hPhi hpos
  · intro N
    exact eventually_remotePassportGaugedCarrierLiCoefficient_pos_prefix
      halpha N M nodes ha
  · intro g hg hg0
    exact remotePassportPolynomialInverseRootSum_tendsto_zero M nodes ha g hg hg0

end

end RHTower
