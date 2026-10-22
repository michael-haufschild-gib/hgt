import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingPreDivisorFiniteEnergyInfiniteRankGramNoGo

/-!
# HB pre-divisor bounded-Krein finite-energy no-go

The exact source-faithful HB compensation kernel cannot be realized by a finite-energy Hilbert
feature field after inserting any bounded operator metric.  This covers every bounded Krein
fundamental symmetry, without using self-adjointness, involutivity, finite negative index, or any
dimension bound.

The proof is diagonal and source-exact.  The corpus hard-edge law gives

`x⁻² ≤ S(x) = K(x,x)` on `(0,1/2)`.

If `K(x,y) = inner (Phi x) (J (Phi y))` for bounded `J`, Cauchy--Schwarz gives

`S(x) ≤ ‖J‖ * ‖Phi x‖²`.

Thus finite feature energy would make `S` integrable, contradicting its exact inverse-square
hard-edge divergence.  Indefinite signature therefore does not rescue finite-energy HB
compensation.  Survivors must use an unbounded/rigged metric, infinite hard-edge feature energy,
renormalized or distributional pairing, domain exclusion, support/sheet change, or a non-scalar
landing.

`[NEW] [HB] [ROUTE KILL] [BOUNDED KREIN] [FINITE ENERGY] [LEAN-PROVED]`
-/

open Complex Set MeasureTheory

namespace RHTower

noncomputable section

/-- Any bounded-operator-metric realization of the exact HB kernel has infinite feature energy.
No positivity, self-adjointness, involution, index, or dimension premise is needed. -/
theorem not_integrableOn_normSq_of_boundedOperatorMetric_d4PreDivisorGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (J : E →L[ℂ] E) (Phi : ℝ → E)
    (hgram : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), ∀ y ∈ Ioo (0 : ℝ) (1 / 2),
      inner ℂ (Phi x) (J (Phi y)) =
        d4PreDivisorOpticalCancellationPolarizedKernel x y) :
    ¬ IntegrableOn (fun x : ℝ => ‖Phi x‖ ^ 2) (Ioo 0 (1 / 2)) := by
  intro henergy
  apply not_integrableOn_d4PreDivisorOpticalCancellationSusceptibility
  have hdom : IntegrableOn
      (fun x : ℝ => ‖J‖ * ‖Phi x‖ ^ 2) (Ioo 0 (1 / 2)) :=
    henergy.const_mul ‖J‖
  refine Integrable.mono' hdom ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold d4PreDivisorOpticalCancellationSusceptibility
      d4PreDivisorEventHorizonThirdMassReflectionSusceptibility
      d4PreDivisorThetaMirrorAIMEDenominator
      d4PreDivisorHorizonAngularShift
      d4PreDivisorReflectedHorizonAngularShift
      d4EventHorizonThirdMassParityCrossNumerator
    fun_prop
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    have hlower :=
      d4PreDivisorOpticalCancellationSusceptibility_rpow_neg_two_le hx
    have hSnonneg : 0 ≤ d4PreDivisorOpticalCancellationSusceptibility x :=
      le_trans (Real.rpow_nonneg hx.1.le _) hlower
    have hdiag := hgram x hx x hx
    rw [d4PreDivisorOpticalCancellationPolarizedKernel,
      show ((x + x) / 2 : ℝ) = x by ring,
      d4PreDivisorOpticalCancellationHolomorphicContinuation_ofReal] at hdiag
    rw [Real.norm_of_nonneg hSnonneg]
    calc
      d4PreDivisorOpticalCancellationSusceptibility x =
          ‖(d4PreDivisorOpticalCancellationSusceptibility x : ℂ)‖ := by
        simpa using (Real.norm_of_nonneg hSnonneg).symm
      _ = ‖inner ℂ (Phi x) (J (Phi x))‖ := by rw [hdiag]
      _ ≤ ‖Phi x‖ * ‖J (Phi x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖Phi x‖ * (‖J‖ * ‖Phi x‖) :=
        mul_le_mul_of_nonneg_left (J.le_opNorm _) (norm_nonneg _)
      _ = ‖J‖ * ‖Phi x‖ ^ 2 := by ring

/-- Closed route class: no bounded indefinite/Krein metric realizes the exact source-faithful HB
pre-divisor kernel with finite Hilbert feature energy on the physical hard-edge square. -/
def D4HBPreDivisorFiniteEnergyBoundedKreinRouteKilled : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      (J : E →L[ℂ] E) (Phi : ℝ → E),
    (∀ x ∈ Ioo (0 : ℝ) (1 / 2), ∀ y ∈ Ioo (0 : ℝ) (1 / 2),
      inner ℂ (Phi x) (J (Phi y)) =
        d4PreDivisorOpticalCancellationPolarizedKernel x y) →
      ¬ IntegrableOn (fun x : ℝ => ‖Phi x‖ ^ 2) (Ioo 0 (1 / 2))

/-- Premise-free certificate killing bounded-Krein finite-energy HB pre-divisor compensation. -/
theorem d4HBPreDivisorFiniteEnergyBoundedKreinRouteKilled :
    D4HBPreDivisorFiniteEnergyBoundedKreinRouteKilled := by
  intro E _ _ J Phi hgram
  exact not_integrableOn_normSq_of_boundedOperatorMetric_d4PreDivisorGram J Phi hgram

end

end RHTower
