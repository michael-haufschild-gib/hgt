import GaloisForLFunctions.RHTower.ThetaCuspHawkingPreDivisorFiniteEnergyBoundedKreinNoGo

/-!
# HB pre-divisor finite graph-energy metric no-go

The exact source-faithful HB pre-divisor kernel cannot have a finite-energy two-leg Hilbert
factorization.  This removes boundedness entirely: the second leg may be the image of the first
under an arbitrary unbounded, nonclosable, non-self-adjoint, or partially defined metric action.
Only its values on the feature field enter.

The diagonal identity is enough.  If

`S(x) = inner (Phi x) (Psi x)`,

then the Hilbert bound and Young's inequality give

`S(x) <= norm (Phi x) * norm (Psi x) <= norm (Phi x)^2 + norm (Psi x)^2`.

The corpus hard-edge theorem says that `S` is not integrable because `x^-2 <= S(x)` on
`(0,1/2)`.  Consequently the two square energies cannot both be finite.  In particular, every
exact unbounded metric realization with finite feature energy has infinite metric-image energy.

**Route killed.**  Finite graph-energy unbounded/rigged metric compensation cannot supply the HB
opposite-sign step in

`pre-divisor cancellation kernel -> Ward extinction -> RH`.

The sharp survivor is infinite graph energy in at least one leg.  Other escapes must abandon a
pointwise Hilbert pairing through renormalization, distributions, domain exclusion, support/sheet
change, or a non-scalar landing.

`[NEW] [HB] [ROUTE KILL] [UNBOUNDED METRIC] [FINITE GRAPH ENERGY] [LEAN-PROVED]`
-/

open Complex Set MeasureTheory

namespace RHTower

noncomputable section

/-- No two Hilbert-valued legs with finite square energy can realize even the diagonal of the exact
HB pre-divisor kernel.  No relation between the two legs is assumed. -/
theorem not_integrableOn_both_normSq_of_d4PreDivisorDiagonalPairing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Phi Psi : ℝ → E)
    (hdiag : ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
      inner ℂ (Phi x) (Psi x) =
        (d4PreDivisorOpticalCancellationSusceptibility x : ℂ)) :
    ¬ (IntegrableOn (fun x : ℝ => ‖Phi x‖ ^ 2) (Ioo 0 (1 / 2)) ∧
      IntegrableOn (fun x : ℝ => ‖Psi x‖ ^ 2) (Ioo 0 (1 / 2))) := by
  rintro ⟨hPhi, hPsi⟩
  apply not_integrableOn_d4PreDivisorOpticalCancellationSusceptibility
  have hdom : IntegrableOn
      (fun x : ℝ => ‖Phi x‖ ^ 2 + ‖Psi x‖ ^ 2) (Ioo 0 (1 / 2)) :=
    hPhi.add hPsi
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
    rw [Real.norm_of_nonneg hSnonneg]
    calc
      d4PreDivisorOpticalCancellationSusceptibility x =
          ‖(d4PreDivisorOpticalCancellationSusceptibility x : ℂ)‖ := by
        simpa using (Real.norm_of_nonneg hSnonneg).symm
      _ = ‖inner ℂ (Phi x) (Psi x)‖ := by rw [hdiag x hx]
      _ ≤ ‖Phi x‖ * ‖Psi x‖ := norm_inner_le_norm _ _
      _ ≤ ‖Phi x‖ ^ 2 + ‖Psi x‖ ^ 2 := by
        nlinarith [sq_nonneg (‖Phi x‖ - ‖Psi x‖)]

/-- Sharp energy-allocation survivor: once the feature leg has finite energy, every exact metric
image leg necessarily has infinite energy. -/
theorem not_integrableOn_metricImage_normSq_of_integrableOn_feature_d4PreDivisorDiagonalPairing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Phi Psi : ℝ → E)
    (hdiag : ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
      inner ℂ (Phi x) (Psi x) =
        (d4PreDivisorOpticalCancellationSusceptibility x : ℂ))
    (hPhi : IntegrableOn (fun x : ℝ => ‖Phi x‖ ^ 2) (Ioo 0 (1 / 2))) :
    ¬ IntegrableOn (fun x : ℝ => ‖Psi x‖ ^ 2) (Ioo 0 (1 / 2)) := by
  intro hPsi
  exact not_integrableOn_both_normSq_of_d4PreDivisorDiagonalPairing
    Phi Psi hdiag ⟨hPhi, hPsi⟩

/-- Full-kernel corollary: an exact two-leg factorization cannot have finite energy in both legs. -/
theorem not_integrableOn_both_normSq_of_twoLeg_d4PreDivisorGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Phi Psi : ℝ → E)
    (hgram : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), ∀ y ∈ Ioo (0 : ℝ) (1 / 2),
      inner ℂ (Phi x) (Psi y) =
        d4PreDivisorOpticalCancellationPolarizedKernel x y) :
    ¬ (IntegrableOn (fun x : ℝ => ‖Phi x‖ ^ 2) (Ioo 0 (1 / 2)) ∧
      IntegrableOn (fun x : ℝ => ‖Psi x‖ ^ 2) (Ioo 0 (1 / 2))) := by
  apply not_integrableOn_both_normSq_of_d4PreDivisorDiagonalPairing Phi Psi
  intro x hx
  have h := hgram x hx x hx
  rw [d4PreDivisorOpticalCancellationPolarizedKernel,
    show ((x + x) / 2 : ℝ) = x by ring,
    d4PreDivisorOpticalCancellationHolomorphicContinuation_ofReal] at h
  exact h

/-- Closed route class: no pointwise two-leg Hilbert pairing realizes the exact HB pre-divisor
kernel with finite energy in both legs. -/
def D4HBPreDivisorFiniteGraphEnergyMetricRouteKilled : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      (Phi Psi : ℝ → E),
    (∀ x ∈ Ioo (0 : ℝ) (1 / 2), ∀ y ∈ Ioo (0 : ℝ) (1 / 2),
      inner ℂ (Phi x) (Psi y) =
        d4PreDivisorOpticalCancellationPolarizedKernel x y) →
      ¬ (IntegrableOn (fun x : ℝ => ‖Phi x‖ ^ 2) (Ioo 0 (1 / 2)) ∧
        IntegrableOn (fun x : ℝ => ‖Psi x‖ ^ 2) (Ioo 0 (1 / 2)))

/-- Premise-free certificate killing finite graph-energy unbounded-metric HB compensation. -/
theorem d4HBPreDivisorFiniteGraphEnergyMetricRouteKilled :
    D4HBPreDivisorFiniteGraphEnergyMetricRouteKilled := by
  intro E _ _ Phi Psi hgram
  exact not_integrableOn_both_normSq_of_twoLeg_d4PreDivisorGram Phi Psi hgram

end

end RHTower
