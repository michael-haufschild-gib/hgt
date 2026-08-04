import GaloisForLFunctions.RHTower.PrimeDepthBVWoldCofinalEquicontinuity
import GaloisForLFunctions.HTGeometry.BarrelledSeminormBound

/-!
# Barrelled-source selector for cofinal Wold transport

The missing depth-uniform constant need not be estimated directly.  On a barrelled source space,
Banach--Steinhaus produces it from pointwise boundedness of the complete family of cofinal
readouts.  If a null source orbit is read by those functionals as the exact source-normal inverse
of the deep Wold anomaly, the returned nonzero depth-one coordinate is impossible.

This module turns the completion issue into a precise producer interface.  Algebraic finite-source
spaces do not qualify merely by density: pointwise boundedness must hold on the completed
barrelled source.
-/

namespace RHTower

noncomputable section

open Filter

/-- Banach--Steinhaus null-orbit principle.  A pointwise bounded family of continuous functionals
on a barrelled normed space cannot return one fixed nonzero scalar along a null diagonal orbit. -/
theorem eq_zero_of_barrelled_pointwiseBounded_cofinalReadout
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [BarrelledSpace ℝ E]
    (F : ℕ → E →L[ℝ] ℝ) (x : ℕ → E)
    (hx : Tendsto x atTop (nhds 0))
    (hpointwise : ∀ y : E, BddAbove (Set.range fun n : ℕ => ‖F n y‖))
    (a : ℝ) (hreadout : ∀ n : ℕ, F n (x n) = a) :
    a = 0 := by
  let p : Fin 1 → Seminorm ℝ E := fun _ => normSeminorm ℝ E
  have hp : WithSeminorms p := by
    simpa [p] using (norm_withSeminorms ℝ E)
  obtain ⟨s, C, huniform⟩ :=
    GaloisForLFunctions.HTGeometry.exists_seminorm_bound_of_bddAbove
      hp F hpointwise
  have hseminorm : s.sup p ≤ normSeminorm ℝ E := by
    apply Finset.sup_le
    intro i hi
    rfl
  have hbound : ∀ n : ℕ, ‖F n (x n)‖ ≤ (C : ℝ) * ‖x n‖ := by
    intro n
    refine (huniform n (x n)).trans ?_
    apply mul_le_mul_of_nonneg_left
    · simpa [p] using hseminorm (x n)
    · exact NNReal.coe_nonneg C
  have hnorm : Tendsto (fun n : ℕ => ‖x n‖) atTop (nhds 0) := by
    simpa using (continuous_norm.tendsto 0).comp hx
  have hright : Tendsto (fun n : ℕ => (C : ℝ) * ‖x n‖) atTop (nhds 0) := by
    simpa using hnorm.const_mul (C : ℝ)
  have hle : |a| ≤ 0 := by
    apply le_of_tendsto hright
    filter_upwards with n
    rw [← hreadout n]
    simpa [Real.norm_eq_abs] using hbound n
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg a))

/-- Distinguished prime used only to turn a retained local coordinate into scalar rigidity. -/
def primeDepthBVWoldPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- Concrete source-side obligation.  It packages a completed barrelled source, a null cofinal
orbit, pointwise bounded continuous readouts on the whole completion, and the exact physical
source-normal Wold matrix coefficient. -/
structure PrimeDepthBVWoldBarrelledSourceCertificate
    (sourceDepth : ℕ) (a : ℝ) : Type 1 where
  E : Type
  [normedAddCommGroup_E : NormedAddCommGroup E]
  [normedSpace_E : NormedSpace ℝ E]
  [barrelledSpace_E : BarrelledSpace ℝ E]
  readout : ℕ → E →L[ℝ] ℝ
  orbit : ℕ → E
  orbit_tendsto_zero : Tendsto orbit atTop (nhds 0)
  readout_pointwise_bounded :
    ∀ y : E, BddAbove (Set.range fun n : ℕ => ‖readout n y‖)
  physical_matrix_coefficient : ∀ n : ℕ,
    readout n (orbit n) =
      primeDepthBVWoldSourceNormalCofinalCenteredTransport sourceDepth (n + 1)
        (fun q => a * woldCoeff (n + 2) q) primeDepthBVWoldPrimeTwo

attribute [instance]
  PrimeDepthBVWoldBarrelledSourceCertificate.normedAddCommGroup_E
  PrimeDepthBVWoldBarrelledSourceCertificate.normedSpace_E
  PrimeDepthBVWoldBarrelledSourceCertificate.barrelledSpace_E

/-- Every honest completed-source certificate kills the centered Wold rate. -/
theorem PrimeDepthBVWoldBarrelledSourceCertificate.centeredRate_eq_zero
    {sourceDepth : ℕ} {a : ℝ}
    (cert : PrimeDepthBVWoldBarrelledSourceCertificate sourceDepth a) :
    a = 0 := by
  apply eq_zero_of_barrelled_pointwiseBounded_cofinalReadout
    cert.readout cert.orbit cert.orbit_tendsto_zero
    cert.readout_pointwise_bounded (a * woldCoeff 1 primeDepthBVWoldPrimeTwo)
  intro n
  rw [cert.physical_matrix_coefficient]
  exact sourceNormalCofinalCenteredTransport_from_deep
    a sourceDepth n primeDepthBVWoldPrimeTwo

/-- Xi-labelled completed-source certificate. -/
abbrev PrimeDepthBVWoldXiBarrelledSourceCertificate
    (sourceDepth : ℕ) (rho : XiDivisorSupport) : Type 1 :=
  PrimeDepthBVWoldBarrelledSourceCertificate sourceDepth
    (primeDepthBVWoldXiCenteredRate rho)

/-- One Xi-labelled source certificate places its divisor on the critical line. -/
theorem re_eq_half_of_barrelledSourceCertificate
    {sourceDepth : ℕ} {rho : XiDivisorSupport}
    (cert : PrimeDepthBVWoldXiBarrelledSourceCertificate sourceDepth rho) :
    (rho : ℂ).re = 1 / 2 := by
  exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).1 cert.centeredRate_eq_zero

/-- Source-only global producer statement.  Unlike an RH-equivalent summability definition, its
fields name the exact completion, boundedness, convergence, and coefficient obligations. -/
def PrimeDepthBVWoldXiGlobalBarrelledSourceProducer (sourceDepth : ℕ) : Prop :=
  ∀ rho : XiDivisorSupport,
    Nonempty (PrimeDepthBVWoldXiBarrelledSourceCertificate sourceDepth rho)

/-- A global completed barrelled-source producer proves RH unconditionally. -/
theorem riemannHypothesis_of_globalBarrelledSourceProducer
    (sourceDepth : ℕ)
    (hsource : PrimeDepthBVWoldXiGlobalBarrelledSourceProducer sourceDepth) :
    RiemannHypothesis := by
  apply rh_iff_xi_ne_zero_right.mpr
  intro z hz hzero
  let rho : XiDivisorSupport :=
    ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hline : z.re = 1 / 2 :=
    re_eq_half_of_barrelledSourceCertificate (hsource rho).some
  linarith [mem_rightHalf.mp hz]

end

end RHTower
