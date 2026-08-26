import GaloisForLFunctions.RHTower.StaticChoiCarrierPurityCrowdingLaw
import GaloisForLFunctions.RHTower.StaticChoiForwardWeightedCrowdingLaw

/-!
# Static Choi carrier purity from microcanonical near-action mass

Two points on one static Choi orbit have the same uniform diagonal weight
profile.  Consequently their Gaussian pair purity is controlled by total
microcanonical near-action mass, rather than worst-neighbor spectral crowding.
Carrier covariance compression and arbitrary return removal preserve this
bound.  Circuit families therefore cost only occupied replica-carrier rank;
no circuit union and no target-dependent spectral invariant remain.
-/

open Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Every static spectral Choi vector induces the exact microcanonical
spectral weight, independently of time. -/
theorem directStaticChoiTargetWeight_staticSpectralChoiVector_eq_microcanonical
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (t : ℝ) :
    directStaticChoiTargetWeight d (staticSpectralChoiVector d t energy) =
      microcanonicalWeight (Fin d) := by
  funext i
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  unfold directStaticChoiTargetWeight microcanonicalWeight staticSpectralChoiVector
  rw [fullUniformPhaseChoiVector_apply]
  simp only [ite_true, norm_mul, fourier_apply, Circle.norm_coe, mul_one,
    Fintype.card_fin]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt]
  rw [← mul_inv, show Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) by
    nlinarith [Real.sq_sqrt hdR.le]]

/-- The near-action invariant of an orbit target is exactly the
microcanonical invariant of the spectrum. -/
theorem directStaticChoiTargetNearActionMass_staticSpectralChoiVector
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (t : ℝ)
    (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass
        (staticSpectralChoiVector d t energy) energy r δ =
      fidelityReplicaNearActionMass
        (microcanonicalWeight (Fin d)) energy r δ := by
  unfold directStaticChoiTargetNearActionMass
  rw [directStaticChoiTargetWeight_staticSpectralChoiVector_eq_microcanonical
    hd energy t]
  unfold fidelityReplicaNearActionMass
  simp_rw [replicaNearAction_neg_iff energy r δ]

/-- Same-orbit Gaussian pair purity depends on total microcanonical near-action
mass, never worst-neighbor crowding. -/
theorem integral_gaussianPair_staticChoi_fidelity_pow_le_weightedCrowding
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (r : ℕ) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    (∫ p : ℝ × ℝ, finitePureStateFidelity
        (staticSpectralChoiVector d (T * p.1) energy).ofLp
        (staticSpectralChoiVector d (T * p.2) energy).ofLp ^ r
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) ≤
      (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
        fidelityReplicaNearActionMass
          (microcanonicalWeight (Fin d)) energy r δ +
        Real.exp (-((T * δ) ^ 2) / 2) := by
  let f : ℝ × ℝ → ℝ := fun p => finitePureStateFidelity
    (staticSpectralChoiVector d (T * p.1) energy).ofLp
    (staticSpectralChoiVector d (T * p.2) energy).ofLp ^ r
  let B : ℝ :=
    (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
      fidelityReplicaNearActionMass
        (microcanonicalWeight (Fin d)) energy r δ +
      Real.exp (-((T * δ) ^ 2) / 2)
  have hf : Integrable f
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    integrable_gaussianPair_staticChoi_fidelity_pow hd energy T r
  have hslice : ∀ y : ℝ,
      (∫ x, f (x, y) ∂gaussianReal 0 1) ≤ B := by
    intro y
    have h := integral_gaussian_staticChoi_fidelity_pow_le_weightedCrowding
      hd hmax (staticSpectralChoiVector d (T * y) energy)
      (staticSpectralChoiVector_norm hd (T * y) energy) r hT hδ
    rw [directStaticChoiTargetNearActionMass_staticSpectralChoiVector
      hd energy (T * y) r δ] at h
    exact h
  rw [show (∫ p : ℝ × ℝ, finitePureStateFidelity
        (staticSpectralChoiVector d (T * p.1) energy).ofLp
        (staticSpectralChoiVector d (T * p.2) energy).ofLp ^ r
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) =
      ∫ p, f p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) by rfl]
  rw [integral_prod_symm f hf]
  calc
    (∫ y, ∫ x, f (x, y) ∂gaussianReal 0 1 ∂gaussianReal 0 1) ≤
        ∫ _y : ℝ, B ∂gaussianReal 0 1 := by
      apply integral_mono_ae hf.integral_prod_right (integrable_const B)
      exact Filter.Eventually.of_forall hslice
    _ = B := by simp
    _ = _ := rfl

/-- Return removal and arbitrary carrier compression preserve the stronger
microcanonical weighted near-action budget. -/
theorem returnExcisedReplicaCarrierIncidenceAction_staticChoi_le_weightedCrowding
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (r : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (Fin r → (Fin d × Fin d))))
    (returnSet : Set ℝ) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    returnExcisedReplicaCarrierIncidenceAction (gaussianReal 0 1) r S
        (fun x => (staticSpectralChoiVector d (T * x) energy).ofLp)
        returnSet ≤
      (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
        fidelityReplicaNearActionMass
          (microcanonicalWeight (Fin d)) energy r δ +
        Real.exp (-((T * δ) ^ 2) / 2) := by
  let f : ℝ × ℝ → ℝ := fun p => finitePureStateFidelity
    (staticSpectralChoiVector d (T * p.1) energy).ofLp
    (staticSpectralChoiVector d (T * p.2) energy).ofLp ^ r
  have hcompression :=
    returnExcisedReplicaCarrierIncidenceAction_le_fullReplicaPurity
      (gaussianReal 0 1) r S
      (fun x => (staticSpectralChoiVector d (T * x) energy).ofLp)
      returnSet
      (fun u => (Continuous.inner continuous_const
        (continuous_finitePureTensorPowerEuclidean_comp
          (fun x : ℝ => staticSpectralChoiVector d (T * x) energy)
          (continuous_staticSpectralChoiVector_scaled hd energy T))).aestronglyMeasurable)
      (fun u => integrable_sq_inner_staticChoiReplica
        hd energy T u returnSetᶜ)
  have hf : Integrable f
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    integrable_gaussianPair_staticChoi_fidelity_pow hd energy T r
  have hmeasure :
      ((gaussianReal 0 1).restrict returnSetᶜ).prod
          ((gaussianReal 0 1).restrict returnSetᶜ) ≤
        (gaussianReal 0 1).prod (gaussianReal 0 1) :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hrestricted :
      (∫ p, f p ∂(((gaussianReal 0 1).restrict returnSetᶜ).prod
        ((gaussianReal 0 1).restrict returnSetᶜ))) ≤
      ∫ p, f p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    apply integral_mono_measure hmeasure
    · exact Filter.Eventually.of_forall fun p =>
        pow_nonneg (by unfold finitePureStateFidelity; exact sq_nonneg _) r
    · exact hf
  exact hcompression.trans (hrestricted.trans
    (integral_gaussianPair_staticChoi_fidelity_pow_le_weightedCrowding
      hd hmax r hT hδ))

end RHTower
