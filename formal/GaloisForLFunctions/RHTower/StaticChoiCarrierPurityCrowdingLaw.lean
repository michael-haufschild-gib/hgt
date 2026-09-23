import GaloisForLFunctions.RHTower.ReplicaCarrierCompressionPurityLaw
import GaloisForLFunctions.RHTower.StaticChoiOptimalDesignFirstReturnLaw

/-!
# Static Choi carrier action from global replica purity

For static spectral Choi evolution, condition one Gaussian time on the other.
The remaining integral is the uniform one-target spectral moment.  Combining
this observation with covariance-compression dominance bounds every
return-excised carrier action by

`r! * d⁻ʳ + crowdingDegree * r! * d⁻ʳ + exp (-(T*δ)^(2 : ℕ)/2)`.

Bound is independent of target labels, target geometry, and carrier
orientation.  It therefore applies unchanged to complete continuous circuit
classes; their only cost is sharp carrier rank in coarea inequality.
-/

open Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem integrable_gaussianPair_staticChoi_fidelity_pow
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (T : ℝ) (r : ℕ) :
    Integrable
      (fun p : ℝ × ℝ => finitePureStateFidelity
        (staticSpectralChoiVector d (T * p.1) energy).ofLp
        (staticSpectralChoiVector d (T * p.2) energy).ofLp ^ r)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let psi : ℝ → EuclideanSpace ℂ (Fin d × Fin d) :=
    fun x => staticSpectralChoiVector d (T * x) energy
  have hcpsi : Continuous psi :=
    continuous_staticSpectralChoiVector_scaled hd energy T
  have hcinner : Continuous (fun p : ℝ × ℝ =>
      inner ℂ (psi p.2) (psi p.1)) :=
    (hcpsi.comp continuous_snd).inner (hcpsi.comp continuous_fst)
  have hc : Continuous (fun p : ℝ × ℝ => finitePureStateFidelity
      (psi p.1).ofLp (psi p.2).ofLp ^ r) := by
    simp_rw [finitePureStateFidelity_eq_norm_inner_sq]
    simp only [WithLp.toLp_ofLp]
    exact (hcinner.norm.pow 2).pow r
  apply Integrable.of_bound hc.aestronglyMeasurable 1
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sq_nonneg _) r)]
  have hinner : ‖inner ℂ (psi p.2) (psi p.1)‖ ≤ 1 := by
    calc
      ‖inner ℂ (psi p.2) (psi p.1)‖ ≤ ‖psi p.2‖ * ‖psi p.1‖ :=
        norm_inner_le_norm _ _
      _ = 1 := by
        rw [staticSpectralChoiVector_norm hd,
          staticSpectralChoiVector_norm hd, one_mul]
  have hsquare : ‖inner ℂ (psi p.2) (psi p.1)‖ ^ (2 : ℕ) ≤ 1 := by
    nlinarith [norm_nonneg (inner ℂ (psi p.2) (psi p.1))]
  simp only [finitePureStateFidelity_eq_norm_inner_sq,
    WithLp.toLp_ofLp]
  exact pow_le_one₀ (by positivity) hsquare

/-- Pair-purity bound. Conditioning on either Gaussian time turns the other
time into the uniform one-target moment; no target union remains. -/
theorem integral_gaussianPair_staticChoi_fidelity_pow_le_crowding
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (r : ℕ) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    (∫ p : ℝ × ℝ, finitePureStateFidelity
        (staticSpectralChoiVector d (T * p.1) energy).ofLp
        (staticSpectralChoiVector d (T * p.2) energy).ofLp ^ r
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) ≤
      (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
        (replicaActionCrowdingDegree energy r δ : ℝ) *
          ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r) +
        Real.exp (-((T * δ) ^ (2 : ℕ)) / 2) := by
  let f : ℝ × ℝ → ℝ := fun p => finitePureStateFidelity
    (staticSpectralChoiVector d (T * p.1) energy).ofLp
    (staticSpectralChoiVector d (T * p.2) energy).ofLp ^ r
  let B : ℝ :=
    (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
      (replicaActionCrowdingDegree energy r δ : ℝ) *
        ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r) +
      Real.exp (-((T * δ) ^ (2 : ℕ)) / 2)
  have hf : Integrable f
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    exact integrable_gaussianPair_staticChoi_fidelity_pow hd energy T r
  have hslice : ∀ y : ℝ,
      (∫ x, f (x, y) ∂gaussianReal 0 1) ≤ B := by
    intro y
    exact integral_gaussian_staticChoi_fidelity_pow_le_crowding
      hd hmax (staticSpectralChoiVector d (T * y) energy)
      (staticSpectralChoiVector_norm hd (T * y) energy) r hT hδ
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

theorem integrable_sq_inner_staticChoiReplica
    {d r : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (T : ℝ)
    (u : EuclideanSpace ℂ (Fin r → (Fin d × Fin d))) (R : Set ℝ) :
    Integrable
      (fun x => ‖inner ℂ u (finitePureTensorPowerEuclidean r
        (staticSpectralChoiVector d (T * x) energy))‖ ^ (2 : ℕ))
      ((gaussianReal 0 1).restrict R) := by
  have hcTensor := continuous_finitePureTensorPowerEuclidean_comp
    (r := r)
    (fun x : ℝ => staticSpectralChoiVector d (T * x) energy)
    (continuous_staticSpectralChoiVector_scaled hd energy T)
  have hc : Continuous (fun x => inner ℂ u (finitePureTensorPowerEuclidean r
      (staticSpectralChoiVector d (T * x) energy))) :=
    Continuous.inner continuous_const hcTensor
  apply Integrable.of_bound (hc.norm.pow 2).aestronglyMeasurable (‖u‖ ^ (2 : ℕ))
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hinner := norm_inner_le_norm (𝕜 := ℂ) u
    (finitePureTensorPowerEuclidean r
      (staticSpectralChoiVector d (T * x) energy))
  have htensor : ‖finitePureTensorPowerEuclidean r
      (staticSpectralChoiVector d (T * x) energy)‖ = 1 :=
    norm_finitePureTensorPowerEuclidean_eq_one r _
      (finiteComplexInner_staticSpectralChoiVector_self hd energy (T * x))
  rw [htensor, mul_one] at hinner
  exact pow_le_pow_left₀ (norm_nonneg _) hinner 2

/-- Every return-excised carrier action of a static Choi orbit is bounded by
the same global spectral crowding budget. -/
theorem returnExcisedReplicaCarrierIncidenceAction_staticChoi_le_crowding
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (r : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (Fin r → (Fin d × Fin d))))
    (returnSet : Set ℝ) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    returnExcisedReplicaCarrierIncidenceAction (gaussianReal 0 1) r S
        (fun x => (staticSpectralChoiVector d (T * x) energy).ofLp)
        returnSet ≤
      (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
        (replicaActionCrowdingDegree energy r δ : ℝ) *
          ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r) +
        Real.exp (-((T * δ) ^ (2 : ℕ)) / 2) := by
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
        pow_nonneg (by
          unfold finitePureStateFidelity
          exact sq_nonneg _) r
    · exact hf
  exact hcompression.trans (hrestricted.trans
    (integral_gaussianPair_staticChoi_fidelity_pow_le_crowding
      hd hmax r hT hδ))

end RHTower
