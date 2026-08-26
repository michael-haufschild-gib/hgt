import GaloisForLFunctions.HTGeometry.FiniteUniformCollectiveCovarianceLaw
import GaloisForLFunctions.RHTower.StaticChoiCarrierPurityCrowdingLaw

open scoped BigOperators ComplexConjugate
open Set MeasureTheory ProbabilityTheory
noncomputable section

namespace RHTower
open GaloisForLFunctions.HTGeometry

def staticChoiReplicaDiagonalEmbedding {d r : ℕ}
    (α : Fin r → Fin d) : Fin r → (Fin d × Fin d) :=
  fun a => (α a, α a)

theorem staticChoiReplicaDiagonalEmbedding_injective {d r : ℕ} :
    Function.Injective (staticChoiReplicaDiagonalEmbedding :
      (Fin r → Fin d) → Fin r → (Fin d × Fin d)) := by
  intro α β h
  funext a
  exact congrArg Prod.fst (congrFun h a)

def staticChoiReplicaConjugateDiagonalRestriction {d r : ℕ}
    (u : EuclideanSpace ℂ (Fin r → (Fin d × Fin d))) :
    EuclideanSpace ℂ (Fin r → Fin d) :=
  WithLp.toLp 2 fun α => star (u (staticChoiReplicaDiagonalEmbedding α))

theorem norm_staticChoiReplicaConjugateDiagonalRestriction_le
    {d r : ℕ} (u : EuclideanSpace ℂ (Fin r → (Fin d × Fin d))) :
    ‖staticChoiReplicaConjugateDiagonalRestriction u‖ ≤ ‖u‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [staticChoiReplicaConjugateDiagonalRestriction, norm_star]
  let diag := staticChoiReplicaDiagonalEmbedding (d := d) (r := r)
  calc
    ∑ α : Fin r → Fin d, ‖u (diag α)‖ ^ 2 =
        ∑ x ∈ Finset.univ.image diag, ‖u x‖ ^ 2 := by
      rw [Finset.sum_image]
      exact staticChoiReplicaDiagonalEmbedding_injective.injOn
    _ ≤ ∑ x : Fin r → (Fin d × Fin d), ‖u x‖ ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _

theorem sqrt_natCast_pow (d r : ℕ) :
    Real.sqrt ((d : ℝ) ^ r) = Real.sqrt (d : ℝ) ^ r := by
  rw [← sq_eq_sq₀ (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)]
  rw [Real.sq_sqrt (by positivity : 0 ≤ (d : ℝ) ^ r)]
  calc
    (d : ℝ) ^ r = (Real.sqrt (d : ℝ) ^ 2) ^ r := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ (d : ℝ))]
    _ = Real.sqrt (d : ℝ) ^ (2 * r) := (pow_mul _ 2 r).symm
    _ = Real.sqrt (d : ℝ) ^ (r * 2) := by rw [mul_comm r 2]
    _ = (Real.sqrt (d : ℝ) ^ r) ^ 2 := pow_mul _ r 2

theorem finiteUniformWeight_restriction_eq
    {d r : ℕ} (u : EuclideanSpace ℂ (Fin r → (Fin d × Fin d)))
    (α : Fin r → Fin d) :
    finiteUniformDirectionalWeight
        (staticChoiReplicaConjugateDiagonalRestriction u) α =
      (Real.sqrt (d : ℝ))⁻¹ ^ r *
        ‖u (staticChoiReplicaDiagonalEmbedding α)‖ := by
  unfold finiteUniformDirectionalWeight
  rw [Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [sqrt_natCast_pow, inv_pow]
  simp [staticChoiReplicaConjugateDiagonalRestriction]

theorem finiteUniformWeight_mul_twist_restriction
    {d r : ℕ} (u : EuclideanSpace ℂ (Fin r → (Fin d × Fin d)))
    (α : Fin r → Fin d) :
    (finiteUniformDirectionalWeight
        (staticChoiReplicaConjugateDiagonalRestriction u) α : ℂ) *
      finiteUniformDirectionalTwist
        (staticChoiReplicaConjugateDiagonalRestriction u) α =
      (((Real.sqrt (d : ℝ))⁻¹ ^ r : ℝ) : ℂ) *
        star (u (staticChoiReplicaDiagonalEmbedding α)) := by
  rw [finiteUniformWeight_restriction_eq]
  unfold finiteUniformDirectionalTwist
  simp only [staticChoiReplicaConjugateDiagonalRestriction]
  split_ifs with h
  · simp at h
    simp [h]
  · have hn : ‖star (u (staticChoiReplicaDiagonalEmbedding α))‖ ≠ 0 :=
      norm_ne_zero_iff.mpr h
    push_cast
    rw [norm_star]
    rw [norm_star] at hn
    field_simp [hn]

theorem finitePureTensorPowerEuclidean_staticChoi_diag
    {d : ℕ} (r : ℕ) (t : ℝ) (energy : Fin d → ℝ)
    (α : Fin r → Fin d) :
    finitePureTensorPowerEuclidean r (staticSpectralChoiVector d t energy)
        (staticChoiReplicaDiagonalEmbedding α) =
      ((((Real.sqrt (d : ℝ))⁻¹ ^ r : ℝ) : ℂ) *
        Complex.exp ((((collectiveReplicaEnergy energy α) * t : ℝ) : ℂ) *
          Complex.I)) := by
  change
    (∏ a, staticSpectralChoiVector d t energy (α a, α a)) = _
  simp_rw [staticSpectralChoiVector, fullUniformPhaseChoiVector_apply,
    fourier_finiteHamiltonianAddCirclePhase,
    finiteObserverHamiltonianVertexPhase]
  simp only [if_true]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Complex.exp_sum]
  congr 1
  · norm_cast
  · congr 1
    push_cast
    unfold collectiveReplicaEnergy
    rw [Complex.ofReal_sum, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ring

theorem inner_staticChoiReplica_eq_collectiveTwistedAmplitude
    {d r : ℕ} (t : ℝ) (energy : Fin d → ℝ)
    (u : EuclideanSpace ℂ (Fin r → (Fin d × Fin d))) :
    inner ℂ u
        (finitePureTensorPowerEuclidean r (staticSpectralChoiVector d t energy)) =
      twistedFiniteSpectralAmplitude
        (finiteUniformDirectionalWeight
          (staticChoiReplicaConjugateDiagonalRestriction u))
        (collectiveReplicaEnergy energy)
        (finiteUniformDirectionalTwist
          (staticChoiReplicaConjugateDiagonalRestriction u)) t := by
  rw [EuclideanSpace.inner_toLp_toLp]
  change
    (∑ x : Fin r → (Fin d × Fin d),
      finitePureTensorPowerEuclidean r (staticSpectralChoiVector d t energy) x *
        star (u x)) = _
  let diag := staticChoiReplicaDiagonalEmbedding (d := d) (r := r)
  have hsupport :
      (∑ x : Fin r → (Fin d × Fin d),
        finitePureTensorPowerEuclidean r (staticSpectralChoiVector d t energy) x *
          star (u x)) =
      ∑ x ∈ Finset.univ.image diag,
        finitePureTensorPowerEuclidean r (staticSpectralChoiVector d t energy) x *
          star (u x) := by
    symm
    apply Finset.sum_subset (Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _)
    intro x hxuniv hxdiag
    have hneq : ∃ a, (x a).1 ≠ (x a).2 := by
      by_contra h
      simp only [not_exists, not_ne_iff] at h
      apply hxdiag
      rw [Finset.mem_image]
      refine ⟨(fun a => (x a).1), Finset.mem_univ _, ?_⟩
      funext a
      exact Prod.ext rfl (h a)
    obtain ⟨a, ha⟩ := hneq
    have hzero :
        finitePureTensorPowerEuclidean r
          (staticSpectralChoiVector d t energy) x = 0 := by
      change ∏ b, staticSpectralChoiVector d t energy (x b) = 0
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      simp [staticSpectralChoiVector, fullUniformPhaseChoiVector_apply, ha]
    rw [hzero, zero_mul]
  rw [hsupport]
  rw [Finset.sum_image staticChoiReplicaDiagonalEmbedding_injective.injOn]
  unfold twistedFiniteSpectralAmplitude
  apply Finset.sum_congr rfl
  intro α hα
  rw [finitePureTensorPowerEuclidean_staticChoi_diag,
    finiteUniformWeight_mul_twist_restriction]
  ring

theorem integral_sq_inner_staticChoiReplica_le_operatorCrowding
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (henergy : MaximallyProjectiveEnergy energy)
    {r : ℕ} (u : EuclideanSpace ℂ (Fin r → (Fin d × Fin d)))
    (hu : ‖u‖ ≤ 1) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    (∫ x, ‖inner ℂ u (finitePureTensorPowerEuclidean r
        (staticSpectralChoiVector d (T * x) energy))‖ ^ 2
      ∂gaussianReal 0 1) ≤
      (r.factorial : ℝ) *
          (1 + replicaActionCrowdingDegree energy r δ) *
          (d : ℝ)⁻¹ ^ r +
      Real.exp (-((T * δ) ^ 2) / 2) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let target := staticChoiReplicaConjugateDiagonalRestriction u
  let weight := finiteUniformDirectionalWeight target
  let twist := finiteUniformDirectionalTwist target
  let replicaEnergy : (Fin r → Fin d) → ℝ := collectiveReplicaEnergy energy
  have hInt : Integrable
      (fun x => ‖inner ℂ u (finitePureTensorPowerEuclidean r
        (staticSpectralChoiVector d (T * x) energy))‖ ^ 2)
      (gaussianReal 0 1) := by
    simpa using integrable_sq_inner_staticChoiReplica
      hd energy T u Set.univ
  have hmean :
      (((∫ x, ‖inner ℂ u (finitePureTensorPowerEuclidean r
          (staticSpectralChoiVector d (T * x) energy))‖ ^ 2
        ∂gaussianReal 0 1 : ℝ) : ℂ)) =
        twistedGaussianSpectralFidelityMean weight replicaEnergy twist 1 T := by
    unfold twistedGaussianSpectralFidelityMean
    change Complex.ofRealCLM (∫ x, ‖inner ℂ u
        (finitePureTensorPowerEuclidean r
          (staticSpectralChoiVector d (T * x) energy))‖ ^ 2
      ∂gaussianReal 0 1) = _
    rw [← Complex.ofRealCLM.integral_comp_comm hInt]
    apply integral_congr_ae
    filter_upwards with x
    rw [inner_staticChoiReplica_eq_collectiveTwistedAmplitude]
    simp only [weight, replicaEnergy, twist, twistedFiniteSpectralFidelity,
      pow_one]
    rw [Complex.ofRealCLM_apply]
    exact_mod_cast Complex.sq_norm
      (twistedFiniteSpectralAmplitude
        (finiteUniformDirectionalWeight target)
        (collectiveReplicaEnergy energy)
        (finiteUniformDirectionalTwist target) (T * x))
  have htarget : ‖target‖ ≤ 1 :=
    (norm_staticChoiReplicaConjugateDiagonalRestriction_le u).trans hu
  have hbound := norm_twistedGaussian_collectiveUniformDirection_le
    henergy target htarget hT hδ
  have hreal :
      (∫ x, ‖inner ℂ u (finitePureTensorPowerEuclidean r
          (staticSpectralChoiVector d (T * x) energy))‖ ^ 2
        ∂gaussianReal 0 1) =
      (twistedGaussianSpectralFidelityMean weight replicaEnergy twist 1 T).re := by
    rw [← hmean]
    simp
  rw [hreal]
  exact (Complex.re_le_norm _).trans (by
    simpa only [Fintype.card_fin] using hbound)

theorem integral_replicaSubspaceProjectionMass_staticChoi_le_operatorCrowding
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (henergy : MaximallyProjectiveEnergy energy)
    {r : ℕ}
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → (Fin d × Fin d))))
    {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    (∫ x, replicaSubspaceProjectionMass r S
        (staticSpectralChoiVector d (T * x) energy)
      ∂gaussianReal 0 1) ≤
      (Module.finrank ℂ S : ℝ) *
        ((r.factorial : ℝ) *
            (1 + replicaActionCrowdingDegree energy r δ) *
            (d : ℝ)⁻¹ ^ r +
          Real.exp (-((T * δ) ^ 2) / 2)) := by
  let b := replicaSubspaceOrthonormalBasis r S
  let B : ℝ := (r.factorial : ℝ) *
      (1 + replicaActionCrowdingDegree energy r δ) *
      (d : ℝ)⁻¹ ^ r + Real.exp (-((T * δ) ^ 2) / 2)
  calc
    (∫ x, replicaSubspaceProjectionMass r S
        (staticSpectralChoiVector d (T * x) energy)
      ∂gaussianReal 0 1) =
      ∫ x, ∑ i, ‖replicaSubspaceCoordinate r S
          (staticSpectralChoiVector d (T * x) energy) i‖ ^ 2
        ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        replicaSubspaceProjectionMass_eq_finiteCoordinateEnergy r S _
    _ = ∑ i, ∫ x, ‖replicaSubspaceCoordinate r S
          (staticSpectralChoiVector d (T * x) energy) i‖ ^ 2
        ∂gaussianReal 0 1 := by
      rw [integral_finsetSum Finset.univ]
      intro i hi
      let u : EuclideanSpace ℂ (Fin r → (Fin d × Fin d)) := (b i : S)
      change Integrable (fun x => ‖inner ℂ u
        (finitePureTensorPowerEuclidean r
          (staticSpectralChoiVector d (T * x) energy))‖ ^ 2) _
      simpa using integrable_sq_inner_staticChoiReplica hd energy T u Set.univ
    _ ≤ ∑ _i : Fin (Module.finrank ℂ S), B := by
      apply Finset.sum_le_sum
      intro i hi
      let u : EuclideanSpace ℂ (Fin r → (Fin d × Fin d)) := (b i : S)
      change (∫ x, ‖inner ℂ u (finitePureTensorPowerEuclidean r
          (staticSpectralChoiVector d (T * x) energy))‖ ^ 2
        ∂gaussianReal 0 1) ≤ B
      exact integral_sq_inner_staticChoiReplica_le_operatorCrowding
        hd henergy u (by
          simpa only [u, b, Submodule.coe_norm] using
            ((replicaSubspaceOrthonormalBasis r S).orthonormal.norm_eq_one i).le)
        hT hδ
    _ = (Module.finrank ℂ S : ℝ) * B := by
      simp [Fintype.card_fin]
    _ = _ := rfl

theorem integral_replicaTargetProjectionMass_staticChoi_le_operatorCrowding
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (henergy : MaximallyProjectiveEnergy energy)
    {C : Type*} (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    {r : ℕ} {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    (∫ x, replicaTargetProjectionMass r
        (fun c => (target c : (Fin d × Fin d) → ℂ))
        (staticSpectralChoiVector d (T * x) energy)
      ∂gaussianReal 0 1) ≤
      (Module.finrank ℂ (replicaTargetSpan r
        (fun c => (target c : (Fin d × Fin d) → ℂ))) : ℝ) *
        ((r.factorial : ℝ) *
            (1 + replicaActionCrowdingDegree energy r δ) *
            (d : ℝ)⁻¹ ^ r +
          Real.exp (-((T * δ) ^ 2) / 2)) := by
  simpa only [replicaTargetProjectionMass, replicaSubspaceProjectionMass] using
    integral_replicaSubspaceProjectionMass_staticChoi_le_operatorCrowding
      hd henergy (replicaTargetSpan r
        (fun c => (target c : (Fin d × Fin d) → ℂ))) hT hδ

/-- **One-cell complete-union operator-covariance law.**  Every target label,
including an infinite family, is compressed to occupied replica rank.  The
rank pays linearly against the directional covariance budget; no squared
carrier action or targetwise union appears. -/
theorem gaussian_completeStaticChoiTargetCapture_measure_le_operatorCrowding
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (henergy : MaximallyProjectiveEnergy energy)
    {C : Type*} (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ ≤ 1)
    {r : ℕ} (hr : 0 < r) {T δ threshold : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hthreshold : 0 < threshold) :
    (gaussianReal 0 1).real
        {x | ∃ c, threshold ≤ finitePureStateFidelity
          (staticSpectralChoiVector d (T * x) energy) (target c)} ≤
      ((Module.finrank ℂ (replicaTargetSpan r
          (fun c => (target c : (Fin d × Fin d) → ℂ))) : ℝ) *
        ((r.factorial : ℝ) *
            (1 + replicaActionCrowdingDegree energy r δ) *
            (d : ℝ)⁻¹ ^ r +
          Real.exp (-((T * δ) ^ 2) / 2))) /
        threshold ^ r := by
  have hint : Integrable
      (fun x => replicaTargetProjectionMass r
        (fun c => (target c : (Fin d × Fin d) → ℂ))
        (staticSpectralChoiVector d (T * x) energy))
      (gaussianReal 0 1) := by
    apply integrable_replicaTargetProjectionMass_of_coordinates
    intro i
    let u : EuclideanSpace ℂ (Fin r → (Fin d × Fin d)) :=
      ((replicaTargetOrthonormalBasis r
          (fun c => (target c : (Fin d × Fin d) → ℂ)) i :
        replicaTargetSpan r
          (fun c => (target c : (Fin d × Fin d) → ℂ))) :
          EuclideanSpace ℂ (Fin r → (Fin d × Fin d)))
    change Integrable (fun x => ‖inner ℂ u
      (finitePureTensorPowerEuclidean r
        (staticSpectralChoiVector d (T * x) energy))‖ ^ 2) _
    simpa using integrable_sq_inner_staticChoiReplica hd energy T u Set.univ
  have hincidence := measure_completePureStateTargetCapture_le_replicaProjectionMoment
    (gaussianReal 0 1) hr
    (fun c => (target c : (Fin d × Fin d) → ℂ))
    (fun x => staticSpectralChoiVector d (T * x) energy)
    (fun c => norm_finitePureTensorPowerEuclidean_le_one r (target c)
      (by simpa using htarget c))
    threshold hthreshold hint
  exact hincidence.trans (div_le_div_of_nonneg_right
    (integral_replicaTargetProjectionMass_staticChoi_le_operatorCrowding
      hd henergy target hT hδ)
    (pow_nonneg hthreshold.le r))

theorem integrable_replicaSubspaceProjectionMass_staticChoi
    {d r : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (T : ℝ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → (Fin d × Fin d))))
    (R : Set ℝ) :
    Integrable (fun x => replicaSubspaceProjectionMass r S
      (staticSpectralChoiVector d (T * x) energy))
      ((gaussianReal 0 1).restrict R) := by
  have hsum : Integrable
      (fun x => ∑ i, ‖replicaSubspaceCoordinate r S
        (staticSpectralChoiVector d (T * x) energy) i‖ ^ 2)
      ((gaussianReal 0 1).restrict R) := by
    apply integrable_finsetSum
    intro i hi
    let u : EuclideanSpace ℂ (Fin r → (Fin d × Fin d)) :=
      ((replicaSubspaceOrthonormalBasis r S i : S) :
        EuclideanSpace ℂ (Fin r → (Fin d × Fin d)))
    change Integrable (fun x => ‖inner ℂ u
      (finitePureTensorPowerEuclidean r
        (staticSpectralChoiVector d (T * x) energy))‖ ^ 2) _
    exact integrable_sq_inner_staticChoiReplica hd energy T u R
  exact hsum.congr (Filter.Eventually.of_forall fun x =>
    (replicaSubspaceProjectionMass_eq_finiteCoordinateEnergy r S _).symm)

/-- Return removal preserves every source sheet and replaces full target rank
by the replica image actually occupied off the initial-return cell. -/
theorem gaussian_returnExcised_completeStaticChoiTargetCapture_measure_le_operatorCrowding
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (henergy : MaximallyProjectiveEnergy energy)
    {C : Type*} (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ ≤ 1)
    {r : ℕ} (hr : 0 < r) (returnSet : Set ℝ)
    (hreturn : MeasurableSet returnSet)
    {T δ threshold : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hthreshold : 0 < threshold) :
    ((gaussianReal 0 1).restrict returnSetᶜ).real
        {x | ∃ c, threshold ≤ finitePureStateFidelity
          (staticSpectralChoiVector d (T * x) energy) (target c)} ≤
      ((returnExcisedReplicaIncidenceNumber r
          (fun c => (target c : (Fin d × Fin d) → ℂ))
          (fun x => (staticSpectralChoiVector d (T * x) energy :
            (Fin d × Fin d) → ℂ)) returnSet : ℝ) *
        ((r.factorial : ℝ) *
            (1 + replicaActionCrowdingDegree energy r δ) *
            (d : ℝ)⁻¹ ^ r +
          Real.exp (-((T * δ) ^ 2) / 2))) /
        threshold ^ r := by
  let targetFun : C → (Fin d × Fin d) → ℂ := fun c => target c
  let state : ℝ → (Fin d × Fin d) → ℂ :=
    fun x => staticSpectralChoiVector d (T * x) energy
  let S := returnExcisedReplicaIncidenceSpan r targetFun state returnSet
  have hintTarget : Integrable
      (fun x => replicaTargetProjectionMass r targetFun (state x))
      ((gaussianReal 0 1).restrict returnSetᶜ) := by
    apply integrable_replicaTargetProjectionMass_of_coordinates
    intro i
    let u : EuclideanSpace ℂ (Fin r → (Fin d × Fin d)) :=
      ((replicaTargetOrthonormalBasis r targetFun i :
        replicaTargetSpan r targetFun) :
          EuclideanSpace ℂ (Fin r → (Fin d × Fin d)))
    change Integrable (fun x => ‖inner ℂ u
      (finitePureTensorPowerEuclidean r
        (staticSpectralChoiVector d (T * x) energy))‖ ^ 2) _
    exact integrable_sq_inner_staticChoiReplica hd energy T u returnSetᶜ
  have hincidence := measure_completePureStateTargetCapture_le_replicaProjectionMoment
    ((gaussianReal 0 1).restrict returnSetᶜ) hr targetFun state
    (fun c => norm_finitePureTensorPowerEuclidean_le_one r (target c)
      (by simpa using htarget c)) threshold hthreshold hintTarget
  have heq :
      (∫ x, replicaTargetProjectionMass r targetFun (state x)
        ∂((gaussianReal 0 1).restrict returnSetᶜ)) =
      ∫ x, replicaSubspaceProjectionMass r S (state x)
        ∂((gaussianReal 0 1).restrict returnSetᶜ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hreturn.compl] with x hx
    exact replicaTargetProjectionMass_eq_incidenceProjectionMass_offReturn
      r targetFun state returnSet hx
  have hIntS : Integrable
      (fun x => replicaSubspaceProjectionMass r S (state x))
      (gaussianReal 0 1) := by
    simpa only [state, Measure.restrict_univ] using
      integrable_replicaSubspaceProjectionMass_staticChoi
        hd energy T S Set.univ
  have hrestrict :
      (∫ x, replicaSubspaceProjectionMass r S (state x)
        ∂((gaussianReal 0 1).restrict returnSetᶜ)) ≤
      ∫ x, replicaSubspaceProjectionMass r S (state x)
        ∂gaussianReal 0 1 := by
    apply integral_mono_measure Measure.restrict_le_self
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _
    · exact hIntS
  have hmoment :=
    integral_replicaSubspaceProjectionMass_staticChoi_le_operatorCrowding
      hd henergy S hT hδ
  have hupper :
      (∫ x, replicaTargetProjectionMass r targetFun (state x)
        ∂((gaussianReal 0 1).restrict returnSetᶜ)) ≤
      (Module.finrank ℂ S : ℝ) *
        ((r.factorial : ℝ) *
            (1 + replicaActionCrowdingDegree energy r δ) *
            (d : ℝ)⁻¹ ^ r +
          Real.exp (-((T * δ) ^ 2) / 2)) := by
    rw [heq]
    exact hrestrict.trans (by simpa only [state] using hmoment)
  exact hincidence.trans (div_le_div_of_nonneg_right
    (by simpa only [S, returnExcisedReplicaIncidenceNumber,
      targetFun, state] using hupper)
    (pow_nonneg hthreshold.le r))

/-- A return-excised one-cell measure bound, rather than a two-cell collision,
is sufficient to exclude every continuous later hit. -/
theorem no_second_capture_of_returnExcised_gaussianMeasure_lt
    {C α : Type*} [Fintype α]
    (D : (α → ℂ) → (α → ℂ) → ℝ)
    (psi : ℝ → α → ℂ) (target : C → α → ℂ)
    {speed epsn epsw T threshold : ℝ}
    (hspeed : 0 < speed) (hTpos : 0 < T)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hT : epsw / speed ≤ T)
    (htriangle : ∀ t u c,
      D (psi t) (target c) ≤ D (psi t) (psi u) + D (psi u) (target c))
    (hLip : ∀ t u, D (psi t) (psi u) ≤ speed * |t - u|)
    (hfidelity : ∀ t c, D (psi t) (target c) ≤ epsw →
      threshold ≤ finitePureStateFidelity (psi t) (target c))
    (hmeasure :
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / speed / T)) (epsw / speed / T))ᶜ).real
          {x | ∃ c, threshold ≤
            finitePureStateFidelity (psi (T * x)) (target c)} <
        gaussianFloorTwo * ((epsw - epsn) / speed / (2 * T))) :
    ¬ ∃ t ∈ Icc
        (epsw / speed + (epsw - epsn) / speed) T,
      ∃ c, D (psi t) (target c) ≤ epsn := by
  let a := epsw / speed
  let mesh := (epsw - epsn) / speed
  let R : Set ℝ := Icc (-(a / T)) (a / T)
  let state : ℝ → α → ℂ := fun x => psi (T * x)
  let E : Set ℝ :=
    {x | ∃ c, threshold ≤ finitePureStateFidelity (state x) (target c)}
  have hepsw : 0 < epsw := lt_of_le_of_lt hepsn hgap
  have ha : 0 < a := div_pos hepsw hspeed
  have hmesh : 0 < mesh := div_pos (sub_pos.mpr hgap) hspeed
  rintro ⟨t, ht, c, hcap⟩
  let rho := mesh / (4 * T)
  let center := (t - mesh / 4) / T
  let I : Set ℝ := Icc ((t - mesh / 2) / T) (t / T)
  have hrho : 0 < rho := div_pos hmesh (by positivity)
  have hmeshLeA : mesh ≤ a := by
    dsimp [mesh, a]
    exact div_le_div_of_nonneg_right (sub_le_self epsw hepsn) hspeed.le
  have hcenter_nonneg : 0 ≤ center := by
    dsimp [center]
    apply div_nonneg
    · have hta : a + mesh ≤ t := by simpa [a, mesh] using ht.1
      linarith
    · exact hTpos.le
  have hcenter_le : center ≤ 1 := by
    dsimp [center]
    rw [div_le_one hTpos]
    exact (sub_le_self t (by positivity)).trans ht.2
  have hcenter : |center| ≤ 1 := by
    rw [abs_of_nonneg hcenter_nonneg]
    exact hcenter_le
  have hrhoOne : rho ≤ 1 := by
    have haT : a ≤ T := by simpa [a] using hT
    have hmeshT : mesh ≤ T := hmeshLeA.trans haT
    dsimp [rho]
    rw [div_le_one (by positivity : 0 < 4 * T)]
    linarith
  have hI : I = Icc (center - rho) (center + rho) := by
    dsimp [I, center, rho]
    congr 1 <;> field_simp <;> ring
  have hIR : I ⊆ Rᶜ := by
    intro x hx hxR
    have hta : a + mesh ≤ t := by simpa [a, mesh] using ht.1
    have hxlower : (t - mesh / 2) / T ≤ x := by simpa [I] using hx.1
    have hxRupper : x ≤ a / T := by simpa [R] using hxR.2
    rw [div_le_iff₀ hTpos] at hxlower
    rw [le_div_iff₀ hTpos] at hxRupper
    nlinarith
  have hIE : I ⊆ E := by
    intro x hx
    refine ⟨c, hfidelity (T * x) c ?_⟩
    have hxlower : t - mesh / 2 ≤ T * x := by
      have h := hx.1
      rw [div_le_iff₀ hTpos] at h
      simpa [mul_comm] using h
    have hxupper : T * x ≤ t := by
      have h := hx.2
      rw [le_div_iff₀ hTpos] at h
      simpa [mul_comm] using h
    have hxt : |T * x - t| ≤ mesh / 2 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxupper)]
      linarith
    have hmove := hLip (T * x) t
    calc
      D (psi (T * x)) (target c) ≤
          D (psi (T * x)) (psi t) + D (psi t) (target c) :=
        htriangle (T * x) t c
      _ ≤ speed * |T * x - t| + epsn := add_le_add hmove hcap
      _ ≤ speed * (mesh / 2) + epsn :=
        add_le_add (mul_le_mul_of_nonneg_left hxt hspeed.le) le_rfl
      _ ≤ epsw := by dsimp [mesh]; field_simp; nlinarith
  have hmuE := gaussianReal_Icc_shifted_lower
    (a := center) (rho := rho) hcenter hrho.le hrhoOne
  rw [← hI] at hmuE
  have hlowerI : gaussianFloorTwo * (mesh / (2 * T)) ≤
      (gaussianReal 0 1).real I := by
    have hnonneg : 0 ≤ 2 * gaussianFloorTwo * rho :=
      mul_nonneg (mul_nonneg (by norm_num) gaussianFloorTwo_pos.le) hrho.le
    have hreal : 2 * gaussianFloorTwo * rho ≤
        (gaussianReal 0 1).real I := by
      rw [← ENNReal.toReal_ofReal hnonneg]
      exact ENNReal.toReal_mono (measure_ne_top _ _) hmuE
    convert hreal using 1
    dsimp [rho]
    field_simp
    ring
  have hrestrictI : ((gaussianReal 0 1).restrict Rᶜ).real I =
      (gaussianReal 0 1).real I := by
    rw [measureReal_restrict_apply' measurableSet_Icc.compl]
    rw [inter_eq_left.mpr hIR]
  have hmass : gaussianFloorTwo * (mesh / (2 * T)) ≤
      ((gaussianReal 0 1).restrict Rᶜ).real E := by
    calc
      gaussianFloorTwo * (mesh / (2 * T)) ≤
          (gaussianReal 0 1).real I := hlowerI
      _ = ((gaussianReal 0 1).restrict Rᶜ).real I := hrestrictI.symm
      _ ≤ ((gaussianReal 0 1).restrict Rᶜ).real E :=
        measureReal_mono hIE (measure_ne_top _ _)
  exact (not_lt_of_ge (by simpa [R, E, state, a, mesh] using hmass)) hmeasure

/-- **Continuous initial post-ramp exclusion from operator covariance.**
The sufficient budget is linear in occupied return-excised replica rank and
in one directional spectral moment.  This replaces the former squared
incidence-action condition. -/
theorem no_forward_pureChoiCircuitReturn_of_operatorCrowding
    {d : ℕ} (hd : 0 < d)
    {energy : Fin d → ℝ} (henergy : MaximallyProjectiveEnergy energy)
    {C : Type*} (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ = 1)
    {r : ℕ} (hr : 0 < r) {T δ epsn epsw : ℝ}
    (hTpos : 0 < T) (hδ : 0 < δ)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw) (hepswOne : epsw < 1)
    (hT : epsw / staticChoiSpeed energy ≤ T)
    (hbudget :
      (returnExcisedReplicaIncidenceNumber r
          (fun c => (target c : (Fin d × Fin d) → ℂ))
          (fun x => (staticSpectralChoiVector d (T * x) energy :
            (Fin d × Fin d) → ℂ))
          (Icc (-(epsw / staticChoiSpeed energy / T))
            (epsw / staticChoiSpeed energy / T)) : ℝ) *
        ((r.factorial : ℝ) *
            (1 + replicaActionCrowdingDegree energy r δ) *
            (d : ℝ)⁻¹ ^ r +
          Real.exp (-((T * δ) ^ 2) / 2)) <
      gaussianFloorTwo *
        ((epsw - epsn) / staticChoiSpeed energy / (2 * T)) *
          (1 - epsw ^ 2) ^ r) :
    ¬ ∃ t ∈ Icc
        (epsw / staticChoiSpeed energy +
          (epsw - epsn) / staticChoiSpeed energy) T,
      ∃ c, pureStateTraceDistance
        (staticSpectralChoiVector d t energy) (target c) ≤ epsn := by
  have hepsw : 0 ≤ epsw := hepsn.trans (le_of_lt hgap)
  have hthreshold : 0 < 1 - epsw ^ 2 := by
    nlinarith [sq_nonneg epsw]
  let R : Set ℝ := Icc
    (-(epsw / staticChoiSpeed energy / T))
    (epsw / staticChoiSpeed energy / T)
  have hmeasureUpper :=
    gaussian_returnExcised_completeStaticChoiTargetCapture_measure_le_operatorCrowding
      hd henergy target (fun c => (htarget c).le) hr R measurableSet_Icc
      hTpos hδ hthreshold
  have hmeasureStrict :
      ((gaussianReal 0 1).restrict Rᶜ).real
          {x | ∃ c, 1 - epsw ^ 2 ≤ finitePureStateFidelity
            (staticSpectralChoiVector d (T * x) energy) (target c)} <
        gaussianFloorTwo *
          ((epsw - epsn) / staticChoiSpeed energy / (2 * T)) := by
    refine hmeasureUpper.trans_lt ?_
    apply (div_lt_iff₀' (pow_pos hthreshold r)).2
    simpa only [R] using (show
      (returnExcisedReplicaIncidenceNumber r
          (fun c => (target c : (Fin d × Fin d) → ℂ))
          (fun x => (staticSpectralChoiVector d (T * x) energy :
            (Fin d × Fin d) → ℂ))
          (Icc (-(epsw / staticChoiSpeed energy / T))
            (epsw / staticChoiSpeed energy / T)) : ℝ) *
        ((r.factorial : ℝ) *
            (1 + replicaActionCrowdingDegree energy r δ) *
            (d : ℝ)⁻¹ ^ r +
          Real.exp (-((T * δ) ^ 2) / 2)) <
        (1 - epsw ^ 2) ^ r *
          (gaussianFloorTwo *
            ((epsw - epsn) / staticChoiSpeed energy / (2 * T))) by
      nlinarith [hbudget])
  have htriangle : ∀ t u c,
      pureStateTraceDistance
          (staticSpectralChoiVector d t energy)
          (target c) ≤
        pureStateTraceDistance
            (staticSpectralChoiVector d t energy)
            (staticSpectralChoiVector d u energy) +
          pureStateTraceDistance
            (staticSpectralChoiVector d u energy) (target c) := by
    intro t u c
    exact pureStateTraceDistance_triangle
      (staticSpectralChoiVector d t energy)
      (staticSpectralChoiVector d u energy) (target c)
      (staticSpectralChoiVector_norm hd t energy)
      (staticSpectralChoiVector_norm hd u energy) (htarget c)
  have hLip : ∀ t u,
      pureStateTraceDistance
          (staticSpectralChoiVector d t energy)
          (staticSpectralChoiVector d u energy) ≤
        staticChoiSpeed energy * |t - u| := by
    intro t u
    exact pureStateTraceDistance_staticSpectralChoiVector_time_le
      hd energy t u
  have hfidelity : ∀ t c,
      pureStateTraceDistance
          (staticSpectralChoiVector d t energy) (target c) ≤ epsw →
        1 - epsw ^ 2 ≤ finitePureStateFidelity
          (staticSpectralChoiVector d t energy) (target c) := by
    intro t c hdist
    rw [finitePureStateFidelity_eq_norm_inner_sq]
    rw [norm_inner_symm]
    have hsq := sq_pureStateTraceDistance
      (staticSpectralChoiVector d t energy) (target c)
      (staticSpectralChoiVector_norm hd t energy).le (htarget c).le
    have hdistSq : pureStateTraceDistance
        (staticSpectralChoiVector d t energy) (target c) ^ 2 ≤ epsw ^ 2 :=
      (sq_le_sq₀ (pureStateTraceDistance_nonneg _ _) hepsw).2 hdist
    nlinarith
  exact no_second_capture_of_returnExcised_gaussianMeasure_lt
    (fun u v => pureStateTraceDistance
      (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin d × Fin d))
      (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d × Fin d)))
    (fun t => (staticSpectralChoiVector d t energy).ofLp)
    (fun c => (target c).ofLp)
    (staticChoiSpeed_pos energy) hTpos hepsn hgap hT
    (by simpa only [WithLp.toLp_ofLp] using htriangle)
    (by simpa only [WithLp.toLp_ofLp] using hLip)
    (by simpa only [WithLp.toLp_ofLp] using hfidelity)
    (by simpa only [R, WithLp.toLp_ofLp] using hmeasureStrict)

end RHTower
