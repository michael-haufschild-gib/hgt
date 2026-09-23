import GaloisForLFunctions.HTGeometry.PhaseSeedCollisionVariance
import GaloisForLFunctions.HTGeometry.PhaseSeedCollisionMoments
import GaloisForLFunctions.HTGeometry.UpperMeanChebyshev

/-!
# Basis-uniform concentration of the phase-seed collision

The spectral collision of the equal-amplitude phase seed in an orthonormal family is the quartic
character sum of the unit-weight phase orbit divided by the squared dimension.  The replica moment
bound therefore gives mean at most `2|ι|/D²`, and the torus Poincaré inequality gives variance at
most `96|ι|/D⁴`; at family size `D` these are `2/D` and `96/D³`.

Chebyshev against the upper mean then bounds the probability that the collision exceeds
`(2+κ)/D` by `96/(κ²D)`, uniformly over the orthonormal family -- in particular over an eigenbasis
chosen independently of the phases.
-/

open MeasureTheory ProbabilityTheory Set

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Concentration

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

theorem sum_normSq_of_orthonormal {e : ι → α → ℂ}
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0) (j : ι) :
    (∑ a, ‖e j a‖ ^ (2 : ℕ)) = 1 := by
  have h := horth j j
  rw [if_pos rfl, finiteComplexInner] at h
  have hre : ((∑ a, ‖e j a‖ ^ (2 : ℕ) : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.conj_mul']
  exact_mod_cast hre

/-- The normalized collision is the unit-weight quartic sum over the squared dimension. -/
theorem phaseCollision_eq_quartic_div (e : ι → α → ℂ) (x : α → ℝ) :
    phaseCollision e x = (∑ j, ‖phaseAmp e j x‖ ^ (4 : ℕ)) / (Fintype.card α : ℝ) ^ (2 : ℕ) := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card α) with hcard | hcard
  · have hempty : IsEmpty α := Fintype.card_eq_zero_iff.mp hcard
    have hterm : ∀ j : ι, finitePureStateFidelity (uniformPhaseSeed x) (e j) = 0 := by
      intro j
      rw [finitePureStateFidelity, finiteComplexInner]
      simp [Finset.univ_eq_empty]
    have hterm' : ∀ j : ι, ‖phaseAmp e j x‖ = 0 := by
      intro j
      rw [phaseAmp_eq_inner, finiteComplexInner]
      simp [Finset.univ_eq_empty]
    rw [phaseCollision, hcard]
    simp [hterm, hterm']
  · have hD : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hcard
    have hpt : ∀ j : ι, finitePureStateFidelity (uniformPhaseSeed x) (e j)
        = ‖phaseAmp e j x‖ ^ (2 : ℕ) / (Fintype.card α : ℝ) := by
      intro j
      have hinner : finiteComplexInner (uniformPhaseSeed x) (e j)
          = ((Real.sqrt ((Fintype.card α : ℝ))⁻¹ : ℝ) : ℂ) * phaseAmp e j x := by
        rw [phaseAmp_eq_inner, finiteComplexInner, finiteComplexInner, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [uniformPhaseSeed, torusReplicaPhaseOrbit, torusReplicaPhaseOrbit,
          uniformPhaseWeights, Real.sqrt_one]
        rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
        push_cast
        ring
      rw [finitePureStateFidelity, hinner, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
    rw [phaseCollision, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hpt j, div_pow]
    congr 1
    ring

/-- **The variance half of `(8)`.**  The normalized collision has variance at most `96|ι|/D⁴`. -/
theorem integral_box_variance_phaseCollision_le (e : ι → α → ℂ)
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0) :
    (∫ x in torusBox α, (phaseCollision e x) ^ (2 : ℕ)) -
        (∫ x in torusBox α, phaseCollision e x) ^ (2 : ℕ)
      ≤ 96 * (Fintype.card ι : ℝ) / (Fintype.card α : ℝ) ^ (4 : ℕ) := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card α) with hcard | hcard
  · have hzero : ∀ x : α → ℝ, phaseCollision e x = 0 := by
      intro x
      rw [phaseCollision_eq_quartic_div, hcard]
      simp
    simp only [hzero]
    simp [hcard]
  · have hD : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hcard
    have hsq : ∀ x : α → ℝ, (phaseCollision e x) ^ (2 : ℕ)
        = (∑ j, ‖phaseAmp e j x‖ ^ (4 : ℕ)) ^ (2 : ℕ) / (Fintype.card α : ℝ) ^ (4 : ℕ) := by
      intro x
      rw [phaseCollision_eq_quartic_div, div_pow]
      congr 1
      ring
    have hmain := integral_box_variance_collision_le e horth
    have h1 : (∫ x in torusBox α, (phaseCollision e x) ^ (2 : ℕ))
        = (∫ x in torusBox α, (∑ j, ‖phaseAmp e j x‖ ^ (4 : ℕ)) ^ (2 : ℕ)) / (Fintype.card α : ℝ) ^ (4 : ℕ) := by
      rw [← integral_div]
      exact integral_congr_ae (Filter.Eventually.of_forall hsq)
    have h2 : (∫ x in torusBox α, phaseCollision e x)
        = (∫ x in torusBox α, ∑ j, ‖phaseAmp e j x‖ ^ (4 : ℕ)) / (Fintype.card α : ℝ) ^ (2 : ℕ) := by
      rw [← integral_div]
      exact integral_congr_ae (Filter.Eventually.of_forall
        fun x => phaseCollision_eq_quartic_div e x)
    rw [h1, h2, div_pow]
    have hpow : ((Fintype.card α : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) = (Fintype.card α : ℝ) ^ (4 : ℕ) := by ring
    rw [hpow, div_sub_div_same, div_le_div_iff_of_pos_right (by positivity)]
    exact hmain


/-- The collision is bounded by the family size. -/
theorem phaseCollision_le_card (e : ι → α → ℂ)
    (he : ∀ j, (∑ a, ‖e j a‖ ^ (2 : ℕ)) ≤ 1) (x : α → ℝ) :
    phaseCollision e x ≤ (Fintype.card ι : ℝ) := by
  classical
  have hterm : ∀ j : ι, finitePureStateFidelity (uniformPhaseSeed x) (e j) ^ (2 : ℕ) ≤ 1 := by
    intro j
    have h0 : 0 ≤ finitePureStateFidelity (uniformPhaseSeed x) (e j) :=
      fidelity_torusReplicaPhaseOrbit_nonneg _ _ _
    have h1 : finitePureStateFidelity (uniformPhaseSeed x) (e j) ≤ 1 :=
      fidelity_torusReplicaPhaseOrbit_le_one (fun _ => uniformPhaseWeights_nonneg _)
        sum_uniformPhaseWeights_le_one (he j) x
    nlinarith
  calc phaseCollision e x = ∑ j, finitePureStateFidelity (uniformPhaseSeed x) (e j) ^ (2 : ℕ) := rfl
    _ ≤ ∑ _j : ι, (1 : ℝ) := Finset.sum_le_sum fun j _ => hterm j
    _ = (Fintype.card ι : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem memLp_phaseCollision (e : ι → α → ℂ) (he : ∀ j, (∑ a, ‖e j a‖ ^ (2 : ℕ)) ≤ 1) :
    MemLp (phaseCollision e) 2 ((volume : Measure (α → ℝ)).restrict (torusBox α)) := by
  classical
  haveI := isFiniteMeasure_restrict_torusBox (d := α)
  have hcont : Continuous (phaseCollision e) := by
    refine continuous_finsetSum _ fun j _ => ?_
    exact (continuous_fidelity_torusReplicaPhaseOrbit _ (e j)).pow 2
  refine MemLp.of_bound hcont.aestronglyMeasurable (Fintype.card ι : ℝ) ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (phaseCollision_nonneg e x)]
  exact phaseCollision_le_card e he x

/-- **`(9)`.**  Chebyshev against the upper mean: the collision of the uniform phase seed in an
orthonormal basis exceeds `(2+κ)/D` with probability at most `96/(κ²D)`. -/
theorem measureReal_phaseCollision_gt_le (e : ι → α → ℂ)
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0)
    (hcard : Fintype.card ι = Fintype.card α) (hD : 0 < Fintype.card α) {κ : ℝ} (hκ : 0 < κ) :
    ((volume : Measure (α → ℝ)).restrict (torusBox α)).real
        {x | (2 + κ) / (Fintype.card α : ℝ) < phaseCollision e x}
      ≤ 96 / (κ ^ (2 : ℕ) * (Fintype.card α : ℝ)) := by
  classical
  haveI : IsProbabilityMeasure ((volume : Measure (α → ℝ)).restrict (torusBox α)) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_torusBox]⟩
  have hDR : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hD
  have he : ∀ j, (∑ a, ‖e j a‖ ^ (2 : ℕ)) ≤ 1 := fun j => le_of_eq (sum_normSq_of_orthonormal horth j)
  have hmem := memLp_phaseCollision e he
  have hmean : (∫ x in torusBox α, phaseCollision e x) ≤ 2 / (Fintype.card α : ℝ) := by
    have h := integral_box_phaseCollision_le e he
    rw [hcard] at h
    calc (∫ x in torusBox α, phaseCollision e x)
        ≤ 2 * (Fintype.card α : ℝ) * ((Fintype.card α : ℝ))⁻¹ ^ (2 : ℕ) := h
      _ = 2 / (Fintype.card α : ℝ) := by
          field_simp
  have hvar : Var[phaseCollision e; (volume : Measure (α → ℝ)).restrict (torusBox α)]
      ≤ 96 / (Fintype.card α : ℝ) ^ (3 : ℕ) := by
    rw [variance_eq_sub hmem]
    have h := integral_box_variance_phaseCollision_le e horth
    rw [hcard] at h
    have hpt : ∀ x : α → ℝ, ((phaseCollision e) ^ (2 : ℕ)) x = (phaseCollision e x) ^ (2 : ℕ) := fun x => rfl
    calc (∫ x in torusBox α, ((phaseCollision e) ^ (2 : ℕ)) x) -
          (∫ x in torusBox α, phaseCollision e x) ^ (2 : ℕ)
        = (∫ x in torusBox α, (phaseCollision e x) ^ (2 : ℕ)) -
          (∫ x in torusBox α, phaseCollision e x) ^ (2 : ℕ) := by
          rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      _ ≤ 96 * (Fintype.card α : ℝ) / (Fintype.card α : ℝ) ^ (4 : ℕ) := h
      _ = 96 / (Fintype.card α : ℝ) ^ (3 : ℕ) := by
          field_simp
  have hcheb := measureReal_gt_le_of_mean_le hmem hmean hvar (κ := κ / (Fintype.card α : ℝ))
    (by positivity)
  rw [← collision_threshold_split (ne_of_gt hDR)] at hcheb
  rw [collision_tail_scale hDR hκ] at hcheb
  exact hcheb

end Concentration

end

end GaloisForLFunctions.HTGeometry
