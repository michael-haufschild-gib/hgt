import GaloisForLFunctions.HTGeometry.ReturnExcisedPhaseIncidenceLaw

/-!
# Collision moments of a uniform phase seed

The equal-amplitude seed with independent uniform coordinate phases is the phase orbit of the
uniform spectral weight.  Its pairing with any fixed subunit vector therefore obeys the replica
moment bound of the occupation expansion: the `r`-th moment of the squared pairing is at most
`r!` times the `r`-th power of the uniform weight.  Summing the second moment over an orthonormal
family bounds the mean spectral collision of the seed in an arbitrary basis by twice the ratio of
the family size to the squared dimension.
-/

open MeasureTheory Complex UnitAddTorus Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance phaseSeedCollisionMomentsMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance phaseSeedCollisionMomentsIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance phaseSeedCollisionMomentsIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The uniform spectral weight of a finite index set. -/
def uniformPhaseWeights (α : Type*) [Fintype α] : α → ℝ := fun _ => ((Fintype.card α : ℝ))⁻¹

theorem uniformPhaseWeights_nonneg (j : α) : 0 ≤ uniformPhaseWeights α j := by
  simp only [uniformPhaseWeights]
  positivity

theorem sum_uniformPhaseWeights_le_one : (∑ j, uniformPhaseWeights α j) ≤ 1 := by
  simp only [uniformPhaseWeights]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h | h
  · rw [h]
    norm_num
  · have hpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast h
    rw [mul_inv_cancel₀ (ne_of_gt hpos)]

/-- The equal-amplitude seed with independent uniform coordinate phases. -/
def uniformPhaseSeed (x : α → ℝ) : α → ℂ := torusReplicaPhaseOrbit (uniformPhaseWeights α) x

/-- **Replica moments of the uniform phase seed.**  The `r`-th moment of the squared pairing with
any subunit vector is at most `r!` times the `r`-th power of the uniform weight. -/
theorem integral_box_fidelity_uniformPhaseSeed_pow_le {z : α → ℂ}
    (hz : (∑ a, ‖z a‖ ^ (2 : ℕ)) ≤ 1) (r : ℕ) :
    (∫ x in torusBox α, finitePureStateFidelity (uniformPhaseSeed x) z ^ r) ≤
      (r.factorial : ℝ) * ((Fintype.card α : ℝ))⁻¹ ^ r :=
  integral_box_fidelity_pow_le (fun _ => uniformPhaseWeights_nonneg _)
    (τ := ((Fintype.card α : ℝ))⁻¹) (fun _ => le_of_eq rfl) (by positivity) hz r

/-- **Fourth phase moment.**  Two is the number of index pairings. -/
theorem integral_box_fidelity_uniformPhaseSeed_sq_le {z : α → ℂ}
    (hz : (∑ a, ‖z a‖ ^ (2 : ℕ)) ≤ 1) :
    (∫ x in torusBox α, finitePureStateFidelity (uniformPhaseSeed x) z ^ (2 : ℕ)) ≤
      2 * ((Fintype.card α : ℝ))⁻¹ ^ (2 : ℕ) := by
  have h := integral_box_fidelity_uniformPhaseSeed_pow_le hz 2
  norm_num at h
  rw [inv_pow]
  exact h

/-- **Sixth phase moment.**  Six is the number of index triple pairings. -/
theorem integral_box_fidelity_uniformPhaseSeed_cube_le {z : α → ℂ}
    (hz : (∑ a, ‖z a‖ ^ (2 : ℕ)) ≤ 1) :
    (∫ x in torusBox α, finitePureStateFidelity (uniformPhaseSeed x) z ^ (3 : ℕ)) ≤
      6 * ((Fintype.card α : ℝ))⁻¹ ^ (3 : ℕ) := by
  have h := integral_box_fidelity_uniformPhaseSeed_pow_le hz 3
  norm_num at h
  rw [inv_pow]
  exact h

/-- The spectral collision of the uniform phase seed in a given family. -/
def phaseCollision {ι : Type*} [Fintype ι] (e : ι → α → ℂ) (x : α → ℝ) : ℝ :=
  ∑ j, finitePureStateFidelity (uniformPhaseSeed x) (e j) ^ (2 : ℕ)

theorem phaseCollision_nonneg {ι : Type*} [Fintype ι] (e : ι → α → ℂ) (x : α → ℝ) :
    0 ≤ phaseCollision e x :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem integrableOn_box_fidelity_uniformPhaseSeed_pow {z : α → ℂ}
    (hz : (∑ a, ‖z a‖ ^ (2 : ℕ)) ≤ 1) (r : ℕ) :
    IntegrableOn (fun x => finitePureStateFidelity (uniformPhaseSeed x) z ^ r)
      (torusBox α) volume :=
  integrableOn_box_fidelity_pow (fun _ => uniformPhaseWeights_nonneg _)
    sum_uniformPhaseWeights_le_one hz r

/-- **Mean spectral collision of a uniform phase seed.**  Against any orthonormal family the mean
collision is at most twice the family size over the squared dimension; at family size the
dimension this is `2 / D`. -/
theorem integral_box_phaseCollision_le {ι : Type*} [Fintype ι] (e : ι → α → ℂ)
    (he : ∀ j, (∑ a, ‖e j a‖ ^ (2 : ℕ)) ≤ 1) :
    (∫ x in torusBox α, phaseCollision e x) ≤
      2 * (Fintype.card ι : ℝ) * ((Fintype.card α : ℝ))⁻¹ ^ (2 : ℕ) := by
  classical
  simp only [phaseCollision]
  rw [integral_finsetSum _ fun j _ => integrableOn_box_fidelity_uniformPhaseSeed_pow (he j) 2]
  calc (∑ j : ι, ∫ x in torusBox α, finitePureStateFidelity (uniformPhaseSeed x) (e j) ^ (2 : ℕ))
      ≤ ∑ _j : ι, 2 * ((Fintype.card α : ℝ))⁻¹ ^ (2 : ℕ) :=
        Finset.sum_le_sum fun j _ => integral_box_fidelity_uniformPhaseSeed_sq_le (he j)
    _ = 2 * (Fintype.card ι : ℝ) * ((Fintype.card α : ℝ))⁻¹ ^ (2 : ℕ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        ring

end GaloisForLFunctions.HTGeometry
