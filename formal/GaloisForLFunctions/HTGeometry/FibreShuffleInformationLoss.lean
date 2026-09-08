import GaloisForLFunctions.HTGeometry.FiniteNoiseMixingApplications
import GaloisForLFunctions.RHTower.RouteEUniformFibreShuffle

/-!
# Exact information loss under the corpus's uniform fibre shuffle

Sapienza, arXiv:2608.22463v1, Appendix A supplies a transferable bistochastic
mixing argument. Here the matrix is the existing uniform resampling kernel of
`RouteEUniformFibreShuffle`. Its information loss is exactly within-label
variation: quadratic mass is preserved precisely for label-constant input.
The kernel and its normalization are taken from the corpus, not assumed.
-/

open scoped BigOperators NNReal
open Matrix RHTower
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {Ω Λ : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω] [DecidableEq Λ]

/-- The existing uniform fibre kernel as an actual bistochastic matrix. -/
def fibreShuffleMixing (label : Ω → Λ) : doublyStochastic ℝ Ω :=
  ⟨routeEUniformFibreKernel label, mem_doublyStochastic_iff_sum.mpr
    ⟨routeEUniformFibreKernel_nonneg label,
      routeEUniformFibreKernel_row_sum label, routeEUniformFibreKernel_column_sum label⟩⟩

/-- A positive entry records exactly membership in the same label fibre. -/
theorem fibreShuffleMixing_pos_iff (label : Ω → Λ) (i j : Ω) :
    0 < (fibreShuffleMixing label).val i j ↔ label i = label j := by
  change 0 < routeEUniformFibreKernel label i j ↔ _
  simp only [routeEUniformFibreKernel]
  split_ifs with h
  · simp only [h, iff_true]
    exact div_pos zero_lt_one (by exact_mod_cast routeEUniformFibre_card_pos label i)
  · simp only [lt_self_iff_false, false_iff]
    exact h

/-- Every shuffled value is constant along its label fibre. -/
theorem fibreShuffleMixing_same_label (label : Ω → Λ) (v : Ω → ℝ) :
    ∀ i j, label i = label j →
      ((fibreShuffleMixing label).val *ᵥ v) i = ((fibreShuffleMixing label).val *ᵥ v) j := by
  intro i j h
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact (routeEUniformFibreKernel_eq_of_same_source_label label h k).symm

/-- Fixed data are exactly those already constant on each label class. -/
theorem fibreShuffleMixing_fixed_iff (label : Ω → Λ) (v : Ω → ℝ) :
    (fibreShuffleMixing label).val *ᵥ v = v ↔
      ∀ i j, label i = label j → v i = v j := by
  constructor
  · intro h
    have he := fibreShuffleMixing_same_label label v
    rwa [h] at he
  · intro h
    ext i
    change (∑ j, routeEUniformFibreKernel label i j * v j) = v i
    calc
      _ = ∑ j, routeEUniformFibreKernel label i j * v i := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : label i = label j
        · rw [h i j hij]
        · simp only [routeEUniformFibreKernel, if_neg hij, zero_mul]
      _ = v i := by rw [← Finset.sum_mul, routeEUniformFibreKernel_row_sum, one_mul]

/-- A second shuffle removes no further information. -/
theorem fibreShuffleMixing_idempotent (label : Ω → Λ) (v : Ω → ℝ) :
    (fibreShuffleMixing label).val *ᵥ ((fibreShuffleMixing label).val *ᵥ v) =
      (fibreShuffleMixing label).val *ᵥ v :=
  (fibreShuffleMixing_fixed_iff label _).mpr (fibreShuffleMixing_same_label label v)

/-- The amount removed is the exact sum of within-fibre conditional variances. -/
theorem fibreShuffleMixing_variance_identity (label : Ω → Λ) (v : Ω → ℝ) :
    (∑ i, v i ^ 2) - (∑ i, ((fibreShuffleMixing label).val *ᵥ v) i ^ 2) =
      ∑ i, ∑ j, routeEUniformFibreKernel label i j *
        (v j - ((fibreShuffleMixing label).val *ᵥ v) i) ^ 2 :=
  bistochasticMixing_variance_identity (fibreShuffleMixing label) v

/-- No quadratic information is lost exactly when there is no within-label variation. -/
theorem fibreShuffleMixing_quadratic_eq_iff (label : Ω → Λ) (v : Ω → ℝ) :
    (∑ i, ((fibreShuffleMixing label).val *ᵥ v) i ^ 2) = (∑ i, v i ^ 2) ↔
      ∀ i j, label i = label j → v i = v j := by
  constructor
  · intro he
    have hr := (bistochasticMixing_sum_sq_eq_iff (fibreShuffleMixing label) v).mp he
    intro i j hij
    have hi := (hr i i).resolve_left
      (ne_of_gt ((fibreShuffleMixing_pos_iff label i i).mpr rfl))
    have hj := (hr i j).resolve_left
      (ne_of_gt ((fibreShuffleMixing_pos_iff label i j).mpr hij))
    exact hi.trans hj.symm
  · intro h
    rw [(fibreShuffleMixing_fixed_iff label v).mpr h]

/-- Every finite probability law gains Shannon entropy under the actual fibre shuffle. -/
theorem fibreShuffleMixing_entropy_le (label : Ω → Λ) (p : FiniteProbabilityLaw Ω) :
    entropy p.prob ≤ entropy (p.mix (fibreShuffleMixing label)).prob :=
  p.entropy_le_mix (fibreShuffleMixing label)

/-- Differences between two inputs contract under the same label observation. -/
theorem fibreShuffleMixing_totalVariation_le (label : Ω → Λ) (v w : Ω → ℝ) :
    (∑ i, |((fibreShuffleMixing label).val *ᵥ v) i -
      ((fibreShuffleMixing label).val *ᵥ w) i|) ≤ ∑ i, |v i - w i| :=
  bistochasticMixing_abs_sub_sum_le (fibreShuffleMixing label) v w

/-- All sorted partial sums decrease under the existing finite fibre shuffle. -/
theorem fibreShuffleMixing_topSum_le {n : ℕ} [Nonempty (Fin n)]
    (label : Fin n → Λ) (v : Fin n → ℝ) (k : Fin (n + 1)) :
    topSum k.val ((fibreShuffleMixing label).val *ᵥ v) ≤ topSum k.val v :=
  bistochasticMixing_topSum_le (fibreShuffleMixing label) v k

end
end GaloisForLFunctions.HTGeometry
