import GaloisForLFunctions.HTGeometry.AltynbekovSelfConsistentGroupTransfer
import GaloisForLFunctions.HTGeometry.LotzSpectralTailStatistics
import GaloisForLFunctions.HTGeometry.CanaryKimExtremalConcentration

/-!
# Entropy, spectral order and concentration along nonlinear group transfer

The finite-group model inspired by Altynbekov–Olimov–Ruziboev (arXiv:2609.10119)
selects a bistochastic kernel from its current law. This connects it to the
coefficient-tail tests inspired by Lotz (arXiv:2609.09335) and to the extremal
support mechanism in Canary–Kim (arXiv:2609.10325). The statements concern this
concrete finite model; they do not assert the papers' geometric or Sobolev results.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators NNReal
open Matrix
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The nonlinear transfer selects an actual bistochastic kernel from its current law. -/
def selfConsistentRefreshKernel (r : ℝ) (p : FiniteProbabilityLaw G) : doublyStochastic ℝ G := by
  refine ⟨fun i j => refreshRate r * (relativeGroupNoise p).val i j +
    (1-refreshRate r) * (uniformNoiseMatrix (ι := G)).val i j,
    mem_doublyStochastic_iff_sum.mpr ⟨?_,?_,?_⟩⟩
  · intro i j
    exact add_nonneg (mul_nonneg (refreshRate_pos r).le ((relativeGroupNoise p).property.1 i j))
      (mul_nonneg (sub_nonneg.mpr (refreshRate_lt_one r).le) (uniformNoiseMatrix.property.1 i j))
  · intro i
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_row_of_mem_doublyStochastic (relativeGroupNoise p).property,
      sum_row_of_mem_doublyStochastic uniformNoiseMatrix.property]
    ring
  · intro j
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_col_of_mem_doublyStochastic (relativeGroupNoise p).property,
      sum_col_of_mem_doublyStochastic uniformNoiseMatrix.property]
    ring

theorem selfConsistentRefreshKernel_action (r : ℝ) (p : FiniteProbabilityLaw G) :
    (p.mix (selfConsistentRefreshKernel r p)).prob = (selfConsistentRefreshAt r p).prob := by
  funext i
  change (∑ j, (refreshRate r*(relativeGroupNoise p).val i j+
    (1-refreshRate r)*(uniformNoiseMatrix (ι := G)).val i j)*p.prob j) = _
  simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  change refreshRate r*(p.mix (relativeGroupNoise p)).prob i +
    (1-refreshRate r)*(p.mix uniformNoiseMatrix).prob i = _
  rw [mix_uniformNoise_prob]
  rfl

/-- The original Shannon entropy increases under the genuinely nonlinear evolution. -/
theorem selfConsistentRefreshAt_entropy (r : ℝ) (p : FiniteProbabilityLaw G) :
    entropy p.prob ≤ entropy (selfConsistentRefreshAt r p).prob := by
  have h := p.entropy_le_mix (selfConsistentRefreshKernel r p)
  rwa [selfConsistentRefreshKernel_action] at h

theorem selfConsistentRefreshAtOrbit_entropy_monotone (r : ℝ) (p : FiniteProbabilityLaw G) :
    Monotone (fun n => entropy (selfConsistentRefreshAtOrbit r p n).prob) := by
  apply monotone_nat_of_le_succ
  intro n
  exact selfConsistentRefreshAt_entropy r (selfConsistentRefreshAtOrbit r p n)

/-- A canonical finite indexing lets spectral statistics apply to any finite group. -/
def indexedGroupLaw (p : FiniteProbabilityLaw G) : Fin (Fintype.card G) → ℝ :=
  fun i => p.prob ((Fintype.equivFin G).symm i)

/-- Bistochastic kernels retain both marginals under the same finite indexing. -/
def indexedGroupKernel (M : doublyStochastic ℝ G) : doublyStochastic ℝ (Fin (Fintype.card G)) := by
  let e := (Fintype.equivFin G).symm
  refine ⟨fun i j => M.val (e i) (e j), mem_doublyStochastic_iff_sum.mpr ⟨?_,?_,?_⟩⟩
  · intro i j
    exact M.property.1 _ _
  · intro i
    exact (Equiv.sum_comp e (fun j => M.val (e i) j)).trans
      (sum_row_of_mem_doublyStochastic M.property (e i))
  · intro j
    exact (Equiv.sum_comp e (fun i => M.val i (e j))).trans
      (sum_col_of_mem_doublyStochastic M.property (e j))

omit [Group G] in
theorem indexedGroupKernel_action (M : doublyStochastic ℝ G) (p : FiniteProbabilityLaw G) :
    (indexedGroupKernel M).val *ᵥ indexedGroupLaw p = indexedGroupLaw (p.mix M) := by
  funext i
  exact Equiv.sum_comp (Fintype.equivFin G).symm
    (fun j => M.val ((Fintype.equivFin G).symm i) j * p.prob j)

/-- Every Lotz-type spectral test decreases along the nonlinear group transfer. -/
theorem selfConsistentRefreshAt_spectral (r : ℝ) (p : FiniteProbabilityLaw G)
    (a : ℝ) (c : Fin (Fintype.card G+1) → ℝ≥0) :
    lotzSpectralStatistic a c (indexedGroupLaw (selfConsistentRefreshAt r p)) ≤
      lotzSpectralStatistic a c (indexedGroupLaw p) := by
  have h := lotzSpectralStatistic_mixing_le (indexedGroupKernel (selfConsistentRefreshKernel r p))
    (indexedGroupLaw p) a c
  rw [indexedGroupKernel_action] at h
  have hi : indexedGroupLaw (p.mix (selfConsistentRefreshKernel r p)) =
      indexedGroupLaw (selfConsistentRefreshAt r p) :=
    congrArg (fun f : G → ℝ => fun i : Fin (Fintype.card G) => f ((Fintype.equivFin G).symm i))
      (selfConsistentRefreshKernel_action r p)
  rwa [hi] at h

/-- An exact positive lower bound on every refreshed population. -/
theorem selfConsistentRefreshAt_probability_floor (r : ℝ) (p : FiniteProbabilityLaw G) (i : G) :
    (1-refreshRate r)*(Fintype.card G : ℝ)⁻¹ ≤ (selfConsistentRefreshAt r p).prob i := by
  exact le_add_of_nonneg_left (mul_nonneg (refreshRate_pos r).le
    ((p.mix (relativeGroupNoise p)).nonneg i))

theorem selfConsistentRefreshAt_probability_pos (r : ℝ) (p : FiniteProbabilityLaw G) (i : G) :
    0 < (selfConsistentRefreshAt r p).prob i := by
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  exact (mul_pos (sub_pos.mpr (refreshRate_lt_one r)) (inv_pos.mpr hc)).trans_le
    (selfConsistentRefreshAt_probability_floor r p i)

/-- Refresh destroys exact extremal concentration unless the whole source maximizes. -/
theorem selfConsistentRefreshAt_extremal_iff (r : ℝ) (p : FiniteProbabilityLaw G) (x : G → ℝ) :
    (∑ i, (selfConsistentRefreshAt r p).prob i*x i) = canaryKimMaxRate x ↔
      ∀ i, x i = canaryKimMaxRate x := by
  rw [canaryKim_maximizing_support_iff]
  simp only [(selfConsistentRefreshAt_probability_pos r p _).ne', false_or]

/-- Exact extremal-defect decomposition separates self-convolution and uniform refresh. -/
theorem selfConsistentRefreshAt_extremal_defect (r : ℝ) (p : FiniteProbabilityLaw G) (x : G → ℝ) :
    canaryKimMaxRate x-(∑ i, (selfConsistentRefreshAt r p).prob i*x i) =
      refreshRate r*(canaryKimMaxRate x-∑ i, (p.mix (relativeGroupNoise p)).prob i*x i) +
      (1-refreshRate r)*(canaryKimMaxRate x-∑ i, (uniformNoiseLaw (ι := G)).prob i*x i) := by
  simp_rw [canaryKim_mean_defect]
  simp only [selfConsistentRefreshAt, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

/-- Uniform refresh imposes a source-dependent deficit floor for every initial law. -/
theorem selfConsistentRefreshAt_extremal_floor (r : ℝ) (p : FiniteProbabilityLaw G) (x : G → ℝ) :
    (1-refreshRate r)*(canaryKimMaxRate x-∑ i, (uniformNoiseLaw (ι := G)).prob i*x i) ≤
      canaryKimMaxRate x-∑ i, (selfConsistentRefreshAt r p).prob i*x i := by
  rw [selfConsistentRefreshAt_extremal_defect]
  apply le_add_of_nonneg_left
  apply mul_nonneg (refreshRate_pos r).le
  rw [canaryKim_mean_defect]
  exact Finset.sum_nonneg fun i _ => mul_nonneg ((p.mix (relativeGroupNoise p)).nonneg i)
    (sub_nonneg.mpr (canaryKimRate_le_max x i))

end GaloisForLFunctions.HTGeometry
