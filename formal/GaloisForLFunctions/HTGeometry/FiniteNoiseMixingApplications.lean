import GaloisForLFunctions.HTGeometry.BistochasticMixingMajorization
import GaloisForLFunctions.HTGeometry.FiniteUnitaryAdjointAutocorrelationLaw
import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedFellerAdmission
import GaloisForLFunctions.HTGeometry.SelectionSynthesisDivergence

/-!
# Noise majorization for unitary coordinates and finite group laws

Sapienza, arXiv:2608.22463v1, Appendix A identifies relative-permutation
transitions as bistochastic. This construction works for every finite group.
It also applies to the corpus's unitary diagonal coordinates and Shannon
entropy of finite probability laws. These are exact finite mixing results;
no claim about arbitrary signal-dependent observational noise is needed.
-/

open scoped BigOperators NNReal
open Matrix
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The corpus's unitary transition weights, oriented as an output-by-input matrix. -/
def finiteUnitaryMixing (U : Matrix.unitaryGroup ι ℂ) : doublyStochastic ℝ ι :=
  ⟨fun i j => finiteUnitaryEntryWeight U j i, mem_doublyStochastic_iff_sum.mpr
    ⟨fun i j => Complex.normSq_nonneg ((U : Matrix ι ι ℂ) j i), sum_finiteUnitaryEntryWeight_column U,
      sum_finiteUnitaryEntryWeight_row U⟩⟩

theorem finiteUnitaryMixing_mulVec (U : Matrix.unitaryGroup ι ℂ) (x : ι → ℝ) :
    (finiteUnitaryMixing U).val *ᵥ x = finiteUnitaryDiagonalCoordinate x U := by
  ext i
  simp only [finiteUnitaryMixing, Matrix.mulVec, dotProduct, finiteUnitaryDiagonalCoordinate]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Unitary observation majorizes every finite spectral prefix. -/
theorem finiteUnitaryDiagonalCoordinate_topSum_le {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (x : Fin n → ℝ) (k : Fin (n + 1)) :
    topSum k.val (finiteUnitaryDiagonalCoordinate x U) ≤ topSum k.val x := by
  simpa only [finiteUnitaryMixing_mulVec] using
    bistochasticMixing_topSum_le (finiteUnitaryMixing U) x k

/-- The norm lost by a diagonal observer is exactly its unresolved spectral variance. -/
theorem finiteUnitaryDiagonalCoordinate_variance_identity
    (U : Matrix.unitaryGroup ι ℂ) (x : ι → ℝ) :
    (∑ i, x i ^ 2) - (∑ i, finiteUnitaryDiagonalCoordinate x U i ^ 2) =
      ∑ i, ∑ j, finiteUnitaryEntryWeight U j i *
        (x j - finiteUnitaryDiagonalCoordinate x U i) ^ 2 := by
  have h := bistochasticMixing_variance_identity (finiteUnitaryMixing U) x
  rw [finiteUnitaryMixing_mulVec] at h
  exact h

/-- Equality classifies exactly the spectral information retained by the observer. -/
theorem finiteUnitaryDiagonalCoordinate_norm_preserved_iff
    (U : Matrix.unitaryGroup ι ℂ) (x : ι → ℝ) :
    (∑ i, finiteUnitaryDiagonalCoordinate x U i ^ 2) = (∑ i, x i ^ 2) ↔
      ∀ i j, finiteUnitaryEntryWeight U j i = 0 ∨
        x j = finiteUnitaryDiagonalCoordinate x U i := by
  have h := bistochasticMixing_sum_sq_eq_iff (finiteUnitaryMixing U) x
  rw [finiteUnitaryMixing_mulVec] at h
  exact h

/-- Diagonal unitary observation can only increase the corpus's Shannon entropy. -/
theorem entropy_le_entropy_finiteUnitaryDiagonalCoordinate
    (U : Matrix.unitaryGroup ι ℂ) (x : ι → ℝ≥0) :
    entropy (fun i => (x i : ℝ)) ≤
      entropy (finiteUnitaryDiagonalCoordinate (fun i => (x i : ℝ)) U) := by
  simpa only [entropy, tsum_fintype, Real.negMulLog, neg_mul,
    finiteUnitaryMixing_mulVec] using
    bistochasticMixing_negMulLog_sum_le (finiteUnitaryMixing U) x

namespace FiniteProbabilityLaw

/-- Bistochastic evolution preserves the actual finite probability simplex. -/
def mix (p : FiniteProbabilityLaw ι) (M : doublyStochastic ℝ ι) :
    FiniteProbabilityLaw ι where
  prob := M.val *ᵥ p.prob
  nonneg i := Finset.sum_nonneg fun j _ => mul_nonneg (M.property.1 i j) (p.nonneg j)
  sum_prob := (sum_mulVec_of_mem_doublyStochastic M.property).trans p.sum_prob

/-- Entropy is monotone for every probability law under this evolution. -/
theorem entropy_le_mix (p : FiniteProbabilityLaw ι) (M : doublyStochastic ℝ ι) :
    entropy p.prob ≤ entropy (p.mix M).prob := by
  have h := bistochasticMixing_negMulLog_sum_le M
    (fun i => (⟨p.prob i, p.nonneg i⟩ : ℝ≥0))
  change (∑ i, Real.negMulLog (p.prob i)) ≤
    ∑ i, Real.negMulLog ((M.val *ᵥ p.prob) i) at h
  simpa only [entropy, tsum_fintype, Real.negMulLog, neg_mul, mix] using h

/-- Independent successive mixing stages lose information monotonically. -/
theorem entropy_mix_le_mix_mul
    (p : FiniteProbabilityLaw ι) (M N : doublyStochastic ℝ ι) :
    entropy (p.mix M).prob ≤ entropy (p.mix (N * M)).prob := by
  simpa only [mix, Submonoid.coe_mul, Matrix.mulVec_mulVec] using
    (p.mix M).entropy_le_mix N

/-- Collision probability contracts, with the full variance deficit retained. -/
theorem collision_mix_le (p : FiniteProbabilityLaw ι) (M : doublyStochastic ℝ ι) :
    (∑ i, (p.mix M).prob i ^ 2) ≤ ∑ i, p.prob i ^ 2 :=
  bistochasticMixing_sum_sq_le M p.prob

end FiniteProbabilityLaw

section Group
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Relative-increment noise on a finite group, including ordinal permutation groups. -/
def relativeGroupNoise (p : FiniteProbabilityLaw G) : doublyStochastic ℝ G := by
  refine ⟨fun i j => p.prob (i * j⁻¹), mem_doublyStochastic_iff_sum.mpr
    ⟨fun i j => p.nonneg _, ?_, ?_⟩⟩
  · intro i
    exact ((Equiv.inv G |>.trans (Equiv.mulLeft i)).sum_comp p.prob).trans p.sum_prob
  · intro j
    exact (Equiv.sum_comp (Equiv.mulRight j⁻¹) p.prob).trans p.sum_prob

/-- A noisy group law is literally the group convolution of two finite laws. -/
theorem relativeGroupNoise_prob (p q : FiniteProbabilityLaw G) (i : G) :
    (q.mix (relativeGroupNoise p)).prob i = ∑ j, p.prob (i * j⁻¹) * q.prob j := rfl

/-- Relative-permutation noise increases the existing discrete Shannon entropy. -/
theorem entropy_le_relativeGroupNoise (p q : FiniteProbabilityLaw G) :
    entropy q.prob ≤ entropy (q.mix (relativeGroupNoise p)).prob :=
  q.entropy_le_mix (relativeGroupNoise p)

/-- All convex permutation witnesses exist for the noisy group law. -/
theorem relativeGroupNoise_permutation_decomposition (p q : FiniteProbabilityLaw G) :
    ∃ w : Equiv.Perm G → ℝ, (∀ e, 0 ≤ w e) ∧ ∑ e, w e = 1 ∧
      (q.mix (relativeGroupNoise p)).prob = ∑ e, w e • (q.prob ∘ e) :=
  bistochasticMixing_permutation_decomposition (relativeGroupNoise p) q.prob

/-- Independent noise contracts distinguishability of any two input group laws. -/
theorem relativeGroupNoise_totalVariation_le (p q r : FiniteProbabilityLaw G) :
    (∑ i, |(q.mix (relativeGroupNoise p)).prob i -
      (r.mix (relativeGroupNoise p)).prob i|) ≤ ∑ i, |q.prob i - r.prob i| :=
  bistochasticMixing_abs_sub_sum_le (relativeGroupNoise p) q.prob r.prob

end Group
end
end GaloisForLFunctions.HTGeometry
