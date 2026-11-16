import GaloisForLFunctions.HTGeometry.CharacteristicFunctionPositiveDefinite
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.MixtureRigidity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-!
# Gaussian cluster aging and inter-cluster dispersion

A finite nonnegative mixture of shifted Gaussian characteristic functions is
a valid temporal correlation kernel. Its second-moment defect separates into
intra-cluster variance and pairwise dispersion of cluster means. This applies
the geometry-dependent correlation model of arXiv:2611.08007, equation (12),
to the corpus's positive-definite kernels and character-mixture rigidity.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.SymmetricCharacters

namespace HilbertMetric.Correlation
variable {ι : Type*} [Fintype ι]

/-- The continuous temporal kernel of finitely many Doppler clusters. -/
def dopplerClusterKernel (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal)
    (t : ℝ) : ℂ :=
  ∑ i, (w i : ℂ) * Complex.exp
    ((t : ℂ) * mean i * Complex.I - (variance i : ℂ) * (t : ℂ) ^ 2 / 2)

/-- Every cluster is an actual Gaussian spectral measure. -/
theorem dopplerClusterKernel_eq_charFun_sum (w : ι → NNReal)
    (mean : ι → ℝ) (variance : ι → NNReal) (t : ℝ) :
    dopplerClusterKernel w mean variance t =
      ∑ i, (w i : ℂ) * charFun (gaussianReal (mean i) (variance i)) t := by
  simp only [dopplerClusterKernel, charFun_gaussianReal]

/-- Gaussian cluster aging gives positive semidefinite correlations at all sampling times. -/
theorem dopplerClusterKernel_positiveDefinite (w : ι → NNReal)
    (mean : ι → ℝ) (variance : ι → NNReal) :
    PositiveDefiniteOnReal (dopplerClusterKernel w mean variance) := by
  intro N t c
  classical
  choose r hr he using fun i : ι =>
    positiveDefiniteOnReal_charFun (gaussianReal (mean i) (variance i)) N t c
  refine ⟨∑ i, (w i : ℝ) * r i,
    Finset.sum_nonneg (fun i _ => mul_nonneg (w i).coe_nonneg (hr i)), ?_⟩
  simp only [dopplerClusterKernel_eq_charFun_sum, Finset.mul_sum, Finset.sum_mul,
    Complex.ofReal_sum, Complex.ofReal_mul]
  calc
    _ = ∑ k, (w k : ℂ) *
        (∑ i, ∑ j, star (c i) * charFun (gaussianReal (mean k) (variance k))
          (t j - t i) * c j) := by
      calc
        _ = ∑ i, ∑ k, ∑ j, star (c i) *
            ((w k : ℂ) * charFun (gaussianReal (mean k) (variance k))
              (t j - t i)) * c j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = _ := ?_
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp only [he]

/-- Total mass times the second moment minus the squared first moment. -/
def dopplerAgingDefect (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal) : ℝ :=
  (∑ i, (w i : ℝ)) * (∑ i, (w i : ℝ) * (mean i ^ 2 + variance i)) -
    (∑ i, (w i : ℝ) * mean i) ^ 2

/-- The aging defect is intrinsic spread plus the existing character-mixture defect. -/
theorem dopplerAgingDefect_decomposition (w : ι → NNReal)
    (mean : ι → ℝ) (variance : ι → NNReal) :
    dopplerAgingDefect w mean variance =
      (∑ i, (w i : ℝ)) * (∑ i, (w i : ℝ) * variance i) + mixtureDefect w mean := by
  simp only [dopplerAgingDefect, mixtureDefect, mul_add, Finset.sum_add_distrib]
  ring

/-- Independent cluster spreads and pairwise mean differences both cause aging. -/
theorem two_mul_dopplerAgingDefect (w : ι → NNReal)
    (mean : ι → ℝ) (variance : ι → NNReal) :
    2 * dopplerAgingDefect w mean variance =
      2 * (∑ i, (w i : ℝ)) * (∑ i, (w i : ℝ) * variance i) +
        ∑ i, ∑ j, (w i : ℝ) * (w j : ℝ) * (mean i - mean j) ^ 2 := by
  rw [dopplerAgingDefect_decomposition, mul_add, two_mul_mixtureDefect]
  ring

/-- Mixing cannot reduce the contribution of the intrinsic cluster spreads. -/
theorem dopplerAgingDefect_intrinsic_le (w : ι → NNReal)
    (mean : ι → ℝ) (variance : ι → NNReal) :
    (∑ i, (w i : ℝ)) * (∑ i, (w i : ℝ) * variance i) ≤
      dopplerAgingDefect w mean variance := by
  rw [dopplerAgingDefect_decomposition]
  exact le_add_of_nonneg_right (mixtureDefect_nonneg w mean)

/-- Zero aging means every occupied cluster is monochromatic with a common mean. -/
theorem dopplerAgingDefect_eq_zero_iff (w : ι → NNReal)
    (mean : ι → ℝ) (variance : ι → NNReal) :
    dopplerAgingDefect w mean variance = 0 ↔
      (∀ i, w i = 0 ∨ variance i = 0) ∧
      (∀ i j, w i = 0 ∨ w j = 0 ∨ mean i = mean j) := by
  have hmass : 0 ≤ ∑ i, (w i : ℝ) := Finset.sum_nonneg fun i _ => (w i).coe_nonneg
  have hv : 0 ≤ ∑ i, (w i : ℝ) * variance i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (w i).coe_nonneg (variance i).coe_nonneg
  have hprod (i : ι) : 0 ≤ (w i : ℝ) * variance i :=
    mul_nonneg (w i).coe_nonneg (variance i).coe_nonneg
  rw [dopplerAgingDefect_decomposition,
    add_eq_zero_iff_of_nonneg (mul_nonneg hmass hv) (mixtureDefect_nonneg w mean),
    mixtureDefect_eq_zero_iff]
  apply and_congr_left
  intro _
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hzero | hzero
    · have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => (w i).coe_nonneg)).mp hzero
      intro i
      exact Or.inl (NNReal.coe_eq_zero.mp (hz i (Finset.mem_univ i)))
    · have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hprod i)).mp hzero
      intro i
      simpa only [mul_eq_zero, NNReal.coe_eq_zero] using hz i (Finset.mem_univ i)
  · intro h
    have hz : ∑ i, (w i : ℝ) * variance i = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rcases h i with hi | hi <;> simp only [hi, NNReal.coe_zero, zero_mul, mul_zero]
    rw [hz, mul_zero]

end HilbertMetric.Correlation

