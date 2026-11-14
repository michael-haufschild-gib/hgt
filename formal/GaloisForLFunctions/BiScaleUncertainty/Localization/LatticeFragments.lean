import GaloisForLFunctions.RHTower.Deninger.DeningerPeriodizationSplit
import Mathlib.Data.NNReal.Basic

/-!
# Exact finite lattice fragmentation of compact sources

A fixed smooth lattice partition of unity gives fragments at every reciprocal
scale. A source restricted to `[-A,A]` has an exact finite decomposition with
indices `|j| ≤ ceil(A(m+1)+3)`. Each fragment has support width `6/(m+1)`.
The partition is taken from the existing smooth periodization splitting;
no approximation of the source is involved.
-/

noncomputable section
open Set Filter RHTower
open scoped NNReal
namespace GaloisForLFunctions.BiScaleUncertainty

/-- A compact lattice fragment at reciprocal scale `m+1`. -/
def latticeFragment (m : ℕ) (j : ℤ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x * deningerPartitionUnity 1 (((m : ℝ) + 1) * x + j)

private theorem unitPartition_eq_zero {x : ℝ} (hx : 3 ≤ |x|) :
    deningerPartitionUnity 1 x = 0 := by
  have hb : (deningerPartitionBump 1 : ℝ → ℝ) x = 0 :=
    (deningerPartitionBump 1).zero_of_le_dist (by
      simpa only [deningerPartitionBump_rOut, abs_one, Real.dist_eq, sub_zero] using hx)
  simp only [deningerPartitionUnity, hb, zero_mul]

/-- Lattice fragmentation reconstructs every source pointwise. -/
theorem tsum_latticeFragment (m : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (∑' j : ℤ, latticeFragment m j f x) = f x := by
  unfold latticeFragment
  rw [tsum_mul_left]
  have h := deningerPartitionUnity_tsum (by norm_num : (0 : ℝ) < 1)
    (((m : ℝ) + 1) * x)
  simp only [mul_one] at h
  rw [h, mul_one]

/-- Each lattice fragment lies in an explicitly located interval of width `6/(m+1)`. -/
theorem latticeFragment_eq_zero_of_outside (m : ℕ) (j : ℤ) (f : ℝ → ℝ) (x : ℝ)
    (hx : x ∉ Icc ((-(j : ℝ) - 3) / (m + 1)) ((-(j : ℝ) + 3) / (m + 1))) :
    latticeFragment m j f x = 0 := by
  have hm : 0 < (m : ℝ) + 1 := by positivity
  have hshift : 3 ≤ |((m : ℝ) + 1) * x + j| := by
    by_contra h
    have hh := abs_lt.mp (lt_of_not_ge h)
    apply hx
    constructor
    · apply (div_le_iff₀ hm).mpr
      linarith only [hh.1]
    · apply (le_div_iff₀ hm).mpr
      linarith only [hh.2]
  rw [latticeFragment, unitPartition_eq_zero hshift, mul_zero]

/-- Smooth sources have smooth fragments at every scale. -/
theorem contDiff_latticeFragment (m : ℕ) (j : ℤ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (latticeFragment m j f) := by
  apply hf.mul
  exact (deningerPartitionUnity_contDiff (by norm_num : (0 : ℝ) < 1)).comp
    ((contDiff_const.mul contDiff_id).add contDiff_const)

/-- A restricted source needs only linearly many lattice indices in its reciprocal scale. -/
theorem latticeFragment_interval_eq_zero (A : ℝ≥0) (m : ℕ) (f : ℝ → ℝ) (j : ℤ)
    (hj : j ∉ Finset.Icc (-(⌈(A : ℝ) * (m + 1) + 3⌉₊ : ℤ))
      (⌈(A : ℝ) * (m + 1) + 3⌉₊ : ℤ)) (x : ℝ) :
    latticeFragment m j ((Icc (-(A : ℝ)) A).indicator f) x = 0 := by
  by_contra hne
  have hx : x ∈ Icc (-(A : ℝ)) A := by
    by_contra hx
    exact hne (by simp only [latticeFragment, indicator_of_notMem hx, zero_mul])
  have hshift : |((m : ℝ) + 1) * x + j| < 3 := by
    apply lt_of_not_ge
    intro h
    exact hne (by rw [latticeFragment, unitPartition_eq_zero h, mul_zero])
  have hbounds := abs_lt.mp hshift
  have hm : 0 ≤ (m : ℝ) + 1 := by positivity
  have hlo := mul_le_mul_of_nonneg_left hx.1 hm
  have hhi := mul_le_mul_of_nonneg_left hx.2 hm
  have hceil : (A : ℝ) * (m + 1) + 3 ≤ (⌈(A : ℝ) * (m + 1) + 3⌉₊ : ℝ) :=
    Nat.le_ceil _
  apply hj
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast (show -(⌈(A : ℝ) * (m + 1) + 3⌉₊ : ℝ) ≤ (j : ℝ) by
      nlinarith only [hhi, hbounds.1, hceil])
  · exact_mod_cast (show (j : ℝ) ≤ (⌈(A : ℝ) * (m + 1) + 3⌉₊ : ℝ) by
      nlinarith only [hlo, hbounds.2, hceil])

/-- Exact finite reconstruction of every restricted source. -/
theorem sum_latticeFragment_interval (A : ℝ≥0) (m : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (∑ j ∈ Finset.Icc (-(⌈(A : ℝ) * (m + 1) + 3⌉₊ : ℤ))
      (⌈(A : ℝ) * (m + 1) + 3⌉₊ : ℤ),
      latticeFragment m j ((Icc (-(A : ℝ)) A).indicator f) x) =
        (Icc (-(A : ℝ)) A).indicator f x := by
  rw [← tsum_latticeFragment m ((Icc (-(A : ℝ)) A).indicator f) x]
  exact (tsum_eq_sum fun j hj => latticeFragment_interval_eq_zero A m f j hj x).symm

end GaloisForLFunctions.BiScaleUncertainty
