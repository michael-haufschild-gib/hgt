import GaloisForLFunctions.HTGeometry.BoundedReplicaThresholdProjector
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef

/-!
# Amplified generative admission

This file certifies two exact finite cores of amplified generative-response mechanics.

* A positive rank-one pencil has sharp admission threshold equal to its rank-one weight.  This is
  the spectral calculation underlying the Choi matrix of the reduction map.
* The reduction threshold profile `min n k` is bounded at every fixed amplification depth while
  its complete diagonal profile is cofinally unbounded.

No arithmetic or RH statement is used.
-/

open Finset Matrix
open scoped ComplexConjugate ComplexOrder MatrixOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rank-one admission pencil with base weight `c` and obstructing weight `r`. -/
def rankOneAdmissionPencil (z : ι → ℂ) (r c : ℝ) : Matrix ι ι ℂ :=
  c • (1 : Matrix ι ι ℂ) - r • rankOne z

omit [DecidableEq ι] in
private theorem quadForm_sub_for_admission (M N : Matrix ι ι ℂ) (z : ι → ℂ) :
    quadForm (M - N) z = quadForm M z - quadForm N z := by
  simp only [quadForm_eq_sum, Matrix.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [DecidableEq ι] in
private theorem quadForm_real_smul_for_admission (a : ℝ) (M : Matrix ι ι ℂ) (z : ι → ℂ) :
    quadForm (a • M) z = (a : ℂ) * quadForm M z := by
  simp only [quadForm_eq_sum, Matrix.smul_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.real_smul]
  ring

/-- The orthogonal complement of a normalized rank-one ray is positive semidefinite. -/
theorem one_sub_rankOne_posSemidef {z : ι → ℂ} (hz : hermInner z z = 1) :
    ((1 : Matrix ι ι ℂ) - rankOne z).PosSemidef := by
  let A : Matrix ι ι ℂ := 1 - rankOne z
  have hherm : Aᴴ = A := by
    simp [A, rankOne_conjTranspose]
  have hidem : A * A = A := by
    simp only [A]
    rw [sub_mul, mul_sub, mul_sub]
    simp only [one_mul, mul_one]
    rw [rankOne_mul_rankOne hz]
    abel
  have h := Matrix.posSemidef_conjTranspose_mul_self A
  rw [hherm, hidem] at h
  exact h

/-- **Sharp rank-one admission law.**  A normalized rank-one obstruction of weight `r > 0`
is absorbed by the positive identity ray exactly when the identity coefficient is at least `r`. -/
theorem rankOneAdmissionPencil_posSemidef_iff {z : ι → ℂ} (hz : hermInner z z = 1)
    {r c : ℝ} (hr : 0 < r) :
    (rankOneAdmissionPencil z r c).PosSemidef ↔ r ≤ c := by
  constructor
  · intro h
    have hq := h.dotProduct_mulVec_nonneg z
    change 0 ≤ quadForm (rankOneAdmissionPencil z r c) z at hq
    have hval : quadForm (rankOneAdmissionPencil z r c) z = ((c - r : ℝ) : ℂ) := by
      rw [rankOneAdmissionPencil, quadForm_sub_for_admission,
        quadForm_real_smul_for_admission, quadForm_real_smul_for_admission,
        quadForm_one, hz, quadForm_rankOne, hz]
      norm_num
    rw [hval] at hq
    exact sub_nonneg.mp (RCLike.ofReal_nonneg.mp hq)
  · intro hrc
    have hcr : 0 ≤ c - r := sub_nonneg.mpr hrc
    have hr0 : 0 ≤ r := hr.le
    have hI : ((1 : Matrix ι ι ℂ)).PosSemidef := Matrix.PosSemidef.one
    have hP := one_sub_rankOne_posSemidef hz
    have hsum : (((c - r) • (1 : Matrix ι ι ℂ)) +
        r • ((1 : Matrix ι ι ℂ) - rankOne z)).PosSemidef :=
      (hI.smul hcr).add (hP.smul hr0)
    convert hsum using 1
    ext i j
    simp [rankOneAdmissionPencil]
    ring

/-- Choi-normalized reduction pencil.  At dimension `n`, its rank-one weight is `n`. -/
def reductionChoiPencil (n : ℕ) (z : ι → ℂ) (c : ℝ) : Matrix ι ι ℂ :=
  rankOneAdmissionPencil z n c

/-- The reduction Choi pencil is positive semidefinite exactly at coefficient `c ≥ n`. -/
theorem reductionChoiPencil_posSemidef_iff {n : ℕ} (hn : 0 < n) {z : ι → ℂ}
    (hz : hermInner z z = 1) {c : ℝ} :
    (reductionChoiPencil n z c).PosSemidef ↔ (n : ℝ) ≤ c := by
  exact rankOneAdmissionPencil_posSemidef_iff hz (Nat.cast_pos.mpr hn)

/-- Exact finite reduction threshold at aperture `n` and amplification depth `k`. -/
def reductionAmplifiedThreshold (n k : ℕ) : ℕ := min n k

theorem reductionAmplifiedThreshold_le_depth (n k : ℕ) :
    reductionAmplifiedThreshold n k ≤ k := min_le_right _ _

theorem reductionAmplifiedThreshold_diagonal (n : ℕ) :
    reductionAmplifiedThreshold n n = n := min_self n

/-- Every fixed amplification depth has one aperture-uniform finite bound. -/
theorem reductionAmplifiedThreshold_fixed_depth_uniform :
    ∀ k : ℕ, ∃ C : ℕ, ∀ n : ℕ, reductionAmplifiedThreshold n k ≤ C := by
  intro k
  exact ⟨k, fun n => reductionAmplifiedThreshold_le_depth n k⟩

/-- Complete diagonal thresholds admit no aperture-uniform finite bound. -/
theorem reductionAmplifiedThreshold_diagonal_not_uniform :
    ¬ ∃ C : ℕ, ∀ n : ℕ, reductionAmplifiedThreshold n n ≤ C := by
  rintro ⟨C, hC⟩
  have h := hC (C + 1)
  rw [reductionAmplifiedThreshold_diagonal] at h
  omega

/-- **False-promotion capstone.**  Separate fixed-depth bounds do not promote to one complete
cofinal bound; the rejecting depth migrates along the diagonal. -/
theorem reductionAmplifiedThreshold_false_promotion :
    (∀ k : ℕ, ∃ C : ℕ, ∀ n : ℕ, reductionAmplifiedThreshold n k ≤ C) ∧
      ¬ ∃ C : ℕ, ∀ n : ℕ, reductionAmplifiedThreshold n n ≤ C :=
  ⟨reductionAmplifiedThreshold_fixed_depth_uniform,
    reductionAmplifiedThreshold_diagonal_not_uniform⟩

end

end GaloisForLFunctions.HTGeometry
