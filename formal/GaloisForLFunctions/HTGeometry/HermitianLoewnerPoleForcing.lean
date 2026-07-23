import GaloisForLFunctions.HTGeometry.PositiveResiduePoleForcing
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Hermitian Loewner pole forcing

Two resolvent columns of one real symmetric operator have nonnegative cross Gram product whenever
their real spectral parameters lie in a common closed spectral gap.  Therefore a negative Loewner
divided difference forces an eigenvalue into that interval.  This is the operator realization of
the positive-residue descent--pole law.
-/

open scoped InnerProductSpace Matrix

namespace HTGeometry

noncomputable section

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Resolvent columns of a real symmetric matrix have nonnegative cross Gram product across a
closed spectral gap.  Contrapositively, a negative cross Gram product forces an eigenvalue into
the closed interval between the two spectral parameters. -/
theorem exists_eigenvalue_mem_Icc_of_symmetric_resolvent_cross_neg
    (C : Matrix m m ℝ) (hC : C.transpose = C)
    (u v w : m → ℝ) {x y : ℝ} (hxy : x < y)
    (hv : C *ᵥ v = x • v - u) (hw : C *ᵥ w = y • w - u)
    (hcross : v ⬝ᵥ w < 0) :
    ∃ j : m, (show C.IsHermitian from by simpa [Matrix.IsHermitian] using hC).eigenvalues j ∈
      Set.Icc x y := by
  let hHerm : C.IsHermitian := by simpa [Matrix.IsHermitian] using hC
  let basis := hHerm.eigenvectorBasis
  by_contra hnone
  push Not at hnone
  have hterm : ∀ j : m,
      0 ≤ ((basis j : EuclideanSpace ℝ m) : m → ℝ) ⬝ᵥ v *
        (w ⬝ᵥ ((basis j : EuclideanSpace ℝ m) : m → ℝ)) := by
    intro j
    let e : m → ℝ := (basis j : EuclideanSpace ℝ m)
    let lambda : ℝ := hHerm.eigenvalues j
    have hCe : C *ᵥ e = lambda • e := by
      simpa [basis, e, lambda] using hHerm.mulVec_eigenvectorBasis j
    have hadjointV : e ⬝ᵥ (C *ᵥ v) = (C *ᵥ e) ⬝ᵥ v := by
      calc
        e ⬝ᵥ (C *ᵥ v) = e ⬝ᵥ (C.transpose *ᵥ v) := by rw [hC]
        _ = v ⬝ᵥ (C *ᵥ e) := Matrix.dotProduct_transpose_mulVec C e v
        _ = (C *ᵥ e) ⬝ᵥ v := dotProduct_comm _ _
    have hadjointW : e ⬝ᵥ (C *ᵥ w) = (C *ᵥ e) ⬝ᵥ w := by
      calc
        e ⬝ᵥ (C *ᵥ w) = e ⬝ᵥ (C.transpose *ᵥ w) := by rw [hC]
        _ = w ⬝ᵥ (C *ᵥ e) := Matrix.dotProduct_transpose_mulVec C e w
        _ = (C *ᵥ e) ⬝ᵥ w := dotProduct_comm _ _
    have hcoordV : e ⬝ᵥ u = (x - lambda) * (e ⬝ᵥ v) := by
      have hsource : e ⬝ᵥ (C *ᵥ v) = x * (e ⬝ᵥ v) - e ⬝ᵥ u := by
        simpa [dotProduct_sub, dotProduct_smul] using
          congrArg (fun q : m → ℝ => e ⬝ᵥ q) hv
      have hspectral : e ⬝ᵥ (C *ᵥ v) = lambda * (e ⬝ᵥ v) := by
        rw [hadjointV, hCe]
        simp
      linarith
    have hcoordW : e ⬝ᵥ u = (y - lambda) * (e ⬝ᵥ w) := by
      have hsource : e ⬝ᵥ (C *ᵥ w) = y * (e ⬝ᵥ w) - e ⬝ᵥ u := by
        simpa [dotProduct_sub, dotProduct_smul] using
          congrArg (fun q : m → ℝ => e ⬝ᵥ q) hw
      have hspectral : e ⬝ᵥ (C *ᵥ w) = lambda * (e ⬝ᵥ w) := by
        rw [hadjointW, hCe]
        simp
      linarith
    have hout : lambda < x ∨ y < lambda := by
      by_cases hlx : lambda < x
      · exact Or.inl hlx
      · have hxl : x ≤ lambda := le_of_not_gt hlx
        have hnotle : ¬lambda ≤ y := by
          intro hly
          exact hnone j ⟨hxl, hly⟩
        exact Or.inr (lt_of_not_ge hnotle)
    have hden : 0 < (x - lambda) * (y - lambda) := by
      rcases hout with hout | hout
      · exact mul_pos (by linarith) (by linarith)
      · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have heq : (e ⬝ᵥ u) ^ 2 =
        ((x - lambda) * (y - lambda)) * ((e ⬝ᵥ v) * (e ⬝ᵥ w)) := by
      symm
      calc
        ((x - lambda) * (y - lambda)) * ((e ⬝ᵥ v) * (e ⬝ᵥ w)) =
            ((x - lambda) * (e ⬝ᵥ v)) *
              ((y - lambda) * (e ⬝ᵥ w)) := by ring
        _ = (e ⬝ᵥ u) * (e ⬝ᵥ u) := congrArg₂ (· * ·) hcoordV.symm hcoordW.symm
        _ = (e ⬝ᵥ u) ^ 2 := (pow_two _).symm
    have hlocal : 0 ≤ (e ⬝ᵥ v) * (e ⬝ᵥ w) := by
      nlinarith [sq_nonneg (e ⬝ᵥ u)]
    simpa [e, dotProduct_comm w e] using hlocal
  have hparseval :
      (∑ j : m, (((basis j : EuclideanSpace ℝ m) : m → ℝ) ⬝ᵥ v) *
          (w ⬝ᵥ ((basis j : EuclideanSpace ℝ m) : m → ℝ))) = v ⬝ᵥ w := by
    have hp := basis.sum_inner_mul_inner (WithLp.toLp 2 v) (WithLp.toLp 2 w)
    change (∑ j : m, (((basis j : EuclideanSpace ℝ m) : m → ℝ) ⬝ᵥ v) *
        (w ⬝ᵥ ((basis j : EuclideanSpace ℝ m) : m → ℝ))) = w ⬝ᵥ v at hp
    exact hp.trans (dotProduct_comm _ _)
  have hnonneg : 0 ≤ v ⬝ᵥ w := by
    rw [← hparseval]
    exact Finset.sum_nonneg fun j _ => hterm j
  linarith

end

end HTGeometry
