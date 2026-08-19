/-
# Summed rank-one kernels are positive semidefinite

A kernel presented as an absolutely convergent sum of rank-one Gram terms
`K j k = ∑' q, v q j · conj (v q k)` is positive semidefinite: its quadratic form is the sum of the
squared moduli `|∑ j conj (c j) · v q j|²`.
-/
import Mathlib

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions.HTGeometry

/-- A single rank-one Gram matrix is positive semidefinite. -/
theorem posSemidef_rankOne {n : ℕ} (u : Fin n → ℂ) :
    (Matrix.of fun j k => u j * (starRingEnd ℂ) (u k)).PosSemidef := by
  classical
  set B : Matrix (Fin n) (Fin 1) ℂ := Matrix.of fun j _ => u j with hB
  have hentry : (Matrix.of fun j k => u j * (starRingEnd ℂ) (u k)) = B * Bᴴ := by
    ext j k
    rw [Matrix.mul_apply, Matrix.of_apply]
    simp [hB, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [hentry]
  exact Matrix.posSemidef_self_mul_conjTranspose B

/-- **A convergent sum of rank-one Gram terms is positive semidefinite.** -/
theorem posSemidef_tsum_rankOne {ι : Type*} {n : ℕ} (v : ι → Fin n → ℂ)
    (hsum : ∀ j k, Summable (fun q : ι => v q j * (starRingEnd ℂ) (v q k))) :
    (Matrix.of fun j k => ∑' q : ι, v q j * (starRingEnd ℂ) (v q k)).PosSemidef := by
  classical
  have hherm : (Matrix.of fun j k => ∑' q : ι, v q j * (starRingEnd ℂ) (v q k)).IsHermitian := by
    ext j k
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, RCLike.star_def]
    rw [show (starRingEnd ℂ) (∑' q : ι, v q k * (starRingEnd ℂ) (v q j))
        = ∑' q : ι, (starRingEnd ℂ) (v q k * (starRingEnd ℂ) (v q j)) from
      Complex.conjCLE.map_tsum]
    refine tsum_congr (fun q => ?_)
    simp only [map_mul, Complex.conj_conj]
    ring
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun c => ?_)
  set P : ι → ℂ := fun q => ∑ j, (starRingEnd ℂ) (c j) * v q j with hP
  have hintp : ∀ j k : Fin n,
      Summable (fun q : ι => (starRingEnd ℂ) (c j) * (v q j * (starRingEnd ℂ) (v q k)) * c k) := by
    intro j k
    exact ((hsum j k).mul_left ((starRingEnd ℂ) (c j))).mul_right (c k)
  have key : star c ⬝ᵥ
      (Matrix.of fun j k => ∑' q : ι, v q j * (starRingEnd ℂ) (v q k)).mulVec c
      = ∑' q : ι, P q * (starRingEnd ℂ) (P q) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
    have hstep : ∀ j k : Fin n,
        (starRingEnd ℂ) (c j) * ((∑' q : ι, v q j * (starRingEnd ℂ) (v q k)) * c k)
          = ∑' q : ι, (starRingEnd ℂ) (c j) * (v q j * (starRingEnd ℂ) (v q k)) * c k := by
      intro j k
      rw [← tsum_mul_right, ← tsum_mul_left]
      exact tsum_congr (fun q => by ring)
    have hrow : ∀ j : Fin n,
        (∑ k, (starRingEnd ℂ) (c j) * ((∑' q : ι, v q j * (starRingEnd ℂ) (v q k)) * c k))
          = ∑' q : ι, ∑ k, (starRingEnd ℂ) (c j) * (v q j * (starRingEnd ℂ) (v q k)) * c k := by
      intro j
      calc (∑ k, (starRingEnd ℂ) (c j) * ((∑' q : ι, v q j * (starRingEnd ℂ) (v q k)) * c k))
          = ∑ k, ∑' q : ι, (starRingEnd ℂ) (c j) * (v q j * (starRingEnd ℂ) (v q k)) * c k :=
            Finset.sum_congr rfl (fun k _ => hstep j k)
        _ = ∑' q : ι, ∑ k, (starRingEnd ℂ) (c j) * (v q j * (starRingEnd ℂ) (v q k)) * c k :=
            (Summable.tsum_finsetSum (fun k _ => hintp j k)).symm
    calc (∑ j, (starRingEnd ℂ) (c j) *
            ∑ k, (∑' q : ι, v q j * (starRingEnd ℂ) (v q k)) * c k)
        = ∑ j, ∑' q : ι, ∑ k, (starRingEnd ℂ) (c j) * (v q j * (starRingEnd ℂ) (v q k)) * c k := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum]
          exact hrow j
      _ = ∑' q : ι, ∑ j, ∑ k,
            (starRingEnd ℂ) (c j) * (v q j * (starRingEnd ℂ) (v q k)) * c k :=
          (Summable.tsum_finsetSum (fun j _ => summable_sum (fun k _ => hintp j k))).symm
      _ = ∑' q : ι, P q * (starRingEnd ℂ) (P q) := by
          refine tsum_congr (fun q => ?_)
          rw [hP]
          simp only [map_sum, map_mul, Complex.conj_conj]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring
  rw [key]
  have hcp : ∀ q : ι, P q * (starRingEnd ℂ) (P q) = ((Complex.normSq (P q) : ℝ) : ℂ) := by
    intro q
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
  simp_rw [hcp]
  rw [← Complex.ofReal_tsum]
  have hnn : (0 : ℝ) ≤ ∑' q : ι, Complex.normSq (P q) :=
    tsum_nonneg (fun q => Complex.normSq_nonneg _)
  exact_mod_cast hnn

end GaloisForLFunctions.HTGeometry
