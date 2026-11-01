import GaloisForLFunctions.EdgeHodgeTheory.TheIndexComputedByDeformation
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminantSignLaw

/-!
# The determinant along the flow

The determinant of a resolution family is the cheapest integer reading: its zeros are the
crossings and its sign is the parity of the Hodge defect.

* **Crossings are the zeros of the determinant** (`det_ne_zero_iff_hermNullIndex_eq_zero`): a
  Hermitian matrix is nondegenerate iff its determinant is nonzero, since the determinant is the
  product of the eigenvalues.
* **The sign is the parity** (`neg_one_pow_horizonDefect_mul_det_nonneg`): `(−1)^{d_f(N)} det ≥ 0`
  for every horizon family, so a negative determinant detects an odd, hence nonzero, defect
  (`odd_horizonDefect_of_det_neg`).
* **Determinants along paths** (`hermNegIndex_eq_of_det_ne_zero`): along a continuous path of
  Hermitian matrices with nonvanishing determinant on a preconnected set the index is constant.
* **Under RH every spline determinant is nonnegative** (`det_shrinkGram_nonneg_of_rh`).
-/

open Matrix Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.EdgeHodgeTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Crossings are the zeros of the determinant.** -/
theorem det_ne_zero_iff_hermNullIndex_eq_zero {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    H.det ≠ 0 ↔ hermNullIndex H = 0 := by
  rw [hH.det_eq_prod_eigenvalues, nullIndex_eq_card_zero_eigenvalues hH, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, true_implies, ne_eq, Complex.ofReal_eq_zero]

/-- **Determinants along paths.** Along a continuous family of Hermitian matrices with nonvanishing
determinant on a preconnected set the negative index is constant. -/
theorem hermNegIndex_eq_of_det_ne_zero {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {H : X → Matrix ι ι ℂ} (hc : ContinuousOn H S)
    (hherm : ∀ x ∈ S, (H x).IsHermitian) (hdet : ∀ x ∈ S, (H x).det ≠ 0) {x y : X} (hx : x ∈ S)
    (hy : y ∈ S) : hermNegIndex (H x) = hermNegIndex (H y) :=
  hermNegIndex_eq_of_isPreconnected hS hc hherm
    (fun z hz => (det_ne_zero_iff_hermNullIndex_eq_zero (hherm z hz)).mp (hdet z hz)) hx hy

/-- **The sign of the determinant is the parity of the defect.** -/
theorem neg_one_pow_horizonDefect_mul_det_nonneg (f : ℝ → ℝ) (N : ℕ) :
    0 ≤ (-1 : ℝ) ^ horizonDefect f N * (horizonGram f N).det.re :=
  _root_.RHTower.neg_one_pow_negIndex_mul_det_re_nonneg
    (ArithmeticCastelnuovoSeveri.weilGram_isHermitian _ _)

/-- A negative determinant detects an odd, hence nonzero, Hodge defect. -/
theorem odd_horizonDefect_of_det_neg {f : ℝ → ℝ} {N : ℕ} (h : (horizonGram f N).det.re < 0) :
    Odd (horizonDefect f N) := by
  have hs := neg_one_pow_horizonDefect_mul_det_nonneg f N
  rcases Nat.even_or_odd (horizonDefect f N) with he | ho
  · rw [he.neg_one_pow, one_mul] at hs
    exact absurd hs (not_le.mpr h)
  · exact ho

/-- **Under RH every spline determinant is nonnegative.** -/
theorem det_shrinkGram_nonneg_of_rh (hRH : RiemannHypothesis) {w : ℝ} (hw : 0 < w) (N : ℕ) :
    0 ≤ (HeckeKreinToeplitz.shrinkGram w N).det.re := by
  have h0 := (riemannHypothesis_iff_forall_shrinkGram hw).mp hRH N
  have hs := _root_.RHTower.neg_one_pow_negIndex_mul_det_re_nonneg (shrinkGram_isHermitian w N)
  rwa [h0, pow_zero, one_mul] at hs

end GaloisForLFunctions.EdgeHodgeTheory
