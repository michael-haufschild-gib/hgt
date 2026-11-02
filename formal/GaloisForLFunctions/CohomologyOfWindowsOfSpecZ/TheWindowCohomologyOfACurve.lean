import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SpanContactLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanHodgeIndexIsRH
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw

/-!
# The window cohomology of a curve

The calibration over `𝔽_q`. A window of length `n` of a curve datum is the span of the first `n`
Frobenius graphs; its window form is the Toeplitz form of the power sums,
`T_n(e) = Σ_{k,l < n} e_k e_l Re Σ_i β_i^{|k−l|}` (the Castelnuovo–Severi defect, ACS).

* **The window object of a curve** (`curveWindowMap`, `toeplitz_eq_norm_sq_curveWindowMap`): for a
  unitary datum `T_n(e) = ‖(Σ_{k<n} e_k β_i^k)_i‖²` in `ℂ^ι`, `#ι = 2g`: the Frobenius orbit of one
  vector in `H¹`. Every window of a curve has a realization in one fixed finite-dimensional space;
  over `ℤ` none is finite-dimensional (`not_isWindowRealization_of_finiteDimensional`).
* **Realizations at every window are RH for the datum**
  (`forall_curveWindowRealization_iff_unitary`).
* **The window genus saturates** (`curveWindow_posDef_iff`): the window form is positive definite on
  the window `n` iff `n ≤ #{distinct β_i} ≤ 2g`; beyond, the reduced characteristic polynomial is a
  section (the radical). Over `ℤ` the genus is infinite and grows like `2e^{A}` (the Young
  conjugate).
* **The golden fake has no window cohomology** (`goldenDatum_not_forall_curveWindowRealization`):
  integral counts, Euler product and functional equation, but some window has no realization.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri ArithmeticCastelnuovoSeveri.CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The **window map of a curve**: `e ↦ (Σ_{k<n} e_k β_i^k)_i ∈ ℂ^ι`, the coordinates of the window
class in the eigenbasis of Frobenius on `H¹`. -/
def curveWindowMap (n : ℕ) : (ℕ → ℝ) →ₗ[ℝ] EuclideanSpace ℂ ι where
  toFun e := WithLp.toLp 2 fun i => ∑ k ∈ range n, (e k : ℂ) * D.β i ^ k
  map_add' e f := by
    rw [← WithLp.toLp_add]
    congr 1; funext i
    simp only [Pi.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
  map_smul' c e := by
    rw [RingHom.id_apply, ← WithLp.toLp_smul]
    congr 1; funext i
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.real_smul,
      Finset.mul_sum, mul_assoc]

/-- **The window form of a unitary curve is a squared length in `ℂ^ι`.** -/
theorem toeplitz_eq_norm_sq_curveWindowMap (hU : ∀ i, ‖D.β i‖ = 1) (n : ℕ) (e : ℕ → ℝ) :
    D.toeplitz (range n) e = ‖curveWindowMap D n e‖ ^ 2 := by
  rw [D.toeplitz_eq_sum_normSq hU, EuclideanSpace.norm_sq_eq]
  rfl

/-- A Toeplitz form on any finite set of lags is one on a window. -/
theorem toeplitz_eq_window {S : Finset ℕ} {n : ℕ} (hS : S ⊆ range n) (e : ℕ → ℝ) :
    D.toeplitz S e = D.toeplitz (range n) fun k => if k ∈ S then e k else 0 := by
  unfold toeplitz
  have hin : ∀ k, ∑ l ∈ range n, (if k ∈ S then e k else 0) * (if l ∈ S then e l else 0) *
      D.trace (Nat.dist k l) =
      ∑ l ∈ S, (if k ∈ S then e k else 0) * (if l ∈ S then e l else 0) *
        D.trace (Nat.dist k l) :=
    fun k => (Finset.sum_subset hS fun l _ hl => by simp [hl]).symm
  rw [Finset.sum_congr rfl fun k _ => hin k, ← Finset.sum_subset hS fun k _ hk => by simp [hk]]
  exact Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => by simp [hk, hl]

/-- **Window realizations at every length are RH for the datum.** -/
theorem forall_curveWindowRealization_iff_unitary :
    (∀ n : ℕ, ∃ r : (ℕ → ℝ) →ₗ[ℝ] EuclideanSpace ℂ ι,
        ∀ e, D.toeplitz (range n) e = ‖r e‖ ^ 2) ↔ ∀ i, ‖D.β i‖ = 1 := by
  constructor
  · intro h
    refine D.hodgeIndexOnSpan_iff_unitary.mp fun S d => ?_
    rw [spanDefect_eq_toeplitz, toeplitz_eq_window D (Finset.subset_range_sup_succ S)]
    obtain ⟨r, hr⟩ := h (S.sup id + 1)
    rw [hr]; positivity
  · exact fun hU n => ⟨curveWindowMap D n, toeplitz_eq_norm_sq_curveWindowMap D hU n⟩

/-- **The window genus of a curve saturates**: the window form is positive definite on the window
`n` iff `n` is at most the number of distinct Frobenius eigenvalues. -/
theorem curveWindow_posDef_iff (hU : ∀ i, ‖D.β i‖ = 1) (n : ℕ) :
    (∀ e : ℕ → ℝ, (∃ k < n, e k ≠ 0) → 0 < ‖curveWindowMap D n e‖ ^ 2) ↔
      n ≤ D.spectrum.card := by
  rw [← D.toeplitz_pos_on_window_iff hU n]
  simp_rw [toeplitz_eq_norm_sq_curveWindowMap D hU]

/-- The distinct eigenvalues number at most `#ι = 2g`. -/
theorem spectrum_card_le : D.spectrum.card ≤ Fintype.card ι :=
  Finset.card_image_le.trans (by simp)

/-- **The golden fake curve has no window cohomology.** -/
theorem goldenDatum_not_forall_curveWindowRealization :
    ¬ ∀ n : ℕ, ∃ r : (ℕ → ℝ) →ₗ[ℝ] EuclideanSpace ℂ (Fin 2),
        ∀ e, goldenDatum.toeplitz (range n) e = ‖r e‖ ^ 2 :=
  fun h => goldenDatum_not_unitary ((forall_curveWindowRealization_iff_unitary goldenDatum).mp h)

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
