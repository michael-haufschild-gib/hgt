import GaloisForLFunctions.RHTower.XiWeilPositivityBand

/-!
# The sign structure of the Weil Gram form

For a finite superposition `F = ∑ i, c i · K (z i)` of regularized Cauchy kernels
the Weil pairing splits over the divisor into one contribution per copy, and the
contribution of a copy whose centered coordinate is real is

`∑ i, ∑ j, c i · conj (c j) · K (z i) (pt) · K (conj (z j)) (pt) = ‖∑ i, c i · K (z i) (pt)‖²`,

because `K (conj z)` agrees with the conjugate of `K z` at real arguments.  So a
critical-line copy can only add to the form, for every superposition and every
family of base points: indefiniteness of the Weil Gram matrix is caused solely by
copies off the real axis, and base points are free to lie anywhere.

This is the structural counterpart of the rank-one detection theorem: the latter
exhibits one base point at which a displaced copy makes the diagonal negative,
while the statements here show that no arrangement of on-line copies can ever
produce a negative value to cancel against.
-/

open Complex

namespace RHTower

noncomputable section

/-- At a real argument the conjugate-base-point kernel is the conjugate kernel. -/
theorem xiCauchyRegularizedKernel_conj_of_real {z w : ℂ} (hw : w.im = 0) :
    xiCauchyRegularizedKernel ((starRingEnd ℂ) z) w =
      (starRingEnd ℂ) (xiCauchyRegularizedKernel z w) := by
  have hwc : (starRingEnd ℂ) w = w := by
    apply Complex.ext <;> simp [hw]
  unfold xiCauchyRegularizedKernel
  rw [map_sub, map_inv₀, map_inv₀, map_sub, hwc]

/-- **On-line copies only add.**  For every finite family of base points and
every coefficient vector, a copy with real centered coordinate contributes the
squared modulus of the superposition, hence a nonnegative amount. -/
theorem weilGram_real_copy_contribution_eq_normSq {n : ℕ} (z : Fin n → ℂ)
    (c : Fin n → ℂ) {w : ℂ} (hw : w.im = 0) :
    ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) *
        (xiCauchyRegularizedKernel (z i) w *
          xiCauchyRegularizedKernel ((starRingEnd ℂ) (z j)) w) =
      ((Complex.normSq (∑ i, c i * xiCauchyRegularizedKernel (z i) w) : ℝ) :
        ℂ) := by
  have hconj : ∀ j, xiCauchyRegularizedKernel ((starRingEnd ℂ) (z j)) w =
      (starRingEnd ℂ) (xiCauchyRegularizedKernel (z j) w) :=
    fun j => xiCauchyRegularizedKernel_conj_of_real hw
  have hstep : ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) *
      (xiCauchyRegularizedKernel (z i) w *
        xiCauchyRegularizedKernel ((starRingEnd ℂ) (z j)) w) =
      (∑ i, c i * xiCauchyRegularizedKernel (z i) w) *
        (starRingEnd ℂ) (∑ j, c j * xiCauchyRegularizedKernel (z j) w) := by
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hconj j, map_mul]
    ring
  rw [hstep, Complex.mul_conj]

/-- The contribution of an on-line copy to the Weil Gram form is nonnegative. -/
theorem weilGram_real_copy_contribution_re_nonneg {n : ℕ} (z : Fin n → ℂ)
    (c : Fin n → ℂ) {w : ℂ} (hw : w.im = 0) :
    0 ≤ (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) *
      (xiCauchyRegularizedKernel (z i) w *
        xiCauchyRegularizedKernel ((starRingEnd ℂ) (z j)) w)).re := by
  rw [weilGram_real_copy_contribution_eq_normSq z c hw, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- **Only displaced copies can break positivity.**  If every copy of the divisor
is on the critical line, then every finite Gram form built from any base points is
nonnegative — the Weil matrix is positive semidefinite, with no constraint on where
the base points lie. -/
theorem weilGram_form_re_nonneg_of_all_real {n : ℕ} (z : Fin n → ℂ)
    (c : Fin n → ℂ) (s : Finset XiZeroCopy)
    (hreal : ∀ q ∈ s, (xiSpectralPoint q).im = 0) :
    0 ≤ (∑ q ∈ s, ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) *
      (xiCauchyRegularizedKernel (z i) (xiSpectralPoint q) *
        xiCauchyRegularizedKernel ((starRingEnd ℂ) (z j))
          (xiSpectralPoint q))).re := by
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun q hq => ?_
  exact weilGram_real_copy_contribution_re_nonneg z c (hreal q hq)

/-- Under the Riemann Hypothesis every finite Gram form is nonnegative. -/
theorem weilGram_form_re_nonneg_of_rh (hRH : RiemannHypothesis) {n : ℕ}
    (z : Fin n → ℂ) (c : Fin n → ℂ) (s : Finset XiZeroCopy) :
    0 ≤ (∑ q ∈ s, ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) *
      (xiCauchyRegularizedKernel (z i) (xiSpectralPoint q) *
        xiCauchyRegularizedKernel ((starRingEnd ℂ) (z j))
          (xiSpectralPoint q))).re := by
  refine weilGram_form_re_nonneg_of_all_real z c s fun q _ => ?_
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  rw [ht, Complex.ofReal_im]

end

end RHTower
