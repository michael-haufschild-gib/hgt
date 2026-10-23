import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanCalibration
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The contact law of the Frobenius span: the genus is the first degenerate window

For a unitary curve datum the defect of a window class `Σ_{k < n} e_k Γ̃_k` is
`Σ_i |E(β_i)|²`, `E = Σ_{k < n} e_k X^k` the **window polynomial** (`toeplitz_eq_sum_normSq`).
So the radical of the defect on the window `n` is the space of window polynomials vanishing on
the spectrum `{β_i}`, and its size is fixed by `s = #{β_i}`, the number of distinct eigenvalues
(at most `2g`):

* `n ≤ s`: the defect is **positive definite** on the window (`toeplitz_pos_of_le`) — a nonzero
  polynomial of degree `< n ≤ s` cannot vanish at `s` points;
* `n > s`: the defect is **degenerate** (`exists_radical_of_lt`) — the reduced characteristic
  polynomial `Π_{z ∈ spectrum} (X − z)` has real coefficients and degree `s < n` and is a radical
  class.

Hence the first degenerate window is exactly `s + 1` (`toeplitz_pos_on_window_iff`). The radical
is the space of sections of the span: the multiples of the reduced characteristic polynomial. Over
`ℚ` the genus is infinite: no compactly supported test has a transform divisible by `Ξ`, so under
RH the Weil form is positive definite at every aperture and the radical is replaced by the
near-radical, whose dimension is the Landau–Widom count.
-/

open Complex Finset Polynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The spectrum: the distinct normalized eigenvalues. -/
def spectrum : Finset ℂ := Finset.univ.image D.β

/-- The window polynomial `Σ_{k < n} e_k X^k` of a window class. -/
def windowPoly (n : ℕ) (e : ℕ → ℝ) : ℂ[X] := ∑ k ∈ range n, C (e k : ℂ) * X ^ k

theorem eval_windowPoly (n : ℕ) (e : ℕ → ℝ) (z : ℂ) :
    (windowPoly n e).eval z = ∑ k ∈ range n, (e k : ℂ) * z ^ k := by
  simp [windowPoly, eval_finsetSum]

theorem coeff_windowPoly (n : ℕ) (e : ℕ → ℝ) (k : ℕ) :
    (windowPoly n e).coeff k = if k < n then (e k : ℂ) else 0 := by
  simp only [windowPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem natDegree_windowPoly_lt {n : ℕ} (hn : 0 < n) (e : ℕ → ℝ) :
    (windowPoly n e).natDegree < n := by
  by_cases h : windowPoly n e = 0
  · rw [h, natDegree_zero]; exact hn
  · rw [natDegree_lt_iff_degree_lt h, degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_windowPoly, if_neg (by omega)]

theorem toeplitz_eq_zero_iff (hU : ∀ i, ‖D.β i‖ = 1) (n : ℕ) (e : ℕ → ℝ) :
    D.toeplitz (range n) e = 0 ↔ ∀ i, (windowPoly n e).eval (D.β i) = 0 := by
  rw [toeplitz_eq_sum_normSq D hU, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  simp only [Finset.mem_univ, true_implies, eval_windowPoly]
  refine forall_congr' fun i => ?_
  rw [sq_eq_zero_iff, norm_eq_zero]

/-- **Positive definite below the contact window.** -/
theorem toeplitz_pos_of_le (hU : ∀ i, ‖D.β i‖ = 1) {n : ℕ} (hn : n ≤ D.spectrum.card)
    {e : ℕ → ℝ} (he : ∃ k < n, e k ≠ 0) : 0 < D.toeplitz (range n) e := by
  have hnn : 0 ≤ D.toeplitz (range n) e := by
    rw [toeplitz_eq_sum_normSq D hU]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  refine lt_of_le_of_ne hnn (fun h0 => ?_)
  have hz := (D.toeplitz_eq_zero_iff hU n e).mp h0.symm
  obtain ⟨k, hk, hek⟩ := he
  have hP : windowPoly n e = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ D.spectrum (fun z hz' => ?_)
      ((natDegree_windowPoly_lt (by omega) e).trans_le hn)
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz'
    exact hz i
  have := congrArg (fun P => P.coeff k) hP
  simp only [coeff_windowPoly, if_pos hk, coeff_zero, Complex.ofReal_eq_zero] at this
  exact hek this

/-- The reduced characteristic polynomial `Π_{z ∈ spectrum} (X − z)`. -/
def reducedCharPoly : ℂ[X] := ∏ z ∈ D.spectrum, (X - C z)

theorem reducedCharPoly_monic : D.reducedCharPoly.Monic :=
  Polynomial.monic_prod_of_monic _ _ fun z _ => monic_X_sub_C z

theorem natDegree_reducedCharPoly : D.reducedCharPoly.natDegree = D.spectrum.card := by
  rw [reducedCharPoly, natDegree_prod_of_monic _ _ fun z _ => monic_X_sub_C z]
  simp

theorem eval_reducedCharPoly (i : ι) : D.reducedCharPoly.eval (D.β i) = 0 := by
  rw [reducedCharPoly, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_image_of_mem D.β (Finset.mem_univ i)) (by simp)

/-- The spectrum is closed under conjugation. -/
theorem conj_mem_spectrum {z : ℂ} (hz : z ∈ D.spectrum) : starRingEnd ℂ z ∈ D.spectrum := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨D.conjPerm i, Finset.mem_univ _, D.β_conjPerm i⟩

/-- **The reduced characteristic polynomial is real.** -/
theorem map_conj_reducedCharPoly : D.reducedCharPoly.map (starRingEnd ℂ) = D.reducedCharPoly := by
  rw [reducedCharPoly, Polynomial.map_prod]
  simp only [Polynomial.map_sub, map_X, map_C]
  refine Finset.prod_nbij' (starRingEnd ℂ) (starRingEnd ℂ) (fun z hz => D.conj_mem_spectrum hz)
    (fun z hz => D.conj_mem_spectrum hz) (fun z _ => by simp) (fun z _ => by simp) (fun z _ => rfl)

theorem coeff_reducedCharPoly_real (k : ℕ) :
    ((D.reducedCharPoly.coeff k).re : ℂ) = D.reducedCharPoly.coeff k := by
  have h := congrArg (fun P => P.coeff k) D.map_conj_reducedCharPoly
  simp only [coeff_map] at h
  exact Complex.conj_eq_iff_re.mp h

/-- **Degenerate above the contact window**: the reduced characteristic polynomial is a nonzero
radical class on every window `n > s`. -/
theorem exists_radical_of_lt (hU : ∀ i, ‖D.β i‖ = 1) {n : ℕ} (hn : D.spectrum.card < n) :
    ∃ e : ℕ → ℝ, (∃ k < n, e k ≠ 0) ∧ D.toeplitz (range n) e = 0 := by
  set e : ℕ → ℝ := fun k => (D.reducedCharPoly.coeff k).re
  have hW : windowPoly n e = D.reducedCharPoly := by
    ext k
    rw [coeff_windowPoly]
    split_ifs with hk
    · exact D.coeff_reducedCharPoly_real k
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_reducedCharPoly]; omega)]
  refine ⟨e, ⟨D.spectrum.card, hn, ?_⟩, ?_⟩
  · have hlead := D.reducedCharPoly_monic.coeff_natDegree
    rw [natDegree_reducedCharPoly] at hlead
    simp [e, hlead]
  · rw [D.toeplitz_eq_zero_iff hU, hW]
    exact D.eval_reducedCharPoly

/-- **The contact law.** For a unitary datum the span defect is positive definite on the window of
`n` Frobenius graphs iff `n` does not exceed the number of distinct eigenvalues. -/
theorem toeplitz_pos_on_window_iff (hU : ∀ i, ‖D.β i‖ = 1) (n : ℕ) :
    (∀ e : ℕ → ℝ, (∃ k < n, e k ≠ 0) → 0 < D.toeplitz (range n) e) ↔ n ≤ D.spectrum.card := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨e, he, h0⟩ := D.exists_radical_of_lt hU hlt
    exact (h e he).ne' h0
  · intro hn e he
    exact D.toeplitz_pos_of_le hU hn he

end CurveDatum

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
