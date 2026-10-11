import GaloisForLFunctions.RHTower.XiHeatMomentSmallTimePositivity
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelRootFlip

/-!
# Stable test polynomials are positive at small heat time

**Theorem** (`exists_heatHankel_re_pos_of_roots_re_nonpos`).  There is `a₀ > 0` such that for
every heat time `0 < a ≤ a₀` and every nonzero `P ∈ ℂ[X]` whose roots all lie in the closed left
half-plane `Re r ≤ 0`, of any degree,

`Re H_a(P, P) = Re Σ_q e^{−a w_q} P(w_q) \overline{P(\overline{w_q})} > 0`.

Proof.  The heat Hankel form only sees the Hermitian square `Q = P · P^*`
(`heatHankelTermAt_eq_eval_mul_conjPoly`), and `H_a(P, P) = Σ_k Q_k M_k(a)` with the heat moments
`M_k(a)` (`heatHankel_eq_sum_coeff_mul_xiHeatMoment`).  For `P = c ∏ (X − r)` the square is
`|c|² ∏ (X² − 2 Re r · X + |r|²)`, a polynomial with nonnegative real coefficients when every
`Re r ≤ 0`.  At small heat time every `M_k(a)` is positive (`exists_heatMoment_re_pos_small_time`),
so the form is a nonnegative combination of positive numbers with a nonzero weight.

The heat Hankel form is therefore unconditionally positive at small heat time on every test whose
nodes stay off the open right half-plane, where the heat frequencies `w_q = z_q²` cluster.
Negative directions require nodes in `Re w > 0`, as the real-node witnesses do
(`exists_realNodes_heatHankel_re_neg_of_not_riemannHypothesis`).
-/

open Complex Polynomial
open GaloisForLFunctions.HTGeometry (conjPoly eval_conjPoly)

namespace RHTower

noncomputable section

/-! ## The heat Hankel form through the Hermitian square -/

/-- `H_a(P, P) = Σ_k Q_k M_k(a)` with `Q = P · P^*`. -/
theorem heatHankel_eq_sum_coeff_mul_xiHeatMoment {a : ℝ} (ha : 0 < a) (P : ℂ[X]) :
    heatHankel a P P =
      ∑ k ∈ (P * conjPoly P).support, (P * conjPoly P).coeff k * xiHeatMoment k a := by
  set Q := P * conjPoly P
  have hterm : ∀ w : ℂ, heatHankelTermAt a P P w =
      ∑ k ∈ Q.support, Q.coeff k * (w ^ k * Complex.exp (-(a : ℂ) * w)) := by
    intro w
    rw [heatHankelTermAt_eq_eval_mul_conjPoly, Polynomial.eval_eq_sum, Polynomial.sum_def,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [heatHankel]
  simp only [hterm]
  rw [Summable.tsum_finsetSum fun k _ =>
    (summable_pow_mul_exp_xiHeatFrequency ha k).mul_left _]
  exact Finset.sum_congr rfl fun k _ => by rw [tsum_mul_left, xiHeatMoment]

/-! ## Polynomials with nonnegative real coefficients -/

/-- Every coefficient is a nonnegative real number. -/
def NonnegRealCoeffs (Q : ℂ[X]) : Prop := ∀ k, (Q.coeff k).im = 0 ∧ 0 ≤ (Q.coeff k).re

theorem nonnegRealCoeffs_C {c : ℝ} (hc : 0 ≤ c) : NonnegRealCoeffs (C (c : ℂ)) := by
  intro k
  rw [coeff_C]
  split_ifs <;> simp [hc]

theorem nonnegRealCoeffs_X : NonnegRealCoeffs (X : ℂ[X]) := by
  intro k
  rw [coeff_X]
  split_ifs <;> simp

theorem NonnegRealCoeffs.add {A B : ℂ[X]} (hA : NonnegRealCoeffs A) (hB : NonnegRealCoeffs B) :
    NonnegRealCoeffs (A + B) := fun k => by
  rw [coeff_add, add_im, add_re]
  exact ⟨by rw [(hA k).1, (hB k).1, add_zero], add_nonneg (hA k).2 (hB k).2⟩

theorem NonnegRealCoeffs.mul {A B : ℂ[X]} (hA : NonnegRealCoeffs A) (hB : NonnegRealCoeffs B) :
    NonnegRealCoeffs (A * B) := fun k => by
  rw [coeff_mul, im_sum, re_sum]
  refine ⟨Finset.sum_eq_zero fun x _ => ?_, Finset.sum_nonneg fun x _ => ?_⟩
  · rw [mul_im, (hA x.1).1, (hB x.2).1]; ring
  · rw [mul_re, (hA x.1).1]
    simpa using mul_nonneg (hA x.1).2 (hB x.2).2

theorem nonnegRealCoeffs_one : NonnegRealCoeffs (1 : ℂ[X]) := by
  simpa using nonnegRealCoeffs_C (c := 1) (by norm_num)

/-- **A conjugate pair of left nodes.**  `(X − r)(X − r̄) = X² − 2 Re r · X + |r|²` has nonnegative
real coefficients when `Re r ≤ 0`. -/
theorem nonnegRealCoeffs_X_sub_C_mul_conj {r : ℂ} (hr : r.re ≤ 0) :
    NonnegRealCoeffs ((X - C r) * (X - C ((starRingEnd ℂ) r))) := by
  have h : (X - C r) * (X - C ((starRingEnd ℂ) r)) =
      X * X + C (((-(2 * r.re)) : ℝ) : ℂ) * X + C ((Complex.normSq r : ℝ) : ℂ) := by
    have h1 : (X - C r) * (X - C ((starRingEnd ℂ) r)) =
        X * X - C (r + (starRingEnd ℂ) r) * X + C (r * (starRingEnd ℂ) r) := by
      rw [C_add, C_mul]
      ring
    rw [h1, Complex.add_conj, Complex.mul_conj]
    push_cast
    rw [C_neg]
    ring
  rw [h]
  exact ((nonnegRealCoeffs_X.mul nonnegRealCoeffs_X).add
    ((nonnegRealCoeffs_C (by linarith)).mul nonnegRealCoeffs_X)).add
    (nonnegRealCoeffs_C (Complex.normSq_nonneg r))

/-- **The Hermitian square of a stable polynomial.**  If every root of `P` has `Re r ≤ 0`, then
`P · P^*` has nonnegative real coefficients. -/
theorem nonnegRealCoeffs_mul_conjPoly_of_roots_re_nonpos {P : ℂ[X]}
    (hroots : ∀ r ∈ P.roots, r.re ≤ 0) : NonnegRealCoeffs (P * conjPoly P) := by
  have hP := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := P))
  have hconj : conjPoly P = C ((starRingEnd ℂ) P.leadingCoeff) *
      (P.roots.map fun r => X - C ((starRingEnd ℂ) r)).prod := by
    conv_lhs => rw [← hP]
    rw [conjPoly, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod,
      Multiset.map_map]
    congr 2
    exact Multiset.map_congr rfl fun r _ => by simp
  have hsplit : P * conjPoly P = C (P.leadingCoeff * (starRingEnd ℂ) P.leadingCoeff) *
      (P.roots.map fun r => (X - C r) * (X - C ((starRingEnd ℂ) r))).prod := by
    have h1 : P * conjPoly P =
        (C P.leadingCoeff * (P.roots.map fun a => X - C a).prod) * conjPoly P := by rw [hP]
    rw [h1, hconj, Multiset.prod_map_mul, C_mul]
    ring
  rw [hsplit, Complex.mul_conj]
  refine (nonnegRealCoeffs_C (Complex.normSq_nonneg _)).mul ?_
  refine Multiset.prod_induction _ _ (fun A B hA hB => hA.mul hB) nonnegRealCoeffs_one ?_
  intro Q hQ
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hQ
  exact nonnegRealCoeffs_X_sub_C_mul_conj (hroots r hr)

/-! ## Positivity -/

/-- **Positivity on the nonnegative-coefficient cone.**  At small heat time, the heat Hankel form is
positive on every nonzero `P` whose Hermitian square has nonnegative real coefficients. -/
theorem exists_heatHankel_re_pos_of_nonnegRealCoeffs :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ → ∀ P : ℂ[X], P ≠ 0 →
      NonnegRealCoeffs (P * conjPoly P) → 0 < (heatHankel a P P).re := by
  obtain ⟨a₀, ha₀, hmom⟩ := exists_heatMoment_re_pos_small_time
  refine ⟨a₀, ha₀, fun a ha haa P hP hQ => ?_⟩
  set Q := P * conjPoly P with hQdef
  have hQ0 : Q ≠ 0 := mul_ne_zero hP (Polynomial.map_ne_zero hP)
  rw [heatHankel_eq_sum_coeff_mul_xiHeatMoment ha, re_sum]
  have hterm : ∀ k ∈ Q.support, (Q.coeff k * xiHeatMoment k a).re =
      (Q.coeff k).re * (xiHeatMoment k a).re := fun k _ => by
    rw [mul_re, (hQ k).1, zero_mul, sub_zero]
  rw [Finset.sum_congr rfl hterm]
  obtain ⟨k, hk⟩ := Polynomial.support_nonempty.2 hQ0
  refine Finset.sum_pos' (fun j _ => mul_nonneg (hQ j).2 (hmom a ha haa j).le) ⟨k, hk, ?_⟩
  have hck : Q.coeff k ≠ 0 := Polynomial.mem_support_iff.1 hk
  have hre : 0 < (Q.coeff k).re := by
    rcases (hQ k).2.lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.ext h.symm (hQ k).1) hck
  exact mul_pos hre (hmom a ha haa k)

/-- **Stable test polynomials are positive at small heat time.**  There is `a₀ > 0` such that
`Re H_a(P, P) > 0` for `0 < a ≤ a₀` and every nonzero `P` with all roots in `Re r ≤ 0`. -/
theorem exists_heatHankel_re_pos_of_roots_re_nonpos :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ → ∀ P : ℂ[X], P ≠ 0 →
      (∀ r ∈ P.roots, r.re ≤ 0) → 0 < (heatHankel a P P).re := by
  obtain ⟨a₀, ha₀, hpos⟩ := exists_heatHankel_re_pos_of_nonnegRealCoeffs
  exact ⟨a₀, ha₀, fun a ha haa P hP hroots =>
    hpos a ha haa P hP (nonnegRealCoeffs_mul_conjPoly_of_roots_re_nonpos hroots)⟩

end

end RHTower
