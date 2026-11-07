import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# The curve stencil stops at the trivial bound

The zeta function of a curve over `𝔽_q` is `Z(u) = P(u) / ((1 − u)(1 − q u))`. A linear stencil is a
polynomial `D` with `D(1/q) = 0`, the balance condition. Multiplying gives a series whose coefficients
from `deg` on are the single number `E(1) P(1)`, where `D = (1 − q u) E`: this is Riemann–Roch for
effective divisors, and the tail reads one value of the numerator, not its roots.

At genus one, with Frobenius trace `a`, the tail over `𝔽_{q^n}` is the point count
`N_n = 1 − (αⁿ + βⁿ) + qⁿ = (1 − αⁿ)(1 − βⁿ)`. Nonnegativity at every `n` holds exactly on
`|a| ≤ q + 1`, where real Frobenius roots satisfy `1 ≤ |α| ≤ q`. In the variable `|α| = q^{Re ρ}` this
is `0 ≤ Re ρ ≤ 1`: the critical strip, not the critical line. Weil's window `a² ≤ 4q` is strictly
smaller, so no linear stencil over any extension sees purity.

Thus the linear theory stops at the analogue of nonvanishing on `Re s = 1` already over a curve. The
Stepanov auxiliary reaches `√q` because it is not a stencil: it uses the Frobenius twist `x ↦ x^q`
inside the polynomial, which is nonlinear in the points counted.
-/

open PowerSeries

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

private lemma coeff_one_sub_X_mul_succ (W : ℤ⟦X⟧) (n : ℕ) :
    coeff (n + 1) ((1 - X) * W) = coeff (n + 1) W - coeff n W := by
  rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul]

/-- `(1 − X) W = P` makes the coefficients of `W` the partial sums of those of `P`. -/
theorem coeff_eq_sum_coeff {W P : ℤ⟦X⟧} (h : (1 - X) * W = P) (n : ℕ) :
    coeff n W = ∑ i ∈ Finset.range (n + 1), coeff i P := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one, ← h, sub_mul, one_mul, map_sub, coeff_zero_X_mul, sub_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, ← h, coeff_one_sub_X_mul_succ]
    ring

private lemma coeff_eq_eval_one {W : ℤ⟦X⟧} {P : Polynomial ℤ} (h : (1 - X) * W = (P : ℤ⟦X⟧)) {n : ℕ}
    (hn : P.natDegree ≤ n) : coeff n W = P.eval 1 := by
  rw [coeff_eq_sum_coeff h, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hn)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_coe, one_pow, mul_one]

/-- **The tail of a curve stencil.** If `(1 − X)(1 − qX) Z = P`, the coefficients of `(1 − qX) Z` from
degree `deg P` on all equal `P(1)`. -/
theorem coeff_stencil_mul_eq_eval_one {q : ℤ} {Z : ℤ⟦X⟧} {P : Polynomial ℤ}
    (h : (1 - X) * ((1 - C q * X) * Z) = (P : ℤ⟦X⟧)) {n : ℕ} (hn : P.natDegree ≤ n) :
    coeff n ((1 - C q * X) * Z) = P.eval 1 :=
  coeff_eq_eval_one h hn

/-- **Every balanced stencil reads one number.** With `D = (1 − qX) E`, the tail of `D Z` is
`E(1) P(1)`, for every numerator `P` with that value at `1`, whatever its roots. -/
theorem coeff_balanced_stencil_mul {q : ℤ} {Z : ℤ⟦X⟧} {P E : Polynomial ℤ}
    (h : (1 - X) * ((1 - C q * X) * Z) = (P : ℤ⟦X⟧)) {n : ℕ} (hn : (E * P).natDegree ≤ n) :
    coeff n ((E : ℤ⟦X⟧) * ((1 - C q * X) * Z)) = E.eval 1 * P.eval 1 := by
  have h' : (1 - X) * ((E : ℤ⟦X⟧) * ((1 - C q * X) * Z)) = ((E * P : Polynomial ℤ) : ℤ⟦X⟧) := by
    rw [Polynomial.coe_mul, ← h]
    ring
  rw [coeff_eq_eval_one h' hn, Polynomial.eval_mul]

/-- The power sums `αⁿ + βⁿ` of a Frobenius pair with trace `a` and product `q`. -/
def frobeniusTrace (q a : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => a
  | n + 2 => a * frobeniusTrace q a (n + 1) - q * frobeniusTrace q a n

/-- The point count of a genus one curve over `𝔽_{q^n}`, the tail of the stencil `1 − qⁿ u`. -/
def curveCount (q a : ℤ) (n : ℕ) : ℤ := 1 - frobeniusTrace q a n + q ^ n

/-- The numerator of the zeta function of the genus one curve over `𝔽_{q^n}`. -/
def weilPoly (q a : ℤ) (n : ℕ) : Polynomial ℤ :=
  1 - Polynomial.C (frobeniusTrace q a n) * Polynomial.X +
    Polynomial.C (q ^ n) * Polynomial.X ^ 2

theorem eval_one_weilPoly (q a : ℤ) (n : ℕ) : (weilPoly q a n).eval 1 = curveCount q a n := by
  simp [weilPoly, curveCount]

theorem natDegree_weilPoly_le (q a : ℤ) (n : ℕ) : (weilPoly q a n).natDegree ≤ 2 := by
  unfold weilPoly
  compute_degree

/-- **The tail of a genus one curve is its point count**, for every coefficient from degree two on. -/
theorem coeff_curve_tail {q a : ℤ} {n k : ℕ} {Z : ℤ⟦X⟧}
    (h : (1 - X) * ((1 - C (q ^ n) * X) * Z) = (weilPoly q a n : ℤ⟦X⟧)) (hk : 2 ≤ k) :
    coeff k ((1 - C (q ^ n) * X) * Z) = curveCount q a n := by
  rw [coeff_stencil_mul_eq_eval_one h ((natDegree_weilPoly_le q a n).trans hk), eval_one_weilPoly]

theorem cast_frobeniusTrace {R : Type*} [CommRing R] {q a : ℤ} {α β : R} (hs : α + β = a)
    (hp : α * β = q) (n : ℕ) : (frobeniusTrace q a n : R) = α ^ n + β ^ n := by
  have key : ∀ n, (frobeniusTrace q a n : R) = α ^ n + β ^ n ∧
      (frobeniusTrace q a (n + 1) : R) = α ^ (n + 1) + β ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [frobeniusTrace, pow_zero]
        push_cast
        ring
      · simp only [frobeniusTrace, zero_add, pow_one]
        exact hs.symm
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [frobeniusTrace]
      push_cast
      rw [ih.1, ih.2, ← hs, ← hp]
      ring
  exact (key n).1

/-- The point count factors through the Frobenius pair. -/
theorem cast_curveCount {R : Type*} [CommRing R] {q a : ℤ} {α β : R} (hs : α + β = a)
    (hp : α * β = q) (n : ℕ) : (curveCount q a n : R) = (1 - α ^ n) * (1 - β ^ n) := by
  rw [curveCount]
  push_cast
  rw [cast_frobeniusTrace hs hp, ← hp, mul_pow]
  ring

private lemma one_le_of_prod_sum {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : 2 ≤ x * y)
    (hsum : x + y ≤ x * y + 1) : 1 ≤ x ∧ 1 ≤ y := by
  have hfac : 0 ≤ (x - 1) * (y - 1) := by nlinarith
  have hne : ¬ (x ≤ 1 ∧ y ≤ 1) := by
    rintro ⟨h1, h2⟩
    nlinarith
  constructor
  · by_contra h
    push Not at h
    refine hne ⟨h.le, ?_⟩
    by_contra h2
    push Not at h2
    nlinarith
  · by_contra h
    push Not at h
    refine hne ⟨?_, h.le⟩
    by_contra h2
    push Not at h2
    nlinarith

private lemma mul_one_sub_pow_nonneg {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (n : ℕ) :
    0 ≤ (1 - x ^ n) * (1 - y ^ n) := by
  have h1 := one_le_pow₀ hx (n := n)
  have h2 := one_le_pow₀ hy (n := n)
  exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

private lemma mul_one_sub_neg_pow_nonneg {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (n : ℕ) :
    0 ≤ (1 - (-x) ^ n) * (1 - (-y) ^ n) := by
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_pow, hn.neg_pow]
    exact mul_one_sub_pow_nonneg hx hy n
  · rw [hn.neg_pow, hn.neg_pow]
    have h1 := one_le_pow₀ hx (n := n)
    have h2 := one_le_pow₀ hy (n := n)
    exact mul_nonneg (by linarith) (by linarith)

private lemma curveCount_nonneg_of_conj {q a : ℤ} (hD : a ^ 2 < 4 * q) (n : ℕ) :
    0 ≤ curveCount q a n := by
  have hDR : (0 : ℝ) ≤ 4 * (q : ℝ) - (a : ℝ) ^ 2 := by
    have : ((a ^ 2 : ℤ) : ℝ) < ((4 * q : ℤ) : ℝ) := by exact_mod_cast hD
    push_cast at this
    linarith
  set α : ℂ := ⟨(a : ℝ) / 2, Real.sqrt (4 * (q : ℝ) - (a : ℝ) ^ 2) / 2⟩ with hα
  have hs : α + (starRingEnd ℂ) α = a := by
    rw [Complex.add_conj]
    simp only [hα]
    push_cast
    ring
  have hp : α * (starRingEnd ℂ) α = q := by
    rw [Complex.mul_conj, Complex.normSq_mk]
    have hsq := Real.mul_self_sqrt hDR
    have : (a : ℝ) / 2 * ((a : ℝ) / 2) +
        Real.sqrt (4 * (q : ℝ) - (a : ℝ) ^ 2) / 2 * (Real.sqrt (4 * (q : ℝ) - (a : ℝ) ^ 2) / 2) =
        (q : ℝ) := by nlinarith
    rw [this]
    simp
  have h := cast_curveCount hs hp n
  have hconj : (1 : ℂ) - ((starRingEnd ℂ) α) ^ n = (starRingEnd ℂ) (1 - α ^ n) := by
    simp [map_sub, map_pow]
  rw [hconj, Complex.mul_conj] at h
  have hR : ((curveCount q a n : ℤ) : ℝ) = Complex.normSq (1 - α ^ n) := by
    exact_mod_cast h
  have : (0 : ℝ) ≤ (curveCount q a n : ℤ) := by
    rw [hR]
    exact Complex.normSq_nonneg _
  exact_mod_cast this

/-- **Stencils cannot exclude the trivial window.** On `|a| ≤ q + 1` every point count is nonnegative. -/
theorem curveCount_nonneg {q a : ℤ} (hq : 2 ≤ q) (ha : |a| ≤ q + 1) (n : ℕ) :
    0 ≤ curveCount q a n := by
  rcases lt_or_ge (a ^ 2) (4 * q) with hD | hD
  · exact curveCount_nonneg_of_conj hD n
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have haR : |(a : ℝ)| ≤ (q : ℝ) + 1 := by exact_mod_cast ha
  have hDR : (0 : ℝ) ≤ (a : ℝ) ^ 2 - 4 * (q : ℝ) := by
    have : ((4 * q : ℤ) : ℝ) ≤ ((a ^ 2 : ℤ) : ℝ) := by exact_mod_cast hD
    push_cast at this
    linarith
  set s := Real.sqrt ((a : ℝ) ^ 2 - 4 * (q : ℝ)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = (a : ℝ) ^ 2 - 4 * (q : ℝ) := Real.mul_self_sqrt hDR
  have habs : |(a : ℝ)| ^ 2 = (a : ℝ) ^ 2 := sq_abs _
  have hle : s ≤ |(a : ℝ)| := by
    refine (sq_le_sq₀ hs0 (abs_nonneg _)).mp ?_
    nlinarith
  set x := (|(a : ℝ)| + s) / 2 with hx
  set y := (|(a : ℝ)| - s) / 2 with hy
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by rw [hy]; linarith
  have hprod : x * y = q := by
    rw [hx, hy]
    nlinarith
  have hsum : x + y = |(a : ℝ)| := by rw [hx, hy]; ring
  obtain ⟨hx1, hy1⟩ := one_le_of_prod_sum hx0 hy0 (by rw [hprod]; exact hqR)
    (by rw [hsum, hprod]; exact haR)
  have goal : (0 : ℝ) ≤ (curveCount q a n : ℤ) := by
    rcases le_or_gt 0 a with ha0 | ha0
    · have haR0 : (0 : ℝ) ≤ a := by exact_mod_cast ha0
      have hsum' : x + y = ((a : ℤ) : ℝ) := by rw [hsum, abs_of_nonneg haR0]
      rw [cast_curveCount hsum' hprod]
      exact mul_one_sub_pow_nonneg hx1 hy1 n
    · have haR0 : (a : ℝ) < 0 := by exact_mod_cast ha0
      have hsum' : -x + -y = ((a : ℤ) : ℝ) := by
        rw [← neg_add, hsum, abs_of_neg haR0, neg_neg]
      have hprod' : -x * -y = ((q : ℤ) : ℝ) := by rw [neg_mul_neg, hprod]
      rw [cast_curveCount hsum' hprod']
      exact mul_one_sub_neg_pow_nonneg hx1 hy1 n
  exact_mod_cast goal

/-- **The exact window of the linear stencil.** All point counts are nonnegative iff `|a| ≤ q + 1`. -/
theorem curveCount_nonneg_iff {q a : ℤ} (hq : 2 ≤ q) :
    (∀ n, 1 ≤ n → 0 ≤ curveCount q a n) ↔ |a| ≤ q + 1 := by
  refine ⟨fun h => ?_, fun ha n _ => curveCount_nonneg hq ha n⟩
  have h2 := h 2 (by norm_num)
  simp only [curveCount, frobeniusTrace] at h2
  have hsq : a ^ 2 ≤ (q + 1) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq hsq (by linarith)

/-- **The window is the strip.** Real Frobenius roots in the stencil's window satisfy
`1 ≤ |α| ≤ q`, which reads `0 ≤ Re ρ ≤ 1` under `|α| = q^{Re ρ}`. -/
theorem abs_root_bounds {q a : ℤ} {α β : ℝ} (hq : 2 ≤ q) (ha : |a| ≤ q + 1) (hs : α + β = a)
    (hp : α * β = q) : 1 ≤ |α| ∧ |α| ≤ q := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have haR : |(a : ℝ)| ≤ (q : ℝ) + 1 := by exact_mod_cast ha
  have hprod : |α| * |β| = q := by
    rw [← abs_mul, hp, abs_of_nonneg (by linarith)]
  have hpos : 0 < α * β := by rw [hp]; linarith
  have hsum : |α| + |β| = |(a : ℝ)| := by
    rw [← hs]
    rcases mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_pos h1, abs_of_pos h2, abs_of_pos (add_pos h1 h2)]
    · rw [abs_of_neg h1, abs_of_neg h2, abs_of_neg (add_neg h1 h2)]
      ring
  obtain ⟨h1, h2⟩ := one_le_of_prod_sum (abs_nonneg α) (abs_nonneg β) (by rw [hprod]; exact hqR)
    (by rw [hsum, hprod]; exact haR)
  refine ⟨h1, ?_⟩
  rw [← hprod]
  nlinarith [abs_nonneg α]

/-- Weil's window for a genus one curve: both Frobenius roots have modulus `√q`. -/
def IsPure (q a : ℤ) : Prop := a ^ 2 ≤ 4 * q

/-- **Stencils are blind to purity.** For every `q ≥ 2` some trace outside Weil's window has all point
counts nonnegative: the numerator `(1 − u)(1 − q u)`, with Frobenius roots `1` and `q`. -/
theorem exists_impure_of_stencil {q : ℤ} (hq : 2 ≤ q) :
    ∃ a : ℤ, (∀ n, 0 ≤ curveCount q a n) ∧ ¬ IsPure q a := by
  refine ⟨q + 1, fun n => curveCount_nonneg hq ?_ n, fun h => ?_⟩
  · rw [abs_of_nonneg (by linarith)]
  · rw [IsPure] at h
    nlinarith

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
