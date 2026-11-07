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
`N_n = 1 − (αⁿ + βⁿ) + qⁿ = (1 − αⁿ)(1 − βⁿ)`. For real or integer `a`, nonnegativity at every `n` holds exactly
on `|a| ≤ q + 1`, where real Frobenius roots satisfy `1 ≤ |α| ≤ q`. In the variable `|α| = q^{Re ρ}` this
is `0 ≤ Re ρ ≤ 1`: the critical strip, not the critical line. Weil's window `a² ≤ 4q` is strictly
smaller, so no linear stencil over any extension sees purity.

Thus the linear theory stops at the analogue of nonvanishing on `Re s = 1` already over a curve. Purity
is an inequality in the other direction: `N_n ≤ qⁿ + 1 + C q^{n/2}` for the curve and for its twist holds
iff `a² ≤ 4q`. The Stepanov auxiliary supplies that upper bound because it is not a stencil: it uses the
Frobenius twist `x ↦ x^q` inside the polynomial, which is nonlinear in the points counted.
-/

open Filter PowerSeries

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

/-- The power sums of a Frobenius pair with real trace `a` and real product `q`. -/
def frobeniusTraceR (q a : ℝ) : ℕ → ℝ
  | 0 => 2
  | 1 => a
  | n + 2 => a * frobeniusTraceR q a (n + 1) - q * frobeniusTraceR q a n

/-- The value `(1 − αⁿ)(1 − βⁿ)` of the numerator over `𝔽_{q^n}` at `1`, for a real trace. -/
def curveCountR (q a : ℝ) (n : ℕ) : ℝ := 1 - frobeniusTraceR q a n + q ^ n

theorem map_frobeniusTraceR {R : Type*} [CommRing R] (f : ℝ →+* R) {q a : ℝ} {α β : R}
    (hs : α + β = f a) (hp : α * β = f q) (n : ℕ) :
    f (frobeniusTraceR q a n) = α ^ n + β ^ n := by
  have key : ∀ n, f (frobeniusTraceR q a n) = α ^ n + β ^ n ∧
      f (frobeniusTraceR q a (n + 1)) = α ^ (n + 1) + β ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [frobeniusTraceR, pow_zero, map_ofNat]
        ring
      · simp only [frobeniusTraceR, zero_add, pow_one]
        exact hs.symm
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [frobeniusTraceR, map_sub, map_mul, map_mul, ih.1, ih.2, ← hs, ← hp]
      ring
  exact (key n).1

/-- The count factors through the Frobenius pair. -/
theorem map_curveCountR {R : Type*} [CommRing R] (f : ℝ →+* R) {q a : ℝ} {α β : R}
    (hs : α + β = f a) (hp : α * β = f q) (n : ℕ) :
    f (curveCountR q a n) = (1 - α ^ n) * (1 - β ^ n) := by
  rw [curveCountR, map_add, map_sub, map_one, map_frobeniusTraceR f hs hp, map_pow, ← hp, mul_pow]
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

private lemma curveCountR_nonneg_of_conj {q a : ℝ} (hD : a ^ 2 < 4 * q) (n : ℕ) :
    0 ≤ curveCountR q a n := by
  have hDR : 0 ≤ 4 * q - a ^ 2 := by linarith
  set α : ℂ := ⟨a / 2, Real.sqrt (4 * q - a ^ 2) / 2⟩ with hα
  have hs : α + (starRingEnd ℂ) α = Complex.ofRealHom a := by
    rw [Complex.add_conj]
    simp only [hα, Complex.ofRealHom_eq_coe]
    push_cast
    ring
  have hp : α * (starRingEnd ℂ) α = Complex.ofRealHom q := by
    rw [Complex.mul_conj, Complex.normSq_mk]
    have hsq := Real.mul_self_sqrt hDR
    have : a / 2 * (a / 2) + Real.sqrt (4 * q - a ^ 2) / 2 * (Real.sqrt (4 * q - a ^ 2) / 2) = q := by
      nlinarith
    rw [this]
    rfl
  have h := map_curveCountR Complex.ofRealHom hs hp n
  have hconj : (1 : ℂ) - ((starRingEnd ℂ) α) ^ n = (starRingEnd ℂ) (1 - α ^ n) := by
    simp [map_sub, map_pow]
  rw [hconj, Complex.mul_conj, Complex.ofRealHom_eq_coe, Complex.ofReal_inj] at h
  rw [h]
  exact Complex.normSq_nonneg _

/-- **Stencils cannot exclude the trivial window.** On `|a| ≤ q + 1` every count is nonnegative, for a real
trace `a` and `q ≥ 2`. -/
theorem curveCountR_nonneg {q a : ℝ} (hq : 2 ≤ q) (ha : |a| ≤ q + 1) (n : ℕ) :
    0 ≤ curveCountR q a n := by
  rcases lt_or_ge (a ^ 2) (4 * q) with hD | hD
  · exact curveCountR_nonneg_of_conj hD n
  have hDR : 0 ≤ a ^ 2 - 4 * q := by linarith
  set s := Real.sqrt (a ^ 2 - 4 * q) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = a ^ 2 - 4 * q := Real.mul_self_sqrt hDR
  have habs : |a| ^ 2 = a ^ 2 := sq_abs _
  have hle : s ≤ |a| := by
    refine (sq_le_sq₀ hs0 (abs_nonneg _)).mp ?_
    nlinarith
  set x := (|a| + s) / 2 with hx
  set y := (|a| - s) / 2 with hy
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by rw [hy]; linarith
  have hprod : x * y = q := by
    rw [hx, hy]
    nlinarith
  have hsum : x + y = |a| := by rw [hx, hy]; ring
  obtain ⟨hx1, hy1⟩ := one_le_of_prod_sum hx0 hy0 (by rw [hprod]; exact hq)
    (by rw [hsum, hprod]; exact ha)
  rcases le_or_gt 0 a with ha0 | ha0
  · have hsum' : x + y = (RingHom.id ℝ) a := by rw [hsum, abs_of_nonneg ha0]; rfl
    have h := map_curveCountR (RingHom.id ℝ) hsum' hprod n
    rw [RingHom.id_apply] at h
    rw [h]
    exact mul_one_sub_pow_nonneg hx1 hy1 n
  · have hsum' : -x + -y = (RingHom.id ℝ) a := by
      rw [← neg_add, hsum, abs_of_neg ha0, neg_neg]
      rfl
    have hprod' : -x * -y = (RingHom.id ℝ) q := by rw [neg_mul_neg, hprod]; rfl
    have h := map_curveCountR (RingHom.id ℝ) hsum' hprod' n
    rw [RingHom.id_apply] at h
    rw [h]
    exact mul_one_sub_neg_pow_nonneg hx1 hy1 n

/-- **The exact window of the linear stencil.** All counts are nonnegative iff `|a| ≤ q + 1`. -/
theorem curveCountR_nonneg_iff {q a : ℝ} (hq : 2 ≤ q) :
    (∀ n, 1 ≤ n → 0 ≤ curveCountR q a n) ↔ |a| ≤ q + 1 := by
  refine ⟨fun h => ?_, fun ha n _ => curveCountR_nonneg hq ha n⟩
  have h2 := h 2 (by norm_num)
  simp only [curveCountR, frobeniusTraceR] at h2
  have hsq : a ^ 2 ≤ (q + 1) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq hsq (by linarith)

/-- **Kloosterman data do not move the stencil.** A sum of `q − 1` unit phases has `|a| ≤ q − 1`, so all counts are
nonnegative with no use of Weil's bound `2√q`. -/
theorem curveCountR_nonneg_of_trivial {q a : ℝ} (hq : 2 ≤ q) (ha : |a| ≤ q - 1) (n : ℕ) :
    0 ≤ curveCountR q a n :=
  curveCountR_nonneg hq (by linarith) n

theorem cast_frobeniusTrace (q a : ℤ) (n : ℕ) :
    ((frobeniusTrace q a n : ℤ) : ℝ) = frobeniusTraceR q a n := by
  have key : ∀ n, ((frobeniusTrace q a n : ℤ) : ℝ) = frobeniusTraceR q a n ∧
      ((frobeniusTrace q a (n + 1) : ℤ) : ℝ) = frobeniusTraceR q a (n + 1) := by
    intro n
    induction n with
    | zero => simp [frobeniusTrace, frobeniusTraceR]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [frobeniusTrace, frobeniusTraceR]
      push_cast
      rw [ih.1, ih.2]
  exact (key n).1

theorem cast_curveCount (q a : ℤ) (n : ℕ) : ((curveCount q a n : ℤ) : ℝ) = curveCountR q a n := by
  rw [curveCount, curveCountR]
  push_cast
  rw [cast_frobeniusTrace]

/-- The integer form of the window: all point counts are nonnegative iff `|a| ≤ q + 1`. -/
theorem curveCount_nonneg_iff {q a : ℤ} (hq : 2 ≤ q) :
    (∀ n, 1 ≤ n → 0 ≤ curveCount q a n) ↔ |a| ≤ q + 1 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hiff := curveCountR_nonneg_iff (a := (a : ℝ)) hqR
  have hL : (∀ n, 1 ≤ n → 0 ≤ curveCount q a n) ↔ ∀ n, 1 ≤ n → 0 ≤ curveCountR q a n := by
    refine forall_congr' fun n => imp_congr_right fun _ => ?_
    rw [← cast_curveCount]
    constructor <;> intro h <;> exact_mod_cast h
  rw [hL, hiff]
  constructor <;> intro h <;> exact_mod_cast h

theorem curveCount_nonneg {q a : ℤ} (hq : 2 ≤ q) (ha : |a| ≤ q + 1) (n : ℕ) :
    0 ≤ curveCount q a n := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have haR : |(a : ℝ)| ≤ (q : ℝ) + 1 := by exact_mod_cast ha
  have h := curveCountR_nonneg hqR haR n
  rw [← cast_curveCount] at h
  exact_mod_cast h

/-- **The window is the strip.** Real Frobenius roots in the stencil's window satisfy
`1 ≤ |α| ≤ q`, which reads `0 ≤ Re ρ ≤ 1` under `|α| = q^{Re ρ}`. -/
theorem abs_root_bounds {q a α β : ℝ} (hq : 2 ≤ q) (ha : |a| ≤ q + 1) (hs : α + β = a)
    (hp : α * β = q) : 1 ≤ |α| ∧ |α| ≤ q := by
  have hprod : |α| * |β| = q := by
    rw [← abs_mul, hp, abs_of_nonneg (by linarith)]
  have hpos : 0 < α * β := by rw [hp]; linarith
  have hsum : |α| + |β| = |a| := by
    rw [← hs]
    rcases mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_pos h1, abs_of_pos h2, abs_of_pos (add_pos h1 h2)]
    · rw [abs_of_neg h1, abs_of_neg h2, abs_of_neg (add_neg h1 h2)]
      ring
  obtain ⟨h1, h2⟩ := one_le_of_prod_sum (abs_nonneg α) (abs_nonneg β) (by rw [hprod]; exact hq)
    (by rw [hsum, hprod]; exact ha)
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

/-- The quadratic twist of a Frobenius pair changes the sign of the trace. -/
theorem frobeniusTraceR_neg (q a : ℝ) (n : ℕ) :
    frobeniusTraceR q (-a) n = (-1) ^ n * frobeniusTraceR q a n := by
  have key : ∀ n, frobeniusTraceR q (-a) n = (-1) ^ n * frobeniusTraceR q a n ∧
      frobeniusTraceR q (-a) (n + 1) = (-1) ^ (n + 1) * frobeniusTraceR q a (n + 1) := by
    intro n
    induction n with
    | zero => simp [frobeniusTraceR]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [frobeniusTraceR, frobeniusTraceR, ih.1, ih.2]
      ring
  exact (key n).1

/-- The pure case: `|αⁿ + βⁿ| ≤ 2 q^{n/2}`. -/
private lemma abs_frobeniusTraceR_le {q a : ℝ} (hq : 0 < q) (hD : a ^ 2 ≤ 4 * q) (n : ℕ) :
    |frobeniusTraceR q a n| ≤ 2 * √q ^ n := by
  have hDR : 0 ≤ 4 * q - a ^ 2 := by linarith
  set α : ℂ := ⟨a / 2, Real.sqrt (4 * q - a ^ 2) / 2⟩ with hα
  have hs : α + (starRingEnd ℂ) α = Complex.ofRealHom a := by
    rw [Complex.add_conj]
    simp only [hα, Complex.ofRealHom_eq_coe]
    push_cast
    ring
  have hsq : a / 2 * (a / 2) + Real.sqrt (4 * q - a ^ 2) / 2 * (Real.sqrt (4 * q - a ^ 2) / 2) = q := by
    have := Real.mul_self_sqrt hDR
    nlinarith
  have hp : α * (starRingEnd ℂ) α = Complex.ofRealHom q := by
    rw [Complex.mul_conj, Complex.normSq_mk, hsq]
    rfl
  have hnorm : ‖α‖ = √q := by
    rw [Complex.norm_def, Complex.normSq_mk, hsq]
  have h := map_frobeniusTraceR Complex.ofRealHom hs hp n
  have hn : ‖((frobeniusTraceR q a n : ℝ) : ℂ)‖ ≤ ‖α‖ ^ n + ‖α‖ ^ n := by
    have hc : ‖(starRingEnd ℂ) α‖ = ‖α‖ := Complex.norm_conj α
    calc ‖((frobeniusTraceR q a n : ℝ) : ℂ)‖ = ‖α ^ n + (starRingEnd ℂ) α ^ n‖ := by
          rw [← h]
          rfl
      _ ≤ ‖α ^ n‖ + ‖(starRingEnd ℂ) α ^ n‖ := norm_add_le _ _
      _ = _ := by rw [norm_pow, norm_pow, hc]
  rw [Complex.norm_real, Real.norm_eq_abs, hnorm] at hn
  linarith

/-- **Purity is an upper bound at square root precision, for the curve and its twist.** Stencils give the lower bound `N_n ≥ 0`.
What is equivalent to Weil's window is the upper bound `N_n ≤ qⁿ + 1 + C q^{n/2}` for the trace `a` and for its twist `−a`: this is the
inequality that Stepanov's auxiliary supplies, by size against multiplicity. -/
theorem isPure_iff_upper_bound {q a : ℝ} (hq : 2 ≤ q) :
    (∃ C : ℝ, ∀ n, curveCountR q a n ≤ q ^ n + 1 + C * √q ^ n ∧
      curveCountR q (-a) n ≤ q ^ n + 1 + C * √q ^ n) ↔ a ^ 2 ≤ 4 * q := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < √q := Real.sqrt_pos.mpr hq0
  constructor
  · rintro ⟨C, hC⟩
    by_contra hD
    push Not at hD
    -- Real roots `x > √q > y > 0` with sum `|a|`.
    have hDR : 0 ≤ a ^ 2 - 4 * q := by linarith
    set s := Real.sqrt (a ^ 2 - 4 * q) with hs
    have hs1 : 0 ≤ s := Real.sqrt_nonneg _
    have hss : s * s = a ^ 2 - 4 * q := Real.mul_self_sqrt hDR
    have habs : |a| ^ 2 = a ^ 2 := sq_abs _
    have hle : s ≤ |a| := by
      refine (sq_le_sq₀ hs1 (abs_nonneg _)).mp ?_
      nlinarith
    set x := (|a| + s) / 2 with hx
    set y := (|a| - s) / 2 with hy
    have hy0 : 0 ≤ y := by rw [hy]; linarith
    have hprod : x * y = q := by
      rw [hx, hy]
      nlinarith
    have hsum : x + y = |a| := by rw [hx, hy]; ring
    have hq2 : √q * √q = q := Real.mul_self_sqrt hq0.le
    have habsgt : 2 * √q < |a| := by
      refine (sq_lt_sq₀ (by positivity) (abs_nonneg _)).mp ?_
      nlinarith
    have hxgt : √q < x := by
      have : |a| / 2 ≤ x := by rw [hx]; linarith
      linarith
    have hratio : 1 < x / √q := (one_lt_div hs0).mpr hxgt
    -- At odd `n` one of the two counts is at least `xⁿ`.
    have hodd : ∀ j, x ^ (2 * j + 1) ≤ |C| * √q ^ (2 * j + 1) := by
      intro j
      have hn : Odd (2 * j + 1) := ⟨j, rfl⟩
      obtain ⟨h1, h2⟩ := hC (2 * j + 1)
      have hxy : frobeniusTraceR q |a| (2 * j + 1) = x ^ (2 * j + 1) + y ^ (2 * j + 1) := by
        have := map_frobeniusTraceR (RingHom.id ℝ) (q := q) (a := |a|) (α := x) (β := y)
          (by rw [hsum]; rfl) (by rw [hprod]; rfl) (2 * j + 1)
        simpa using this
      have hy1 : 0 ≤ y ^ (2 * j + 1) := pow_nonneg hy0 _
      have hC1 : C * √q ^ (2 * j + 1) ≤ |C| * √q ^ (2 * j + 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      rcases le_or_gt 0 a with ha | ha
      · rw [abs_of_nonneg ha] at hxy
        have h3 := frobeniusTraceR_neg q a (2 * j + 1)
        rw [hn.neg_one_pow, neg_one_mul] at h3
        rw [curveCountR, h3, hxy] at h2
        linarith
      · rw [abs_of_neg ha] at hxy
        have h3 := frobeniusTraceR_neg q (-a) (2 * j + 1)
        rw [neg_neg, hn.neg_one_pow, neg_one_mul] at h3
        rw [curveCountR, h3, hxy] at h1
        linarith
    have hgrow := tendsto_pow_atTop_atTop_of_one_lt hratio
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hgrow.eventually_gt_atTop |C|)
    have hj := hN (2 * N + 1) (by omega)
    have hb := hodd N
    have hpow : (x / √q) ^ (2 * N + 1) * √q ^ (2 * N + 1) = x ^ (2 * N + 1) := by
      rw [div_pow]
      field_simp
    have hsp : 0 < √q ^ (2 * N + 1) := by positivity
    rw [← hpow] at hb
    exact absurd (le_of_mul_le_mul_right hb hsp) (not_le.mpr hj)
  · intro hD
    refine ⟨2, fun n => ⟨?_, ?_⟩⟩
    · have h1 := (abs_le.mp (abs_frobeniusTraceR_le hq0 hD n)).1
      rw [curveCountR]
      linarith
    · have hD' : (-a) ^ 2 ≤ 4 * q := by rwa [neg_sq]
      have h1 := (abs_le.mp (abs_frobeniusTraceR_le hq0 hD' n)).1
      rw [curveCountR]
      linarith

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
