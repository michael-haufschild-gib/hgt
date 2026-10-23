import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanCalibration
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Order.Chebyshev

/-!
# Fake curves and the window law: the two walls over `𝔽_q`

Hodge index on the Frobenius span is RH for the curve datum (`hodgeIndexOnSpan_iff_unitary`).
This file shows that the *data of the span* do not force it, in the two ways the corpus's walls
predict for `ζ`.

**The Beurling wall: a fake elliptic curve over `𝔽₅`.** The datum `q = 5`, `β = (φ, φ⁻¹)`
(`φ` the golden ratio) has integral point counts `N_j = 5^j + 1 − L_j`, where
`L_j = a^j + b^j`, `a, b = (5 ± √5)/2`, is an integer recurrence (`goldenDatum_pointCount_eq`),
with `N_j ≥ 1` for `j ≥ 1` (`one_le_goldenDatum_pointCount`), and it satisfies the functional
equation. Its zeta function `(1 − 5u + 5u²)/((1 − u)(1 − 5u))` is rational. Yet `φ > 1`, and the
span class `Δ − Γ₁/√5` has defect `4 − 2√5 < 0` (`goldenDatum_spanDefect_neg`): the Hodge index
fails on the span. Point counts, functional equation and rationality are span data; the
index theorem is not.

**The finite-window wall: hiding needs genus exponential in the window.** A real off-circle pair
`r, r⁻¹` (`r > 1`, depth `log r / log q`) is invisible to every span class of degree `< n` once the
genus is large:

* (*hiding*, `exists_hidden_on_window`) for every `n` there is a datum with `|β| = 2` whose span
  defect is nonnegative on all classes supported in degrees `< n` — `2N` roots of unity cancel the
  pair in all power sums of order `< N` and their count dominates the window;
* (*visibility*, `two_mul_genus_ge_of_window`) if all other eigenvalues are unitary and the span
  is Hodge in degrees `< n`, then `r^{n−1} + r^{1−n} + 2 ≤ 2·#ι`, i.e. the genus is at least
  `(r^{n−1} + 2)/4`.

So the degree needed to see the pair is `≍ log(genus)/log r`. Over `ℚ` the genus is the zero count
`≍ T log T` and the degree is the aperture: an off-line zero of depth `δ` at height `T` becomes
visible at aperture `≍ log T/δ` — the resolution law of the corpus, calibrated.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- **Window bound.** Hodge index on the span classes of degree `< n` bounds the power sums of
order `< n` by the genus. -/
theorem norm_powerSum_le_of_window {n : ℕ}
    (h : ∀ S ⊆ Finset.range n, ∀ d, 0 ≤ D.spanDefect S d) {j : ℕ} (hj : j < n) :
    ‖D.powerSum j‖ ≤ Fintype.card ι := by
  rcases eq_or_ne j 0 with rfl | hj0
  · simp [D.powerSum_eq_trace, trace_zero]
  have hS : ({0, j} : Finset ℕ) ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [Finset.mem_range] <;> omega
  have hT : ∀ e : ℕ → ℝ, 0 ≤ D.toeplitz {0, j} e := by
    intro e
    have := h {0, j} hS (fun k => e k / D.sqrtq ^ k)
    rw [spanDefect_eq_toeplitz] at this
    convert this using 3
    exact (div_mul_cancel₀ _ (pow_ne_zero _ D.sqrtq_pos.ne')).symm
  have h1 := hT (fun k => if k = 0 then 1 else 1)
  have h2 := hT (fun k => if k = 0 then 1 else -1)
  rw [toeplitz_pair D j hj0] at h1 h2
  rw [D.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

/-- **Visibility: the genus needed to hide a real off-circle pair.** If `β i₀ = r` and
`β (fe i₀) = r⁻¹` with `r > 1` and every other eigenvalue unitary, Hodge index in degrees `< n`
forces `r^{n−1} + r^{1−n} + 2 ≤ 2·#ι`. -/
theorem two_mul_genus_ge_of_window {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ S ⊆ Finset.range n, ∀ d, 0 ≤ D.spanDefect S d) {i₀ : ι} {r : ℝ} (hr : 1 < r)
    (hfe : D.fePerm i₀ ≠ i₀) (h0 : D.β i₀ = r) (h1 : D.β (D.fePerm i₀) = (r⁻¹ : ℝ))
    (hU : ∀ i, i ≠ i₀ → i ≠ D.fePerm i₀ → ‖D.β i‖ = 1) :
    r ^ (n - 1) + (r⁻¹) ^ (n - 1) + 2 ≤ 2 * Fintype.card ι := by
  classical
  set j := n - 1
  have hb := D.norm_powerSum_le_of_window h (j := j) (by omega)
  set T : Finset ι := {i₀, D.fePerm i₀}
  have hsplit : D.powerSum j = (r ^ j + (r⁻¹) ^ j : ℝ) + ∑ i ∈ Finset.univ \ T, D.β i ^ j := by
    rw [powerSum, ← Finset.sum_sdiff (Finset.subset_univ T), add_comm]
    congr 1
    rw [Finset.sum_pair (Ne.symm hfe), h0, h1]
    push_cast; ring
  have hrest : ‖∑ i ∈ Finset.univ \ T, D.β i ^ j‖ ≤ Fintype.card ι - 2 := by
    calc ‖∑ i ∈ Finset.univ \ T, D.β i ^ j‖ ≤ ∑ i ∈ Finset.univ \ T, ‖D.β i ^ j‖ :=
          norm_sum_le _ _
      _ = ∑ i ∈ Finset.univ \ T, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, T, Finset.mem_insert,
            Finset.mem_singleton, not_or] at hi
          rw [norm_pow, hU i hi.1 hi.2, one_pow]
      _ = Fintype.card ι - 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_sdiff_of_subset
            (Finset.subset_univ T), Finset.card_univ, Finset.card_pair (Ne.symm hfe)]
          have : 2 ≤ Fintype.card ι := by
            rw [← Finset.card_pair (Ne.symm hfe)]; exact Finset.card_le_univ T
          push_cast [this]; ring
  have hpos : 0 ≤ r ^ j + (r⁻¹) ^ j := by positivity
  have htri : r ^ j + (r⁻¹) ^ j ≤ ‖D.powerSum j‖ + ‖∑ i ∈ Finset.univ \ T, D.β i ^ j‖ := by
    have := norm_sub_le (D.powerSum j) (∑ i ∈ Finset.univ \ T, D.β i ^ j)
    rw [hsplit, add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
      at this
    rw [hsplit] at hb ⊢
    linarith [norm_sub_le ((r ^ j + (r⁻¹) ^ j : ℝ) + ∑ i ∈ Finset.univ \ T, D.β i ^ j)
      (∑ i ∈ Finset.univ \ T, D.β i ^ j)]
  linarith

end CurveDatum

/-! ### The fake elliptic curve over `𝔽₅` -/

open Real in
/-- The **golden datum**: `q = 5`, normalized eigenvalues `φ, φ⁻¹`. -/
def goldenDatum : CurveDatum (Fin 2) where
  q := 5
  one_lt_q := by norm_num
  β := ![((goldenRatio : ℝ) : ℂ), ((goldenRatio⁻¹ : ℝ) : ℂ)]
  conjPerm := Equiv.refl _
  β_conjPerm i := by fin_cases i <;> exact (Complex.conj_ofReal _).symm
  fePerm := Equiv.swap 0 1
  β_fePerm i := by
    fin_cases i
    · show ((goldenRatio⁻¹ : ℝ) : ℂ) * ((goldenRatio : ℝ) : ℂ) = 1
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ goldenRatio_ne_zero, Complex.ofReal_one]
    · show ((goldenRatio : ℝ) : ℂ) * ((goldenRatio⁻¹ : ℝ) : ℂ) = 1
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ goldenRatio_ne_zero, Complex.ofReal_one]

open Real in
theorem goldenDatum_trace (j : ℕ) :
    goldenDatum.trace j = goldenRatio ^ j + (goldenRatio⁻¹) ^ j := by
  have h : goldenDatum.powerSum j = ((goldenRatio ^ j + (goldenRatio⁻¹) ^ j : ℝ) : ℂ) := by
    rw [CurveDatum.powerSum, Fin.sum_univ_two, Complex.ofReal_add, Complex.ofReal_pow,
      Complex.ofReal_pow]
    rfl
  rw [CurveDatum.trace, h, Complex.ofReal_re]

/-- The integer recurrence `L₀ = 2`, `L₁ = 5`, `L_{j+2} = 5 L_{j+1} − 5 L_j`. -/
def goldenLucas : ℕ → ℤ
  | 0 => 2
  | 1 => 5
  | (j + 2) => 5 * goldenLucas (j + 1) - 5 * goldenLucas j

open Real in
/-- `√5 φ` and `√5 φ⁻¹` are the roots of `X² − 5X + 5`. -/
theorem sqrt_five_goldenRatio_sq :
    (√5 * goldenRatio) ^ 2 = 5 * (√5 * goldenRatio) - 5 ∧
      (√5 * goldenRatio⁻¹) ^ 2 = 5 * (√5 * goldenRatio⁻¹) - 5 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [inv_goldenRatio]
  constructor <;> simp only [goldenRatio, goldenConj] <;> nlinarith [h5]

open Real in
theorem sqrt_five_pow_sum (j : ℕ) :
    (√5 * goldenRatio) ^ j + (√5 * goldenRatio⁻¹) ^ j = goldenLucas j := by
  obtain ⟨ha, hb⟩ := sqrt_five_goldenRatio_sq
  set a := √5 * goldenRatio
  set b := √5 * goldenRatio⁻¹
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => simp [goldenLucas]; norm_num
    | 1, _ =>
      have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      simp only [pow_one, goldenLucas, a, b, inv_goldenRatio, goldenRatio, goldenConj]
      push_cast
      nlinarith [h5]
    | (k + 2), ih =>
      have e1 := ih (k + 1) (by omega)
      have e0 := ih k (by omega)
      have : a ^ (k + 2) + b ^ (k + 2) = 5 * (a ^ (k + 1) + b ^ (k + 1)) - 5 * (a ^ k + b ^ k) := by
        have hak : a ^ (k + 2) = a ^ k * a ^ 2 := by ring
        have hbk : b ^ (k + 2) = b ^ k * b ^ 2 := by ring
        rw [hak, hbk, ha, hb]; ring
      rw [this, e1, e0, goldenLucas]
      push_cast; ring

open Real in
/-- **Integral point counts**: `N_j = 5^j + 1 − L_j`. -/
theorem goldenDatum_pointCount_eq (j : ℕ) :
    goldenDatum.pointCount j = ((5 ^ j + 1 - goldenLucas j : ℤ) : ℝ) := by
  push_cast
  rw [← sqrt_five_pow_sum, CurveDatum.pointCount, goldenDatum_trace]
  have hq : goldenDatum.q = 5 := rfl
  have hs : goldenDatum.sqrtq = √5 := rfl
  rw [hq, hs, mul_pow, mul_pow]
  ring

open Real in
/-- **Positive point counts**: `N_j ≥ 1` for `j ≥ 1`, since `a^j + b^j ≤ (a + b)^j = 5^j`. -/
theorem one_le_goldenDatum_pointCount {j : ℕ} (hj : 1 ≤ j) : 1 ≤ goldenDatum.pointCount j := by
  rw [CurveDatum.pointCount, goldenDatum_trace]
  have hq : goldenDatum.q = 5 := rfl
  have hs : goldenDatum.sqrtq = √5 := rfl
  rw [hq, hs]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsum : √5 * goldenRatio + √5 * goldenRatio⁻¹ = 5 := by
    rw [inv_goldenRatio]; simp only [goldenRatio, goldenConj]; nlinarith [h5]
  have ha : 0 ≤ √5 * goldenRatio := by positivity
  have hb : 0 ≤ √5 * goldenRatio⁻¹ := by positivity
  have hpow : (√5 * goldenRatio) ^ j + (√5 * goldenRatio⁻¹) ^ j ≤ 5 ^ j := by
    have := pow_add_pow_le ha hb (n := j) (by omega)
    rwa [hsum] at this
  have : √5 ^ j * (goldenRatio ^ j + (goldenRatio⁻¹) ^ j)
      = (√5 * goldenRatio) ^ j + (√5 * goldenRatio⁻¹) ^ j := by rw [mul_pow, mul_pow]; ring
  rw [this]
  linarith

open Real in
/-- **The fake curve violates the Hodge index on its span**: the class `Δ − Γ₁/√5` has
defect `4 − 2√5 < 0`. -/
theorem goldenDatum_spanDefect_neg :
    goldenDatum.spanDefect {0, 1} (fun k => if k = 0 then 1 else -1 / √5) < 0 := by
  rw [CurveDatum.spanDefect_eq_toeplitz]
  have hs : goldenDatum.sqrtq = √5 := rfl
  have h5 : 0 < √5 := by positivity
  have hsum : goldenRatio + goldenRatio⁻¹ = √5 := by
    rw [inv_goldenRatio]; simp only [goldenRatio, goldenConj]; ring
  rw [hs, CurveDatum.toeplitz, Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num),
    Finset.sum_pair (by norm_num)]
  simp only [Nat.dist_self, Nat.dist_zero_left, Nat.dist_zero_right, goldenDatum_trace,
    if_true, one_ne_zero, if_false, pow_zero, pow_one]
  have hsq : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have h1 : -1 / √5 * √5 = -1 := by field_simp
  rw [h1, hsum]
  have : (2 : ℝ) < √5 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith

/-- **The fake curve is not unitary**: `|β₀| = φ > 1`. -/
theorem goldenDatum_not_unitary : ¬ ∀ i, ‖goldenDatum.β i‖ = 1 := by
  intro h
  have := h 0
  simp only [goldenDatum, Matrix.cons_val_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.goldenRatio_pos] at this
  linarith [Real.one_lt_goldenRatio]

/-! ### Hiding an off-circle pair on a window -/

/-- The hiding datum: the pair `2, 1/2` together with the `N`-th roots of unity and their
conjugates (`N ≥ 1`), over `q = 2`. -/
def hidingDatum (N : ℕ) [NeZero N] : CurveDatum (Bool ⊕ (Fin N × Bool)) where
  q := 2
  one_lt_q := by norm_num
  β
    | Sum.inl true => ((2 : ℝ) : ℂ)
    | Sum.inl false => ((1 / 2 : ℝ) : ℂ)
    | Sum.inr (k, true) => Complex.exp (2 * Real.pi * I / N) ^ (k : ℕ)
    | Sum.inr (k, false) => starRingEnd ℂ (Complex.exp (2 * Real.pi * I / N) ^ (k : ℕ))
  conjPerm := Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (Equiv.swap true false))
  β_conjPerm i := by
    rcases i with b | ⟨k, b⟩ <;> cases b <;> first | exact (Complex.conj_ofReal _).symm | simp
  fePerm := Equiv.sumCongr (Equiv.swap true false)
    (Equiv.prodCongr (Equiv.refl _) (Equiv.swap true false))
  β_fePerm i := by
    have hz : ∀ z : ℂ, ‖z‖ = 1 → starRingEnd ℂ z * z = 1 := fun z hz => by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
    have hn : ∀ k : ℕ, ‖Complex.exp (2 * Real.pi * I / N) ^ k‖ = 1 := fun k => by
      rw [norm_pow, Complex.norm_exp]
      simp
    rcases i with b | ⟨k, b⟩ <;> cases b
    · norm_num
    · norm_num
    · simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.prodCongr_apply, Prod.map_apply,
        Equiv.refl_apply]
      rw [mul_comm]; exact hz _ (hn _)
    · simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.prodCongr_apply, Prod.map_apply,
        Equiv.refl_apply]
      exact hz _ (hn _)

theorem hidingDatum_trace {N : ℕ} [NeZero N] {j : ℕ} (hj0 : j ≠ 0) (hjN : j < N) :
    (hidingDatum N).trace j = 2 ^ j + (1 / 2) ^ j := by
  set ζ := Complex.exp (2 * Real.pi * I / N)
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have hgeom : ∑ k : Fin N, (ζ ^ (k : ℕ)) ^ j = 0 := by
    have hne : ζ ^ j ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hj0 hjN
    simp_rw [← pow_mul, mul_comm _ j, pow_mul]
    rw [Fin.sum_univ_eq_sum_range (fun k => (ζ ^ j) ^ k), geom_sum_eq hne, ← pow_mul,
      mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]
  have hpow : (hidingDatum N).powerSum j
      = ((2 ^ j + (1 / 2) ^ j : ℝ) : ℂ) + (∑ k : Fin N, (ζ ^ (k : ℕ)) ^ j
          + starRingEnd ℂ (∑ k : Fin N, (ζ ^ (k : ℕ)) ^ j)) := by
    simp only [CurveDatum.powerSum, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fintype.univ_bool, Finset.sum_insert (by decide : true ∉ ({false} : Finset Bool)),
      Finset.sum_singleton, map_sum, map_pow, Finset.sum_add_distrib]
    simp [hidingDatum, ζ]
  rw [CurveDatum.trace, hpow, hgeom, map_zero, add_zero, add_zero, Complex.ofReal_re]

theorem card_hiding (N : ℕ) [NeZero N] : Fintype.card (Bool ⊕ (Fin N × Bool)) = 2 + 2 * N := by
  simp [Fintype.card_sum, Fintype.card_prod]; ring

/-- A Toeplitz form with dominant diagonal: entries `c` off the diagonal bounded by `C` give
`Σ e_k e_l c_{kl} ≥ −C·#S·Σ e_k²`. -/
theorem sum_mul_ge_of_abs_le (S : Finset ℕ) (e : ℕ → ℝ) (c : ℕ → ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ k ∈ S, ∀ l ∈ S, |c k l| ≤ C) :
    -(C * S.card * ∑ k ∈ S, e k ^ 2) ≤ ∑ k ∈ S, ∑ l ∈ S, e k * e l * c k l := by
  have hterm : ∀ k ∈ S, ∀ l ∈ S, -(C * (|e k| * |e l|)) ≤ e k * e l * c k l := by
    intro k hk l hl
    have h1 : |e k * e l * c k l| ≤ C * (|e k| * |e l|) := by
      rw [abs_mul, abs_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hc k hk l hl) (by positivity)
    linarith [neg_abs_le (e k * e l * c k l)]
  have hsum : -(C * (∑ k ∈ S, |e k|) ^ 2) ≤ ∑ k ∈ S, ∑ l ∈ S, e k * e l * c k l := by
    have : C * (∑ k ∈ S, |e k|) ^ 2 = ∑ k ∈ S, ∑ l ∈ S, C * (|e k| * |e l|) := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
    rw [this, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun l hl => hterm k hk l hl
  have hcs : (∑ k ∈ S, |e k|) ^ 2 ≤ S.card * ∑ k ∈ S, e k ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := S) (f := fun k => |e k|)
    simpa [sq_abs] using this
  nlinarith [mul_le_mul_of_nonneg_left hcs hC]

/-- **Hiding.** For every window `n` some datum with an eigenvalue of modulus `2` is Hodge on
every span class of degree `< n`. -/
theorem exists_hidden_on_window (n : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (D : CurveDatum ι), (∃ i, ‖D.β i‖ ≠ 1) ∧
      ∀ S ⊆ Finset.range n, ∀ d, 0 ≤ D.spanDefect S d := by
  set N := n * 2 ^ n + n + 1
  haveI : NeZero N := ⟨by omega⟩
  refine ⟨Bool ⊕ (Fin N × Bool), inferInstance, hidingDatum N, ⟨Sum.inl true, ?_⟩, ?_⟩
  · simp [hidingDatum]
  intro S hS d
  rw [CurveDatum.spanDefect_eq_toeplitz]
  set e := fun k => d k * (hidingDatum N).sqrtq ^ k
  -- the diagonal carries `2N`, the off-diagonal entries are `2^d + 2^{-d} ≤ 2·2^n`
  have hsplit : (hidingDatum N).toeplitz S e = (2 * N) * ∑ k ∈ S, e k ^ 2
      + ∑ k ∈ S, ∑ l ∈ S, e k * e l * (2 ^ Nat.dist k l + (1 / 2) ^ Nat.dist k l) := by
    rw [CurveDatum.toeplitz, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← Finset.add_sum_erase _ _ hk, ← Finset.add_sum_erase S _ hk]
    have hoff : ∀ l ∈ S.erase k, (hidingDatum N).trace (Nat.dist k l)
        = 2 ^ Nat.dist k l + (1 / 2) ^ Nat.dist k l := by
      intro l hl
      have hlk := (Finset.mem_erase.mp hl).1
      have hk' := Finset.mem_range.mp (hS hk)
      have hl' := Finset.mem_range.mp (hS (Finset.mem_of_mem_erase hl))
      refine hidingDatum_trace ?_ ?_
      · intro h0; exact hlk (Nat.eq_of_dist_eq_zero h0).symm
      · have : Nat.dist k l < n := by
          rcases le_total k l with h | h
          · rw [Nat.dist_eq_sub_of_le h]; omega
          · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]; omega
        have : n ≤ N := by simp only [N]; omega
        omega
    rw [Finset.sum_congr rfl fun l hl => by rw [hoff l hl]]
    simp only [Nat.dist_self, CurveDatum.trace_zero, card_hiding, pow_zero]
    push_cast; ring
  have hbound : ∀ k ∈ S, ∀ l ∈ S, |2 ^ Nat.dist k l + (1 / 2 : ℝ) ^ Nat.dist k l| ≤ 2 * 2 ^ n := by
    intro k hk l hl
    have hk' := Finset.mem_range.mp (hS hk)
    have hl' := Finset.mem_range.mp (hS hl)
    have hd : Nat.dist k l ≤ n := by
      rcases le_total k l with h | h
      · rw [Nat.dist_eq_sub_of_le h]; omega
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]; omega
    have h2 : (2 : ℝ) ^ Nat.dist k l ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hd
    have h3 : (1 / 2 : ℝ) ^ Nat.dist k l ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h4 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hlow := sum_mul_ge_of_abs_le S e (fun k l => 2 ^ Nat.dist k l + (1 / 2) ^ Nat.dist k l)
    (by positivity) hbound
  have hcard : (S.card : ℝ) ≤ n := by
    have := Finset.card_le_card hS
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hN : 2 * 2 ^ n * (n : ℝ) ≤ 2 * N := by
    simp only [N]; push_cast; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
  have hsq : 0 ≤ ∑ k ∈ S, e k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_right
    (le_trans (mul_le_mul_of_nonneg_left hcard (by positivity)) hN) hsq]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
