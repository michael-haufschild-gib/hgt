import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import GaloisForLFunctions.SurfaceOfSpecZ.HeightsAtTheZerosOfTheSplineAreInPhase

/-!
# Positive cosine sums outside a small arc

For every `0 < δ ≤ 1/2` there is a finite zero-mean cosine polynomial
`∑_{m=1}^M p_m cos(2π m t)` with integer coefficients `p_m ∈ ℕ`, not all zero, that is bounded
below by `η ∑_{m=1}^M p_m` (`η > 0`) at every `t ∈ ℝ` at distance at least `δ/2` from `ℤ + 1/2`
(`exists_nat_cosine_sum_pos_off_hole`).

**Mechanism.** Let `a_s` be the discrete tent of length `2N − 1` (`∑_{s < 2N} a_s z^s = (∑_{j < N} z^j)^2`),
with autocorrelation `c_m = ∑_{s < 2N} a_s a_{s+m}`. The normalized Fejér square
`J_N(t) = 1 + 2 ∑_{m ≥ 1} (c_m / c_0) cos(2π m t)` is nonnegative everywhere and decays as
`O(1 / (N^3 δ^4))` outside a `δ`-arc around `0`, while the Poisson kernel
`P_r(t) = 1 + 2 ∑_{m ≥ 1} r^m cos(2π m t)` at radius `r = 1 − 1/(256 N^2)` stays bounded below by
`1/(512 N^2)` everywhere on `ℝ` and dominates `c_m / c_0` for every `m ≥ 2`. Consequently,

  `G(t) = ½ J_N(t) + ½ P_r(t) − J_N(t − ½)`

has zero constant term, nonnegative cosine coefficients at all frequencies `m ≥ 1` (`3 c_m / c_0 + r^m`
for odd `m`, `r^m − c_m / c_0 ≥ 0` for even `m ≥ 2`), and satisfies `G(t) ≥ 1/(2048 N^2)` outside
`(ℤ + 1/2) + (−δ/2, δ/2)` once `N ≫ δ^{−4}`. Truncating the geometric tail of `P_r` and rounding
scaled coefficients up to `ℕ` gives integer weights with the same property.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

namespace CosineArcConcentration

/-! ### Elementary inequalities -/

/-- Bernoulli's inequality on `(-∞, 1]`: `1 − m x ≤ (1 − x)^m`. -/
theorem one_sub_mul_le_pow {x : ℝ} (hx1 : x ≤ 1) (m : ℕ) :
    1 - (m : ℝ) * x ≤ (1 - x) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast
    rw [pow_succ]
    have h1 : (1 - (m : ℝ) * x) * (1 - x) ≤ (1 - x) ^ m * (1 - x) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have h2 : 0 ≤ (m : ℝ) * x ^ 2 := mul_nonneg (Nat.cast_nonneg m) (sq_nonneg x)
    nlinarith

/-- `cos(x − mπ) = (−1)^m cos x`. -/
theorem cos_sub_nat_mul_pi (x : ℝ) (m : ℕ) :
    Real.cos (x - (m : ℝ) * Real.pi) = (-1 : ℝ) ^ m * Real.cos x := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast
    rw [show x - ((m : ℝ) + 1) * Real.pi = (x - (m : ℝ) * Real.pi) - Real.pi by ring,
      Real.cos_sub_pi, ih, pow_succ]
    ring

/-- On the torus `ℝ/ℤ`, distance at least `δ/2` from `ℤ` gives chord length `‖1 − e^{2πiu}‖ ≥ 2δ`. -/
theorem two_mul_le_norm_one_sub_exp {u δ : ℝ} (hδ0 : 0 ≤ δ)
    (hdist : ∀ n : ℤ, δ / 2 ≤ |u - n|) :
    2 * δ ≤ ‖(1 : ℂ) - cexp (((2 * Real.pi * u : ℝ) : ℂ) * I)‖ := by
  set n : ℤ := ⌊u + 1 / 2⌋
  set y : ℝ := u - n
  have hy_lo : -1 / 2 ≤ y := by
    have := Int.floor_le (u + 1 / 2)
    linarith
  have hy_hi : y ≤ 1 / 2 := by
    have := (Int.lt_floor_add_one (u + 1 / 2)).le
    linarith
  have hy_abs_le : |y| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, hy_hi⟩
  have hy_abs_ge : δ / 2 ≤ |y| := hdist n
  have hexp : cexp (((2 * Real.pi * u : ℝ) : ℂ) * I) =
      cexp (((2 * Real.pi * y : ℝ) : ℂ) * I) := by
    have hsplit : (((2 * Real.pi * u : ℝ) : ℂ) * I) =
        (((2 * Real.pi * y : ℝ) : ℂ) * I) + (n : ℂ) * (2 * Real.pi * I) := by
      simp only [y]; push_cast; ring
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hexp]
  have hsq : ‖(1 : ℂ) - cexp (((2 * Real.pi * y : ℝ) : ℂ) * I)‖ ^ 2 =
      (2 * Real.sin (Real.pi * |y|)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re,
      Complex.sub_im, Complex.one_im, Complex.exp_ofReal_mul_I_im, zero_sub]
    have hsc := Real.sin_sq_add_cos_sq (2 * Real.pi * y)
    have hdouble : Real.cos (2 * Real.pi * y) = 1 - 2 * Real.sin (Real.pi * y) ^ 2 := by
      rw [show 2 * Real.pi * y = 2 * (Real.pi * y) by ring, Real.cos_two_mul]
      linarith [Real.sin_sq_add_cos_sq (Real.pi * y)]
    have habs_sin : Real.sin (Real.pi * |y|) ^ 2 = Real.sin (Real.pi * y) ^ 2 := by
      rcases le_total 0 y with hy0 | hy0
      · rw [abs_of_nonneg hy0]
      · rw [abs_of_nonpos hy0, mul_neg, Real.sin_neg, neg_sq]
    nlinarith
  have hsin_ge : δ ≤ Real.sin (Real.pi * |y|) := by
    have h1 := Real.le_sin_mul (x := 2 * |y|) (by positivity) (by linarith)
    rw [show Real.pi / 2 * (2 * |y|) = Real.pi * |y| by ring] at h1
    linarith
  have hsin_nn : 0 ≤ 2 * Real.sin (Real.pi * |y|) := by linarith
  have hnorm_eq : ‖(1 : ℂ) - cexp (((2 * Real.pi * y : ℝ) : ℂ) * I)‖ =
      2 * Real.sin (Real.pi * |y|) := by
    nlinarith [norm_nonneg ((1 : ℂ) - cexp (((2 * Real.pi * y : ℝ) : ℂ) * I)), hsq]
  linarith

/-! ### Autocorrelation of a finite real sequence -/

/-- Norm-squared expansion of a trigonometric polynomial `∑_{s < d} a_s e^{2πist}` into diagonal and
cosine autocorrelation terms. -/
theorem norm_sq_trig_sum (a : ℕ → ℝ) (t : ℝ) (d : ℕ) :
    ‖∑ s ∈ Finset.range d, (a s : ℂ) * cexp (((2 * Real.pi * s * t : ℝ) : ℂ) * I)‖ ^ 2 =
      (∑ s ∈ Finset.range d, a s ^ 2) +
        2 * ∑ j ∈ Finset.range d,
          (∑ s ∈ Finset.range (d - (j + 1)), a s * a (s + (j + 1))) *
            Real.cos (2 * Real.pi * (j + 1 : ℕ) * t) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ih]
    have hlast : ‖(a d : ℂ) * cexp (((2 * Real.pi * (d : ℕ) * t : ℝ) : ℂ) * I)‖ ^ 2 = a d ^ 2 := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        sq_abs]
    have hcross : ((∑ s ∈ Finset.range d, (a s : ℂ) *
          cexp (((2 * Real.pi * s * t : ℝ) : ℂ) * I)) *
        (starRingEnd ℂ) ((a d : ℂ) * cexp (((2 * Real.pi * (d : ℕ) * t : ℝ) : ℂ) * I))).re =
        ∑ j ∈ Finset.range d, a (d - 1 - j) * a d *
          Real.cos (2 * Real.pi * (j + 1 : ℕ) * t) := by
      rw [Finset.sum_mul, Complex.re_sum]
      have hterm : ∀ s ∈ Finset.range d,
          (((a s : ℂ) * cexp (((2 * Real.pi * s * t : ℝ) : ℂ) * I)) *
            (starRingEnd ℂ) ((a d : ℂ) * cexp (((2 * Real.pi * (d : ℕ) * t : ℝ) : ℂ) * I))).re =
          a s * a d * Real.cos (2 * Real.pi * ((d - s : ℕ) : ℝ) * t) := by
        intro s hs
        have hsd : s ≤ d := (Finset.mem_range.mp hs).le
        rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
          Complex.conj_I, mul_neg]
        have he : cexp (((2 * Real.pi * s * t : ℝ) : ℂ) * I) *
            cexp (-(((2 * Real.pi * (d : ℕ) * t : ℝ) : ℂ) * I)) =
            cexp (((-(2 * Real.pi * ((d - s : ℕ) : ℝ) * t) : ℝ) : ℂ) * I) := by
          rw [← Complex.exp_add]
          congr 1
          rw [Nat.cast_sub hsd]
          push_cast
          ring
        rw [show ((a s : ℂ) * cexp (((2 * Real.pi * s * t : ℝ) : ℂ) * I)) *
            ((a d : ℂ) * cexp (-(((2 * Real.pi * (d : ℕ) * t : ℝ) : ℂ) * I))) =
            ((a s * a d : ℝ) : ℂ) * (cexp (((2 * Real.pi * s * t : ℝ) : ℂ) * I) *
              cexp (-(((2 * Real.pi * (d : ℕ) * t : ℝ) : ℂ) * I))) by push_cast; ring,
          he, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjd : j < d := Finset.mem_range.mp hj
      have hsub : d - (d - 1 - j) = j + 1 := by omega
      rw [hsub]
    have hstep : ∑ j ∈ Finset.range (d + 1),
          (∑ s ∈ Finset.range (d + 1 - (j + 1)), a s * a (s + (j + 1))) *
            Real.cos (2 * Real.pi * (j + 1 : ℕ) * t) =
        (∑ j ∈ Finset.range d,
          (∑ s ∈ Finset.range (d - (j + 1)), a s * a (s + (j + 1))) *
            Real.cos (2 * Real.pi * (j + 1 : ℕ) * t)) +
        ∑ j ∈ Finset.range d, a (d - 1 - j) * a d *
          Real.cos (2 * Real.pi * (j + 1 : ℕ) * t) := by
      rw [Finset.sum_range_succ, Nat.sub_self, Finset.range_zero, Finset.sum_empty, zero_mul,
        add_zero, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjd : j < d := Finset.mem_range.mp hj
      have hsub1 : d + 1 - (j + 1) = (d - (j + 1)) + 1 := by omega
      have hsub2 : d - (j + 1) = d - 1 - j := by omega
      have hsub3 : d - 1 - j + (j + 1) = d := by omega
      rw [hsub1, Finset.sum_range_succ, hsub2, hsub3]
      ring
    rw [hlast, hcross, hstep, Finset.sum_range_succ]
    ring

/-! ### The discrete tent sequence and Jackson kernel -/

/-- The discrete tent sequence `1, 2, …, N, N − 1, …, 1, 0, …` of support `< 2N`. -/
def tentSeq (N s : ℕ) : ℝ :=
  if s < N then (s : ℝ) + 1 else if s < 2 * N then (2 * N : ℝ) - 1 - s else 0

theorem tentSeq_nonneg (N s : ℕ) : 0 ≤ tentSeq N s := by
  unfold tentSeq
  split_ifs with h1 h2
  · positivity
  · have : (s : ℝ) + 1 ≤ 2 * N := by exact_mod_cast h2
    linarith
  · exact le_rfl

theorem tentSeq_le (N s : ℕ) : tentSeq N s ≤ N := by
  unfold tentSeq
  split_ifs with h1 h2
  · have : (s : ℝ) + 1 ≤ N := by exact_mod_cast h1
    linarith
  · have : (N : ℝ) ≤ s := by exact_mod_cast Nat.not_lt.mp h1
    linarith
  · positivity

theorem tentSeq_eq_zero_of_ge {N s : ℕ} (hs : 2 * N ≤ s) : tentSeq N s = 0 := by
  unfold tentSeq
  rw [if_neg (by omega), if_neg (by omega)]

/-- Generating-polynomial identity `∑_{s < 2N} a_s z^s = (∑_{j < N} z^j)^2`. -/
theorem sum_tentSeq_mul_pow (N : ℕ) (z : ℂ) :
    (∑ s ∈ Finset.range (2 * N), (tentSeq N s : ℂ) * z ^ s) =
      (∑ j ∈ Finset.range N, z ^ j) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ (f := fun j => z ^ j)]
    have hstep : (∑ s ∈ Finset.range (2 * (N + 1)), (tentSeq (N + 1) s : ℂ) * z ^ s) -
        (∑ s ∈ Finset.range (2 * N), (tentSeq N s : ℂ) * z ^ s) =
        2 * z ^ N * (∑ j ∈ Finset.range N, z ^ j) + z ^ (2 * N) := by
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ]
      have hlast1 : tentSeq (N + 1) (2 * N + 1) = 0 := by
        unfold tentSeq
        rw [if_neg (by omega), if_pos (by omega)]
        push_cast; ring
      have hlast0 : tentSeq (N + 1) (2 * N) = 1 := by
        unfold tentSeq
        rcases Nat.eq_zero_or_pos N with rfl | hN
        · simp
        · rw [if_neg (by omega), if_pos (by omega)]
          push_cast; ring
      rw [hlast1, Complex.ofReal_zero, zero_mul, add_zero, hlast0, Complex.ofReal_one, one_mul]
      have hdiff : (∑ s ∈ Finset.range (2 * N), (tentSeq (N + 1) s : ℂ) * z ^ s) -
          (∑ s ∈ Finset.range (2 * N), (tentSeq N s : ℂ) * z ^ s) =
          2 * z ^ N * (∑ j ∈ Finset.range N, z ^ j) := by
        rw [← Finset.sum_sub_distrib, show 2 * N = N + N by omega, Finset.sum_range_add]
        have hlo : ∑ s ∈ Finset.range N,
            ((tentSeq (N + 1) s : ℂ) * z ^ s - (tentSeq N s : ℂ) * z ^ s) = 0 := by
          refine Finset.sum_eq_zero fun s hs => ?_
          have hsN : s < N := Finset.mem_range.mp hs
          unfold tentSeq
          rw [if_pos (by omega), if_pos hsN, sub_self]
        rw [hlo, zero_add, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjN : j < N := Finset.mem_range.mp hj
        have hval : tentSeq (N + 1) (N + j) - tentSeq N (N + j) = 2 := by
          unfold tentSeq
          rcases Nat.eq_zero_or_pos j with rfl | hj0
          · rw [add_zero, if_pos (by omega), if_neg (by omega), if_pos (by omega)]
            ring
          · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
            push_cast; ring
        have hvalC : (tentSeq (N + 1) (N + j) : ℂ) - (tentSeq N (N + j) : ℂ) = 2 := by
          exact_mod_cast hval
        rw [← sub_mul, hvalC, pow_add]
        ring
      linear_combination hdiff
    linear_combination hstep + ih

theorem sum_tentSeq (N : ℕ) : ∑ s ∈ Finset.range (2 * N), tentSeq N s = (N : ℝ) ^ 2 := by
  have h := congrArg Complex.re (sum_tentSeq_mul_pow N 1)
  simp only [one_pow, mul_one, Complex.re_sum, Complex.ofReal_re, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one] at h
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re] at h
  exact h

/-- Autocorrelation `c_{N, m} = ∑_{s < 2N} a_s a_{s + m}`. -/
def tentCorr (N m : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (2 * N), tentSeq N s * tentSeq N (s + m)

theorem tentCorr_nonneg (N m : ℕ) : 0 ≤ tentCorr N m :=
  Finset.sum_nonneg fun s _ => mul_nonneg (tentSeq_nonneg N s) (tentSeq_nonneg N (s + m))

theorem tentCorr_eq_zero_of_ge {N m : ℕ} (hm : 2 * N ≤ m) : tentCorr N m = 0 := by
  unfold tentCorr
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [tentSeq_eq_zero_of_ge (N := N) (s := s + m) (by omega), mul_zero]

theorem tentCorr_zero_ge (N : ℕ) : (N : ℝ) ^ 3 / 2 ≤ tentCorr N 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [tentCorr]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (2 * N)) (f := tentSeq N)
  rw [Finset.card_range, sum_tentSeq] at hcs
  have heq : ∑ i ∈ Finset.range (2 * N), tentSeq N i ^ 2 = tentCorr N 0 := by
    unfold tentCorr
    refine Finset.sum_congr rfl fun s _ => by simp [sq]
  rw [heq] at hcs
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Nat.cast_mul, Nat.cast_two] at hcs
  rw [div_le_iff₀ (by norm_num)]
  have hpow : ((N : ℝ) ^ 2) ^ 2 = (N : ℝ) * (N : ℝ) ^ 3 := by ring
  rw [hpow] at hcs
  have : (N : ℝ) * (N : ℝ) ^ 3 ≤ (N : ℝ) * (tentCorr N 0 * 2) := by linarith
  exact le_of_mul_le_mul_left this hN0

theorem tentCorr_zero_pos {N : ℕ} (hN : 1 ≤ N) : 0 < tentCorr N 0 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact lt_of_lt_of_le (by positivity) (tentCorr_zero_ge N)

theorem tentCorr_zero_le (N : ℕ) : tentCorr N 0 ≤ (N : ℝ) ^ 3 := by
  calc tentCorr N 0
      = ∑ s ∈ Finset.range (2 * N), tentSeq N s * tentSeq N s := by
          unfold tentCorr; simp
    _ ≤ ∑ s ∈ Finset.range (2 * N), (N : ℝ) * tentSeq N s :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (tentSeq_le N s)
            (tentSeq_nonneg N s)
    _ = (N : ℝ) * ∑ s ∈ Finset.range (2 * N), tentSeq N s := (Finset.mul_sum _ _ _).symm
    _ = (N : ℝ) ^ 3 := by rw [sum_tentSeq]; ring

/-- Exact second-difference identity for the tent autocorrelation. -/
theorem two_mul_tentCorr_zero_sub (N m : ℕ) :
    2 * (tentCorr N 0 - tentCorr N m) =
      (∑ s ∈ Finset.range m, tentSeq N s ^ 2) +
        ∑ s ∈ Finset.range (2 * N), (tentSeq N (s + m) - tentSeq N s) ^ 2 := by
  have htotal : (∑ s ∈ Finset.range m, tentSeq N s ^ 2) +
      (∑ s ∈ Finset.range (2 * N), tentSeq N (s + m) ^ 2) = tentCorr N 0 := by
    have h1 := (Finset.sum_range_add (fun j => tentSeq N j ^ 2) m (2 * N)).symm
    have h2 : ∑ j ∈ Finset.range (m + 2 * N), tentSeq N j ^ 2 = tentCorr N 0 := by
      rw [show m + 2 * N = 2 * N + m by omega, Finset.sum_range_add]
      have hzero : ∑ x ∈ Finset.range m, tentSeq N (2 * N + x) ^ 2 = 0 :=
        Finset.sum_eq_zero fun x _ => by rw [tentSeq_eq_zero_of_ge (by omega)]; ring
      rw [hzero, add_zero]
      unfold tentCorr
      exact Finset.sum_congr rfl fun s _ => by simp [sq]
    rw [← h2, ← h1]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by rw [add_comm]
  have hexp : ∑ s ∈ Finset.range (2 * N), (tentSeq N (s + m) - tentSeq N s) ^ 2 =
      (∑ s ∈ Finset.range (2 * N), tentSeq N (s + m) ^ 2) - 2 * tentCorr N m + tentCorr N 0 := by
    have h0 : tentCorr N 0 = ∑ s ∈ Finset.range (2 * N), tentSeq N s ^ 2 := by
      unfold tentCorr; exact Finset.sum_congr rfl fun s _ => by simp [sq]
    rw [h0]
    unfold tentCorr
    have hterm : ∀ s ∈ Finset.range (2 * N),
        (tentSeq N (s + m) - tentSeq N s) ^ 2 =
          (tentSeq N (s + m) ^ 2 + tentSeq N s ^ 2) - 2 * (tentSeq N s * tentSeq N (s + m)) :=
      fun _ _ => by ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.mul_sum]
    ring
  linarith

theorem tentCorr_le_zero (N m : ℕ) : tentCorr N m ≤ tentCorr N 0 := by
  have h := two_mul_tentCorr_zero_sub N m
  have h1 : 0 ≤ ∑ s ∈ Finset.range m, tentSeq N s ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∑ s ∈ Finset.range (2 * N), (tentSeq N (s + m) - tentSeq N s) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- For `N ≥ 10` and `m ≥ 2`, the Poisson geometric weight `(1 − 1/(256 N^2))^m` dominates
`c_{N, m} / c_{N, 0}`. -/
theorem tentCorr_div_le_poisson_pow {N m : ℕ} (hN : 10 ≤ N) (hm : 2 ≤ m) :
    tentCorr N m / tentCorr N 0 ≤ (1 - 1 / (256 * (N : ℝ) ^ 2)) ^ m := by
  have hN1 : 1 ≤ N := by omega
  have hc0 : 0 < tentCorr N 0 := tentCorr_zero_pos hN1
  have hNR : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 ≤ 1 / (256 * (N : ℝ) ^ 2) := by positivity
  have hx1 : 1 / (256 * (N : ℝ) ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hbern := one_sub_mul_le_pow hx1 m
  by_cases hm2N : 2 * N ≤ m
  · rw [tentCorr_eq_zero_of_ge hm2N, zero_div]
    exact pow_nonneg (by linarith) m
  push Not at hm2N
  refine le_trans ?_ hbern
  rw [mul_one_div]
  by_cases hmhalf : m ≤ N / 2
  · -- Small shifts `2 ≤ m ≤ N/2`: at least `N/2` interior points satisfy `a_{s+m} − a_s = m`.
    have hcard : N ≤ 2 * (N - m) := by omega
    have hcardR : (N : ℝ) / 2 ≤ ((N - m : ℕ) : ℝ) := by
      have : (N : ℝ) ≤ 2 * ((N - m : ℕ) : ℝ) := by exact_mod_cast hcard
      linarith
    have hsub : ((N - m : ℕ) : ℝ) * (m : ℝ) ^ 2 ≤
        ∑ s ∈ Finset.range (2 * N), (tentSeq N (s + m) - tentSeq N s) ^ 2 := by
      calc ((N - m : ℕ) : ℝ) * (m : ℝ) ^ 2
          = ∑ _s ∈ Finset.range (N - m), (m : ℝ) ^ 2 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = ∑ s ∈ Finset.range (N - m), (tentSeq N (s + m) - tentSeq N s) ^ 2 := by
              refine Finset.sum_congr rfl fun s hs => ?_
              have hs' : s < N - m := Finset.mem_range.mp hs
              unfold tentSeq
              rw [if_pos (by omega), if_pos (by omega)]
              push_cast; ring
        _ ≤ ∑ s ∈ Finset.range (2 * N), (tentSeq N (s + m) - tentSeq N s) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.range_mono (by omega)) (fun _ _ _ => sq_nonneg _)
    have hdiff : (N : ℝ) * (m : ℝ) ^ 2 / 4 ≤ tentCorr N 0 - tentCorr N m := by
      have hid := two_mul_tentCorr_zero_sub N m
      have h0 : 0 ≤ ∑ s ∈ Finset.range m, tentSeq N s ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hm2 : ((N : ℝ) / 2) * (m : ℝ) ^ 2 ≤ ((N - m : ℕ) : ℝ) * (m : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcardR (sq_nonneg _)
      linarith
    have hrat : (m : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2) ≤ 1 - tentCorr N m / tentCorr N 0 := by
      rw [show 1 - tentCorr N m / tentCorr N 0 = (tentCorr N 0 - tentCorr N m) / tentCorr N 0 by
        field_simp]
      calc (m : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)
          = ((N : ℝ) * (m : ℝ) ^ 2 / 4) / (N : ℝ) ^ 3 := by field_simp
        _ ≤ (tentCorr N 0 - tentCorr N m) / (N : ℝ) ^ 3 :=
              div_le_div_of_nonneg_right hdiff (by positivity)
        _ ≤ (tentCorr N 0 - tentCorr N m) / tentCorr N 0 :=
              div_le_div_of_nonneg_left (by linarith [tentCorr_le_zero N m]) hc0
                (tentCorr_zero_le N)
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hcmp : (m : ℝ) / (256 * (N : ℝ) ^ 2) ≤ (m : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2) := by
      have hm2 : (m : ℝ) ≤ 64 * (m : ℝ) ^ 2 := by nlinarith
      calc (m : ℝ) / (256 * (N : ℝ) ^ 2)
          ≤ (64 * (m : ℝ) ^ 2) / (256 * (N : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right hm2 (by positivity)
        _ = (m : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2) := by ring
    linarith
  · -- Large shifts `N/2 < m < 2N`: the prefix `∑_{s < N/2} a_s^2` exceeds `c_{N, 0} / 50`.
    push Not at hmhalf
    set L : ℕ := N / 2
    have hL_ge : 9 * N ≤ 20 * L := by omega
    have hLR : (9 / 20 : ℝ) * N ≤ L := by
      have : (9 : ℝ) * N ≤ 20 * L := by exact_mod_cast hL_ge
      linarith
    have hsum_lin : (L : ℝ) ^ 2 / 2 ≤ ∑ s ∈ Finset.range L, tentSeq N s := by
      have htri : ∀ K : ℕ, (K : ℝ) ^ 2 ≤ 2 * ∑ s ∈ Finset.range K, ((s : ℝ) + 1) := by
        intro K
        induction K with
        | zero => simp
        | succ K ih =>
          rw [Finset.sum_range_succ, Nat.cast_succ]
          nlinarith [Nat.cast_nonneg (α := ℝ) K]
      have heq : ∑ s ∈ Finset.range L, tentSeq N s = ∑ s ∈ Finset.range L, ((s : ℝ) + 1) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        have hsL : s < L := Finset.mem_range.mp hs
        unfold tentSeq
        rw [if_pos (by omega)]
      rw [heq]
      linarith [htri L]
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range L) (f := tentSeq N)
    rw [Finset.card_range] at hcs
    have hLpos : (0 : ℝ) < L := by
      have : 5 ≤ L := by omega
      exact_mod_cast (by omega : 0 < L)
    have hsq_ge : (L : ℝ) ^ 3 / 4 ≤ ∑ s ∈ Finset.range L, tentSeq N s ^ 2 := by
      have h1 : ((L : ℝ) ^ 2 / 2) ^ 2 ≤ (∑ s ∈ Finset.range L, tentSeq N s) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hsum_lin 2
      have h2 : (L : ℝ) * ((L : ℝ) ^ 3 / 4) ≤ (L : ℝ) * ∑ s ∈ Finset.range L, tentSeq N s ^ 2 := by
        nlinarith
      exact le_of_mul_le_mul_left h2 hLpos
    have hN3 : (N : ℝ) ^ 3 / 50 ≤ ∑ s ∈ Finset.range m, tentSeq N s ^ 2 := by
      have hcube : ((9 / 20 : ℝ) * N) ^ 3 / 4 ≤ (L : ℝ) ^ 3 / 4 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hLR 3) (by norm_num)
      have h50 : (N : ℝ) ^ 3 / 50 ≤ ((9 / 20 : ℝ) * N) ^ 3 / 4 := by
        have : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
        nlinarith
      exact (h50.trans (hcube.trans hsq_ge)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmhalf.le)
          (fun _ _ _ => sq_nonneg _))
    have hdiff : tentCorr N 0 / 100 ≤ tentCorr N 0 - tentCorr N m := by
      have hid := two_mul_tentCorr_zero_sub N m
      have h0 : 0 ≤ ∑ s ∈ Finset.range (2 * N), (tentSeq N (s + m) - tentSeq N s) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hc_le := tentCorr_zero_le N
      linarith
    have hrat : (1 / 100 : ℝ) ≤ 1 - tentCorr N m / tentCorr N 0 := by
      rw [show 1 - tentCorr N m / tentCorr N 0 = (tentCorr N 0 - tentCorr N m) / tentCorr N 0 by
        field_simp]
      rw [le_div_iff₀ hc0]
      linarith
    have hm_small : (m : ℝ) / (256 * (N : ℝ) ^ 2) ≤ 1 / 100 := by
      have hmR : (m : ℝ) ≤ 2 * N := by exact_mod_cast hm2N.le
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith

/-! ### The normalized Jackson kernel -/

/-- Normalized Jackson kernel `J_N(t) = ‖∑_{s < 2N} a_s e^{2πist}‖^2 / c_{N, 0}`. -/
def jacksonKernel (N : ℕ) (t : ℝ) : ℝ :=
  ‖∑ s ∈ Finset.range (2 * N),
      (tentSeq N s : ℂ) * cexp (((2 * Real.pi * s * t : ℝ) : ℂ) * I)‖ ^ 2 / tentCorr N 0

theorem jacksonKernel_nonneg {N : ℕ} (hN : 1 ≤ N) (t : ℝ) : 0 ≤ jacksonKernel N t :=
  div_nonneg (sq_nonneg _) (tentCorr_zero_pos hN).le

/-- Cosine expansion `J_N(t) = 1 + 2 ∑_{j < M} (c_{N, j+1} / c_{N, 0}) cos(2π(j + 1)t)` for every
`M ≥ 2N`. -/
theorem jacksonKernel_eq_sum {N M : ℕ} (hN : 1 ≤ N) (hM : 2 * N ≤ M) (t : ℝ) :
    jacksonKernel N t = 1 + 2 * ∑ j ∈ Finset.range M,
      (tentCorr N (j + 1) / tentCorr N 0) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t) := by
  have hc0 : (tentCorr N 0 : ℝ) ≠ 0 := (tentCorr_zero_pos hN).ne'
  have hvanish : ∑ s ∈ Finset.range M,
      (tentSeq N s : ℂ) * cexp (((2 * Real.pi * s * t : ℝ) : ℂ) * I) =
      ∑ s ∈ Finset.range (2 * N),
        (tentSeq N s : ℂ) * cexp (((2 * Real.pi * s * t : ℝ) : ℂ) * I) := by
    rw [show M = 2 * N + (M - 2 * N) by omega, Finset.sum_range_add]
    have htail : ∑ x ∈ Finset.range (M - 2 * N),
        (tentSeq N (2 * N + x) : ℂ) * cexp (((2 * Real.pi * (2 * N + x : ℕ) * t : ℝ) : ℂ) * I) =
        0 := Finset.sum_eq_zero fun x _ => by
      rw [tentSeq_eq_zero_of_ge (by omega), Complex.ofReal_zero, zero_mul]
    rw [htail, add_zero]
  unfold jacksonKernel
  rw [← hvanish, norm_sq_trig_sum]
  have hdiag : ∑ s ∈ Finset.range M, tentSeq N s ^ 2 = tentCorr N 0 := by
    rw [show M = 2 * N + (M - 2 * N) by omega, Finset.sum_range_add]
    have htail : ∑ x ∈ Finset.range (M - 2 * N), tentSeq N (2 * N + x) ^ 2 = 0 :=
      Finset.sum_eq_zero fun x _ => by rw [tentSeq_eq_zero_of_ge (by omega)]; ring
    rw [htail, add_zero]
    unfold tentCorr
    exact Finset.sum_congr rfl fun s _ => by simp [sq]
  have hoff : ∀ j ∈ Finset.range M,
      ∑ s ∈ Finset.range (M - (j + 1)), tentSeq N s * tentSeq N (s + (j + 1)) =
        tentCorr N (j + 1) := by
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    by_cases hjm : 2 * N ≤ j + 1
    · rw [tentCorr_eq_zero_of_ge hjm]
      exact Finset.sum_eq_zero fun s _ => by
        rw [tentSeq_eq_zero_of_ge (N := N) (s := s + (j + 1)) (by omega), mul_zero]
    · push Not at hjm
      by_cases hsub : 2 * N ≤ M - (j + 1)
      · rw [show M - (j + 1) = 2 * N + (M - (j + 1) - 2 * N) by omega, Finset.sum_range_add]
        have htail : ∑ x ∈ Finset.range (M - (j + 1) - 2 * N),
            tentSeq N (2 * N + x) * tentSeq N (2 * N + x + (j + 1)) = 0 :=
          Finset.sum_eq_zero fun x _ => by
            rw [tentSeq_eq_zero_of_ge (N := N) (s := 2 * N + x) (by omega), zero_mul]
        rw [htail, add_zero]; rfl
      · push Not at hsub
        unfold tentCorr
        rw [show 2 * N = (M - (j + 1)) + (2 * N - (M - (j + 1))) by omega, Finset.sum_range_add]
        have htail : ∑ x ∈ Finset.range (2 * N - (M - (j + 1))),
            tentSeq N (M - (j + 1) + x) * tentSeq N (M - (j + 1) + x + (j + 1)) = 0 :=
          Finset.sum_eq_zero fun x _ => by
            have hge : 2 * N ≤ M - (j + 1) + x + (j + 1) := by omega
            rw [tentSeq_eq_zero_of_ge hge, mul_zero]
        rw [htail, add_zero]
  rw [hdiag, add_div, div_self hc0]
  congr 1
  rw [mul_div_assoc, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hoff j hj]
  ring

/-- Off-origin localization bound `J_N(u) ≤ 32 / (N^3 ‖1 − e^{2πiu}‖^4)`. -/
theorem jacksonKernel_le {N : ℕ} (hN : 1 ≤ N) {u : ℝ}
    (hu : (1 : ℂ) - cexp (((2 * Real.pi * u : ℝ) : ℂ) * I) ≠ 0) :
    jacksonKernel N u ≤
      32 / ((N : ℝ) ^ 3 * ‖(1 : ℂ) - cexp (((2 * Real.pi * u : ℝ) : ℂ) * I)‖ ^ 4) := by
  set z : ℂ := cexp (((2 * Real.pi * u : ℝ) : ℂ) * I)
  have hrew : (∑ s ∈ Finset.range (2 * N),
      (tentSeq N s : ℂ) * cexp (((2 * Real.pi * s * u : ℝ) : ℂ) * I)) =
      ∑ s ∈ Finset.range (2 * N), (tentSeq N s : ℂ) * z ^ s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  have hpoly : (1 - z) ^ 2 * (∑ s ∈ Finset.range (2 * N), (tentSeq N s : ℂ) * z ^ s) =
      (1 - z ^ N) ^ 2 := by
    rw [sum_tentSeq_mul_pow, ← mul_pow]
    congr 1
    have hgeom := geom_sum_mul z N
    linear_combination -hgeom
  have hnorm_poly : ‖1 - z‖ ^ 2 * ‖∑ s ∈ Finset.range (2 * N), (tentSeq N s : ℂ) * z ^ s‖ ≤ 4 := by
    have h1 := congrArg norm hpoly
    rw [norm_mul, norm_pow, norm_pow] at h1
    have hzn : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have h2 : ‖1 - z ^ N‖ ≤ 2 := by
      calc ‖1 - z ^ N‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ N‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_one, norm_pow, hzn, one_pow]; norm_num
    have h3 : ‖1 - z ^ N‖ ^ 2 ≤ 4 := by
      calc ‖1 - z ^ N‖ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ = 4 := by norm_num
    linarith
  have hsq : ‖1 - z‖ ^ 4 * ‖∑ s ∈ Finset.range (2 * N), (tentSeq N s : ℂ) * z ^ s‖ ^ 2 ≤ 16 := by
    calc ‖1 - z‖ ^ 4 * ‖∑ s ∈ Finset.range (2 * N), (tentSeq N s : ℂ) * z ^ s‖ ^ 2
        = (‖1 - z‖ ^ 2 * ‖∑ s ∈ Finset.range (2 * N), (tentSeq N s : ℂ) * z ^ s‖) ^ 2 := by ring
      _ ≤ 4 ^ 2 := pow_le_pow_left₀ (by positivity) hnorm_poly 2
      _ = 16 := by norm_num
  have hnz : 0 < ‖1 - z‖ := norm_pos_iff.mpr hu
  have hc0 := tentCorr_zero_ge N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold jacksonKernel
  rw [hrew]
  calc ‖∑ s ∈ Finset.range (2 * N), (tentSeq N s : ℂ) * z ^ s‖ ^ 2 / tentCorr N 0
      ≤ (16 / ‖1 - z‖ ^ 4) / ((N : ℝ) ^ 3 / 2) := by
          refine div_le_div₀ (by positivity) ?_ (by positivity) hc0
          rwa [le_div_iff₀' (by positivity)]
    _ = 32 / ((N : ℝ) ^ 3 * ‖1 - z‖ ^ 4) := by field_simp; ring

/-! ### The Poisson kernel -/

/-- Torus Poisson kernel `P_r(t) = 1 + 2 ∑_{m ≥ 1} r^m cos(2πmt)`. -/
def torusPoisson (r t : ℝ) : ℝ :=
  1 + 2 * ∑' j : ℕ, r ^ (j + 1) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t)

theorem summable_poissonTerm {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    Summable fun j : ℕ => r ^ (j + 1) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left r) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr0 _), pow_succ']
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

/-- Closed-form lower bound `P_r(t) ≥ (1 − r) / 2` for `0 ≤ r < 1`. -/
theorem torusPoisson_ge {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    (1 - r) / 2 ≤ torusPoisson r t := by
  set w : ℂ := (r : ℂ) * cexp (((2 * Real.pi * t : ℝ) : ℂ) * I)
  have hwn : ‖w‖ = r := by
    simp only [w, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hgeom := hasSum_geometric_of_norm_lt_one (show ‖w‖ < 1 by rw [hwn]; exact hr1)
  have hre := Complex.reCLM.hasSum hgeom
  simp only [Complex.reCLM_apply] at hre
  have hterm : (fun m : ℕ => (w ^ m).re) =
      fun m : ℕ => r ^ m * Real.cos (2 * Real.pi * (m : ℝ) * t) := by
    ext m
    simp only [w, mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul]
    rw [show (m : ℂ) * (((2 * Real.pi * t : ℝ) : ℂ) * I) =
        ((2 * Real.pi * (m : ℝ) * t : ℝ) : ℂ) * I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [hterm] at hre
  have hsum := hre.summable
  have hsplit := hsum.tsum_eq_zero_add
  rw [hre.tsum_eq] at hsplit
  simp only [pow_zero, Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one] at hsplit
  have hp : torusPoisson r t = 2 * ((1 - w)⁻¹).re - 1 := by
    unfold torusPoisson
    have hshift : (∑' j : ℕ, r ^ (j + 1) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t)) =
        ∑' j : ℕ, r ^ (j + 1) * Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * t) := rfl
    linarith [hsplit]
  have hnsq_pos : 0 < Complex.normSq (1 - w) := by
    rw [Complex.normSq_pos]
    intro h0
    have : w = 1 := by linear_combination -h0
    rw [this, norm_one] at hwn
    linarith
  have hnsq_eq : Complex.normSq (1 - w) = 1 - 2 * w.re + r ^ 2 := by
    have hw_sq : Complex.normSq w = r ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, hwn]
    rw [Complex.normSq_apply] at hw_sq ⊢
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub]
    linarith
  have hval : 2 * ((1 - w)⁻¹).re - 1 = (1 - r ^ 2) / Complex.normSq (1 - w) := by
    rw [Complex.inv_re, Complex.sub_re, Complex.one_re]
    field_simp [hnsq_pos.ne']
    linarith [hnsq_eq]
  have hnsq_le : Complex.normSq (1 - w) ≤ (1 + r) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    have h1 : ‖1 - w‖ ≤ 1 + r := by
      calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
        _ = 1 + r := by rw [norm_one, hwn]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [hp, hval]
  calc (1 - r) / 2
      ≤ (1 - r) / (1 + r) :=
          div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
    _ = (1 - r ^ 2) / (1 + r) ^ 2 := by field_simp; ring
    _ ≤ (1 - r ^ 2) / Complex.normSq (1 - w) :=
          div_le_div_of_nonneg_left (by nlinarith) hnsq_pos hnsq_le

theorem abs_poissonTail_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) (t : ℝ) :
    |∑' i : ℕ, r ^ (i + M + 1) * Real.cos (2 * Real.pi * (i + M + 1 : ℕ) * t)| ≤
      r ^ (M + 1) / (1 - r) := by
  have hdom : Summable fun i : ℕ => r ^ (i + M + 1) := by
    refine ((summable_geometric_of_lt_one hr0 hr1).mul_left (r ^ (M + 1))).congr fun i => ?_
    rw [← pow_add, show M + 1 + i = i + M + 1 by omega]
  have hterm : ∀ i : ℕ,
      ‖r ^ (i + M + 1) * Real.cos (2 * Real.pi * (i + M + 1 : ℕ) * t)‖ ≤ r ^ (i + M + 1) := by
    intro i
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr0 _)]
    exact mul_le_of_le_one_right (pow_nonneg hr0 _) (Real.abs_cos_le_one _)
  have hsum : Summable fun i : ℕ =>
      r ^ (i + M + 1) * Real.cos (2 * Real.pi * (i + M + 1 : ℕ) * t) :=
    Summable.of_norm_bounded hdom hterm
  rw [← Real.norm_eq_abs]
  calc ‖∑' i : ℕ, r ^ (i + M + 1) * Real.cos (2 * Real.pi * (i + M + 1 : ℕ) * t)‖
      ≤ ∑' i : ℕ, ‖r ^ (i + M + 1) * Real.cos (2 * Real.pi * (i + M + 1 : ℕ) * t)‖ :=
          norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' i : ℕ, r ^ (i + M + 1) := Summable.tsum_le_tsum hterm hsum.norm hdom
    _ = ∑' i : ℕ, r ^ (M + 1) * r ^ i := by
          refine tsum_congr fun i => ?_
          rw [show i + M + 1 = (M + 1) + i by omega, pow_add]
    _ = r ^ (M + 1) / (1 - r) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

end CosineArcConcentration

open CosineArcConcentration in
/-- **Zero-mean integer-coefficient cosine concentration outside a periodic hole.**
For every `0 < δ ≤ 1/2`, there exist `M ≥ 1`, integer weights `p : ℕ → ℕ` with `∑_{m=1}^M p_m ≥ 1`,
and `η > 0` such that whenever `|t − (n + 1/2)| ≥ δ/2` for all `n ∈ ℤ`,
`∑_{m=1}^M p_m cos(2πmt) ≥ η ∑_{m=1}^M p_m`. -/
theorem exists_nat_cosine_sum_pos_off_hole {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ (M : ℕ) (p : ℕ → ℕ) (η : ℝ),
      1 ≤ M ∧ 1 ≤ ∑ m ∈ Finset.Icc 1 M, p m ∧ 0 < η ∧
      ∀ t : ℝ, (∀ n : ℤ, δ / 2 ≤ |t - (n + 1 / 2)|) →
        η * (∑ m ∈ Finset.Icc 1 M, (p m : ℝ)) ≤
          ∑ m ∈ Finset.Icc 1 M, (p m : ℝ) * Real.cos (2 * Real.pi * m * t) := by
  set N : ℕ := ⌈4096 / δ ^ 4⌉₊ + 10
  have hN10 : 10 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNR : (10 : ℝ) ≤ N := by exact_mod_cast hN10
  have hN_large : 4096 / δ ^ 4 ≤ N := by
    have := Nat.le_ceil (4096 / δ ^ 4)
    have hcast : (⌈4096 / δ ^ 4⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈4096 / δ ^ 4⌉₊ ≤ N)
    linarith
  set r : ℝ := 1 - 1 / (256 * (N : ℝ) ^ 2)
  have hr_sub : 1 - r = 1 / (256 * (N : ℝ) ^ 2) := by simp only [r]; ring
  have hr0 : 0 ≤ r := by
    have : 1 / (256 * (N : ℝ) ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hr_pos : 0 < r := by
    have : 1 / (256 * (N : ℝ) ^ 2) < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    linarith
  have hr1 : r < 1 := by
    have : 0 < 1 / (256 * (N : ℝ) ^ 2) := by positivity
    linarith
  set η₀ : ℝ := 1 / (4096 * (N : ℝ) ^ 2)
  have hη₀ : 0 < η₀ := by positivity
  obtain ⟨M₀, hM₀⟩ := exists_pow_lt_of_lt_one (mul_pos hη₀ (sub_pos.mpr hr1)) hr1
  set M : ℕ := max (2 * N) M₀
  have hM2N : 2 * N ≤ M := le_max_left _ _
  have hM1 : 1 ≤ M := by omega
  have hrM : r ^ (M + 1) / (1 - r) ≤ η₀ := by
    rw [div_le_iff₀ (sub_pos.mpr hr1)]
    have hle : r ^ (M + 1) ≤ r ^ M₀ :=
      pow_le_pow_of_le_one hr0 hr1.le (le_trans (le_max_right _ _) (Nat.le_succ M))
    exact hle.trans hM₀.le
  -- Nonnegative real Fourier weights `α_m` of `½ J_N(t) + ½ P_r(t) − J_N(t − ½)`
  set α : ℕ → ℝ := fun m =>
    r ^ m + (1 - 2 * (-1 : ℝ) ^ m) * (tentCorr N m / tentCorr N 0)
  have hα_nonneg : ∀ m : ℕ, 1 ≤ m → 0 ≤ α m := by
    intro m hm
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · have hm2 : 2 ≤ 2 * k := by omega
      have hpow : (-1 : ℝ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
      simp only [α, hpow]
      linarith [tentCorr_div_le_poisson_pow hN10 hm2]
    · have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_add, pow_mul]; norm_num
      simp only [α, hpow]
      have hdiv : 0 ≤ tentCorr N (2 * k + 1) / tentCorr N 0 :=
        div_nonneg (tentCorr_nonneg N _) (tentCorr_zero_pos hN1).le
      have hrp : 0 ≤ r ^ (2 * k + 1) := pow_nonneg hr0 _
      linarith
  have hα_le : ∀ m : ℕ, α m ≤ 4 := by
    intro m
    have hr_le : r ^ m ≤ 1 := pow_le_one₀ hr0 hr1.le
    have hdiv_nn : 0 ≤ tentCorr N m / tentCorr N 0 :=
      div_nonneg (tentCorr_nonneg N m) (tentCorr_zero_pos hN1).le
    have hdiv_le : tentCorr N m / tentCorr N 0 ≤ 1 :=
      (div_le_one (tentCorr_zero_pos hN1)).mpr (tentCorr_le_zero N m)
    have hsign : |1 - 2 * (-1 : ℝ) ^ m| ≤ 3 := by
      rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
      · have : (-1 : ℝ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
        rw [this]; norm_num
      · have : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_add, pow_mul]; norm_num
        rw [this]; norm_num
    have hmul : (1 - 2 * (-1 : ℝ) ^ m) * (tentCorr N m / tentCorr N 0) ≤ 3 := by
      have h1 := le_abs_self (1 - 2 * (-1 : ℝ) ^ m)
      nlinarith
    simp only [α]
    linarith
  have hα1_pos : 0 < α 1 := by
    simp only [α, pow_one]
    have hdiv : 0 ≤ tentCorr N 1 / tentCorr N 0 :=
      div_nonneg (tentCorr_nonneg N 1) (tentCorr_zero_pos hN1).le
    linarith
  -- Truncated real cosine sum off the holes
  have hreal_off : ∀ t : ℝ, (∀ n : ℤ, δ / 2 ≤ |t - (n + 1 / 2)|) →
      η₀ ≤ ∑ j ∈ Finset.range M, α (j + 1) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t) := by
    intro t ht
    have hJ0 := jacksonKernel_nonneg hN1 t
    have hP := torusPoisson_ge hr0 hr1 t
    have hdist_shift : ∀ n : ℤ, δ / 2 ≤ |(t - 1 / 2) - n| := fun n => by
      rw [show (t - 1 / 2) - (n : ℝ) = t - ((n : ℝ) + 1 / 2) by ring]
      exact ht n
    have hchord := two_mul_le_norm_one_sub_exp hδ0.le hdist_shift
    have hne : (1 : ℂ) - cexp (((2 * Real.pi * (t - 1 / 2) : ℝ) : ℂ) * I) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hchord
      linarith
    have hJshift : jacksonKernel N (t - 1 / 2) ≤ 2 * η₀ := by
      have h1 := jacksonKernel_le hN1 hne
      have h4 : (2 * δ) ^ 4 ≤
          ‖(1 : ℂ) - cexp (((2 * Real.pi * (t - 1 / 2) : ℝ) : ℂ) * I)‖ ^ 4 :=
        pow_le_pow_left₀ (by positivity) hchord 4
      have hNδ : 4096 ≤ (N : ℝ) * δ ^ 4 := by
        rwa [div_le_iff₀ (by positivity)] at hN_large
      have hden : 16 * 4096 * (N : ℝ) ^ 2 ≤
          (N : ℝ) ^ 3 * ‖(1 : ℂ) - cexp (((2 * Real.pi * (t - 1 / 2) : ℝ) : ℂ) * I)‖ ^ 4 := by
        calc 16 * 4096 * (N : ℝ) ^ 2
            ≤ 16 * ((N : ℝ) * δ ^ 4) * (N : ℝ) ^ 2 := by nlinarith
          _ = (N : ℝ) ^ 3 * (2 * δ) ^ 4 := by ring
          _ ≤ (N : ℝ) ^ 3 * ‖(1 : ℂ) - cexp (((2 * Real.pi * (t - 1 / 2) : ℝ) : ℂ) * I)‖ ^ 4 :=
                mul_le_mul_of_nonneg_left h4 (by positivity)
      calc jacksonKernel N (t - 1 / 2)
          ≤ 32 / ((N : ℝ) ^ 3 *
              ‖(1 : ℂ) - cexp (((2 * Real.pi * (t - 1 / 2) : ℝ) : ℂ) * I)‖ ^ 4) := h1
        _ ≤ 32 / (16 * 4096 * (N : ℝ) ^ 2) :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
        _ = 2 * η₀ := by simp only [η₀]; field_simp; ring
    -- Relate the finite sum of `α` to `½ J_N(t) + ½ P_r(t) − J_N(t − ½)` minus the Poisson tail
    have hJ_eq := jacksonKernel_eq_sum hN1 hM2N t
    have hJshift_eq : jacksonKernel N (t - 1 / 2) = 1 + 2 * ∑ j ∈ Finset.range M,
        (-1 : ℝ) ^ (j + 1) * (tentCorr N (j + 1) / tentCorr N 0) *
          Real.cos (2 * Real.pi * (j + 1 : ℕ) * t) := by
      rw [jacksonKernel_eq_sum hN1 hM2N (t - 1 / 2)]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      have harg : 2 * Real.pi * (j + 1 : ℕ) * (t - 1 / 2) =
          2 * Real.pi * (j + 1 : ℕ) * t - ((j + 1 : ℕ) : ℝ) * Real.pi := by ring
      rw [harg, cos_sub_nat_mul_pi]
      ring
    have hP_split : torusPoisson r t = 1 +
        2 * (∑ j ∈ Finset.range M, r ^ (j + 1) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t)) +
        2 * ∑' i : ℕ, r ^ (i + M + 1) * Real.cos (2 * Real.pi * (i + M + 1 : ℕ) * t) := by
      unfold torusPoisson
      rw [← (summable_poissonTerm hr0 hr1 t).sum_add_tsum_nat_add M]
      have hshift : (∑' i : ℕ, r ^ (i + M + 1) * Real.cos (2 * Real.pi * (i + M + 1 : ℕ) * t)) =
          ∑' i : ℕ, r ^ (i + M + 1) * Real.cos (2 * Real.pi * ((i + M : ℕ) + 1 : ℕ) * t) := by
        refine tsum_congr fun i => by rw [Nat.add_assoc]
      rw [hshift]
      ring
    have hcomb : (∑ j ∈ Finset.range M, α (j + 1) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t)) =
        (1 / 2) * jacksonKernel N t + (1 / 2) * torusPoisson r t - jacksonKernel N (t - 1 / 2) -
          ∑' i : ℕ, r ^ (i + M + 1) * Real.cos (2 * Real.pi * (i + M + 1 : ℕ) * t) := by
      rw [hJ_eq, hP_split, hJshift_eq]
      have hsum_α : (∑ j ∈ Finset.range M, α (j + 1) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t)) =
          (∑ j ∈ Finset.range M, r ^ (j + 1) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t)) +
          (∑ j ∈ Finset.range M,
            (tentCorr N (j + 1) / tentCorr N 0) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t)) -
          2 * ∑ j ∈ Finset.range M,
            (-1 : ℝ) ^ (j + 1) * (tentCorr N (j + 1) / tentCorr N 0) *
              Real.cos (2 * Real.pi * (j + 1 : ℕ) * t) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [α]
        ring
      linarith
    have htail_le : ∑' i : ℕ, r ^ (i + M + 1) * Real.cos (2 * Real.pi * (i + M + 1 : ℕ) * t) ≤
        η₀ := (le_abs_self _).trans ((abs_poissonTail_le hr0 hr1 M t).trans hrM)
    have hP_ge : 4 * η₀ ≤ (1 / 2) * torusPoisson r t := by
      have : (1 - r) / 4 = 4 * η₀ := by rw [hr_sub]; simp only [η₀]; field_simp; ring
      linarith
    linarith
  -- Round scaled coefficients up to natural numbers
  set Q : ℕ := ⌈2 * (M : ℝ) / η₀⌉₊ + 1
  have hQ1 : 1 ≤ Q := by omega
  have hQR : 2 * (M : ℝ) / η₀ ≤ Q := by
    have := Nat.le_ceil (2 * (M : ℝ) / η₀)
    have hcast : (⌈2 * (M : ℝ) / η₀⌉₊ : ℝ) ≤ Q := by exact_mod_cast (by omega : ⌈2 * (M : ℝ) / η₀⌉₊ ≤ Q)
    linarith
  set p : ℕ → ℕ := fun m => ⌈(Q : ℝ) * α m⌉₊
  set η : ℝ := η₀ / (10 * (M : ℝ))
  have hMR_pos : (0 : ℝ) < M := by exact_mod_cast hM1
  refine ⟨M, p, η, hM1, ?_, by positivity, fun t ht => ?_⟩
  · have hp1 : 1 ≤ p 1 := Nat.one_le_iff_ne_zero.mpr <|
      (Nat.ceil_pos.mpr (mul_pos (by exact_mod_cast hQ1) hα1_pos)).ne'
    exact hp1.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_Icc.mpr ⟨le_rfl, hM1⟩))
  · have hIcc_eq : ∀ f : ℕ → ℝ, ∑ m ∈ Finset.Icc 1 M, f m = ∑ j ∈ Finset.range M, f (j + 1) := by
      intro f
      have hset : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by ext x; simp
      rw [hset, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ => by rw [add_comm]
    have hD_le : (∑ m ∈ Finset.Icc 1 M, (p m : ℝ)) ≤ 5 * (M : ℝ) * Q := by
      rw [hIcc_eq]
      calc (∑ j ∈ Finset.range M, (p (j + 1) : ℝ))
          ≤ ∑ _j ∈ Finset.range M, (5 * (Q : ℝ)) := by
              refine Finset.sum_le_sum fun j _ => ?_
              have hnn : 0 ≤ (Q : ℝ) * α (j + 1) :=
                mul_nonneg (Nat.cast_nonneg Q) (hα_nonneg (j + 1) (by omega))
              have hceil := (Nat.ceil_lt_add_one hnn).le
              have hle4 := hα_le (j + 1)
              have hQ1R : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
              simp only [p]
              nlinarith
        _ = 5 * (M : ℝ) * Q := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have hcos_ge : (Q : ℝ) * η₀ - M ≤
        ∑ m ∈ Finset.Icc 1 M, (p m : ℝ) * Real.cos (2 * Real.pi * m * t) := by
      rw [hIcc_eq]
      have hdiff : (∑ j ∈ Finset.range M,
          ((Q : ℝ) * α (j + 1) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t) -
            (p (j + 1) : ℝ) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t))) ≤ M := by
        calc (∑ j ∈ Finset.range M,
              ((Q : ℝ) * α (j + 1) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t) -
                (p (j + 1) : ℝ) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t)))
            ≤ ∑ _j ∈ Finset.range M, (1 : ℝ) := by
                refine Finset.sum_le_sum fun j _ => ?_
                have hnn : 0 ≤ (Q : ℝ) * α (j + 1) :=
                  mul_nonneg (Nat.cast_nonneg Q) (hα_nonneg (j + 1) (by omega))
                have hlo : (Q : ℝ) * α (j + 1) ≤ p (j + 1) := Nat.le_ceil _
                have hhi : (p (j + 1) : ℝ) ≤ (Q : ℝ) * α (j + 1) + 1 :=
                  (Nat.ceil_lt_add_one hnn).le
                have hcos := Real.abs_cos_le_one (2 * Real.pi * (j + 1 : ℕ) * t)
                rw [abs_le] at hcos
                nlinarith
          _ = M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [Finset.sum_sub_distrib] at hdiff
      have hQsum : (Q : ℝ) * η₀ ≤
          ∑ j ∈ Finset.range M,
            (Q : ℝ) * α (j + 1) * Real.cos (2 * Real.pi * (j + 1 : ℕ) * t) := by
        have h1 := mul_le_mul_of_nonneg_left (hreal_off t ht) (Nat.cast_nonneg Q)
        rw [Finset.mul_sum] at h1
        refine h1.trans (le_of_eq (Finset.sum_congr rfl fun j _ => by ring))
      linarith
    have hQη : 2 * (M : ℝ) ≤ (Q : ℝ) * η₀ := by
      have := (div_le_iff₀ hη₀).mp hQR
      linarith
    have hgoal1 : η * (∑ m ∈ Finset.Icc 1 M, (p m : ℝ)) ≤ (Q : ℝ) * η₀ / 2 := by
      calc η * (∑ m ∈ Finset.Icc 1 M, (p m : ℝ))
          ≤ (η₀ / (10 * (M : ℝ))) * (5 * (M : ℝ) * Q) :=
              mul_le_mul_of_nonneg_left hD_le (by positivity)
        _ = (Q : ℝ) * η₀ / 2 := by field_simp; ring
    linarith

end GaloisForLFunctions.SurfaceOfSpecZ
