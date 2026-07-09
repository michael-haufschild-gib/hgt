import Mathlib

/-!
# The theta-side polynomial envelope

Coefficients with a polynomial bound `‖a n‖ ≤ C·n^A` make the exponential sum
`θ(x) = ∑' n, a n · exp(−n·x)` absolutely convergent on the right half-plane `Re x > 0`
(`theta_summable`) and give it the polynomial envelope

  `‖θ(x)‖ ≤ 3 · A! · 2^A · C / (Re x)^(A+1)`   for `0 < Re x ≤ 1`   (`theta_halfplane_bound`).

**Mechanism.**  Split `e^{−nσ} = e^{−nσ/2}·e^{−nσ/2}` with `σ = Re x`.  The elementary envelope
`y^A·e^{−y} ≤ A!` at `y = nσ/2` converts the polynomial weight and the first exponential factor
into the static bound `A!·(2/σ)^A`; the second factor sums geometrically, and on `0 < σ ≤ 1` the
denominator obeys `1 − e^{−σ/2} ≥ σ/3`.

The envelope depends on `x` only through `Re x`, so it is uniform on every ray of the open right
half-plane: this is the growth input for rotating a Mellin transform of `θ` inside the sector
`|arg x| < π/2`, where the loss is polynomial in `1/cos(arg x)` while the kernel gains the decay
`e^{−t·arg x}`.
-/

noncomputable section

namespace RHTower

open Complex

/-- The elementary envelope `y^k ≤ k!·e^y` for `y ≥ 0`: the single term `y^k/k!` of the
exponential series is at most the whole series. -/
theorem pow_le_factorial_mul_exp {y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    y ^ k ≤ (k.factorial : ℝ) * Real.exp y := by
  have hkpos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hterm : y ^ k / (k.factorial : ℝ)
      ≤ ∑ i ∈ Finset.range (k + 1), y ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (f := fun i => y ^ i / (i.factorial : ℝ))
      (fun i _ => by positivity) (Finset.self_mem_range_succ k)
  exact (div_le_iff₀' hkpos).mp (hterm.trans (Real.sum_le_exp_of_nonneg hy (k + 1)))

/-- The decaying form of the elementary envelope: `y^k·e^{−y} ≤ k!` for `y ≥ 0`. -/
theorem pow_mul_exp_neg_le {y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    y ^ k * Real.exp (-y) ≤ (k.factorial : ℝ) := by
  calc y ^ k * Real.exp (-y)
      ≤ ((k.factorial : ℝ) * Real.exp y) * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right (pow_le_factorial_mul_exp hy k) (Real.exp_pos _).le
    _ = (k.factorial : ℝ) := by rw [mul_assoc, ← Real.exp_add]; simp

/-- On `0 < σ ≤ 1` the geometric denominator at half rate obeys `1 − e^{−σ/2} ≥ σ/3`:
from `e^{σ/2} ≥ 1 + σ/2` one gets `e^{−σ/2} ≤ 1/(1 + σ/2)`, and `1 − 1/(1+σ/2) = (σ/2)/(1+σ/2)
≥ σ/3` because `1 + σ/2 ≤ 3/2`. -/
theorem one_sub_exp_neg_half_ge {σ : ℝ} (h0 : 0 < σ) (h1 : σ ≤ 1) :
    σ / 3 ≤ 1 - Real.exp (-(σ / 2)) := by
  have hexp : 1 + σ / 2 ≤ Real.exp (σ / 2) := by
    have := Real.add_one_le_exp (σ / 2); linarith
  have hinv : Real.exp (-(σ / 2)) * (1 + σ / 2) ≤ 1 := by
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
    calc 1 + σ / 2 ≤ Real.exp (σ / 2) := hexp
      _ = Real.exp (σ / 2) * 1 := by ring
  nlinarith [Real.exp_pos (-(σ / 2))]

/-- Per-term envelope: for `σ > 0`,
`n^A·e^{−nσ} ≤ A!·(2/σ)^A·e^{−nσ/2}` — the polynomial weight is absorbed into a static constant
at the cost of halving the decay rate. -/
theorem pow_mul_exp_neg_term_envelope {σ : ℝ} (h0 : 0 < σ) (A n : ℕ) :
    (n : ℝ) ^ A * Real.exp (-((n : ℝ) * σ)) ≤
      (A.factorial : ℝ) * (2 / σ) ^ A * Real.exp (-((n : ℝ) * σ / 2)) := by
  have key : ((n : ℝ) * σ / 2) ^ A * Real.exp (-((n : ℝ) * σ / 2)) ≤ (A.factorial : ℝ) :=
    pow_mul_exp_neg_le (by positivity) A
  have hsplit : (n : ℝ) ^ A = ((n : ℝ) * σ / 2) ^ A * (2 / σ) ^ A := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hexp2 : Real.exp (-((n : ℝ) * σ)) =
      Real.exp (-((n : ℝ) * σ / 2)) * Real.exp (-((n : ℝ) * σ / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit, hexp2]
  calc ((n : ℝ) * σ / 2) ^ A * (2 / σ) ^ A *
        (Real.exp (-((n : ℝ) * σ / 2)) * Real.exp (-((n : ℝ) * σ / 2)))
      = (((n : ℝ) * σ / 2) ^ A * Real.exp (-((n : ℝ) * σ / 2))) *
        ((2 / σ) ^ A * Real.exp (-((n : ℝ) * σ / 2))) := by ring
    _ ≤ (A.factorial : ℝ) * ((2 / σ) ^ A * Real.exp (-((n : ℝ) * σ / 2))) :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = (A.factorial : ℝ) * (2 / σ) ^ A * Real.exp (-((n : ℝ) * σ / 2)) := by ring

/-- Absolute convergence of the polynomially weighted exponential sum on `σ > 0`. -/
theorem summable_pow_mul_exp_neg (A : ℕ) {σ : ℝ} (h0 : 0 < σ) :
    Summable (fun n : ℕ => (n : ℝ) ^ A * Real.exp (-((n : ℝ) * σ))) := by
  have hr : ‖Real.exp (-σ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  refine (summable_pow_mul_geometric_of_norm_lt_one (k := A) hr).congr fun n => ?_
  rw [← Real.exp_nat_mul, show (n : ℝ) * -σ = -((n : ℝ) * σ) from by ring]

/-- The geometric tail at half rate: for `0 < σ ≤ 1`, `∑' n, e^{−nσ/2} ≤ 3/σ`. -/
theorem tsum_exp_neg_half_le {σ : ℝ} (h0 : 0 < σ) (h1 : σ ≤ 1) :
    ∑' n : ℕ, Real.exp (-((n : ℝ) * σ / 2)) ≤ 3 / σ := by
  have hrpos : (0 : ℝ) ≤ Real.exp (-(σ / 2)) := (Real.exp_pos _).le
  have hrlt : Real.exp (-(σ / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have heq : (fun n : ℕ => Real.exp (-((n : ℝ) * σ / 2)))
      = fun n : ℕ => (Real.exp (-(σ / 2))) ^ n := by
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq, tsum_geometric_of_lt_one hrpos hrlt]
  have hden := one_sub_exp_neg_half_ge h0 h1
  have hpos : 0 < 1 - Real.exp (-(σ / 2)) := lt_of_lt_of_le (by linarith) hden
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  calc (1 : ℝ) = 3 / σ * (σ / 3) := by field_simp
    _ ≤ 3 / σ * (1 - Real.exp (-(σ / 2))) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- Absolute convergence of `θ(x) = ∑' n, a n · exp(−n·x)` on the open right half-plane, for
coefficients with a polynomial bound. -/
theorem theta_summable {a : ℕ → ℂ} {A : ℕ} {C : ℝ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ A) {x : ℂ} (hx0 : 0 < x.re) :
    Summable (fun n : ℕ => a n * Complex.exp (-(n : ℂ) * x)) := by
  refine Summable.of_norm ?_
  have hterm : ∀ n : ℕ, ‖a n * Complex.exp (-(n : ℂ) * x)‖
      = ‖a n‖ * Real.exp (-((n : ℝ) * x.re)) := by
    intro n
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (((summable_pow_mul_exp_neg A hx0).mul_left C))
  rw [hterm n, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (ha n) (Real.exp_pos _).le

/-- **The theta-side polynomial envelope.**  For coefficients with the polynomial bound
`‖a n‖ ≤ C·n^A` and `0 < Re x ≤ 1`,

  `‖∑' n, a n · exp(−n·x)‖ ≤ 3·A!·2^A·C / (Re x)^(A+1)`.

The bound reads only `Re x`, so it is uniform on every ray `arg x = φ`, `|φ| < π/2`, of the right
half-plane — the input that prices the rotation of a Mellin contour towards the boundary rays. -/
theorem theta_halfplane_bound {a : ℕ → ℂ} {A : ℕ} {C : ℝ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ A) {x : ℂ}
    (hx0 : 0 < x.re) (hx1 : x.re ≤ 1) :
    ‖∑' n : ℕ, a n * Complex.exp (-(n : ℂ) * x)‖ ≤
      3 * (A.factorial : ℝ) * 2 ^ A * C / x.re ^ (A + 1) := by
  have hC : 0 ≤ C := le_trans (norm_nonneg (a 1)) (by simpa using ha 1)
  set σ := x.re with hσ
  have hterm : ∀ n : ℕ, ‖a n * Complex.exp (-(n : ℂ) * x)‖
      = ‖a n‖ * Real.exp (-((n : ℝ) * σ)) := by
    intro n
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re, hσ]
  -- the three comparison series
  have hsum_pow : Summable (fun n : ℕ => (n : ℝ) ^ A * Real.exp (-((n : ℝ) * σ))) :=
    summable_pow_mul_exp_neg A hx0
  have hsum_env : Summable
      (fun n : ℕ => (A.factorial : ℝ) * (2 / σ) ^ A * Real.exp (-((n : ℝ) * σ / 2))) := by
    have hhalf : Summable (fun n : ℕ => Real.exp (-((n : ℝ) * σ / 2))) := by
      refine (summable_pow_mul_exp_neg 0 (by linarith : (0 : ℝ) < σ / 2)).congr fun n => ?_
      rw [pow_zero, one_mul]
      congr 1
      ring
    exact hhalf.mul_left _
  have hsum_norm : Summable (fun n : ℕ => ‖a n * Complex.exp (-(n : ℂ) * x)‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (hsum_pow.mul_left C)
    rw [hterm n, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (ha n) (Real.exp_pos _).le
  -- assemble
  calc ‖∑' n : ℕ, a n * Complex.exp (-(n : ℂ) * x)‖
      ≤ ∑' n : ℕ, ‖a n * Complex.exp (-(n : ℂ) * x)‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' n : ℕ, C * ((n : ℝ) ^ A * Real.exp (-((n : ℝ) * σ))) := by
        refine hsum_norm.tsum_le_tsum (fun n => ?_) (hsum_pow.mul_left C)
        rw [hterm n, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (ha n) (Real.exp_pos _).le
    _ = C * ∑' n : ℕ, (n : ℝ) ^ A * Real.exp (-((n : ℝ) * σ)) := tsum_mul_left
    _ ≤ C * ((A.factorial : ℝ) * (2 / σ) ^ A * ∑' n : ℕ, Real.exp (-((n : ℝ) * σ / 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        calc ∑' n : ℕ, (n : ℝ) ^ A * Real.exp (-((n : ℝ) * σ))
            ≤ ∑' n : ℕ, (A.factorial : ℝ) * (2 / σ) ^ A * Real.exp (-((n : ℝ) * σ / 2)) :=
              hsum_pow.tsum_le_tsum
                (fun n => pow_mul_exp_neg_term_envelope hx0 A n) hsum_env
          _ = (A.factorial : ℝ) * (2 / σ) ^ A * ∑' n : ℕ, Real.exp (-((n : ℝ) * σ / 2)) := by
              rw [← tsum_mul_left]
    _ ≤ C * ((A.factorial : ℝ) * (2 / σ) ^ A * (3 / σ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        exact mul_le_mul_of_nonneg_left (tsum_exp_neg_half_le hx0 hx1) (by positivity)
    _ = 3 * (A.factorial : ℝ) * 2 ^ A * C / σ ^ (A + 1) := by
        rw [div_pow, pow_succ]
        field_simp

end RHTower
