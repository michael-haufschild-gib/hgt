/-
Doc 51 §§5, 9 + doc 46 §5 (task #157): the (HOLD-phase) proved bricks.

* `pair_hasDerivAt` / `pair_deriv_norm` — the two-zero factorization identity
  |Z′(iη)| = 2η|g(iη)| for Z(v) = (v² + η²)g(v): the exact reach denominator
  of doc 46 §5, the (MOAT-shallow) technology at the derivative level.
* `hold_kill_criterion` — the dichotomy margin algebra: the holding term of
  capacity A and alignment c kills the pair of depth d iff (A/d)·(−c) ≥ 1 —
  the cos(slip)·R ≥ 1 criterion of doc 51 §9(b) in exact form.
* `coherent_sum_lower` — the coherent accumulation lower bound: within a
  third-of-π of total phase spread, a nonneg-amplitude sum keeps at least
  half its mass. This is the |H|-growth engine: the background stiffens as
  the tail leaves anti-phase.

The remaining analytic content of (HOLD-phase) — the configurational |H|
anti-correlation — enters `MidCentral` as a named hypothesis field.
-/
import Mathlib

namespace RHTower

/-- The two-zero pair carrier Z(v) = (v² + η²)·g(v) has derivative
2iη·g(iη) at the pair point v = iη: the cofactor is the exact stiffness. -/
theorem pair_hasDerivAt {g : ℂ → ℂ} (η : ℝ)
    (hg : DifferentiableAt ℂ g (Complex.I * (η : ℂ))) :
    HasDerivAt (fun v : ℂ => (v ^ (2 : ℕ) + ((η : ℂ)) ^ (2 : ℕ)) * g v)
      (2 * Complex.I * (η : ℂ) * g (Complex.I * (η : ℂ)))
      (Complex.I * (η : ℂ)) := by
  set v₀ : ℂ := Complex.I * (η : ℂ) with hv₀
  have hpoly : HasDerivAt (fun v : ℂ => v ^ (2 : ℕ) + ((η : ℂ)) ^ (2 : ℕ)) (2 * v₀) v₀ := by
    have := (hasDerivAt_pow 2 v₀).add_const (((η : ℂ)) ^ (2 : ℕ))
    simpa [pow_one] using this
  have hprod := hpoly.mul hg.hasDerivAt
  have hzero : v₀ ^ (2 : ℕ) + ((η : ℂ)) ^ (2 : ℕ) = 0 := by
    simp only [hv₀]
    rw [mul_pow, Complex.I_sq]
    ring
  have harith : 2 * v₀ * g v₀ + (v₀ ^ (2 : ℕ) + ((η : ℂ)) ^ (2 : ℕ)) * deriv g v₀
      = 2 * Complex.I * (η : ℂ) * g v₀ := by
    rw [hzero]
    simp only [hv₀]
    ring
  rw [← harith]
  exact hprod

/-- The factorization identity in norm: |Z′| = 2η·|g| at the pair. -/
theorem pair_deriv_norm {g : ℂ → ℂ} {η : ℝ} (hη : 0 ≤ η) :
    ‖2 * Complex.I * (η : ℂ) * g (Complex.I * (η : ℂ))‖
      = 2 * η * ‖g (Complex.I * (η : ℂ))‖ := by
  rw [norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hη]
  norm_num

/-- **The hold/kill margin (doc 51 §9(b))**: capacity A, alignment c, depth
d > 0 — the entry kills iff the reach ratio R = A/d times the anti-alignment
−c reaches 1. This is cos(slip)·R ≥ 1 in exact algebra. -/
theorem hold_kill_criterion {d A c : ℝ} (hd : 0 < d) :
    A * c ≤ -d ↔ 1 ≤ A / d * (-c) := by
  have hrw : A / d * (-c) = A * (-c) / d := by ring
  rw [hrw]
  constructor
  · intro h
    have h2 : d ≤ A * (-c) := by nlinarith
    calc (1 : ℝ) = d / d := by field_simp
      _ ≤ A * (-c) / d := by gcongr
  · intro h
    have h2 : d ≤ A * (-c) := by
      have hmul := mul_le_mul_of_nonneg_right h hd.le
      rw [one_mul, div_mul_cancel₀ _ hd.ne'] at hmul
      exact hmul
    nlinarith

/-- **Coherent accumulation (the |H|-growth engine)**: if the total phase
spread K·|ϑ| stays within π/3, a nonnegative-amplitude phased sum retains at
least half its mass in the real part. -/
theorem coherent_sum_lower {ϑ : ℝ} {K : ℕ}
    (h : |ϑ| * K ≤ Real.pi / 3)
    {a : ℕ → ℝ} (hnn : ∀ n, 0 ≤ a n) :
    (∑ m ∈ Finset.range K, a m) / 2
      ≤ (∑ m ∈ Finset.range K,
          (a m : ℂ) * Complex.exp ((((m : ℝ) * ϑ : ℝ) : ℂ) * Complex.I)).re := by
  rw [Complex.re_sum]
  have hterm : ∀ m ∈ Finset.range K,
      a m / 2 ≤ ((a m : ℂ) * Complex.exp ((((m : ℝ) * ϑ : ℝ) : ℂ) * Complex.I)).re := by
    intro m hm
    have hre : ((a m : ℂ) * Complex.exp ((((m : ℝ) * ϑ : ℝ) : ℂ) * Complex.I)).re
        = a m * Real.cos ((m : ℝ) * ϑ) := by
      rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    rw [hre]
    have hmK : (m : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast (Finset.mem_range.mp hm).le
    have habs : |(m : ℝ) * ϑ| ≤ Real.pi / 3 := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
      calc (m : ℝ) * |ϑ| ≤ (K : ℝ) * |ϑ| :=
            mul_le_mul_of_nonneg_right hmK (abs_nonneg ϑ)
        _ = |ϑ| * K := by ring
        _ ≤ Real.pi / 3 := h
    have hcos : Real.cos (Real.pi / 3) ≤ Real.cos |(m : ℝ) * ϑ| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (by linarith [Real.pi_pos]) habs
    rw [Real.cos_abs, Real.cos_pi_div_three] at hcos
    have := hnn m
    nlinarith
  calc (∑ m ∈ Finset.range K, a m) / 2
      = ∑ m ∈ Finset.range K, a m / 2 := by rw [Finset.sum_div]
    _ ≤ _ := Finset.sum_le_sum hterm

end RHTower
