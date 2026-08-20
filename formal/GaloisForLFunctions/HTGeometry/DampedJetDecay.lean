import Mathlib

/-!
# Damped jets decay

Multiplying a function by an exponential character `exp (a z)` multiplies every derivative by a
polynomial in `a`: the Leibniz expansion of the `m`-th derivative has `∑_i C(m,i) a^i` for its
coefficient growth, so the whole jet of order `m` is bounded by `(1 + ‖a‖)^m` times the character
and the jet of the undamped factor.

When the character is evaluated where its real part is at most `-c ‖B‖` for a positive `c`, the
exponential beats the polynomial and every fixed jet tends to zero as the damping parameter grows.
This is the estimate that lets a damped Poincaré-series remainder be discarded to any prescribed
finite jet order.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-! ### Derivatives of an exponential character -/

theorem contDiffAt_cexp_mul (a : ℂ) (n : ℕ) (z : ℂ) :
    ContDiffAt ℂ (n : ℕ) (fun w : ℂ => Complex.exp (a * w)) z :=
  (Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffAt

theorem deriv_cexp_mul (a : ℂ) :
    deriv (fun w : ℂ => Complex.exp (a * w)) = fun w => a * Complex.exp (a * w) := by
  funext w
  have h : HasDerivAt (fun w : ℂ => Complex.exp (a * w)) (Complex.exp (a * w) * a) w := by
    simpa using ((hasDerivAt_id w).const_mul a).cexp
  rw [h.deriv]
  ring

/-- Every derivative of an exponential character. -/
theorem iteratedDeriv_cexp_mul (a : ℂ) (m : ℕ) (z : ℂ) :
    iteratedDeriv m (fun w : ℂ => Complex.exp (a * w)) z = a ^ m * Complex.exp (a * z) := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
      rw [iteratedDeriv_succ', deriv_cexp_mul,
        iteratedDeriv_const_mul _ (contDiffAt_cexp_mul a m z), ih]
      ring

/-! ### The damped jet -/

/-- **Leibniz expansion of a damped jet.** -/
theorem iteratedDeriv_cexp_mul_mul (a : ℂ) {g : ℂ → ℂ} {z : ℂ} {m : ℕ}
    (hg : ContDiffAt ℂ (m : ℕ) g z) :
    iteratedDeriv m (fun w => Complex.exp (a * w) * g w) z
      = ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℂ) * (a ^ i * Complex.exp (a * z)) * iteratedDeriv (m - i) g z := by
  have hmul : (fun w : ℂ => Complex.exp (a * w) * g w)
      = (fun w : ℂ => Complex.exp (a * w)) * g := rfl
  rw [hmul, iteratedDeriv_mul (contDiffAt_cexp_mul a m z) hg]
  exact Finset.sum_congr rfl fun i _ => by rw [iteratedDeriv_cexp_mul]

/-- **The damped jet bound.**  Every derivative of order at most `m` of `exp (a ·) g` is bounded by
`(1 + ‖a‖)^m` times the character and the jets of `g`. -/
theorem norm_iteratedDeriv_cexp_mul_mul_le (a : ℂ) {g : ℂ → ℂ} {z : ℂ} {m : ℕ} {M : ℝ}
    (hg : ContDiffAt ℂ (m : ℕ) g z) (hM : ∀ i, ‖iteratedDeriv i g z‖ ≤ M) :
    ‖iteratedDeriv m (fun w => Complex.exp (a * w) * g w) z‖
      ≤ (1 + ‖a‖) ^ m * Real.exp (a * z).re * M := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  rw [iteratedDeriv_cexp_mul_mul a hg]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ i ∈ Finset.range (m + 1),
      ‖(m.choose i : ℂ) * (a ^ i * Complex.exp (a * z)) * iteratedDeriv (m - i) g z‖
        ≤ ((m.choose i : ℝ) * ‖a‖ ^ i) * (Real.exp (a * z).re * M) := by
    intro i _
    have hnormeq : ‖(m.choose i : ℂ) * (a ^ i * Complex.exp (a * z)) * iteratedDeriv (m - i) g z‖
        = ((m.choose i : ℝ) * ‖a‖ ^ i)
            * (Real.exp (a * z).re * ‖iteratedDeriv (m - i) g z‖) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, norm_pow, Complex.norm_exp]
      ring
    rw [hnormeq]
    have hpos : (0 : ℝ) ≤ (m.choose i : ℝ) * ‖a‖ ^ i := by positivity
    have hexp : (0 : ℝ) ≤ Real.exp (a * z).re := (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hM (m - i)) hexp) hpos
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  have hbin : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖a‖ ^ i = (1 + ‖a‖) ^ m := by
    rw [show (1 : ℝ) + ‖a‖ = ‖a‖ + 1 by ring, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_pow, mul_one]
    ring
  rw [hbin]
  exact le_of_eq (by ring)

/-! ### Decay -/

private theorem tendsto_pow_mul_exp_neg_mul {k : ℕ} {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => t ^ k * Real.exp (-(c * t))) atTop (nhds 0) := by
  have hbase : Tendsto (fun u : ℝ => u ^ k * Real.exp (-u)) atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  have hcomp : Tendsto (fun t : ℝ => c * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_id
  have h := (hbase.comp hcomp).const_mul (c ^ k)⁻¹
  rw [mul_zero] at h
  refine h.congr fun t => ?_
  simp only [Function.comp_apply]
  rw [mul_pow]
  field_simp

/-- **Damped jets tend to zero.**  A fixed jet order of `exp (a_n ·) g_n`, with the character's real
part at most `-c B_n` and `B_n → ∞`, tends to zero uniformly in the undamped jets. -/
theorem tendsto_norm_iteratedDeriv_damped_zero {m : ℕ} {c M L : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    {a : ℕ → ℂ} {g : ℕ → ℂ → ℂ} {z : ℂ} {B : ℕ → ℝ}
    (hcd : ∀ n, ContDiffAt ℂ (m : ℕ) (g n) z)
    (hjet : ∀ n, ∀ i, ‖iteratedDeriv i (g n) z‖ ≤ M)
    (hnorm : ∀ n, ‖a n‖ ≤ L * B n)
    (hre : ∀ n, (a n * z).re ≤ -(c * B n))
    (hB : Tendsto B atTop atTop) :
    Tendsto (fun n => ‖iteratedDeriv m (fun w => Complex.exp (a n * w) * g n w) z‖)
      atTop (nhds 0) := by
  have hmaj : Tendsto (fun n => (1 + L * B n) ^ m * Real.exp (-(c * B n)) * M) atTop (nhds 0) := by
    have hpoly : Tendsto (fun t : ℝ => (1 + L * t) ^ m * Real.exp (-(c * t))) atTop (nhds 0) := by
      have hexp : ∀ t : ℝ, (1 + L * t) ^ m * Real.exp (-(c * t))
          = ∑ i ∈ Finset.range (m + 1),
              ((m.choose i : ℝ) * L ^ i) * (t ^ i * Real.exp (-(c * t))) := by
        intro t
        rw [show (1 : ℝ) + L * t = L * t + 1 by ring, add_pow, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [one_pow, mul_one, mul_pow]
        ring
      simp only [hexp]
      have hone : ∀ i ∈ Finset.range (m + 1),
          Tendsto (fun t : ℝ => ((m.choose i : ℝ) * L ^ i) * (t ^ i * Real.exp (-(c * t))))
            atTop (nhds 0) := by
        intro i _
        have h := (tendsto_pow_mul_exp_neg_mul (k := i) hc).const_mul
          ((m.choose i : ℝ) * L ^ i)
        rwa [mul_zero] at h
      have hsum := tendsto_finsetSum (Finset.range (m + 1)) hone
      simpa using hsum
    have := (hpoly.comp hB).mul_const M
    rw [zero_mul] at this
    exact this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hmaj
  refine le_trans (norm_iteratedDeriv_cexp_mul_mul_le (a n) (hcd n) (hjet n)) ?_
  have h1 : (1 + ‖a n‖) ^ m ≤ (1 + L * B n) ^ m := by
    refine pow_le_pow_left₀ (by positivity) (by linarith [hnorm n]) m
  have h2 : Real.exp (a n * z).re ≤ Real.exp (-(c * B n)) := Real.exp_le_exp.mpr (hre n)
  have h3 : (0 : ℝ) ≤ Real.exp (a n * z).re := (Real.exp_pos _).le
  have hbase : (0 : ℝ) ≤ 1 + L * B n := by linarith [hnorm n, norm_nonneg (a n)]
  calc (1 + ‖a n‖) ^ m * Real.exp (a n * z).re * M
      ≤ (1 + L * B n) ^ m * Real.exp (a n * z).re * M := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h3) hM
    _ ≤ (1 + L * B n) ^ m * Real.exp (-(c * B n)) * M := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (pow_nonneg hbase m)) hM

end GaloisForLFunctions.HTGeometry
