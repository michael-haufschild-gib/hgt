/-
Doc 28 §2a (task #143; as corrected 2026-07-04): UHP-stability of the shifted section.

For a hyperbolic polynomial `A = c·∏(X − β_k)` (all `β_k` real) and `τ` with `Im τ > 0`,
every zero `z` of `B := A′ − τ̄·A` with `A(z) ≠ 0` lies in the OPEN upper half-plane.
(At an m-fold real root of `A`, `B` has an (m−1)-fold real zero — the correction — so the
hypothesis `A(z) ≠ 0` is exactly right.)

Engine: the division-free positivity `Im(P′(z)·conj P(z)) ≥ 0` for `Im z ≤ 0`, proved by
multiset induction on the real root list — no logarithmic derivative, no root sums.
-/
import Mathlib

namespace RHTower

open Polynomial Complex

private theorem ofReal_mul_im' (r : ℝ) (w : ℂ) : ((r : ℂ) * w).im = r * w.im := by
  simp [Complex.mul_im]

/-- Division-free Hermite–Biehler positivity: for a monic real-rooted product
`P = ∏_{r ∈ s}(X − r)` and `Im z ≤ 0`, the pairing `Im(P′(z)·conj(P(z)))` is ≥ 0. -/
private theorem im_derivative_mul_conj_nonneg (s : Multiset ℝ) (z : ℂ) (hz : z.im ≤ 0) :
    0 ≤ ((eval z (derivative ((s.map fun r : ℝ => X - C (r : ℂ))).prod))
        * (starRingEnd ℂ) (eval z ((s.map fun r : ℝ => X - C (r : ℂ))).prod)).im := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, derivative_mul]
      set P := ((s.map fun r : ℝ => X - C (r : ℂ))).prod with hP
      set e0 := eval z P with he0
      set e1 := eval z (derivative P) with he1
      have hder : derivative (X - C ((a : ℝ) : ℂ)) = 1 := by
        rw [derivative_sub, derivative_X, derivative_C, sub_zero]
      rw [hder, one_mul]
      set w : ℂ := z - ((a : ℝ) : ℂ) with hw
      have heval : eval z ((X - C ((a : ℝ) : ℂ)) * P) = w * e0 := by
        rw [eval_mul, eval_sub, eval_X, eval_C]
      have heval2 : eval z (P + (X - C ((a : ℝ) : ℂ)) * derivative P) = e0 + w * e1 := by
        rw [eval_add, eval_mul, eval_sub, eval_X, eval_C]
      rw [heval, heval2]
      have hexp : (e0 + w * e1) * (starRingEnd ℂ) (w * e0)
          = (starRingEnd ℂ) w * ((normSq e0 : ℝ) : ℂ)
            + ((normSq w : ℝ) : ℂ) * (e1 * (starRingEnd ℂ) e0) := by
        rw [map_mul]
        have h1 : e0 * (starRingEnd ℂ) e0 = ((normSq e0 : ℝ) : ℂ) := mul_conj e0
        have h2 : w * (starRingEnd ℂ) w = ((normSq w : ℝ) : ℂ) := mul_conj w
        calc (e0 + w * e1) * ((starRingEnd ℂ) w * (starRingEnd ℂ) e0)
            = (starRingEnd ℂ) w * (e0 * (starRingEnd ℂ) e0)
              + (w * (starRingEnd ℂ) w) * (e1 * (starRingEnd ℂ) e0) := by ring
          _ = _ := by rw [h1, h2]
      rw [hexp]
      have hwim : w.im = z.im := by
        rw [hw, sub_im, ofReal_im, sub_zero]
      have him1 : ((starRingEnd ℂ) w * ((normSq e0 : ℝ) : ℂ)).im
          = -z.im * normSq e0 := by
        rw [mul_comm, ofReal_mul_im', conj_im, hwim]
        ring
      have him2 : (((normSq w : ℝ) : ℂ) * (e1 * (starRingEnd ℂ) e0)).im
          = normSq w * (e1 * (starRingEnd ℂ) e0).im := ofReal_mul_im' ..
      rw [add_im, him1, him2]
      have hn0 : 0 ≤ normSq e0 := normSq_nonneg e0
      have hnw : 0 ≤ normSq w := normSq_nonneg w
      nlinarith [ih]

/-- **UHP-stability off the multiple-root set** (doc 28 §2a, corrected form).
If `A = c·∏_{r ∈ s}(X − r)` with real roots, `Im τ > 0`, and `z` is a zero of
`B = A′ − τ̄·A` with `A(z) ≠ 0`, then `z` lies in the open upper half-plane. -/
theorem uhp_of_pair_shift_root {c τ z : ℂ} {s : Multiset ℝ}
    (hb : 0 < τ.im)
    (hAz : eval z (C c * ((s.map fun r : ℝ => X - C (r : ℂ))).prod) ≠ 0)
    (hBz : eval z (derivative (C c * ((s.map fun r : ℝ => X - C (r : ℂ))).prod)
        - C ((starRingEnd ℂ) τ) * (C c * ((s.map fun r : ℝ => X - C (r : ℂ))).prod)) = 0) :
    0 < z.im := by
  by_contra hzim
  rw [not_lt] at hzim
  set P := ((s.map fun r : ℝ => X - C (r : ℂ))).prod with hP
  set eA := eval z (C c * P) with heA
  -- from B(z) = 0: eval of the derivative equals τ̄·A(z)
  have hshift : eval z (derivative (C c * P)) = (starRingEnd ℂ) τ * eA := by
    have := hBz
    rw [eval_sub, eval_mul, eval_C, sub_eq_zero] at this
    exact this
  -- the pairing computed two ways
  have hpair : (eval z (derivative (C c * P)) * (starRingEnd ℂ) eA).im
      = -τ.im * normSq eA := by
    rw [hshift]
    have : (starRingEnd ℂ) τ * eA * (starRingEnd ℂ) eA
        = (starRingEnd ℂ) τ * ((normSq eA : ℝ) : ℂ) := by
      rw [mul_assoc, mul_conj eA]
    rw [this, mul_comm, ofReal_mul_im', conj_im]
    ring
  have hpos : 0 ≤ (eval z (derivative (C c * P)) * (starRingEnd ℂ) eA).im := by
    rw [derivative_C_mul]
    have heval : eval z (C c * derivative P) = c * eval z (derivative P) := by
      rw [eval_mul, eval_C]
    have heA' : eA = c * eval z P := by
      rw [heA, eval_mul, eval_C]
    rw [heval, heA', map_mul]
    have hre : eval z (derivative P) * (starRingEnd ℂ) (eval z P) * ((normSq c : ℝ) : ℂ)
        = c * eval z (derivative P) * ((starRingEnd ℂ) c * (starRingEnd ℂ) (eval z P)) := by
      rw [← mul_conj c]
      ring
    have him : (c * eval z (derivative P) * ((starRingEnd ℂ) c
        * (starRingEnd ℂ) (eval z P))).im
        = normSq c * (eval z (derivative P) * (starRingEnd ℂ) (eval z P)).im := by
      rw [← hre, mul_comm _ (((normSq c : ℝ) : ℂ)), ofReal_mul_im']
    rw [him]
    have := im_derivative_mul_conj_nonneg s z hzim
    have hnc : 0 ≤ normSq c := normSq_nonneg c
    positivity
  have hnsq : 0 < normSq eA := normSq_pos.mpr hAz
  rw [hpair] at hpos
  nlinarith [hpos, hnsq, hb]

end RHTower
