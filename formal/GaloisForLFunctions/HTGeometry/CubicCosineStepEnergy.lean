import Mathlib

/-!
# The cosine step on real cubics: imaginary energy drops by at least `a²`

For a real cubic `p = (X − c)((X − b)² + y²)` and `a ∈ ℝ`, the cosine step
`cos(aD)p = (p(z + ia) + p(z − ia))/2 = p − (a²/2) p''` (exact on cubics) has at most one root
in the upper half-plane. If `w` is such a root, then

`(Im w)² + a² ≤ y²`,

i.e. the imaginary energy `Σ_{Im > 0} (Im)²` of the stepped cubic plus `a²` per non-real root is at
most that of `p` (`sq_im_add_sq_le_of_cubicCosineStep_root`).

**Proof.** Centre at `m = (c + 2b)/3` and put `d = b − m`, so `c = m − 2d`. The stepped cubic is
`P(z) = z³ + Kz + 2d(d² + y²)` in `z − m`, with `K = y² − 3d² − 3a²`. A root `m + u + iv` with
`v > 0` satisfies `v² = 3u² + K` and `4u³ + Ku = d(d² + y²)`. Suppose `u² > d² + 2a²/3`.
* If `a² ≤ y²`, then `4u² + K > d² + y² − a²/3 > 0`, so
  `u²(4u² + K)² > (d² + 2a²/3)(d² + y² − a²/3)² ≥ d²(d² + y²)²`; the last step is
  `G(s) = s·h(s) ≥ 0` with `h` decreasing on `[0, y²]` and `h(y²) ≥ 0`.
* If `a² > y²`, then `4u² + K = u² + v² > u²`, so `u²(4u² + K)² > u⁶ > (d² + 2a²/3)³ ≥
  d²(d² + a²)² ≥ d²(d² + y²)²`.

Both contradict `u²(4u² + K)² = d²(d² + y²)²`. Hence `u² ≤ d² + 2a²/3`, which is
`v² + a² = 3u² + K + a² ≤ y²`. When `a² > y²` the first step of the second case already derives
`u² > d² + 2a²/3` from `v² > 0`, so then there is no root at all.
-/

open Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real cubic `(X − c)((X − b)² + y²)`. -/
def pairRealCubic (b c y : ℝ) : ℝ[X] := (X - C c) * ((X - C b) ^ 2 + C (y ^ 2))

/-- The cosine step on cubics: `p − (a²/2) p''`. -/
def cubicCosineStep (a : ℝ) (p : ℝ[X]) : ℝ[X] := p - C (a ^ 2 / 2) * derivative (derivative p)

theorem pairRealCubic_eq (b c y : ℝ) :
    pairRealCubic b c y =
      X ^ 3 - C (c + 2 * b) * X ^ 2 + C (b ^ 2 + y ^ 2 + 2 * b * c) * X - C (c * (b ^ 2 + y ^ 2)) := by
  apply Polynomial.funext; intro x
  simp [pairRealCubic]
  ring

theorem cubicCosineStep_pairRealCubic (a b c y : ℝ) :
    cubicCosineStep a (pairRealCubic b c y) =
      X ^ 3 - C (c + 2 * b) * X ^ 2 + C (b ^ 2 + y ^ 2 + 2 * b * c - 3 * a ^ 2) * X +
        C (-(c * (b ^ 2 + y ^ 2)) + a ^ 2 * (c + 2 * b)) := by
  rw [cubicCosineStep, pairRealCubic_eq]
  apply Polynomial.funext; intro x
  simp [derivative_mul, derivative_pow]
  ring

/-- Real and imaginary parts of the stepped cubic at `x + iv`. -/
theorem cubicCosineStep_eval_eq (a b c y x v : ℝ) :
    ((cubicCosineStep a (pairRealCubic b c y)).map ofRealHom).eval ((x : ℂ) + (v : ℂ) * I) =
      ((x ^ 3 - 3 * x * v ^ 2 - (c + 2 * b) * (x ^ 2 - v ^ 2) +
          (b ^ 2 + y ^ 2 + 2 * b * c - 3 * a ^ 2) * x - c * (b ^ 2 + y ^ 2) +
          a ^ 2 * (c + 2 * b) : ℝ) : ℂ) +
        ((v * (3 * x ^ 2 - v ^ 2 - 2 * (c + 2 * b) * x +
          (b ^ 2 + y ^ 2 + 2 * b * c - 3 * a ^ 2)) : ℝ) : ℂ) * I := by
  rw [cubicCosineStep_pairRealCubic]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    map_X, map_C, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, ofRealHom_eq_coe]
  push_cast
  have hI3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  linear_combination (3 * (x : ℂ) * v ^ 2 - (c + 2 * b) * v ^ 2) * I_sq + (v : ℂ) ^ 3 * hI3

/-- `(D + 2s/3)(D + Y − s/3)² ≥ D(D + Y)²` on `0 ≤ s ≤ Y`, `D ≥ 0`. -/
theorem cubic_key_ineq {D Y s : ℝ} (hD : 0 ≤ D) (hs : 0 ≤ s) (hsY : s ≤ Y) :
    D * (D + Y) ^ 2 ≤ (D + 2 * s / 3) * (D + Y - s / 3) ^ 2 := by
  have hY : 0 ≤ Y := hs.trans hsY
  have hh : 0 ≤ (2 / 3) * (D + Y) * Y - s / 9 * (3 * D + 4 * Y) + 2 / 27 * s ^ 2 := by
    nlinarith [mul_nonneg hD (sub_nonneg.mpr hsY), mul_nonneg hY (sub_nonneg.mpr hsY),
      mul_nonneg hs (sub_nonneg.mpr hsY), sq_nonneg (Y - s)]
  have hid : (D + 2 * s / 3) * (D + Y - s / 3) ^ 2 - D * (D + Y) ^ 2 =
      s * ((2 / 3) * (D + Y) * Y - s / 9 * (3 * D + 4 * Y) + 2 / 27 * s ^ 2) := by ring
  nlinarith [mul_nonneg hs hh]

/-- `D(D + s)² ≤ (D + 2s/3)³` for `D, s ≥ 0`. -/
theorem cubic_binom_ineq {D s : ℝ} (hD : 0 ≤ D) (hs : 0 ≤ s) :
    D * (D + s) ^ 2 ≤ (D + 2 * s / 3) ^ 3 := by
  have hid : (D + 2 * s / 3) ^ 3 - D * (D + s) ^ 2 = D * s ^ 2 / 3 + 8 / 27 * s ^ 3 := by ring
  nlinarith [mul_nonneg hD (sq_nonneg s), pow_nonneg hs 3]

/-- The real core: centred coordinates `b = m + d`, `c = m − 2d`, `x = m + u`. -/
theorem cubicCosineStep_core {a d u v y : ℝ} (hv : 0 < v)
    (hv2 : v ^ 2 = 3 * u ^ 2 + (y ^ 2 - 3 * d ^ 2 - 3 * a ^ 2))
    (hcub : 4 * u ^ 3 + (y ^ 2 - 3 * d ^ 2 - 3 * a ^ 2) * u = d * (d ^ 2 + y ^ 2)) :
    v ^ 2 + a ^ 2 ≤ y ^ 2 := by
  obtain ⟨K, hK⟩ : ∃ K, K = y ^ 2 - 3 * d ^ 2 - 3 * a ^ 2 := ⟨_, rfl⟩
  rw [← hK] at hv2 hcub
  have hsq : u ^ 2 * (4 * u ^ 2 + K) ^ 2 = d ^ 2 * (d ^ 2 + y ^ 2) ^ 2 := by
    have h : (4 * u ^ 3 + K * u) ^ 2 = (d * (d ^ 2 + y ^ 2)) ^ 2 := by rw [hcub]
    linear_combination h
  have hvpos : 0 < v ^ 2 := by positivity
  have hD : 0 ≤ d ^ 2 := sq_nonneg d
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hu : u ^ 2 ≤ d ^ 2 + 2 * a ^ 2 / 3 := by
    by_contra hcon
    replace hcon := lt_of_not_ge hcon
    have hu2 : 0 < u ^ 2 := lt_of_le_of_lt (by positivity) hcon
    rcases le_or_gt (a ^ 2) (y ^ 2) with hay | hay
    · have hE : 0 ≤ d ^ 2 + y ^ 2 - a ^ 2 / 3 := by linarith
      have h4 : d ^ 2 + y ^ 2 - a ^ 2 / 3 < 4 * u ^ 2 + K := by rw [hK]; linarith
      have hsqlt : (d ^ 2 + y ^ 2 - a ^ 2 / 3) ^ 2 < (4 * u ^ 2 + K) ^ 2 :=
        pow_lt_pow_left₀ h4 hE (by norm_num)
      have h1 : (d ^ 2 + 2 * a ^ 2 / 3) * (d ^ 2 + y ^ 2 - a ^ 2 / 3) ^ 2 ≤
          u ^ 2 * (d ^ 2 + y ^ 2 - a ^ 2 / 3) ^ 2 :=
        mul_le_mul_of_nonneg_right hcon.le (sq_nonneg _)
      have h2 : u ^ 2 * (d ^ 2 + y ^ 2 - a ^ 2 / 3) ^ 2 < u ^ 2 * (4 * u ^ 2 + K) ^ 2 :=
        mul_lt_mul_of_pos_left hsqlt hu2
      have hkey := cubic_key_ineq hD ha2 hay
      linarith
    · have h4 : u ^ 2 < 4 * u ^ 2 + K := by linarith
      have h4sq : u ^ 2 * u ^ 2 < (4 * u ^ 2 + K) ^ 2 := by
        rw [← sq]; exact pow_lt_pow_left₀ h4 hu2.le (by norm_num)
      have h6 : u ^ 2 * (u ^ 2 * u ^ 2) < u ^ 2 * (4 * u ^ 2 + K) ^ 2 :=
        mul_lt_mul_of_pos_left h4sq hu2
      have hcube : (d ^ 2 + 2 * a ^ 2 / 3) ^ 3 ≤ u ^ 2 * (u ^ 2 * u ^ 2) := by
        have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ d ^ 2 + 2 * a ^ 2 / 3) hcon.le 3
        calc (d ^ 2 + 2 * a ^ 2 / 3) ^ 3 ≤ (u ^ 2) ^ 3 := this
          _ = u ^ 2 * (u ^ 2 * u ^ 2) := by ring
      have hbin := cubic_binom_ineq hD ha2
      have hdy : d ^ 2 * (d ^ 2 + y ^ 2) ^ 2 ≤ d ^ 2 * (d ^ 2 + a ^ 2) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hD
        exact pow_le_pow_left₀ (by positivity) (by linarith) 2
      linarith
  rw [hv2, hK]
  linarith

/-- **The cosine step on real cubics.** Every root `w` of `p − (a²/2)p''` with `Im w > 0`, for
`p = (X − c)((X − b)² + y²)`, satisfies `(Im w)² + a² ≤ y²`. -/
theorem sq_im_add_sq_le_of_cubicCosineStep_root {a b c y : ℝ} {w : ℂ} (hw : 0 < w.im)
    (hroot : ((cubicCosineStep a (pairRealCubic b c y)).map ofRealHom).eval w = 0) :
    w.im ^ 2 + a ^ 2 ≤ y ^ 2 := by
  have hwxv : w = (w.re : ℂ) + (w.im : ℂ) * I := (Complex.re_add_im w).symm
  rw [hwxv, cubicCosineStep_eval_eq] at hroot
  have hre := congrArg Complex.re hroot
  have him := congrArg Complex.im hroot
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, sub_zero, zero_re,
    add_im, mul_im, zero_add, mul_one, zero_im, add_zero] at hre him
  generalize w.re = x at hre him
  generalize hv : w.im = v at hre him hw ⊢
  have him' : 3 * x ^ 2 - v ^ 2 - 2 * (c + 2 * b) * x + (b ^ 2 + y ^ 2 + 2 * b * c - 3 * a ^ 2) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact absurd h hw.ne'
    · exact h
  obtain ⟨m, d, u, rfl, rfl, rfl⟩ :
      ∃ m d u : ℝ, b = m + d ∧ c = m - 2 * d ∧ x = m + u :=
    ⟨(c + 2 * b) / 3, b - (c + 2 * b) / 3, x - (c + 2 * b) / 3, by ring, by ring, by ring⟩
  have hv2 : v ^ 2 = 3 * u ^ 2 + (y ^ 2 - 3 * d ^ 2 - 3 * a ^ 2) := by
    linear_combination (-1 : ℝ) * him'
  have hcub : 4 * u ^ 3 + (y ^ 2 - 3 * d ^ 2 - 3 * a ^ 2) * u = d * (d ^ 2 + y ^ 2) := by
    linear_combination (-1 / 2 : ℝ) * hre + (-3 / 2 * u) * hv2
  exact cubicCosineStep_core hw hv2 hcub

end

end GaloisForLFunctions.HTGeometry
