import GaloisForLFunctions.HTGeometry.CosineProductSquaredMajorization

/-!
# Three-point vertical averages: only the Rademacher sums absorb pairs at their budget depth

For `0 ≤ μ ≤ 1` let `X` take the value `0` with probability `1 − μ` and `±1` with probability
`μ/2` each, so `E X² = μ`.  The vertical average `E p(z + iX)` is

`threePointAverage μ p = (1 − μ) p + μ cos(D) p`.

Its characteristic function `φ(ξ) = 1 − μ + μ cos ξ` has only real zeros exactly when `μ ≥ 1/2`
(`threePointSymbol_zero_im_eq_zero`), so for `μ ≥ 1/2` the average preserves real-rootedness.

* `μ = 1` is the cosine step `cos(D)`, and `μ = 1/2` is the product `cos(D/2)²`, i.e.
  `X = (ε₁ + ε₂)/2` (`threePointAverage_half_eq_cosProd`).  Both obey the squared-height
  majorization with budget `E X² = μ` (`sum_roots_cosProd_sq_sub_le`); in particular a pair of
  depth exactly `√μ` is absorbed.
* For every `1/2 < μ < 1` this fails: `p = (X² + μ)³` has all roots at squared height `μ`, but
  `threePointAverage μ p` has a root `iv` with `0 < v < 1` (`exists_threePointAverage_root_im_pos`).
  On the imaginary axis the average is
  `(1 − μ)(μ − v²)³ + (μ/2)((μ − (v+1)²)³ + (μ − (v−1)²)³)`,
  which equals `μ(1 − μ)(2μ − 1) > 0` at `v = 0` and is negative at `v = 1`.

So among three-point laws with a Laguerre–Pólya characteristic function, the energy law with
budget `E X²` holds exactly for the two Rademacher sums `μ ∈ {1/2, 1}`: real zeros of the symbol are
not enough, the Gaussian–Rademacher structure is needed.
-/

open Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The three-point vertical average `(1 − μ) p + μ cos(D) p`. -/
def threePointAverage (μ : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C (1 - μ) * p + C μ * shiftAvg 1 p

/-- The cube of the pair `X² + μ`; every root has squared height `μ`. -/
def threePointBase (μ : ℝ) : ℝ[X] := (X ^ 2 + C μ) ^ 3

/-- **Roots of the base sit at squared height `μ`.** -/
theorem threePointBase_root {μ : ℝ} (hμ : 0 < μ) {w : ℂ}
    (hw : ((threePointBase μ).map ofRealHom).eval w = 0) : w.re = 0 ∧ w.im ^ 2 = μ := by
  simp only [threePointBase, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C,
    Polynomial.map_X, eval_pow, eval_add, eval_X, eval_C, pow_eq_zero_iff (by norm_num : 3 ≠ 0)]
    at hw
  have h1 := congrArg Complex.re hw
  have h2 := congrArg Complex.im hw
  simp [pow_two] at h1 h2
  have hre : w.re = 0 := by
    rcases mul_eq_zero.mp (by linarith : w.re * w.im * 2 = 0) with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · rw [h'] at h1; nlinarith [sq_nonneg w.re]
    · norm_num at h
  refine ⟨hre, ?_⟩
  rw [hre] at h1
  nlinarith

/-- The profile of the average on the imaginary axis. -/
def threePointProfile (μ v : ℝ) : ℝ :=
  (1 - μ) * (μ - v ^ 2) ^ 3 + (μ / 2) * ((μ - (v + 1) ^ 2) ^ 3 + (μ - (v - 1) ^ 2) ^ 3)

theorem eval_threePointAverage_I_mul (μ v : ℝ) :
    ((threePointAverage μ (threePointBase μ)).map ofRealHom).eval ((v : ℂ) * I) =
      ((threePointProfile μ v : ℝ) : ℂ) := by
  simp only [threePointAverage, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    eval_add, eval_mul, eval_C, eval_map_shiftAvg]
  simp only [threePointBase, threePointProfile, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_C, Polynomial.map_X, eval_pow, eval_add, eval_X, eval_C,
    Complex.ofRealHom_eq_coe]
  push_cast
  ring_nf
  simp only [I_sq, I_pow_four, show I ^ 6 = -1 by rw [show (6 : ℕ) = 4 + 2 by rfl, pow_add,
    I_pow_four, I_sq, one_mul]]
  ring

theorem threePointProfile_zero (μ : ℝ) :
    threePointProfile μ 0 = μ * (1 - μ) * (2 * μ - 1) := by
  unfold threePointProfile; ring

theorem threePointProfile_one_neg {μ : ℝ} (h0 : 0 < μ) (h1 : μ < 1) : threePointProfile μ 1 < 0 := by
  unfold threePointProfile
  have ha : (1 - μ) * (μ - 1 ^ 2) ^ 3 < 0 := by
    have : (μ - 1 ^ 2) ^ 3 < 0 := by
      have : μ - 1 ^ 2 < 0 := by linarith
      exact Odd.pow_neg (by decide) this
    nlinarith
  have hb : (μ - (1 + 1) ^ 2) ^ 3 + (μ - (1 - 1) ^ 2) ^ 3 < 0 := by
    norm_num
    nlinarith [sq_nonneg μ, sq_nonneg (μ - 4)]
  nlinarith

/-- **A nonreal root of the three-point average for `1/2 < μ < 1`.** -/
theorem exists_threePointAverage_root_im_pos {μ : ℝ} (hμ : 1 / 2 < μ) (hμ1 : μ < 1) :
    ∃ z : ℂ, 0 < z.im ∧ z.im < 1 ∧
      ((threePointAverage μ (threePointBase μ)).map ofRealHom).eval z = 0 := by
  have hcont : ContinuousOn (threePointProfile μ) (Set.Icc 0 1) := by
    unfold threePointProfile; fun_prop
  have hpos : 0 < threePointProfile μ 0 := by
    rw [threePointProfile_zero]
    have : 0 < 2 * μ - 1 := by linarith
    have : 0 < 1 - μ := by linarith
    positivity
  have hneg := threePointProfile_one_neg (by linarith) hμ1
  obtain ⟨v, hv, hv0⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont
    ⟨hneg.le, hpos.le⟩
  have hvne0 : v ≠ 0 := by rintro rfl; linarith [hv0 ▸ hpos]
  have hvne1 : v ≠ 1 := by rintro rfl; linarith [hv0 ▸ hneg]
  refine ⟨(v : ℂ) * I, by simpa using lt_of_le_of_ne hv.1 (Ne.symm hvne0),
    by simpa using lt_of_le_of_ne hv.2 hvne1, ?_⟩
  rw [eval_threePointAverage_I_mul, show threePointProfile μ v = 0 from hv0, Complex.ofReal_zero]

/-- **At `μ = 1/2` the average is the cosine product `cos(D/2)²`.** -/
theorem threePointAverage_half_eq_cosProd (p : ℝ[X]) :
    threePointAverage (1 / 2) p = cosProd [1 / 2, 1 / 2] p := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
  apply Polynomial.funext
  intro z
  simp only [cosProd, List.foldr, threePointAverage, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, eval_add, eval_mul, eval_C, eval_map_shiftAvg, Complex.ofRealHom_eq_coe]
  push_cast
  ring_nf

theorem re_cos_add_mul_I (x y : ℝ) :
    (Complex.cos ((x : ℂ) + (y : ℂ) * I)).re = Real.cos x * Real.cosh y := by
  rw [Complex.cos_add_mul_I]
  simp [Complex.mul_re, Complex.cosh_ofReal_re, Complex.cos_ofReal_re, Complex.cosh_ofReal_im,
    Complex.cos_ofReal_im, Complex.sinh_ofReal_re, Complex.sinh_ofReal_im, Complex.sin_ofReal_re,
    Complex.sin_ofReal_im]

theorem im_cos_add_mul_I (x y : ℝ) :
    (Complex.cos ((x : ℂ) + (y : ℂ) * I)).im = -(Real.sin x * Real.sinh y) := by
  rw [Complex.cos_add_mul_I]
  simp [Complex.mul_im, Complex.mul_re, Complex.cosh_ofReal_re, Complex.cos_ofReal_re,
    Complex.cosh_ofReal_im, Complex.cos_ofReal_im, Complex.sinh_ofReal_re, Complex.sinh_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im]

/-- **The symbol `1 − μ + μ cos ξ` has only real zeros for `μ ≥ 1/2`.** -/
theorem threePointSymbol_zero_im_eq_zero {μ : ℝ} (hμ : 1 / 2 ≤ μ) {ξ : ℂ}
    (hξ : (1 - μ : ℂ) + μ * Complex.cos ξ = 0) : ξ.im = 0 := by
  by_contra hy
  have him : μ * (Complex.cos ξ).im = 0 := by
    have h := congrArg Complex.im hξ
    simp only [Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, zero_mul, add_zero, sub_zero, Complex.zero_im, zero_add] at h
    exact h
  have hre : (1 - μ) + μ * (Complex.cos ξ).re = 0 := by
    have h := congrArg Complex.re hξ
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at h
    exact h
  have hξ' : ξ = (ξ.re : ℂ) + (ξ.im : ℂ) * I := (Complex.re_add_im ξ).symm
  rw [hξ', im_cos_add_mul_I] at him
  rw [hξ', re_cos_add_mul_I] at hre
  have hμ0 : μ ≠ 0 := by linarith
  have hsinh : Real.sinh ξ.im ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact hy
  have hsin : Real.sin ξ.re = 0 := by
    have h1 : Real.sin ξ.re * Real.sinh ξ.im = 0 := by
      have := mul_eq_zero.mp him
      rcases this with h | h
      · exact absurd h hμ0
      · linarith
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hsinh
  have hcos : Real.cos ξ.re ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq ξ.re]
  have hcosh : 1 < Real.cosh ξ.im := Real.one_lt_cosh.mpr hy
  have h1 : μ * (Real.cos ξ.re * Real.cosh ξ.im) = -(1 - μ) := by linarith
  have hsq : μ ^ 2 * Real.cosh ξ.im ^ 2 = (1 - μ) ^ 2 := by
    calc μ ^ 2 * Real.cosh ξ.im ^ 2 = μ ^ 2 * Real.cos ξ.re ^ 2 * Real.cosh ξ.im ^ 2 := by
          rw [hcos]; ring
      _ = (μ * (Real.cos ξ.re * Real.cosh ξ.im)) ^ 2 := by ring
      _ = (1 - μ) ^ 2 := by rw [h1]; ring
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hc2 : 1 < Real.cosh ξ.im ^ 2 := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left hc2 hμ2]

end

end GaloisForLFunctions.HTGeometry
