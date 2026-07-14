import GaloisForLFunctions.RHTower.XiCTaylorThetaTailDensityAtoms

/-!
# Strict monotonicity of the differentiated theta-tail atoms

The arithmetic phase packets are built from positive translates of the first exact density atom.
This module proves the source property needed to keep each complete translated packet in one
Fourier--Laplace half-plane: every positive-index atom of `4 T''` is strictly decreasing on the
closed positive logarithmic half-line.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

private theorem densityDerivativePolynomial_neg {u : ℝ}
    (hu : Real.pi ≤ u) :
    1 / 2 - 62 * u + 120 * u ^ 2 - 32 * u ^ 3 < 0 := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hu314 : (3.14 : ℝ) < u := hpi.trans_le hu
  have hderneg : -62 + 240 * u - 96 * u ^ 2 < 0 := by
    nlinarith [sq_nonneg (u - 5 / 4)]
  have hbase :
      1 / 2 - 62 * (3.14 : ℝ) + 120 * (3.14 : ℝ) ^ 2 -
          32 * (3.14 : ℝ) ^ 3 < 0 := by norm_num
  have hdiff :
      (1 / 2 - 62 * u + 120 * u ^ 2 - 32 * u ^ 3) -
        (1 / 2 - 62 * (3.14 : ℝ) + 120 * (3.14 : ℝ) ^ 2 -
          32 * (3.14 : ℝ) ^ 3) < 0 := by
    nlinarith [sq_nonneg (u - (3.14 : ℝ))]
  linarith

/-- The derivative of one exact second-density atom is the next Gaussian derivative atom. -/
theorem hasDerivAt_thetaCuspTailSecondDensityAtom
    (n : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspTailSecondDensityAtom n)
      (4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 3) n x) x := by
  unfold thetaCuspTailSecondDensityAtom
  simpa only [thetaCuspTailDerivativePolynomial] using
    (hasDerivAt_thetaCuspPolynomialAtom
      (thetaCuspTailDerivativePolynomial 2) n x).const_mul 4

private theorem thetaCuspTailDerivativePolynomial_three_value :
    thetaCuspTailDerivativePolynomial 3 =
      C (1 / 8) - C (31 * Real.pi / 2) * X ^ 2 +
        C (30 * Real.pi ^ 2) * X ^ 4 -
          C (8 * Real.pi ^ 3) * X ^ 6 := by
  apply Polynomial.funext
  intro y
  simp [thetaCuspTailDerivativePolynomial, thetaCuspLogDerivativeStep]
  ring

/-- The derivative of every positive-index exact density atom is strictly negative on the
positive logarithmic half-line. -/
theorem thetaCuspTailSecondDensityAtom_deriv_neg
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    4 * thetaCuspPolynomialAtom
        (thetaCuspTailDerivativePolynomial 3) n x < 0 := by
  let u : ℝ := Real.pi * ((n : ℝ) * Real.exp x) ^ 2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : 1 ≤ Real.exp x := Real.one_le_exp hx
  have hscale : 1 ≤ (n : ℝ) * Real.exp x := by nlinarith
  have hu : Real.pi ≤ u := by
    dsimp [u]
    nlinarith [Real.pi_pos, sq_nonneg ((n : ℝ) * Real.exp x - 1)]
  have hpoly := densityDerivativePolynomial_neg hu
  rw [thetaCuspTailDerivativePolynomial_three_value]
  unfold thetaCuspPolynomialAtom
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  have hrewrite :
      1 / 8 - 31 * Real.pi / 2 * ((n : ℝ) * Real.exp x) ^ 2 +
          30 * Real.pi ^ 2 * ((n : ℝ) * Real.exp x) ^ 4 -
          8 * Real.pi ^ 3 * ((n : ℝ) * Real.exp x) ^ 6 =
        (1 / 4 : ℝ) *
          (1 / 2 - 62 * u + 120 * u ^ 2 - 32 * u ^ 3) := by
    dsimp [u]
    ring
  have hnegative :
      1 / 8 - 31 * Real.pi / 2 * ((n : ℝ) * Real.exp x) ^ 2 +
          30 * Real.pi ^ 2 * ((n : ℝ) * Real.exp x) ^ 4 -
          8 * Real.pi ^ 3 * ((n : ℝ) * Real.exp x) ^ 6 < 0 := by
    rw [hrewrite]
    nlinarith
  rw [show 4 * (Real.exp (x / 2) *
      (1 / 8 - 31 * Real.pi / 2 * ((n : ℝ) * Real.exp x) ^ 2 +
        30 * Real.pi ^ 2 * ((n : ℝ) * Real.exp x) ^ 4 -
        8 * Real.pi ^ 3 * ((n : ℝ) * Real.exp x) ^ 6) *
      Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2)) =
    (4 * Real.exp (x / 2) *
      Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2)) *
      (1 / 8 - 31 * Real.pi / 2 * ((n : ℝ) * Real.exp x) ^ 2 +
        30 * Real.pi ^ 2 * ((n : ℝ) * Real.exp x) ^ 4 -
        8 * Real.pi ^ 3 * ((n : ℝ) * Real.exp x) ^ 6) by ring]
  exact mul_neg_of_pos_of_neg (by positivity) hnegative

/-- Every positive-index exact density atom is strictly decreasing on `[0,∞)`. -/
theorem strictAntiOn_thetaCuspTailSecondDensityAtom
    {n : ℕ} (hn : 0 < n) :
    StrictAntiOn (thetaCuspTailSecondDensityAtom n) (Ici 0) := by
  exact strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ))
    (fun x _hx =>
      (hasDerivAt_thetaCuspTailSecondDensityAtom n x).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [(hasDerivAt_thetaCuspTailSecondDensityAtom n x).deriv]
      exact thetaCuspTailSecondDensityAtom_deriv_neg hn
        (mem_Ici.mp (interior_subset hx)))

/-- The third raw-tail derivative is strictly negative on the positive logarithmic half-line. -/
theorem thetaCuspTailDerivative_three_neg {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspTailDerivative 3 x < 0 := by
  let f : ℕ → ℝ := fun n =>
    -thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 3) (n + 1) x
  have hf : Summable f :=
    (summable_thetaCuspTailDerivative 3 x).neg
  have hf_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    have hneg := thetaCuspTailSecondDensityAtom_deriv_neg
      (n := n + 1) (Nat.succ_pos n) hx
    dsimp only [f]
    linarith
  have hf_zero : 0 < f 0 := by
    have hneg := thetaCuspTailSecondDensityAtom_deriv_neg
      (n := 1) Nat.zero_lt_one hx
    dsimp only [f]
    linarith
  have hsum := hf.tsum_pos hf_nonneg 0 hf_zero
  unfold thetaCuspTailDerivative
  rw [tsum_neg] at hsum
  linarith

/-- The derivative of the complete canonical density is four times the third raw-tail
derivative. -/
theorem hasDerivAt_thetaCuspTailSecondDensity_fromAtoms (x : ℝ) :
    HasDerivAt thetaCuspTailSecondDensity
      (4 * thetaCuspTailDerivative 3 x) x := by
  unfold thetaCuspTailSecondDensity
  simpa only using (hasDerivAt_thetaCuspTailDerivative 2 x).const_mul 4

/-- The full canonical density `4 T''` is strictly decreasing on `[0,∞)`. -/
theorem strictAntiOn_thetaCuspTailSecondDensity :
    StrictAntiOn thetaCuspTailSecondDensity (Ici 0) := by
  exact strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ))
    (fun x _hx =>
      (hasDerivAt_thetaCuspTailSecondDensity_fromAtoms x).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [(hasDerivAt_thetaCuspTailSecondDensity_fromAtoms x).deriv]
      exact mul_neg_of_pos_of_neg (by norm_num)
        (thetaCuspTailDerivative_three_neg
          (mem_Ici.mp (interior_subset hx))))

end

end RHTower
