import GaloisForLFunctions.ConjugateDiagonalGeometry.ZetaDepthDistribution

/-!
# One weight controls the whole compact source-test space

A Gaussian horizontal envelope and a fourth-order vertical tail dominate the
squared transform of every compact C² test. The same weight has finite mass on
the actual xi divisor. It therefore gives one tail-control channel for source
metrics with arbitrary fixed aperture, rather than choosing a weight per test.
-/

open Complex MeasureTheory Set Metric
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- Positive global control weight for every compact source transform. -/
def universalSourceWeight (z : ℂ) : ℝ :=
  Real.exp (z.re ^ 2) / (1 + z.im ^ 2) ^ 2

theorem universalSourceWeight_pos (z : ℂ) : 0 < universalSourceWeight z := by
  unfold universalSourceWeight
  positivity

theorem contDiff_universalSourceWeight : ContDiff ℝ 2 universalSourceWeight := by
  have hr : ContDiff ℝ 2 (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have hi : ContDiff ℝ 2 (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  exact (hr.pow 2).exp.div ((contDiff_const.add (hi.pow 2)).pow 2)
    (fun z => by positivity)

private theorem horizontal_exp_bound (a x : ℝ) (ha : 0 ≤ a) :
    Real.exp (2 * (|x - 1 / 2| * a)) ≤
      Real.exp (a ^ 2 + a) * Real.exp (x ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ht : |x - 1 / 2| ≤ |x| + 1 / 2 := by
    simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] using
      abs_sub x (1 / 2)
  have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * a by positivity)
  nlinarith only [hm, sq_nonneg (|x| - a), sq_abs x]

/-- Every compact C² test is globally dominated by this single, test-independent weight. -/
theorem normSq_tr_le_universalSourceWeight (f : CompactTest) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      Complex.normSq (tr f.1 z) ≤ C * universalSourceWeight z := by
  obtain ⟨R, hR⟩ := f.2.2.isCompact.isBounded.subset_closedBall (0 : ℝ)
  let a : ℝ := max R 0
  have ha : 0 ≤ a := le_max_right _ _
  have hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a := by
    intro u hu
    have h := hR (subset_tsupport f.1 hu)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  let B : ℝ := 4 * ((∫ u, ‖f.1 u‖) + ∫ u, ‖deriv (deriv f.1) u‖)
  have hB : 0 ≤ B := mul_nonneg (by norm_num)
    (add_nonneg (integral_nonneg fun _ => norm_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _))
  refine ⟨B ^ 2 * Real.exp (a ^ 2 + a), by positivity, ?_⟩
  intro z
  have hre : (gammaOf z).re = z.im := by
    rw [gammaOf, Complex.div_I]
    simp
  have him : |(gammaOf z).im| = |z.re - 1 / 2| := by
    rw [gammaOf, Complex.div_I]
    simp only [Complex.neg_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.I_re, Complex.I_im]
    norm_num
    exact abs_sub_comm _ _
  have ht : ‖tr f.1 z‖ ≤ Real.exp (|z.re - 1 / 2| * a) * B / (1 + |z.im|) ^ 2 := by
    simpa only [tr, hre, him] using norm_paperFT_le_decay f.2.1 hsupp (gammaOf z)
  have hsquare : Complex.normSq (tr f.1 z) ≤
      Real.exp (2 * (|z.re - 1 / 2| * a)) * B ^ 2 / (1 + |z.im|) ^ 4 := by
    rw [Complex.normSq_eq_norm_sq]
    calc
      ‖tr f.1 z‖ ^ 2 ≤ (Real.exp (|z.re - 1 / 2| * a) * B / (1 + |z.im|) ^ 2) ^ 2 := by
        gcongr
      _ = _ := by
        rw [div_pow, mul_pow, ← Real.exp_nat_mul]
        push_cast
        ring
  have hden : (1 + z.im ^ 2) ^ 2 ≤ (1 + |z.im|) ^ 4 := by
    have hbase : 1 + z.im ^ 2 ≤ (1 + |z.im|) ^ 2 := by
      nlinarith only [abs_nonneg z.im, sq_abs z.im]
    calc
      (1 + z.im ^ 2) ^ 2 ≤ ((1 + |z.im|) ^ 2) ^ 2 := by gcongr
      _ = _ := by ring
  calc
    Complex.normSq (tr f.1 z) ≤
        Real.exp (2 * (|z.re - 1 / 2| * a)) * B ^ 2 / (1 + |z.im|) ^ 4 := hsquare
    _ ≤ (Real.exp (a ^ 2 + a) * Real.exp (z.re ^ 2)) * B ^ 2 /
        (1 + z.im ^ 2) ^ 2 := by
      apply div_le_div₀
      · positivity
      · exact mul_le_mul_of_nonneg_right (horizontal_exp_bound a z.re ha) (sq_nonneg B)
      · positivity
      · exact hden
    _ = (B ^ 2 * Real.exp (a ^ 2 + a)) * universalSourceWeight z := by
      unfold universalSourceWeight
      ring

/-- The universal control channel has finite mass on the full zeta divisor. -/
theorem summable_universalSourceWeight :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * universalSourceWeight ρ) := by
  have hb (ρ : zetaZeroConfig.carrier) :
      universalSourceWeight ρ ≤ (5 / 4 * Real.exp 1) /
        (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
    have hstrip := zetaZeroConfig.strip ρ ρ.2
    have hre : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := by
      rw [gammaOf, Complex.div_I]
      simp
    have him : (gammaOf (ρ : ℂ)).im = -((ρ : ℂ).re - 1 / 2) := by
      rw [gammaOf, Complex.div_I]
      simp
    have hnorm : Complex.normSq (gammaOf (ρ : ℂ)) ≤ (ρ : ℂ).im ^ 2 + 1 / 4 := by
      rw [Complex.normSq_apply, hre, him]
      nlinarith only [mul_nonneg hstrip.1 (sub_nonneg.mpr hstrip.2)]
    have hd : 1 + Complex.normSq (gammaOf (ρ : ℂ)) ≤
        (5 / 4 : ℝ) * (1 + (ρ : ℂ).im ^ 2) ^ 2 := by
      nlinarith only [hnorm, sq_nonneg (ρ : ℂ).im, sq_nonneg ((ρ : ℂ).im ^ 2)]
    have hx : (ρ : ℂ).re ^ 2 ≤ 1 := by
      nlinarith only [hstrip.1, hstrip.2, mul_nonneg hstrip.1 (sub_nonneg.mpr hstrip.2)]
    calc
      universalSourceWeight ρ ≤ Real.exp 1 / (1 + (ρ : ℂ).im ^ 2) ^ 2 := by
        unfold universalSourceWeight
        exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hx) (sq_nonneg _)
      _ ≤ _ := by
        have hq : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) :=
          add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _)
        apply (div_le_div_iff₀ (by positivity) hq).2
        have h := mul_le_mul_of_nonneg_left hd (Real.exp_pos 1).le
        nlinarith only [h]
  refine Summable.of_nonneg_of_le
    (fun ρ => mul_nonneg (Nat.cast_nonneg _) (universalSourceWeight_pos ρ).le)
    (fun ρ => ?_) (summable_zetaZeroConfig.mul_left (5 / 4 * Real.exp 1))
  calc
    (zetaZeroConfig.mult ρ : ℝ) * universalSourceWeight ρ ≤
        (zetaZeroConfig.mult ρ : ℝ) * ((5 / 4 * Real.exp 1) /
          (1 + Complex.normSq (gammaOf (ρ : ℂ)))) :=
      mul_le_mul_of_nonneg_left (hb ρ) (Nat.cast_nonneg _)
    _ = _ := by ring

end GaloisForLFunctions.ConjugateDiagonalGeometry
