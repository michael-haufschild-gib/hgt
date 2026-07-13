import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSurvivalMobiusReflection

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

def thetaCuspTailSurvivalAtom (n : ℕ) (x : ℝ) : ℝ :=
  -4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 1) n x

theorem thetaCuspTailSurvival_eq_tsum_atom (x : ℝ) :
    thetaCuspTailSurvival x =
      ∑' n : ℕ, thetaCuspTailSurvivalAtom (n + 1) x := by
  unfold thetaCuspTailSurvival thetaCuspTailDerivative
    thetaCuspTailSurvivalAtom
  simpa only using (Summable.tsum_mul_left (-4)
    (summable_thetaCuspTailDerivative 1 x)).symm

theorem summable_thetaCuspTailSurvivalAtom (x : ℝ) :
    Summable (fun n : ℕ => thetaCuspTailSurvivalAtom (n + 1) x) := by
  unfold thetaCuspTailSurvivalAtom
  exact (summable_thetaCuspTailDerivative 1 x).mul_left (-4)

theorem thetaCuspTailSecondDensityAtom_ge_half_survivalAtom
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    (1 / 2 : ℝ) * thetaCuspTailSurvivalAtom n x ≤
      thetaCuspTailSecondDensityAtom n x := by
  let u : ℝ := (n : ℝ) * Real.exp x
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx
  have hu : 1 ≤ u := by
    dsimp [u]
    nlinarith [Real.exp_pos x]
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpoly :
      -(1 / 2 : ℝ) *
          eval u (thetaCuspTailDerivativePolynomial 1) ≤
        eval u (thetaCuspTailDerivativePolynomial 2) := by
    simp [thetaCuspTailDerivativePolynomial, thetaCuspLogDerivativeStep]
    have hu2 : 1 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
    have hnonneg : 0 ≤ 4 * (Real.pi * u ^ 2) ^ 2 -
        7 * (Real.pi * u ^ 2) + 1 / 2 := by
      nlinarith [sq_nonneg (Real.pi * u ^ 2 - 1)]
    nlinarith
  unfold thetaCuspTailSurvivalAtom thetaCuspTailSecondDensityAtom
    thetaCuspPolynomialAtom
  dsimp [u] at hpoly
  have hfront : 0 ≤
      4 * (Real.exp (x / 2) *
        Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2)) := by positivity
  calc
    (1 / 2 : ℝ) *
        (-4 * (Real.exp (x / 2) *
          eval ((n : ℝ) * Real.exp x) (thetaCuspTailDerivativePolynomial 1) *
            Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2))) =
      (4 * (Real.exp (x / 2) *
        Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2))) *
          (-(1 / 2 : ℝ) *
            eval ((n : ℝ) * Real.exp x) (thetaCuspTailDerivativePolynomial 1)) := by ring
    _ ≤ (4 * (Real.exp (x / 2) *
        Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2))) *
          eval ((n : ℝ) * Real.exp x) (thetaCuspTailDerivativePolynomial 2) :=
      mul_le_mul_of_nonneg_left hpoly hfront
    _ = 4 * (Real.exp (x / 2) *
        eval ((n : ℝ) * Real.exp x) (thetaCuspTailDerivativePolynomial 2) *
          Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2)) := by ring

theorem thetaCuspTailSecondDensity_ge_half_survival
    {x : ℝ} (hx : 0 ≤ x) :
    (1 / 2 : ℝ) * thetaCuspTailSurvival x ≤ thetaCuspTailSecondDensity x := by
  rw [thetaCuspTailSurvival_eq_tsum_atom,
    thetaCuspTailSecondDensity_eq_tsum_atom]
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun n => thetaCuspTailSecondDensityAtom_ge_half_survivalAtom
      (n := n + 1) (by omega) hx)
    ((summable_thetaCuspTailSurvivalAtom x).mul_left (1 / 2 : ℝ))
    (summable_thetaCuspTailDerivative 2 x |>.mul_left 4)

def thetaCuspCompletedSurvivalRemainder (x : ℝ) : ℝ :=
  Real.exp (-x / 2) - thetaCuspTailSurvival x

theorem thetaCuspCompletedSurvivalRemainder_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thetaCuspCompletedSurvivalRemainder x := by
  let f : ℝ → ℝ := fun t => Real.exp (t / 2) * thetaCuspTailSurvival t
  have hfderiv (t : ℝ) : HasDerivAt f
      (Real.exp (t / 2) *
        ((1 / 2 : ℝ) * thetaCuspTailSurvival t -
          thetaCuspTailSecondDensity t)) t := by
    dsimp [f]
    convert
      ((Real.hasDerivAt_exp (t / 2)).comp t ((hasDerivAt_id t).div_const 2)).mul
        (hasDerivAt_thetaCuspTailSurvival t) using 1
    all_goals simp only [Function.comp_apply, id_eq]
    ring
  have hfanti : AntitoneOn f (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr fun t =>
        (hfderiv t).continuousAt).continuousOn
    · exact fun t _ht => (hfderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hfderiv t).deriv]
      have ht0 : 0 ≤ t := by
        have : 0 < t := by simpa [interior_Ici] using ht
        exact this.le
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr (thetaCuspTailSecondDensity_ge_half_survival ht0))
  have hle : f x ≤ f 0 := hfanti (by simp) hx hx
  simp only [f, thetaCuspTailSurvival_zero, zero_div, Real.exp_zero, mul_one] at hle
  unfold thetaCuspCompletedSurvivalRemainder
  have hexp : 0 < Real.exp (x / 2) := Real.exp_pos _
  have heta : thetaCuspTailSurvival x ≤ Real.exp (-x / 2) := by
    apply (mul_le_mul_iff_of_pos_left hexp).mp
    calc
      Real.exp (x / 2) * thetaCuspTailSurvival x ≤ 1 := hle
      _ = Real.exp (x / 2) * Real.exp (-x / 2) := by
        rw [← Real.exp_add]
        ring_nf
        rw [Real.exp_zero]
  exact sub_nonneg.mpr heta

end

end RHTower

