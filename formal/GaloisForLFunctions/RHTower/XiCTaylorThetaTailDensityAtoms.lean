import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSeamJets

/-!
# Exact masses of the differentiated theta-tail atoms

The canonical probability density `4 T''` is a positive sum of integer Gaussian atoms on the
positive logarithmic half-line.  This module proves the exact mass of every atom.  In particular,
the first atom has mass `(8π - 2) exp (-π)`, which makes the possible dominant-atom cancellation
coordinate exact rather than numerical.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The `n`th integer atom of the canonical differentiated tail density. -/
def thetaCuspTailSecondDensityAtom (n : ℕ) (x : ℝ) : ℝ :=
  4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 2) n x

/-- The canonical density is the sum of its positive-index differentiated Gaussian atoms. -/
theorem thetaCuspTailSecondDensity_eq_tsum_atom (x : ℝ) :
    thetaCuspTailSecondDensity x =
      ∑' n : ℕ, thetaCuspTailSecondDensityAtom (n + 1) x := by
  rw [thetaCuspTailSecondDensity, thetaCuspTailDerivative]
  unfold thetaCuspTailSecondDensityAtom
  simpa only using (Summable.tsum_mul_left 4
    (summable_thetaCuspTailDerivative 2 x)).symm

/-- Every positive-index density atom is strictly positive on the closed positive half-line. -/
theorem thetaCuspTailSecondDensityAtom_pos
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspTailSecondDensityAtom n x := by
  unfold thetaCuspTailSecondDensityAtom
  exact mul_pos (by norm_num)
    (thetaCuspTailDerivative_two_atom_pos hn hx)

/-- Each positive-index polynomial-Gaussian atom is integrable on the positive half-line. -/
theorem integrableOn_thetaCuspPolynomialAtom_Ioi_of_pos
    (P : ℝ[X]) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (thetaCuspPolynomialAtom P n) (Ioi 0) := by
  let C : ℝ := thetaCuspGaussianConstant P *
    Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity [thetaCuspGaussianConstant_nonneg P]
  have hdom : IntegrableOn (fun x : ℝ => C * Real.exp (-x)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).const_mul C
  apply Integrable.mono hdom
  · exact ((continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspPolynomialAtom P n x).continuousAt)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)]
    have h := exp_mul_abs_thetaCuspPolynomialAtom_le_of_pos P hx.le hn
    calc
      |thetaCuspPolynomialAtom P n x| =
          Real.exp (-x) * (Real.exp x * |thetaCuspPolynomialAtom P n x|) := by
            rw [← mul_assoc, ← Real.exp_add]
            simp
      _ ≤ Real.exp (-x) * C := by
        exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = C * Real.exp (-x) := by ring

/-- Every positive-index polynomial-Gaussian atom tends to zero at the positive cusp. -/
theorem thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
    (P : ℝ[X]) {n : ℕ} (hn : 0 < n) :
    Tendsto (thetaCuspPolynomialAtom P n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let C : ℝ := thetaCuspGaussianConstant P *
    Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2)
  have hle : ∀ᶠ x : ℝ in atTop,
      ‖thetaCuspPolynomialAtom P n x‖ ≤ C * Real.exp (-x) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.norm_eq_abs]
    have h := exp_mul_abs_thetaCuspPolynomialAtom_le_of_pos P hx hn
    calc
      |thetaCuspPolynomialAtom P n x| =
          Real.exp (-x) * (Real.exp x * |thetaCuspPolynomialAtom P n x|) := by
            rw [← mul_assoc, ← Real.exp_add]
            simp
      _ ≤ Real.exp (-x) * C := by
        exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = C * Real.exp (-x) := by ring
  have hmajor : Tendsto (fun x : ℝ => C * Real.exp (-x)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hle hmajor

/-- Exact mass of every positive-index atom of `4 T''`. -/
theorem integral_thetaCuspTailSecondDensityAtom (n : ℕ) (hn : 0 < n) :
    (∫ x : ℝ in Ioi 0, thetaCuspTailSecondDensityAtom n x) =
      (8 * Real.pi * (n : ℝ) ^ 2 - 2) *
        Real.exp (-Real.pi * (n : ℝ) ^ 2) := by
  have hstep : thetaCuspLogDerivativeStep
      (thetaCuspTailDerivativePolynomial 1) =
      thetaCuspTailDerivativePolynomial 2 := rfl
  have hzero : Tendsto
      (fun x : ℝ => (1 : ℝ) *
        thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 1) n x)
      (𝓝[>] 0)
      (𝓝 (thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 1) n 0)) := by
    have hc : Continuous (fun x : ℝ => (1 : ℝ) *
        thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 1) n x) :=
      continuous_const.mul (continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 1) n x).continuousAt)
    simpa using (hc.continuousAt : Tendsto _ (𝓝 (0 : ℝ)) _).mono_left inf_le_left
  have htop : Tendsto
      (fun x : ℝ => (1 : ℝ) *
        thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 1) n x)
      atTop (𝓝 0) := by
    simpa using thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
      (thetaCuspTailDerivativePolynomial 1) hn
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ))
    (u := fun _ : ℝ => 1)
    (u' := fun _ : ℝ => 0)
    (v := thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 1) n)
    (v' := thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 2) n)
    (fun x _ => hasDerivAt_const x 1)
    (fun x _ => by
      simpa only [hstep] using
        hasDerivAt_thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 1) n x)
    (by
      have heq : ((fun _ : ℝ => (1 : ℝ)) *
          thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 2) n) =
          thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 2) n := by
        funext x
        simp only [Pi.mul_apply, one_mul]
      rw [heq]
      exact integrableOn_thetaCuspPolynomialAtom_Ioi_of_pos
        (thetaCuspTailDerivativePolynomial 2) (n := n) hn)
    (by
      have heq : ((fun _ : ℝ => (0 : ℝ)) *
          thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 1) n) =
          (fun _ : ℝ => (0 : ℝ)) := by
        funext x
        simp only [Pi.mul_apply, zero_mul]
      rw [heq]
      exact integrableOn_zero)
    hzero htop
  change (∫ x : ℝ in Ioi 0,
      4 * thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 2) n x) = _
  rw [integral_const_mul]
  have hmass : (∫ x : ℝ in Ioi 0,
      thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 2) n x) =
      -thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 1) n 0 := by
    simpa only [one_mul, zero_mul, integral_zero, sub_zero, zero_sub] using hibp
  rw [hmass]
  simp [thetaCuspPolynomialAtom, thetaCuspTailDerivativePolynomial,
    thetaCuspLogDerivativeStep]
  ring

/-- The dominant first differentiated theta atom has the closed mass `(8π-2)e^{-π}`. -/
theorem integral_thetaCuspTailSecondDensityAtom_one :
    (∫ x : ℝ in Ioi 0, thetaCuspTailSecondDensityAtom 1 x) =
      (8 * Real.pi - 2) * Real.exp (-Real.pi) := by
  simpa using integral_thetaCuspTailSecondDensityAtom 1 (by omega)

/-- On the positive logarithmic half-line, the second-derivative atom polynomial is bounded below
by its quartic leading scale. -/
theorem thetaCuspTailDerivativePolynomial_two_lower
    {u : ℝ} (hu : 1 ≤ u) :
    Real.pi ^ 2 * u ^ 4 ≤
      eval u (thetaCuspTailDerivativePolynomial 2) := by
  rw [thetaCuspTailDerivativePolynomial_two]
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hu2 : 1 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
  have hv : 3 < Real.pi * u ^ 2 := by nlinarith [Real.pi_pos]
  nlinarith [sq_nonneg (Real.pi * u ^ 2 - 1)]

/-- A matching elementary quartic upper bound for the second-derivative atom polynomial. -/
theorem thetaCuspTailDerivativePolynomial_two_upper
    {u : ℝ} (hu : 1 ≤ u) :
    eval u (thetaCuspTailDerivativePolynomial 2) ≤
      5 * Real.pi ^ 2 * u ^ 4 := by
  rw [thetaCuspTailDerivativePolynomial_two]
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hu2 : 1 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
  have hpi2 : 9 < Real.pi ^ 2 := by
    have hp : 0 < (Real.pi - 3) * (Real.pi + 3) := by positivity
    nlinarith
  have hu4 : 1 ≤ u ^ 4 := by
    rw [show u ^ 4 = (u ^ 2) ^ 2 by ring]
    nlinarith [sq_nonneg (u ^ 2 - 1)]
  have hpi2u4 : 1 / 4 < Real.pi ^ 2 * u ^ 4 := by
    have hprod : 9 ≤ Real.pi ^ 2 * u ^ 4 := by
      calc
        9 = 9 * 1 := by ring
        _ ≤ Real.pi ^ 2 * u ^ 4 :=
          mul_le_mul hpi2.le hu4 (by norm_num) (by positivity)
    linarith
  nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg u)]

/-- Every differentiated integer atom is pointwise dominated by the first atom with an explicit
Gaussian weight.  This is the source-specific domination estimate needed to bound the complete
`n ≥ 2` density tail without discarding its exact atom structure. -/
theorem thetaCuspTailSecondDensityAtom_le_first
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspTailSecondDensityAtom n x ≤
      (5 * (n : ℝ) ^ 4 *
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) *
          thetaCuspTailSecondDensityAtom 1 x := by
  let u : ℝ := Real.exp x
  have hu : 1 ≤ u := by
    dsimp [u]
    simpa using Real.exp_le_exp.mpr hx
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnu : 1 ≤ (n : ℝ) * u := by
    nlinarith [Real.exp_pos x]
  have hpolyLower := thetaCuspTailDerivativePolynomial_two_lower hu
  have hpolyUpper := thetaCuspTailDerivativePolynomial_two_upper hnu
  have hnSq : 1 ≤ (n : ℝ) ^ 2 := by nlinarith
  have huSq : 1 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
  have hprod : 0 ≤ ((n : ℝ) ^ 2 - 1) * (u ^ 2 - 1) :=
    mul_nonneg (sub_nonneg.mpr hnSq) (sub_nonneg.mpr huSq)
  have hexponent :
      -Real.pi * ((n : ℝ) * u) ^ 2 ≤
        -Real.pi * ((n : ℝ) ^ 2 - 1) + (-Real.pi * u ^ 2) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith
  have hgauss :
      Real.exp (-Real.pi * ((n : ℝ) * u) ^ 2) ≤
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1)) *
          Real.exp (-Real.pi * u ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hexponent
  have hfront : 0 ≤ 4 * Real.exp (x / 2) := by positivity
  have hpolyUpper' :
      eval ((n : ℝ) * u) (thetaCuspTailDerivativePolynomial 2) ≤
        5 * Real.pi ^ 2 * (n : ℝ) ^ 4 * u ^ 4 := by
    calc
      eval ((n : ℝ) * u) (thetaCuspTailDerivativePolynomial 2) ≤
          5 * Real.pi ^ 2 * ((n : ℝ) * u) ^ 4 := hpolyUpper
      _ = 5 * Real.pi ^ 2 * (n : ℝ) ^ 4 * u ^ 4 := by ring
  have hpolyNonneg :
      0 ≤ eval ((n : ℝ) * u) (thetaCuspTailDerivativePolynomial 2) :=
    (thetaCuspTailDerivativePolynomial_two_eval_pos hnu).le
  unfold thetaCuspTailSecondDensityAtom thetaCuspPolynomialAtom
  simp only [Nat.cast_one, one_mul]
  change 4 * (Real.exp (x / 2) *
      eval ((n : ℝ) * u) (thetaCuspTailDerivativePolynomial 2) *
        Real.exp (-Real.pi * ((n : ℝ) * u) ^ 2)) ≤ _
  change _ ≤ (5 * (n : ℝ) ^ 4 *
      Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) *
    (4 * (Real.exp (x / 2) *
      eval u (thetaCuspTailDerivativePolynomial 2) *
        Real.exp (-Real.pi * u ^ 2)))
  calc
    4 * (Real.exp (x / 2) *
        eval ((n : ℝ) * u) (thetaCuspTailDerivativePolynomial 2) *
          Real.exp (-Real.pi * ((n : ℝ) * u) ^ 2)) ≤
      4 * (Real.exp (x / 2) *
        (5 * Real.pi ^ 2 * (n : ℝ) ^ 4 * u ^ 4) *
          Real.exp (-Real.pi * ((n : ℝ) * u) ^ 2)) := by
            gcongr
    _ ≤ 4 * (Real.exp (x / 2) *
        (5 * Real.pi ^ 2 * (n : ℝ) ^ 4 * u ^ 4) *
          (Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1)) *
            Real.exp (-Real.pi * u ^ 2))) := by
              gcongr
    _ = (5 * (n : ℝ) ^ 4 *
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) *
      (4 * (Real.exp (x / 2) * (Real.pi ^ 2 * u ^ 4) *
        Real.exp (-Real.pi * u ^ 2))) := by ring
    _ ≤ (5 * (n : ℝ) ^ 4 *
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) *
      (4 * (Real.exp (x / 2) *
        eval u (thetaCuspTailDerivativePolynomial 2) *
          Real.exp (-Real.pi * u ^ 2))) := by
            gcongr

/-- The raw `m`th moment of one differentiated density atom. -/
def thetaCuspTailSecondDensityAtomMoment (n m : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0, x ^ m * thetaCuspTailSecondDensityAtom n x

theorem integrableOn_pow_mul_thetaCuspTailSecondDensity (m : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ m * thetaCuspTailSecondDensity x) (Ioi 0) := by
  have h := (integrableOn_pow_mul_thetaCuspTailDerivative m 2).const_mul 4
  simpa only [thetaCuspTailSecondDensity, mul_assoc, mul_left_comm, mul_comm] using h

/-- Every positive-index density atom has moments of all orders. -/
theorem integrableOn_pow_mul_thetaCuspTailSecondDensityAtom
    (m : ℕ) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ => x ^ m * thetaCuspTailSecondDensityAtom n x) (Ioi 0) := by
  have hfull := integrableOn_pow_mul_thetaCuspTailSecondDensity m
  apply Integrable.mono hfull
  · have hatom : Continuous (thetaCuspTailSecondDensityAtom n) := by
      unfold thetaCuspTailSecondDensityAtom
      exact continuous_const.mul (continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 2) n x).continuousAt)
    exact ((continuous_id.pow m).mul hatom).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg, abs_of_nonneg]
    · have hatom : thetaCuspTailSecondDensityAtom n x ≤
          thetaCuspTailSecondDensity x := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
        rw [thetaCuspTailSecondDensity_eq_tsum_atom]
        have hs : Summable (fun j : ℕ => thetaCuspTailSecondDensityAtom (j + 1) x) := by
          unfold thetaCuspTailSecondDensityAtom
          simpa only using (summable_thetaCuspTailDerivative 2 x).mul_left 4
        exact hs.le_tsum k (fun j _ =>
          (thetaCuspTailSecondDensityAtom_pos (Nat.succ_pos j) hx.le).le)
      exact mul_le_mul_of_nonneg_left hatom (pow_nonneg hx.le _)
    · exact mul_nonneg (pow_nonneg hx.le _)
        (thetaCuspTailSecondDensity_pos hx).le
    · exact mul_nonneg (pow_nonneg hx.le _)
        (thetaCuspTailSecondDensityAtom_pos hn hx.le).le

/-- Every differentiated atom moment is nonnegative. -/
theorem thetaCuspTailSecondDensityAtomMoment_nonneg
    (n m : ℕ) :
    0 ≤ thetaCuspTailSecondDensityAtomMoment n m := by
  rw [thetaCuspTailSecondDensityAtomMoment]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rcases n with _ | n
  · rw [thetaCuspTailSecondDensityAtom, thetaCuspPolynomialAtom,
      thetaCuspTailDerivativePolynomial_two]
    norm_num
    exact mul_nonneg (pow_nonneg hx.le _) (by positivity)
  · exact mul_nonneg (pow_nonneg hx.le _)
      (thetaCuspTailSecondDensityAtom_pos (Nat.succ_pos n) hx.le).le

/-- Pointwise Gaussian domination transfers to every raw moment used by the finite core. -/
theorem thetaCuspTailSecondDensityAtomMoment_le_first
    {n : ℕ} (hn : 0 < n) (m : ℕ) :
    thetaCuspTailSecondDensityAtomMoment n m ≤
      (5 * (n : ℝ) ^ 4 *
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) *
          thetaCuspTailSecondDensityAtomMoment 1 m := by
  let q : ℝ := 5 * (n : ℝ) ^ 4 *
    Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  rw [thetaCuspTailSecondDensityAtomMoment,
    thetaCuspTailSecondDensityAtomMoment]
  change (∫ x : ℝ in Ioi 0,
      x ^ m * thetaCuspTailSecondDensityAtom n x) ≤
    q * ∫ x : ℝ in Ioi 0,
      x ^ m * thetaCuspTailSecondDensityAtom 1 x
  rw [← integral_const_mul]
  apply integral_mono_ae
  · exact integrableOn_pow_mul_thetaCuspTailSecondDensityAtom m hn
  · exact (integrableOn_pow_mul_thetaCuspTailSecondDensityAtom m
      (by omega : 0 < 1)).const_mul q
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [q]
    calc
      x ^ m * thetaCuspTailSecondDensityAtom n x ≤
          x ^ m * ((5 * (n : ℝ) ^ 4 *
            Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) *
              thetaCuspTailSecondDensityAtom 1 x) := by
        exact mul_le_mul_of_nonneg_left
          (thetaCuspTailSecondDensityAtom_le_first hn hx.le)
          (pow_nonneg hx.le _)
      _ = (5 * (n : ℝ) ^ 4 *
            Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1))) *
          (x ^ m * thetaCuspTailSecondDensityAtom 1 x) := by ring

end

end RHTower
