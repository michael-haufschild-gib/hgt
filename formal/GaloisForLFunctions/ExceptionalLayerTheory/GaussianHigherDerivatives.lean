import GaloisForLFunctions.ExceptionalLayerTheory.GaussianTypeIContinuum

/-!
# Higher derivatives of complex Mellin Gaussians

The derivative tower retains Gaussian Mellin weights with shifted exponents.
Its first `p - 1` boundary values vanish when `p - 1 < re w`, while the
`p`th derivative remains integrable. This is the boundary regularity needed
for higher-order complete divisor-lattice comparisons.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Explicit derivatives, including the integrable final derivative at zero. -/
def gaussianMellinJet : ℕ → ℂ → ℂ → ℝ → ℂ
  | 0, w, ε, x => gaussianMellinWeight w ε x
  | k + 1, w, ε, x =>
      w * gaussianMellinJet k (w - 1) ε x - 2 * ε * gaussianMellinJet k (w + 1) ε x

/-- A positive recursive bound for the integral of the derivative norm. -/
def gaussianMellinJetVariation : ℕ → ℂ → ℂ → ℝ
  | 0, w, ε => (1 / 2) * (1 / ε.re) ^ ((w.re + 1) / 2) * Real.Gamma ((w.re + 1) / 2)
  | k + 1, w, ε => ‖w‖ * gaussianMellinJetVariation k (w - 1) ε +
      2 * ‖ε‖ * gaussianMellinJetVariation k (w + 1) ε

private theorem norm_mellinWeight {w ε : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖gaussianMellinWeight w ε x‖ = x ^ w.re * Real.exp (-ε.re * x ^ 2) := by
  rw [gaussianMellinWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp]
  congr 2
  simp [pow_two]

private theorem hasDerivAt_mellinWeight {w : ℂ} (hw : 0 < w.re)
    (ε : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gaussianMellinWeight w ε) (gaussianMellinJet 1 w ε x) x := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hpow := hasDerivAt_ofReal_cpow_const hx.ne' hw0
  have he := (((Complex.ofRealCLM.hasDerivAt (x := x)).pow 2).const_mul ε).neg.cexp
  apply (hpow.mul he).congr_deriv
  have hp : (x : ℂ) ^ (w + 1) = (x : ℂ) ^ w * (x : ℂ) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one]
  dsimp only [gaussianMellinJet, gaussianMellinWeight]
  rw [hp]
  simp only [Pi.neg_apply, Pi.pow_apply, Complex.ofRealCLM_apply, Complex.ofReal_one,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

/-- The explicit tower differentiates on the positive half-line. -/
theorem hasDerivAt_gaussianMellinJet (k : ℕ) {w : ℂ} (hw : (k : ℝ) < w.re)
    (ε : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gaussianMellinJet k w ε) (gaussianMellinJet (k + 1) w ε x) x := by
  induction k generalizing w with
  | zero => exact hasDerivAt_mellinWeight (by simpa only [Nat.cast_zero] using hw) ε hx
  | succ k ih =>
    have hm : (k : ℝ) < (w - 1).re := by
      simp only [Complex.sub_re, Complex.one_re]; push_cast at hw; linarith
    have hp : (k : ℝ) < (w + 1).re := by
      simp only [Complex.add_re, Complex.one_re]; push_cast at hw; linarith
    exact ((ih hm).const_mul w).sub ((ih hp).const_mul (2 * ε))

/-- Every derivative below the real Mellin exponent extends continuously through zero. -/
theorem continuous_gaussianMellinJet (k : ℕ) {w : ℂ} (hw : (k : ℝ) < w.re) (ε : ℂ) :
    Continuous (gaussianMellinJet k w ε) := by
  induction k generalizing w with
  | zero =>
    exact (Complex.continuous_ofReal_cpow_const
      (by simpa only [Nat.cast_zero] using hw)).mul (by fun_prop)
  | succ k ih =>
    have hm : (k : ℝ) < (w - 1).re := by
      simp only [Complex.sub_re, Complex.one_re]; push_cast at hw; linarith
    have hp : (k : ℝ) < (w + 1).re := by
      simp only [Complex.add_re, Complex.one_re]; push_cast at hw; linarith
    exact (continuous_const.mul (ih hm)).sub (continuous_const.mul (ih hp))

/-- Every derivative below the real Mellin exponent vanishes at zero. -/
theorem gaussianMellinJet_zero (k : ℕ) {w : ℂ} (hw : (k : ℝ) < w.re) (ε : ℂ) :
    gaussianMellinJet k w ε 0 = 0 := by
  induction k generalizing w with
  | zero =>
    have hw0 : w ≠ 0 := fun h => by simp [h] at hw
    simp only [gaussianMellinJet, gaussianMellinWeight, Complex.ofReal_zero,
      Complex.zero_cpow hw0, zero_mul]
  | succ k ih =>
    have hm : (k : ℝ) < (w - 1).re := by
      simp only [Complex.sub_re, Complex.one_re]; push_cast at hw; linarith
    have hp : (k : ℝ) < (w + 1).re := by
      simp only [Complex.add_re, Complex.one_re]; push_cast at hw; linarith
    simp only [gaussianMellinJet, ih hm, ih hp, mul_zero, sub_self]

private theorem integrable_mellinWeight {w ε : ℂ}
    (hw : -1 < w.re) (hε : 0 < ε.re) :
    IntegrableOn (gaussianMellinWeight w ε) (Ioi 0) := by
  have hi : IntegrableOn (fun x : ℝ => x ^ w.re * Real.exp (-ε.re * x ^ (2 : ℕ)))
      (Ioi 0) := by
    simpa only [Real.rpow_two] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow hw (by norm_num : (1 : ℝ) ≤ 2) hε)
  have hc : ContinuousOn (gaussianMellinWeight w ε) (Ioi 0) := by
    intro x hx
    exact ((Complex.continuousAt_ofReal_cpow_const x w (Or.inr hx.ne')).mul
      (by fun_prop)).continuousWithinAt
  refine hi.mono' (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (norm_mellinWeight hx).le

/-- The final derivative is integrable even when its value is singular at zero. -/
theorem integrableOn_gaussianMellinJet (k : ℕ) {w ε : ℂ}
    (hw : (k : ℝ) - 1 < w.re) (hε : 0 < ε.re) :
    IntegrableOn (gaussianMellinJet k w ε) (Ioi 0) := by
  induction k generalizing w with
  | zero => exact integrable_mellinWeight (by simpa using hw) hε
  | succ k ih =>
    have hm : (k : ℝ) - 1 < (w - 1).re := by
      simp only [Complex.sub_re, Complex.one_re]; push_cast at hw; linarith
    have hp : (k : ℝ) - 1 < (w + 1).re := by
      simp only [Complex.add_re, Complex.one_re]; push_cast at hw; linarith
    exact ((ih hm).const_mul w).sub ((ih hp).const_mul (2 * ε))

/-- Explicit integral norm bound at every admissible derivative order. -/
theorem integral_norm_gaussianMellinJet_le (k : ℕ) {w ε : ℂ}
    (hw : (k : ℝ) - 1 < w.re) (hε : 0 < ε.re) :
    (∫ x in Ioi (0 : ℝ), ‖gaussianMellinJet k w ε x‖) ≤
      gaussianMellinJetVariation k w ε := by
  induction k generalizing w with
  | zero =>
    apply le_of_eq
    change (∫ x in Ioi (0 : ℝ), ‖gaussianMellinWeight w ε x‖) = _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => norm_mellinWeight hx)]
    exact RHTower.integral_rpow_mul_exp_neg_mul_sq_Ioi (by simpa using hw) hε
  | succ k ih =>
    have hm : (k : ℝ) - 1 < (w - 1).re := by
      simp only [Complex.sub_re, Complex.one_re]; push_cast at hw; linarith
    have hp : (k : ℝ) - 1 < (w + 1).re := by
      simp only [Complex.add_re, Complex.one_re]; push_cast at hw; linarith
    have him := (integrableOn_gaussianMellinJet k hm hε).norm.const_mul ‖w‖
    have hip := (integrableOn_gaussianMellinJet k hp hε).norm.const_mul (2 * ‖ε‖)
    calc
      _ ≤ ∫ x in Ioi (0 : ℝ), ‖w‖ * ‖gaussianMellinJet k (w - 1) ε x‖ +
          2 * ‖ε‖ * ‖gaussianMellinJet k (w + 1) ε x‖ := by
        apply integral_mono_ae (integrableOn_gaussianMellinJet (k + 1) hw hε).norm (him.add hip)
        exact Filter.Eventually.of_forall fun x => by
          simpa only [gaussianMellinJet, norm_mul, norm_ofNat, Pi.add_apply] using
            norm_sub_le (w * gaussianMellinJet k (w - 1) ε x)
              (2 * ε * gaussianMellinJet k (w + 1) ε x)
      _ = ‖w‖ * (∫ x in Ioi (0 : ℝ), ‖gaussianMellinJet k (w - 1) ε x‖) +
          2 * ‖ε‖ * (∫ x in Ioi (0 : ℝ), ‖gaussianMellinJet k (w + 1) ε x‖) := by
        rw [integral_add him hip, integral_const_mul, integral_const_mul]
      _ ≤ _ := _root_.add_le_add
        (mul_le_mul_of_nonneg_left (ih hm) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (ih hp) (by positivity))

/-- Absolute convergence on every positive lattice, with no upper restriction on the exponent. -/
theorem summable_gaussianMellinWeight_lattice_all {w ε : ℂ}
    (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    Summable (fun n : ℕ => gaussianMellinWeight w ε (b * (n + 1))) := by
  obtain ⟨K, hK⟩ := exists_nat_ge w.re
  have hs := (summable_nat_add_iff 1).mpr
    (RHTower.summable_pow_mul_exp_neg_nat_sq K
      (show 0 < ε.re * b ^ 2 by positivity))
  apply (hs.mul_left (b ^ w.re)).of_norm_bounded
  intro n
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hx : 0 < b * ((n : ℝ) + 1) := by positivity
  rw [norm_mellinWeight hx, Real.mul_rpow hb.le (by positivity)]
  have hp : ((n : ℝ) + 1) ^ w.re ≤ ((n : ℝ) + 1) ^ K := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hn hK
  have he : -ε.re * (b * ((n : ℝ) + 1)) ^ 2 =
      -(ε.re * b ^ 2) * ((n : ℝ) + 1) ^ 2 := by ring
  rw [he]
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ b ^ w.re * ((n : ℝ) + 1) ^ K *
        Real.exp (-(ε.re * b ^ 2) * ((n : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hb.le w.re)) (Real.exp_pos _).le
    _ = _ := by ring

/-- Every derivative tower has summable positive-lattice samples. -/
theorem summable_gaussianMellinJet_lattice (k : ℕ) (w : ℂ) {ε : ℂ}
    (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    Summable (fun n : ℕ => gaussianMellinJet k w ε (b * (n + 1))) := by
  induction k generalizing w with
  | zero => exact summable_gaussianMellinWeight_lattice_all hε hb
  | succ k ih => exact ((ih (w - 1)).mul_left w).sub ((ih (w + 1)).mul_left (2 * ε))

/-- Dimensionless Gaussian derivative constants; dependence on height is separated. -/
def gaussianMellinJetConstant : ℕ → ℝ → ℝ
  | 0, a => Real.Gamma ((a + 1) / 2) / 2
  | k + 1, a => (|a| + 1) * gaussianMellinJetConstant k (a - 1) +
      8 * gaussianMellinJetConstant k (a + 1)

theorem gaussianMellinJetConstant_nonneg (k : ℕ) {a : ℝ}
    (ha : (k : ℝ) - 1 < a) : 0 ≤ gaussianMellinJetConstant k a := by
  induction k generalizing a with
  | zero =>
    exact div_nonneg (Real.Gamma_pos_of_pos (by push_cast at ha; linarith)).le (by norm_num)
  | succ k ih =>
    have hm : (k : ℝ) - 1 < a - 1 := by push_cast at ha; linarith
    have hp : (k : ℝ) - 1 < a + 1 := by push_cast at ha; linarith
    exact add_nonneg (mul_nonneg (by positivity) (ih hm)) (mul_nonneg (by norm_num) (ih hp))

/-- Height costs one power per derivative; damping contributes its exact homogeneous power. -/
theorem gaussianMellinJetVariation_le (k : ℕ) {w ε : ℂ} {t : ℝ}
    (hw : (k : ℝ) - 1 < w.re) (hε : 0 < ε.re) (ht : 1 ≤ t)
    (him : |w.im| ≤ t) (hsector : ‖ε‖ ≤ 4 * ε.re * t) :
    gaussianMellinJetVariation k w ε ≤
      gaussianMellinJetConstant k w.re * t ^ k * ε.re ^ (((k : ℝ) - w.re - 1) / 2) := by
  induction k generalizing w with
  | zero =>
    apply le_of_eq
    simp only [gaussianMellinJetVariation, gaussianMellinJetConstant, pow_zero,
      mul_one, Nat.cast_zero, zero_sub]
    simp only [one_div]
    rw [Real.inv_rpow hε.le, ← Real.rpow_neg hε.le]
    rw [show -((w.re + 1) / 2) = (-w.re - 1) / 2 by ring]
    ring
  | succ k ih =>
    have hm : (k : ℝ) - 1 < (w - 1).re := by
      simp only [Complex.sub_re, Complex.one_re]; push_cast at hw; linarith
    have hp : (k : ℝ) - 1 < (w + 1).re := by
      simp only [Complex.add_re, Complex.one_re]; push_cast at hw; linarith
    have hmi : |(w - 1).im| ≤ t := by simpa only [Complex.sub_im, Complex.one_im, sub_zero] using him
    have hpi : |(w + 1).im| ≤ t := by simpa only [Complex.add_im, Complex.one_im, add_zero] using him
    have hm' := ih hm hmi
    have hp' := ih hp hpi
    have hcm := gaussianMellinJetConstant_nonneg k hm
    have hcp := gaussianMellinJetConstant_nonneg k hp
    have hnorm : ‖w‖ ≤ (|w.re| + 1) * t := by
      have h := Complex.norm_le_abs_re_add_abs_im w
      have ha := mul_le_mul_of_nonneg_left ht (abs_nonneg w.re)
      nlinarith only [h, him, ha]
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht
    have hmprod := mul_le_mul hnorm hm'
      (le_trans (integral_nonneg fun _ => norm_nonneg _) (integral_norm_gaussianMellinJet_le k hm hε))
      (by positivity : 0 ≤ (|w.re| + 1) * t)
    have hpprod := mul_le_mul (mul_le_mul_of_nonneg_left hsector (by norm_num : (0 : ℝ) ≤ 2)) hp'
      (le_trans (integral_nonneg fun _ => norm_nonneg _) (integral_norm_gaussianMellinJet_le k hp hε))
      (by positivity : 0 ≤ 2 * (4 * ε.re * t))
    have he : ε.re * ε.re ^ (((k : ℝ) - (w.re + 1) - 1) / 2) =
        ε.re ^ ((((k + 1 : ℕ) : ℝ) - w.re - 1) / 2) := by
      nth_rw 1 [← Real.rpow_one ε.re]
      rw [← Real.rpow_add hε]
      congr 1
      push_cast
      ring
    calc
      _ ≤ (|w.re| + 1) * t *
          (gaussianMellinJetConstant k (w - 1).re * t ^ k *
            ε.re ^ (((k : ℝ) - (w - 1).re - 1) / 2)) +
          2 * (4 * ε.re * t) *
          (gaussianMellinJetConstant k (w + 1).re * t ^ k *
            ε.re ^ (((k : ℝ) - (w + 1).re - 1) / 2)) :=
        _root_.add_le_add hmprod hpprod
      _ = _ := by
        simp only [Complex.sub_re, Complex.add_re, Complex.one_re,
          gaussianMellinJetConstant, pow_succ]
        rw [show ((k : ℝ) - (w.re - 1) - 1) / 2 =
          (((k + 1 : ℕ) : ℝ) - w.re - 1) / 2 by push_cast; ring]
        calc
          _ = ((|w.re| + 1) * gaussianMellinJetConstant k (w.re - 1)) *
              (t ^ k * t) * ε.re ^ ((((k + 1 : ℕ) : ℝ) - w.re - 1) / 2) +
              (8 * gaussianMellinJetConstant k (w.re + 1)) * (t ^ k * t) *
                (ε.re * ε.re ^ (((k : ℝ) - (w.re + 1) - 1) / 2)) := by ring
          _ = _ := by rw [he]; ring

#print axioms hasDerivAt_gaussianMellinJet
#print axioms gaussianMellinJet_zero
#print axioms integrableOn_gaussianMellinJet
#print axioms integral_norm_gaussianMellinJet_le
#print axioms summable_gaussianMellinJet_lattice
#print axioms gaussianMellinJetVariation_le

end GaloisForLFunctions.ExceptionalLayerTheory
