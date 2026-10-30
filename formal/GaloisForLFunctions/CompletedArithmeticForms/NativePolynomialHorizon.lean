import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomPolynomialHorizon
import GaloisForLFunctions.CompletedArithmeticForms.NativeGaussianHorizon

/-!
# Relative polynomial errors for the complete theta source

The literal infinite theta remainder is exponentially small compared with the
native Gamma moments on a joint order and scale domain. Combining it with the
physical polynomial envelope gives quadratic relative error at every admitted order.
-/

noncomputable section

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- The common amplitude in the literal infinite-source likelihood estimate. -/
def nativePolynomialTailConstant : ℝ := 27 * Real.exp (3 * Real.pi) / 399

theorem nativePolynomialTailConstant_pos : 0 < nativePolynomialTailConstant := by
  unfold nativePolynomialTailConstant
  positivity

/-- The Gamma leading coefficient pays the factorial in every exponential remainder. -/
theorem gaussianMoment_factorial_lower (k : ℕ) :
    (8 : ℝ) ^ k * (k.factorial : ℝ) ≤ gaussianMoment k := by
  induction k with
  | zero => simp [gaussianMoment]
  | succ k ih =>
    rw [gaussianMoment_successor, pow_succ, Nat.factorial_succ]
    push_cast
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hg := (gaussianMoment_positive k).le
    have hm := mul_le_mul_of_nonneg_left ih
      (show 0 ≤ 8 * ((k : ℝ) + 1) by positivity)
    have hextra := mul_nonneg hk hg
    nlinarith only [hm, hextra]

private theorem seventy_two_le_exp_eight : (72 : ℝ) ≤ Real.exp 8 := by
  have h : (3 : ℝ) ≤ Real.exp 2 := by linarith only [Real.add_one_le_exp (2 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h 4
  have he : Real.exp 8 = Real.exp 2 ^ 4 := by
    rw [show (8 : ℝ) = 2 + 2 + 2 + 2 by norm_num,
      Real.exp_add, Real.exp_add, Real.exp_add]
    ring
  rw [he]
  norm_num at hp
  linarith only [hp]

private theorem seventy_two_pow_le_exp (k : ℕ) :
    (72 : ℝ) ^ k ≤ Real.exp (8 * (k : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add]
    exact mul_le_mul ih seventy_two_le_exp_eight (by norm_num) (Real.exp_pos _).le

private theorem source_power_le_gamma (k : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (24 : ℝ) ^ (2 * k) * q ^ k * Real.exp (-q) ≤ (72 : ℝ) ^ k * gaussianMoment k := by
  have hp := _root_.RHTower.pow_mul_exp_neg_le_factorial k hq
  have h24 : (24 : ℝ) ^ (2 * k) = (72 : ℝ) ^ k * (8 : ℝ) ^ k := by
    rw [pow_mul, ← mul_pow]
    norm_num
  calc
    _ = (72 : ℝ) ^ k * ((8 : ℝ) ^ k * (q ^ k * Real.exp (-q))) := by rw [h24]; ring
    _ ≤ (72 : ℝ) ^ k * ((8 : ℝ) ^ k * (k.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (gaussianMoment_factorial_lower k) (by positivity)

/-- The full infinite theta remainder costs one common reciprocal-scale multiple of the Gamma moment. -/
theorem nativeScaledEvenJet_firstAtom_relative_error_le (k : ℕ) {x : ℝ}
    (htail : ((2 * k : ℕ) : ℝ) + 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (horder : 8 * (k : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet k x - thetaCuspFirstAtomScaledEvenJet k x| ≤
      nativePolynomialTailConstant * gaussianMoment k /
        thetaCuspSingleAtomReflectionScale 1 x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq6 : 6 ≤ q := by
    dsimp [q]
    linarith only [htail, (Nat.cast_nonneg (2 * k) : (0 : ℝ) ≤ (2 * k : ℕ))]
  have hq : 0 < q := by linarith only [hq6]
  have hx : 0 < x := regimeOne_pos_of_six_le hq6
  have he := abs_thetaCuspNativeScaledEvenJet_sub_first_le_effective k hx htail
  have hgamma := gaussianMoment_positive k
  have hA := nativePolynomialTailConstant_pos
  have hlikelihood :
      27 * (24 : ℝ) ^ (2 * k) * q ^ k * regimeOneLikelihoodScale x =
        nativePolynomialTailConstant *
          ((24 : ℝ) ^ (2 * k) * q ^ k * Real.exp (-q)) * Real.exp (-2 * q) := by
    rw [regimeOneLikelihoodScale_eq]
    unfold nativePolynomialTailConstant
    rw [show -(3 * thetaCuspSingleAtomReflectionScale 1 x) = -q + -2 * q by dsimp [q]; ring,
      Real.exp_add]
    ring
  have hexp : Real.exp (8 * (k : ℝ) - 2 * q) ≤ Real.exp (-q) :=
    Real.exp_le_exp.mpr (by change 8 * (k : ℝ) ≤ q at horder; linarith only [horder])
  have hinv : Real.exp (-q) ≤ 1 / q := by
    apply (le_div_iff₀ hq).mpr
    have hp := _root_.RHTower.pow_mul_exp_neg_le_factorial 1 hq.le
    norm_num at hp
    nlinarith only [hp]
  calc
    _ ≤ 27 * (24 : ℝ) ^ (2 * k) * q ^ k * regimeOneLikelihoodScale x := he
    _ = _ := hlikelihood
    _ ≤ nativePolynomialTailConstant * ((72 : ℝ) ^ k * gaussianMoment k) * Real.exp (-2 * q) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (source_power_le_gamma k hq.le) hA.le) (Real.exp_pos _).le
    _ ≤ nativePolynomialTailConstant * (Real.exp (8 * (k : ℝ)) * gaussianMoment k) *
        Real.exp (-2 * q) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (seventy_two_pow_le_exp k) hgamma.le) hA.le)
        (Real.exp_pos _).le
    _ = nativePolynomialTailConstant * gaussianMoment k * Real.exp (8 * (k : ℝ) - 2 * q) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ nativePolynomialTailConstant * gaussianMoment k * Real.exp (-q) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hA.le hgamma.le)
    _ ≤ nativePolynomialTailConstant * gaussianMoment k * (1 / q) :=
      mul_le_mul_of_nonneg_left hinv (mul_nonneg hA.le hgamma.le)
    _ = _ := by dsimp only [q]; ring

/-- Quadratic relative Gaussian error for every complete native moment on its joint source domain. -/
theorem nativeScaledEvenJet_quadratic_relative_error_le (k : ℕ) {x : ℝ}
    (htail : ((2 * k : ℕ) : ℝ) + 6 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hlinear : 8 * (k : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hquadratic : (k : ℝ) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet k x - gaussianMoment k| ≤
      (3 * (k : ℝ) ^ 2 + nativePolynomialTailConstant) * gaussianMoment k /
        thetaCuspSingleAtomReflectionScale 1 x := by
  have hscale : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    linarith only [htail, (Nat.cast_nonneg (2 * k) : (0 : ℝ) ≤ (2 * k : ℕ))]
  have hfirst := firstAtomScaledEvenJet_quadratic_error_le k hscale hquadratic
  have htail' := nativeScaledEvenJet_firstAtom_relative_error_le k htail hlinear
  calc
    _ ≤ |thetaCuspNativeScaledEvenJet k x - thetaCuspFirstAtomScaledEvenJet k x| +
        |thetaCuspFirstAtomScaledEvenJet k x - gaussianMoment k| := abs_sub_le _ _ _
    _ ≤ nativePolynomialTailConstant * gaussianMoment k / thetaCuspSingleAtomReflectionScale 1 x +
        3 * (k : ℝ) ^ 2 * gaussianMoment k / thetaCuspSingleAtomReflectionScale 1 x :=
      add_le_add htail' hfirst
    _ = _ := by ring

/-- The exact common source domain for quadratic moment control through order `L`. -/
def nativePolynomialOrderScale (L : ℕ) : ℝ :=
  max ((L : ℝ) ^ 2) (max (8 * (L : ℝ)) (2 * (L : ℝ) + 6))

theorem nativePolynomialOrderScale_monotone : Monotone nativePolynomialOrderScale := by
  intro k L h
  have hcast : (k : ℝ) ≤ L := by exact_mod_cast h
  exact max_le_max (pow_le_pow_left₀ (Nat.cast_nonneg k) hcast 2)
    (max_le_max (by linarith only [hcast]) (by linarith only [hcast]))

theorem nativePolynomialOrderScale_ge_six (L : ℕ) : 6 ≤ nativePolynomialOrderScale L := by
  have h : 2 * (L : ℝ) + 6 ≤ nativePolynomialOrderScale L :=
    (le_max_right _ _).trans (le_max_right _ _)
  linarith only [h, (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]

/-- One source scale controls every complete native moment in a finite order range. -/
theorem nativeScaledEvenJet_quadratic_relative_error_le_through {L k : ℕ} (hk : k ≤ L)
    {x : ℝ} (hq : nativePolynomialOrderScale L ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet k x - gaussianMoment k| ≤
      (3 * (L : ℝ) ^ 2 + nativePolynomialTailConstant) * gaussianMoment k /
        thetaCuspSingleAtomReflectionScale 1 x := by
  have hd := (nativePolynomialOrderScale_monotone hk).trans hq
  have hquadratic : (k : ℝ) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x :=
    (le_max_left _ _).trans hd
  have hlinear : 8 * (k : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hd
  have htail : ((2 * k : ℕ) : ℝ) + 6 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    have h : 2 * (k : ℝ) + 6 ≤ thetaCuspSingleAtomReflectionScale 1 x :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hd
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  have hq0 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    have h := (nativePolynomialOrderScale_ge_six L).trans hq
    linarith only [h]
  have hcast : (k : ℝ) ≤ L := by exact_mod_cast hk
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg k) hcast 2
  exact (nativeScaledEvenJet_quadratic_relative_error_le k htail hlinear hquadratic).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hsq]) (gaussianMoment_positive k).le) hq0)

#print axioms gaussianMoment_factorial_lower
#print axioms nativeScaledEvenJet_firstAtom_relative_error_le
#print axioms nativeScaledEvenJet_quadratic_relative_error_le
#print axioms nativeScaledEvenJet_quadratic_relative_error_le_through

end GaloisForLFunctions.CompletedArithmeticForms
