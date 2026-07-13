import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedSurvivalRemainder

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

theorem integral_pow_mul_exp_neg_half (k : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ k * Real.exp (-x / 2)) =
      k.factorial * 2 ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := (1 / 2 : ℝ)) (by positivity) (by positivity)
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  rw [show (∫ x : ℝ in Ioi 0, x ^ k * Real.exp (-x / 2)) =
      (∫ x : ℝ in Ioi 0, x ^ k * Real.exp (-((1 / 2 : ℝ) * x))) by
        congr 1
        funext x
        ring]
  rw [h, Real.Gamma_nat_eq_factorial]
  rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  norm_num [div_pow]
  ring

theorem integrableOn_pow_mul_exp_neg_half (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-x / 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (k : ℝ)) (p := (1 : ℝ)) (b := (1 / 2 : ℝ))
    (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    (by norm_num) (by positivity)
  apply h.congr_fun
  intro x hx
  have hx0 : 0 < x := mem_Ioi.mp hx
  change x ^ (k : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ (1 : ℝ)) =
    x ^ k * Real.exp (-x / 2)
  rw [Real.rpow_natCast, Real.rpow_one]
  congr 2
  ring
  exact measurableSet_Ioi

theorem integral_pow_mul_exp_neg_half_complex (k : ℕ) :
    (∫ x : ℝ in Ioi 0,
      ((x ^ k * Real.exp (-x / 2) : ℝ) : ℂ)) =
      ((k.factorial * 2 ^ (k + 1) : ℕ) : ℂ) := by
  calc
    (∫ x : ℝ in Ioi 0,
        ((x ^ k * Real.exp (-x / 2) : ℝ) : ℂ)) =
      (((∫ x : ℝ in Ioi 0, x ^ k * Real.exp (-x / 2)) : ℝ) : ℂ) :=
        integral_ofReal
    _ = _ := by
      rw [integral_pow_mul_exp_neg_half]
      push_cast
      rfl

theorem integral_exp_neg_half_mul_coreAtomSourceDerivative
    (d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
      (Real.exp (-x / 2) : ℂ) *
        thetaCuspTailSecondCoreAtomSourceDerivative d z x) =
      (-4 * z ^ 2) ^ (d + 1) - 1 := by
  unfold thetaCuspTailSecondCoreAtomSourceDerivative
    thetaCuspTailSecondSectionSourceDerivative
  rw [show (fun x : ℝ => (Real.exp (-x / 2) : ℂ) *
      (-(z ^ 2 + 1 / 4) *
        ∑ k ∈ Finset.range (d + 1),
          (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
            ((x : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial))) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (-(z ^ 2 + 1 / 4)) * (-1 : ℂ) ^ k * z ^ (2 * k) *
          ((2 * k + 2 : ℕ) : ℂ) /
            (((2 * k + 2).factorial : ℕ) : ℂ) *
          (((x ^ (2 * k + 1) * Real.exp (-x / 2) : ℝ) : ℂ)) by
    funext x
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    push_cast
    ring]
  rw [MeasureTheory.integral_finsetSum]
  · calc
      (∑ k ∈ Finset.range (d + 1),
        (∫ x : ℝ in Ioi 0,
          (-(z ^ 2 + 1 / 4)) * (-1 : ℂ) ^ k * z ^ (2 * k) *
            ((2 * k + 2 : ℕ) : ℂ) /
              (((2 * k + 2).factorial : ℕ) : ℂ) *
            (((x ^ (2 * k + 1) * Real.exp (-x / 2) : ℝ) : ℂ)))) =
          ∑ k ∈ Finset.range (d + 1),
            -4 * (z ^ 2 + 1 / 4) * (-4 * z ^ 2) ^ k := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [MeasureTheory.integral_const_mul,
          integral_pow_mul_exp_neg_half_complex]
        have hfac : (2 * k + 2).factorial =
            (2 * k + 2) * (2 * k + 1).factorial := by
          rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ]
        rw [hfac]
        push_cast
        have hne : (((2 * k + 1).factorial : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero (2 * k + 1)
        have heven : ((2 * k + 2 : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast (by omega : 2 * k + 2 ≠ 0)
        field_simp [hne, heven]
        have hfour : (-4 : ℂ) ^ k =
            (-1 : ℂ) ^ k * 2 ^ (2 * k) := by
          rw [show (-4 : ℂ) = (-1) * 4 by ring, mul_pow]
          rw [show (4 : ℂ) = 2 ^ 2 by norm_num, ← pow_mul]
        rw [show (-(z ^ 2 * 4)) ^ k = z ^ (2 * k) * (-4 : ℂ) ^ k by
          rw [show -(z ^ 2 * 4) = z ^ 2 * (-4 : ℂ) by ring, mul_pow, ← pow_mul],
          hfour]
        ring
      _ = (-4 * z ^ 2) ^ (d + 1) - 1 := by
        calc
          (∑ k ∈ Finset.range (d + 1),
              -4 * (z ^ 2 + 1 / 4) * (-4 * z ^ 2) ^ k) =
            ((-4 * z ^ 2) - 1) *
              ∑ k ∈ Finset.range (d + 1), (-4 * z ^ 2) ^ k := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _hk
                ring
          _ = (-4 * z ^ 2) ^ (d + 1) - 1 :=
            mul_geom_sum (-4 * z ^ 2) (d + 1)
  · intro k _hk
    exact (integrableOn_pow_mul_exp_neg_half (2 * k + 1)).ofReal.const_mul _

theorem integrableOn_exp_neg_half_mul_coreAtomSourceDerivative
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (Real.exp (-x / 2) : ℂ) *
        thetaCuspTailSecondCoreAtomSourceDerivative d z x) (Ioi 0) := by
  unfold thetaCuspTailSecondCoreAtomSourceDerivative
    thetaCuspTailSecondSectionSourceDerivative
  rw [show (fun x : ℝ => (Real.exp (-x / 2) : ℂ) *
      (-(z ^ 2 + 1 / 4) *
        ∑ k ∈ Finset.range (d + 1),
          (-1 : ℂ) ^ k * z ^ (2 * k) * ((2 * k + 2 : ℕ) : ℂ) *
            ((x : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial))) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (-(z ^ 2 + 1 / 4)) * (-1 : ℂ) ^ k * z ^ (2 * k) *
          ((2 * k + 2 : ℕ) : ℂ) /
            (((2 * k + 2).factorial : ℕ) : ℂ) *
          (((x ^ (2 * k + 1) * Real.exp (-x / 2) : ℝ) : ℂ)) by
    funext x
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    push_cast
    ring]
  exact MeasureTheory.integrable_finsetSum _ fun k _hk =>
    (integrableOn_pow_mul_exp_neg_half (2 * k + 1)).ofReal.const_mul _

theorem integral_density_mul_coreAtom_eq_pow_sub_completedSurvival
    (d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspTailSecondDensity x : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) =
      (-4 * z ^ 2) ^ (d + 1) -
        ∫ x : ℝ in Ioi 0,
          (thetaCuspCompletedSurvivalRemainder x : ℂ) *
            thetaCuspTailSecondCoreAtomSourceDerivative d z x := by
  rw [integral_density_mul_coreAtom_eq_one_add_survival_sourceDerivative]
  unfold thetaCuspCompletedSurvivalRemainder
  rw [show (fun x : ℝ =>
      ((Real.exp (-x / 2) - thetaCuspTailSurvival x : ℝ) : ℂ) *
        thetaCuspTailSecondCoreAtomSourceDerivative d z x) =
      fun x : ℝ =>
        (Real.exp (-x / 2) : ℂ) *
            thetaCuspTailSecondCoreAtomSourceDerivative d z x -
          (thetaCuspTailSurvival x : ℂ) *
            thetaCuspTailSecondCoreAtomSourceDerivative d z x by
    funext x
    push_cast
    ring]
  rw [integral_sub]
  · rw [integral_exp_neg_half_mul_coreAtomSourceDerivative]
    ring
  · exact integrableOn_exp_neg_half_mul_coreAtomSourceDerivative d z
  · exact integrableOn_thetaCuspTailSurvival_mul_coreAtomSourceDerivative d z

end

end RHTower

