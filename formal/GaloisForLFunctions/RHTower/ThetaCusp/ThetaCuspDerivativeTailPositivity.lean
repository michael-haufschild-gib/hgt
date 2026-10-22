import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspDerivativeLeadingSign
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomAllOrderApproximation

/-!
# Tail positivity of fourth-multiple derivatives of the literal theta source

The first atom's derivative polynomial has positive leading sign for every positive
fourth-multiple order. All-order source approximation transfers this sign to the full
theta source on the positive tail; reflection transfers it to the negative tail.
This is the noncompact positivity hinge for theta differential deformations.
-/

open Filter Topology Polynomial
namespace RHTower
noncomputable section

private theorem seed_eval_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < eval (Real.exp x) thetaCuspSeedPolynomial := by
  have hy : 1 ≤ Real.exp x := Real.one_le_exp hx.le
  have hy2 : 1 ≤ (Real.exp x) ^ (2 : ℕ) := one_le_pow₀ hy
  have hq : 3 < 2 * Real.pi * (Real.exp x) ^ (2 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_left hy2
      (by positivity : 0 ≤ 2 * Real.pi)
    nlinarith [Real.pi_gt_three]
  have hp : 0 < 2 * Real.pi * (Real.exp x) ^ (2 : ℕ) := by positivity
  have hid : eval (Real.exp x) thetaCuspSeedPolynomial =
      (2 * Real.pi * (Real.exp x) ^ (2 : ℕ)) *
        (2 * Real.pi * (Real.exp x) ^ (2 : ℕ) - 3) := by
    simp [thetaCuspSeedPolynomial]
    ring
  rw [hid]
  exact mul_pos hp (sub_pos.mpr hq)

private theorem firstAtom_derivative_ratio (r : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv r (fun y : ℝ => thetaCuspSourceTerm y 1) x /
        thetaCuspSourceTerm x 1 =
      eval (Real.exp x) (thetaCuspLogDerivativePolynomial r) /
        eval (Real.exp x) thetaCuspSeedPolynomial := by
  rw [iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom,
    show thetaCuspSourceTerm x 1 = thetaCuspPolynomialAtom thetaCuspSeedPolynomial 1 x from
      congrFun (thetaCuspSourceTerm_eq_polynomialAtom 1) x]
  unfold thetaCuspPolynomialAtom
  simp only [Nat.cast_one, one_mul]
  field_simp [Real.exp_ne_zero, (seed_eval_pos_of_pos hx).ne']

/-- The literal completed theta source has positive derivative of every positive fourth
multiple sufficiently far on either tail. -/
theorem thetaCuspFullSource_four_mul_derivative_eventually_pos
    (m : ℕ) (hm : 0 < m) :
    ∀ᶠ x : ℝ in atTop,
      0 < iteratedDeriv (4*m) thetaCuspFullSource x := by
  let r := 4*m
  let f : ℝ → ℝ := fun x => thetaCuspSourceTerm x 1
  have hratioPoly :=
    thetaCuspLogDerivativePolynomial_four_mul_ratio_tendsto_atTop m hm
  have hratio : Tendsto (fun x : ℝ => iteratedDeriv r f x / f x) atTop atTop := by
    apply hratioPoly.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (firstAtom_derivative_ratio r hx).symm
  have hlarge : ∀ᶠ x : ℝ in atTop, 1 < iteratedDeriv r f x / f x :=
    hratio.eventually_gt_atTop 1
  have herr : Tendsto (fun x : ℝ =>
      (iteratedDeriv r thetaCuspFullSource x - iteratedDeriv r f x) / f x)
      atTop (𝓝 0) := by
    simpa [r, f] using
      thetaCuspFullSource_derivative_relative_error_scaled_tendsto_zero 0 (4*m)
  have hsmall : ∀ᶠ x : ℝ in atTop,
      -1 < (iteratedDeriv r thetaCuspFullSource x - iteratedDeriv r f x) / f x :=
    herr.eventually (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 0))
  filter_upwards [hlarge, hsmall, eventually_gt_atTop (0 : ℝ)] with x hlargeX hsmallX hx
  have hf : 0 < f x := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)
  have hquot : 0 < iteratedDeriv r thetaCuspFullSource x / f x := by
    have heq : iteratedDeriv r thetaCuspFullSource x / f x =
        (iteratedDeriv r thetaCuspFullSource x - iteratedDeriv r f x) / f x +
          iteratedDeriv r f x / f x := by ring
    rw [heq]
    linarith
  exact (div_pos_iff_of_pos_right hf).mp hquot

/-- The sign of a positive fourth-multiple derivative is positive on both distant tails. -/
theorem thetaCuspFullSource_four_mul_derivative_pos_on_tails
    (m : ℕ) (hm : 0 < m) :
    ∃ R : ℝ, ∀ x : ℝ, R ≤ |x| →
      0 < iteratedDeriv (4*m) thetaCuspFullSource x := by
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1
    (thetaCuspFullSource_four_mul_derivative_eventually_pos m hm)
  refine ⟨max R 0, ?_⟩
  intro x hx
  by_cases hpos : 0 ≤ x
  · exact hR x (le_trans (le_max_left R 0) (by simpa [abs_of_nonneg hpos] using hx))
  · have hneg : R ≤ -x :=
      le_trans (le_max_left R 0) (by simpa [abs_of_neg (lt_of_not_ge hpos)] using hx)
    have htail := hR (-x) hneg
    rw [iteratedDeriv_thetaCuspFullSource_neg] at htail
    have hpow : (-1 : ℝ) ^ (4*m) = 1 := by
      rw [show 4*m = 2*(2*m) by omega, pow_mul]
      norm_num
    simpa [hpow] using htail

end
end RHTower
