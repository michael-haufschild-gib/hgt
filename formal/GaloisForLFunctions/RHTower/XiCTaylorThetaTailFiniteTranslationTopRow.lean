import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSquareIndexPolarization

/-!
# Degree-uniform dyadic top-row bounds

The finite theta-tail core and its spectral derivative have envelopes independent of the Taylor
cutoff. Combining those envelopes with arbitrary-rate decay of the exact translated density gives
an explicit integrated Haar top-row estimate uniform in the cutoff. This is the quantitative form
needed when the Haar depth and Taylor degree vary on the same anisotropic schedule.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

theorem norm_thetaCuspTailSecondSection_le
    (d : ℕ) (z : ℂ) (x : ℝ) :
    ‖thetaCuspTailSecondSection d z x‖ ≤
      |x| ^ 2 * Real.exp (‖z‖ * |x|) := by
  let r : ℝ := ‖z‖ * |x|
  have hr : 0 ≤ r := mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hsum :
      ∑ k ∈ Finset.range (d + 1),
          r ^ (2 * k) / ((2 * k).factorial : ℝ) ≤ Real.cosh r := by
    rw [Real.cosh_eq_tsum]
    exact (r.hasSum_cosh.summable).sum_le_tsum (Finset.range (d + 1))
      (fun k _hk => div_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _))
  calc
    ‖thetaCuspTailSecondSection d z x‖ ≤
        |x| ^ 2 * ∑ k ∈ Finset.range (d + 1),
          r ^ (2 * k) / ((2 * k).factorial : ℝ) := by
      unfold thetaCuspTailSecondSection
      calc
        ‖∑ k ∈ Finset.range (d + 1),
            (-1 : ℂ) ^ k * z ^ (2 * k) *
              ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)‖ ≤
            ∑ k ∈ Finset.range (d + 1),
              ‖(-1 : ℂ) ^ k * z ^ (2 * k) *
                ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range (d + 1),
            |x| ^ 2 * (r ^ (2 * k) / ((2 * k).factorial : ℝ)) := by
          apply Finset.sum_le_sum
          intro k _hk
          simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
            one_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
          have hfac : ((2 * k).factorial : ℝ) ≤ ((2 * k + 2).factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le (by omega : 2 * k ≤ 2 * k + 2)
          have hfac0 : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
          rw [show |x| ^ (2 * k + 2) = |x| ^ 2 * |x| ^ (2 * k) by
            rw [show 2 * k + 2 = 2 + 2 * k by omega, pow_add]]
          dsimp [r]
          rw [mul_pow]
          let A : ℝ := |x| ^ 2 * (‖z‖ ^ (2 * k) * |x| ^ (2 * k))
          have hdiv : A / ((2 * k + 2).factorial : ℝ) ≤
              A / ((2 * k).factorial : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hfac0 hfac
          calc
            _ = A / ((2 * k + 2).factorial : ℝ) := by
              dsimp [A]
              ring
            _ ≤ A / ((2 * k).factorial : ℝ) := hdiv
            _ = _ := by
              dsimp [A]
              ring
        _ = |x| ^ 2 * ∑ k ∈ Finset.range (d + 1),
            r ^ (2 * k) / ((2 * k).factorial : ℝ) := by rw [Finset.mul_sum]
    _ ≤ |x| ^ 2 * Real.cosh r := by gcongr
    _ ≤ |x| ^ 2 * Real.exp r := by
      gcongr
      rw [Real.cosh_eq]
      have hneg : Real.exp (-r) ≤ Real.exp r := Real.exp_le_exp.mpr (by linarith)
      linarith
    _ = _ := by rfl

theorem norm_thetaCuspTailSecondSectionDerivative_le
    (d : ℕ) (z : ℂ) (x : ℝ) :
    ‖thetaCuspTailSecondSectionDerivative d z x‖ ≤
      |x| ^ 3 * Real.exp (‖z‖ * |x|) := by
  let r : ℝ := ‖z‖ * |x|
  have hr : 0 ≤ r := mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hsum :
      ∑ k ∈ Finset.range d,
          r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) ≤ Real.sinh r := by
    rw [Real.sinh_eq_tsum]
    exact (r.hasSum_sinh.summable).sum_le_tsum (Finset.range d)
      (fun k _hk => div_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _))
  calc
    ‖thetaCuspTailSecondSectionDerivative d z x‖ ≤
        |x| ^ 3 * ∑ k ∈ Finset.range d,
          r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
      unfold thetaCuspTailSecondSectionDerivative
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
      calc
        ‖∑ k ∈ Finset.range d,
            (-1 : ℂ) ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℂ) *
              z ^ (2 * (k + 1) - 1) *
                ((x : ℂ) ^ (2 * (k + 1) + 2) /
                  (2 * (k + 1) + 2).factorial)‖ ≤
            ∑ k ∈ Finset.range d,
              ‖(-1 : ℂ) ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℂ) *
                z ^ (2 * (k + 1) - 1) *
                  ((x : ℂ) ^ (2 * (k + 1) + 2) /
                    (2 * (k + 1) + 2).factorial)‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range d,
            |x| ^ 3 *
              (r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) := by
          apply Finset.sum_le_sum
          intro k _hk
          rw [show 2 * (k + 1) = 2 * k + 2 by omega]
          rw [show 2 * k + 2 - 1 = 2 * k + 1 by omega,
            show 2 * k + 2 + 2 = 2 * k + 4 by omega]
          simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
            one_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
          rw [show |x| ^ (2 * k + 4) = |x| ^ 3 * |x| ^ (2 * k + 1) by
            rw [show 2 * k + 4 = 3 + (2 * k + 1) by omega, pow_add]]
          dsimp [r]
          rw [mul_pow]
          have hfacEq : (2 * k + 2) * (2 * k + 1).factorial =
              (2 * k + 2).factorial := by
            convert (Nat.factorial_succ (2 * k + 1)).symm using 1
          have hfac : ((2 * k + 2) * (2 * k + 1).factorial : ℕ) ≤
              (2 * k + 4).factorial := by
            rw [hfacEq]
            exact Nat.factorial_le (by omega)
          have hfacR : ((2 * k + 2 : ℕ) : ℝ) *
              ((2 * k + 1).factorial : ℝ) ≤
                ((2 * k + 4).factorial : ℝ) := by exact_mod_cast hfac
          have hden : (0 : ℝ) < ((2 * k + 4).factorial : ℝ) := by positivity
          have hsmall : (0 : ℝ) < ((2 * k + 1).factorial : ℝ) := by positivity
          let A : ℝ := |x| ^ 3 *
            (‖z‖ ^ (2 * k + 1) * |x| ^ (2 * k + 1))
          have hA : 0 ≤ A := by positivity
          have hleft :
              ((2 * k + 2 : ℕ) : ℝ) * ‖z‖ ^ (2 * k + 1) *
                  (|x| ^ 3 * |x| ^ (2 * k + 1) /
                    ((2 * k + 4).factorial : ℝ)) =
                ((2 * k + 2 : ℕ) : ℝ) * A /
                  ((2 * k + 4).factorial : ℝ) := by
            dsimp [A]
            ring
          have hright :
              |x| ^ 3 *
                  (‖z‖ ^ (2 * k + 1) * |x| ^ (2 * k + 1) /
                    ((2 * k + 1).factorial : ℝ)) =
                A / ((2 * k + 1).factorial : ℝ) := by
            dsimp [A]
            ring
          rw [hleft, hright]
          rw [div_le_iff₀ hden, div_mul_eq_mul_div, le_div_iff₀ hsmall]
          nlinarith [mul_le_mul_of_nonneg_left hfacR hA]
        _ = |x| ^ 3 * ∑ k ∈ Finset.range d,
            r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
          rw [Finset.mul_sum]
    _ ≤ |x| ^ 3 * Real.sinh r := by gcongr
    _ ≤ |x| ^ 3 * Real.exp r := by
      gcongr
      rw [Real.sinh_eq]
      have hneg : 0 < Real.exp (-r) := Real.exp_pos _
      linarith [Real.exp_pos r]
    _ = _ := by rfl

theorem norm_thetaCuspTailSecondCoreAtom_le
    (d : ℕ) (z : ℂ) (x : ℝ) :
    ‖thetaCuspTailSecondCoreAtom d z x‖ ≤
      1 + ‖z ^ 2 + 1 / 4‖ * |x| ^ 2 * Real.exp (‖z‖ * |x|) := by
  unfold thetaCuspTailSecondCoreAtom
  calc
    ‖1 - (z ^ 2 + 1 / 4) * thetaCuspTailSecondSection d z x‖ ≤
        ‖(1 : ℂ)‖ + ‖(z ^ 2 + 1 / 4) * thetaCuspTailSecondSection d z x‖ :=
      norm_sub_le (1 : ℂ)
        ((z ^ 2 + 1 / 4) * thetaCuspTailSecondSection d z x)
    _ = 1 + ‖z ^ 2 + 1 / 4‖ * ‖thetaCuspTailSecondSection d z x‖ := by
      simp
    _ ≤ 1 + ‖z ^ 2 + 1 / 4‖ *
        (|x| ^ 2 * Real.exp (‖z‖ * |x|)) := by
      gcongr
      exact norm_thetaCuspTailSecondSection_le d z x
    _ = _ := by ring

theorem norm_thetaCuspTailSecondCoreAtomDerivative_le
    (d : ℕ) (z : ℂ) (x : ℝ) :
    ‖thetaCuspTailSecondCoreAtomDerivative d z x‖ ≤
      (2 * ‖z‖ * |x| ^ 2 + ‖z ^ 2 + 1 / 4‖ * |x| ^ 3) *
        Real.exp (‖z‖ * |x|) := by
  unfold thetaCuspTailSecondCoreAtomDerivative
  calc
    ‖-2 * z * thetaCuspTailSecondSection d z x -
        (z ^ 2 + 1 / 4) * thetaCuspTailSecondSectionDerivative d z x‖ ≤
      2 * ‖z‖ * ‖thetaCuspTailSecondSection d z x‖ +
        ‖z ^ 2 + 1 / 4‖ * ‖thetaCuspTailSecondSectionDerivative d z x‖ := by
      calc
        _ ≤ ‖-2 * z * thetaCuspTailSecondSection d z x‖ +
            ‖(z ^ 2 + 1 / 4) *
              thetaCuspTailSecondSectionDerivative d z x‖ := norm_sub_le _ _
        _ = _ := by simp
    _ ≤ 2 * ‖z‖ * (|x| ^ 2 * Real.exp (‖z‖ * |x|)) +
        ‖z ^ 2 + 1 / 4‖ *
          (|x| ^ 3 * Real.exp (‖z‖ * |x|)) := by
      gcongr
      · exact norm_thetaCuspTailSecondSection_le d z x
      · exact norm_thetaCuspTailSecondSectionDerivative_le d z x
    _ = _ := by ring

theorem dyadic_weight_le_one (k : ℕ) :
    ((((2 ^ k : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2) :
      (1 : ℕ) ≤ 2 ^ k)
  · norm_num

theorem abs_thetaSquareIndexDyadicDensity_le
    (p k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |thetaSquareIndexDyadicDensity k x| ≤
      4 * thetaCuspTailDerivativeNatExpConstant 2 p *
        Real.exp (-(p : ℝ) * (x + (k : ℝ) * Real.log 2)) := by
  rw [thetaSquareIndexDyadicDensity_eq_scaledDensity]
  rw [abs_mul]
  have hw0 : 0 ≤ ((((2 ^ k : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) :=
    Real.rpow_nonneg (by positivity) _
  rw [abs_of_nonneg hw0]
  have hshift0 : 0 ≤ x + (k : ℝ) * Real.log 2 := by positivity
  have htail := abs_thetaCuspTailDerivative_le_nat_exp_neg 2 p hshift0
  unfold thetaCuspTailSecondDensity
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    ((((2 ^ k : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
        (4 * |thetaCuspTailDerivative 2 (x + (k : ℝ) * Real.log 2)|) ≤
      1 * (4 * (thetaCuspTailDerivativeNatExpConstant 2 p *
        Real.exp (-(p : ℝ) * (x + (k : ℝ) * Real.log 2)))) := by
          gcongr
          exact dyadic_weight_le_one k
    _ = _ := by ring

theorem norm_thetaCuspTailSecondCoreAtom_le_exp
    (d : ℕ) (z : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖thetaCuspTailSecondCoreAtom d z x‖ ≤
      (1 + ‖z ^ 2 + 1 / 4‖ * x ^ 2) * Real.exp (‖z‖ * x) := by
  have hexp : 1 ≤ Real.exp (‖z‖ * x) := by
    simpa using Real.exp_le_exp.mpr (mul_nonneg (norm_nonneg z) hx)
  have h := norm_thetaCuspTailSecondCoreAtom_le d z x
  rw [abs_of_nonneg hx] at h
  calc
    ‖thetaCuspTailSecondCoreAtom d z x‖ ≤
        1 + ‖z ^ 2 + 1 / 4‖ * x ^ 2 * Real.exp (‖z‖ * x) := h
    _ ≤ Real.exp (‖z‖ * x) +
        ‖z ^ 2 + 1 / 4‖ * x ^ 2 * Real.exp (‖z‖ * x) := by gcongr
    _ = _ := by ring

theorem exp_shift_mul_spectral_le
    (r k : ℕ) {z : ℂ} (hz : ‖z‖ ≤ r) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-((r + 2 : ℕ) : ℝ) *
          (x + (k : ℝ) * Real.log 2)) * Real.exp (‖z‖ * x) ≤
      Real.exp (-((r + 2 : ℕ) : ℝ) * ((k : ℝ) * Real.log 2)) *
        Real.exp (-2 * x) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  have hz' : ‖z‖ ≤ (r : ℝ) := by exact_mod_cast hz
  nlinarith

private theorem integrableOn_pow_mul_exp_two_neg (m : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ m * Real.exp (-2 * x)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  have hi := integral_pow_mul_exp_nat_neg m 2 (by omega)
  rw [show (∫ x : ℝ in Ioi 0, x ^ m * Real.exp (-2 * x)) =
      (m.factorial : ℝ) / (2 : ℝ) ^ (m + 1) by
        simpa using! hi]
  positivity

theorem norm_thetaSquareIndexDyadicCoreAtomAverage_le
    (d r k : ℕ) (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖thetaSquareIndexDyadicCoreAtomAverage d z k‖ ≤
      (4 * thetaCuspTailDerivativeNatExpConstant 2 (r + 2)) *
        Real.exp (-((r + 2 : ℕ) : ℝ) * ((k : ℝ) * Real.log 2)) *
          (1 / 2 + ‖z ^ 2 + 1 / 4‖ / 4) := by
  let A : ℝ := 4 * thetaCuspTailDerivativeNatExpConstant 2 (r + 2)
  let q : ℝ := ‖z ^ 2 + 1 / 4‖
  let shift : ℝ := Real.exp (-((r + 2 : ℕ) : ℝ) *
    ((k : ℝ) * Real.log 2))
  let g : ℝ → ℝ := fun x => A * shift *
    ((1 + q * x ^ 2) * Real.exp (-2 * x))
  have hC : 0 ≤ thetaCuspTailDerivativeNatExpConstant 2 (r + 2) := by
    unfold thetaCuspTailDerivativeNatExpConstant
    exact mul_nonneg
      (mul_nonneg (thetaCuspCoeffMass_nonneg _) (Real.exp_pos _).le)
      (tsum_nonneg fun _ => mul_nonneg (pow_nonneg (by positivity) _)
        (Real.exp_pos _).le)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h0 := integrableOn_pow_mul_exp_two_neg 0
  have h2 := integrableOn_pow_mul_exp_two_neg 2
  have hg : IntegrableOn g (Ioi 0) := by
    have hadd : IntegrableOn (fun x : ℝ =>
        Real.exp (-2 * x) + q * (x ^ 2 * Real.exp (-2 * x))) (Ioi 0) := by
      have h0' : IntegrableOn (fun x : ℝ => Real.exp (-2 * x)) (Ioi 0) := by
        simpa using h0
      exact h0'.add (h2.const_mul q)
    apply (hadd.const_mul (A * shift)).congr
    filter_upwards [] with x
    dsimp [g]
    ring
  unfold thetaSquareIndexDyadicCoreAtomAverage
  calc
    ‖∫ x : ℝ in Ioi 0,
        (thetaSquareIndexDyadicDensity k x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x‖ ≤
        ∫ x : ℝ in Ioi 0, g x := by
      apply MeasureTheory.norm_integral_le_of_norm_le hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have hdens := abs_thetaSquareIndexDyadicDensity_le (r + 2) k hx0
      have hcore := norm_thetaCuspTailSecondCoreAtom_le_exp d z hx0
      have hexp := exp_shift_mul_spectral_le r k hz hx0
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        |thetaSquareIndexDyadicDensity k x| *
            ‖thetaCuspTailSecondCoreAtom d z x‖ ≤
          A * Real.exp (-((r + 2 : ℕ) : ℝ) *
              (x + (k : ℝ) * Real.log 2)) *
            ((1 + q * x ^ 2) * Real.exp (‖z‖ * x)) := by
          dsimp [A, q]
          gcongr
        _ = A * (1 + q * x ^ 2) *
            (Real.exp (-((r + 2 : ℕ) : ℝ) *
                (x + (k : ℝ) * Real.log 2)) * Real.exp (‖z‖ * x)) := by ring
        _ ≤ A * (1 + q * x ^ 2) *
            (shift * Real.exp (-2 * x)) := by
          gcongr
        _ = g x := by dsimp [g]; ring
    _ = A * shift * (1 / 2 + q / 4) := by
      have hi0 : (∫ x : ℝ in Ioi 0, Real.exp (-2 * x)) = (1 / 2 : ℝ) := by
        simpa using integral_pow_mul_exp_nat_neg 0 2 (by omega)
      have hi2 : (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-2 * x)) =
          (1 / 4 : ℝ) := by
        have hi := integral_pow_mul_exp_nat_neg 2 2 (by omega)
        convert hi using 1 <;> norm_num
      rw [show g = fun x : ℝ => A * shift *
          (Real.exp (-2 * x) + q * (x ^ 2 * Real.exp (-2 * x))) by
        funext x
        dsimp [g]
        ring]
      rw [integral_const_mul, integral_add, integral_const_mul, hi0, hi2]
      · ring
      · simpa using! h0
      · exact h2.const_mul q
    _ = _ := by rfl

theorem norm_thetaSquareIndexDyadicCoreAtomDerivativeAverage_le
    (d r k : ℕ) (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖thetaSquareIndexDyadicCoreAtomDerivativeAverage d z k‖ ≤
      (4 * thetaCuspTailDerivativeNatExpConstant 2 (r + 2)) *
        Real.exp (-((r + 2 : ℕ) : ℝ) * ((k : ℝ) * Real.log 2)) *
          (‖z‖ / 2 + 3 * ‖z ^ 2 + 1 / 4‖ / 8) := by
  let A : ℝ := 4 * thetaCuspTailDerivativeNatExpConstant 2 (r + 2)
  let q : ℝ := ‖z ^ 2 + 1 / 4‖
  let shift : ℝ := Real.exp (-((r + 2 : ℕ) : ℝ) *
    ((k : ℝ) * Real.log 2))
  let g : ℝ → ℝ := fun x => A * shift *
    ((2 * ‖z‖ * x ^ 2 + q * x ^ 3) * Real.exp (-2 * x))
  have hC : 0 ≤ thetaCuspTailDerivativeNatExpConstant 2 (r + 2) := by
    unfold thetaCuspTailDerivativeNatExpConstant
    exact mul_nonneg
      (mul_nonneg (thetaCuspCoeffMass_nonneg _) (Real.exp_pos _).le)
      (tsum_nonneg fun _ => mul_nonneg (pow_nonneg (by positivity) _)
        (Real.exp_pos _).le)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h2 := integrableOn_pow_mul_exp_two_neg 2
  have h3 := integrableOn_pow_mul_exp_two_neg 3
  have hg : IntegrableOn g (Ioi 0) := by
    have hadd : IntegrableOn (fun x : ℝ =>
        2 * ‖z‖ * (x ^ 2 * Real.exp (-2 * x)) +
          q * (x ^ 3 * Real.exp (-2 * x))) (Ioi 0) :=
      (h2.const_mul (2 * ‖z‖)).add (h3.const_mul q)
    apply (hadd.const_mul (A * shift)).congr
    filter_upwards [] with x
    dsimp [g]
    ring
  unfold thetaSquareIndexDyadicCoreAtomDerivativeAverage
  calc
    ‖∫ x : ℝ in Ioi 0,
        (thetaSquareIndexDyadicDensity k x : ℂ) *
          thetaCuspTailSecondCoreAtomDerivative d z x‖ ≤
        ∫ x : ℝ in Ioi 0, g x := by
      apply MeasureTheory.norm_integral_le_of_norm_le hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have hdens := abs_thetaSquareIndexDyadicDensity_le (r + 2) k hx0
      have hcore := norm_thetaCuspTailSecondCoreAtomDerivative_le d z x
      rw [abs_of_nonneg hx0] at hcore
      have hexp := exp_shift_mul_spectral_le r k hz hx0
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        |thetaSquareIndexDyadicDensity k x| *
            ‖thetaCuspTailSecondCoreAtomDerivative d z x‖ ≤
          A * Real.exp (-((r + 2 : ℕ) : ℝ) *
              (x + (k : ℝ) * Real.log 2)) *
            ((2 * ‖z‖ * x ^ 2 + q * x ^ 3) * Real.exp (‖z‖ * x)) := by
          dsimp [A, q]
          gcongr
        _ = A * (2 * ‖z‖ * x ^ 2 + q * x ^ 3) *
            (Real.exp (-((r + 2 : ℕ) : ℝ) *
                (x + (k : ℝ) * Real.log 2)) * Real.exp (‖z‖ * x)) := by ring
        _ ≤ A * (2 * ‖z‖ * x ^ 2 + q * x ^ 3) *
            (shift * Real.exp (-2 * x)) := by gcongr
        _ = g x := by dsimp [g]; ring
    _ = A * shift * (‖z‖ / 2 + 3 * q / 8) := by
      have hi2 : (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-2 * x)) =
          (1 / 4 : ℝ) := by
        have hi := integral_pow_mul_exp_nat_neg 2 2 (by omega)
        convert hi using 1 <;> norm_num
      have hi3 : (∫ x : ℝ in Ioi 0, x ^ 3 * Real.exp (-2 * x)) =
          (3 / 8 : ℝ) := by
        have hi := integral_pow_mul_exp_nat_neg 3 2 (by omega)
        convert hi using 1 <;> norm_num
      rw [show g = fun x : ℝ => A * shift *
          (2 * ‖z‖ * (x ^ 2 * Real.exp (-2 * x)) +
            q * (x ^ 3 * Real.exp (-2 * x))) by
        funext x
        dsimp [g]
        ring]
      rw [integral_const_mul, integral_add, integral_const_mul,
        integral_const_mul, hi2, hi3]
      · ring
      · exact h2.const_mul (2 * ‖z‖)
      · exact h3.const_mul q
    _ = _ := by rfl

/-- Degree-uniform integrated top-row estimate. -/
theorem abs_integral_xiCTaylorThetaTailCoreDyadicHaarRemainderKernel_le
    (d r k : ℕ) (z : ℂ) (hz : ‖z‖ ≤ r) :
    |∫ p : ℝ × ℝ,
        xiCTaylorThetaTailCoreDyadicHaarRemainderKernel d z k p
          ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))| ≤
      (2 : ℝ) ^ k *
        ((4 * thetaCuspTailDerivativeNatExpConstant 2 (r + 2)) *
          Real.exp (-((r + 2 : ℕ) : ℝ) * ((k : ℝ) * Real.log 2)) *
            (‖z‖ / 2 + 3 * ‖z ^ 2 + 1 / 4‖ / 8)) *
        ((4 * thetaCuspTailDerivativeNatExpConstant 2 (r + 2)) *
          Real.exp (-((r + 2 : ℕ) : ℝ) * ((k : ℝ) * Real.log 2)) *
            (1 / 2 + ‖z ^ 2 + 1 / 4‖ / 4)) := by
  rw [integral_xiCTaylorThetaTailCoreDyadicHaarRemainderKernel_eq]
  calc
    |((2 : ℂ) ^ k * thetaSquareIndexDyadicCoreAtomDerivativeAverage d z k *
        (starRingEnd ℂ) (thetaSquareIndexDyadicCoreAtomAverage d z k)).im| ≤
      ‖(2 : ℂ) ^ k * thetaSquareIndexDyadicCoreAtomDerivativeAverage d z k *
        (starRingEnd ℂ) (thetaSquareIndexDyadicCoreAtomAverage d z k)‖ :=
      Complex.abs_im_le_norm _
    _ = (2 : ℝ) ^ k * ‖thetaSquareIndexDyadicCoreAtomDerivativeAverage d z k‖ *
        ‖thetaSquareIndexDyadicCoreAtomAverage d z k‖ := by simp
    _ ≤ _ := by
      have hD :=
        norm_thetaSquareIndexDyadicCoreAtomDerivativeAverage_le d r k z hz
      have hV := norm_thetaSquareIndexDyadicCoreAtomAverage_le d r k z hz
      have hpow : 0 ≤ (2 : ℝ) ^ k := by positivity
      have hDmax : 0 ≤
          (4 * thetaCuspTailDerivativeNatExpConstant 2 (r + 2)) *
            Real.exp (-((r + 2 : ℕ) : ℝ) * ((k : ℝ) * Real.log 2)) *
              (‖z‖ / 2 + 3 * ‖z ^ 2 + 1 / 4‖ / 8) :=
        (norm_nonneg _).trans hD
      exact mul_le_mul (mul_le_mul_of_nonneg_left hD hpow) hV
        (norm_nonneg _) (mul_nonneg hpow hDmax)

end

end RHTower
