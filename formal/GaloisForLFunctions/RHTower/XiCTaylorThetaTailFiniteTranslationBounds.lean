import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationCurrent
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailRapidDecay
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedFeedback
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Rapid moments for the finite translation edge

The raw theta tail decays at every prescribed natural exponential rate.  Consequently its
moments, after division by the Taylor factorial, have any fixed geometric rate.  Choosing that
rate above the bounded spectral fibre is the quantitative input for controlling logarithmic
translation edges whose displacement is only logarithmic in the Taylor degree.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Absolute raw-tail moments at an arbitrary natural exponential rate. -/
theorem integral_abs_pow_mul_thetaCuspTailDerivative_zero_le_nat_rate
    (m p : ℕ) (hp : 0 < p) :
    (∫ x : ℝ in Ioi 0,
      |x ^ m * thetaCuspTailDerivative 0 x|) ≤
        thetaCuspTailNatExpConstant p *
          (m.factorial / (p : ℝ) ^ (m + 1)) := by
  let C : ℝ := thetaCuspTailNatExpConstant p
  have hf : IntegrableOn
      (fun x : ℝ => |x ^ m * thetaCuspTailDerivative 0 x|) (Ioi 0) := by
    simpa only [Real.norm_eq_abs] using
      (integrableOn_pow_mul_thetaCuspTailDerivative m 0).norm
  have hbase : IntegrableOn
      (fun x : ℝ => x ^ m * Real.exp (-(p : ℝ) * x)) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_pow_mul_exp_nat_neg m p hp]
    positivity
  have hg : IntegrableOn
      (fun x : ℝ => C * (x ^ m * Real.exp (-(p : ℝ) * x))) (Ioi 0) :=
    hbase.const_mul C
  calc
    (∫ x : ℝ in Ioi 0, |x ^ m * thetaCuspTailDerivative 0 x|) ≤
        ∫ x : ℝ in Ioi 0,
          C * (x ^ m * Real.exp (-(p : ℝ) * x)) := by
      apply MeasureTheory.integral_mono_ae hf hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have htail := abs_thetaCuspTailDerivative_zero_le_nat_exp_neg p hx0
      rw [abs_mul, abs_pow, abs_of_nonneg hx0]
      calc
        x ^ m * |thetaCuspTailDerivative 0 x| ≤
            x ^ m * (C * Real.exp (-(p : ℝ) * x)) :=
          mul_le_mul_of_nonneg_left htail (pow_nonneg hx0 _)
        _ = C * (x ^ m * Real.exp (-(p : ℝ) * x)) := by ring
    _ = thetaCuspTailNatExpConstant p *
          (m.factorial / (p : ℝ) ^ (m + 1)) := by
      rw [integral_const_mul, integral_pow_mul_exp_nat_neg m p hp]

/-- Normalizing by the Taylor factorial leaves a freely prescribed geometric moment rate. -/
theorem integral_abs_pow_mul_thetaCuspTailDerivative_zero_div_factorial_le_nat_rate
    (m p : ℕ) (hp : 0 < p) :
    (∫ x : ℝ in Ioi 0,
      |x ^ m * thetaCuspTailDerivative 0 x|) /
        (m.factorial : ℝ) ≤
      thetaCuspTailNatExpConstant p / (p : ℝ) ^ (m + 1) := by
  have h := integral_abs_pow_mul_thetaCuspTailDerivative_zero_le_nat_rate m p hp
  have hfac : (0 : ℝ) < m.factorial := by positivity
  rw [div_le_iff₀ hfac]
  calc
    (∫ x : ℝ in Ioi 0, |x ^ m * thetaCuspTailDerivative 0 x|) ≤
        thetaCuspTailNatExpConstant p *
          (m.factorial / (p : ℝ) ^ (m + 1)) := h
    _ = (thetaCuspTailNatExpConstant p / (p : ℝ) ^ (m + 1)) *
          (m.factorial : ℝ) := by ring

/-- Every finite cosine section is dominated by the full exponential series, uniformly in its
degree.  This is the degree-free envelope used for the dyadic top row. -/
theorem norm_truncatedCosineSection_le_exp
    (d : ℕ) (z : ℂ) (x : ℝ) :
    ‖truncatedCosineSection d z x‖ ≤ Real.exp (‖z‖ * |x|) := by
  let r : ℝ := ‖z‖ * |x|
  have hr : 0 ≤ r := mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hsum :
      ∑ k ∈ Finset.range (d + 1), r ^ (2 * k) / ((2 * k).factorial : ℝ) ≤
        Real.cosh r := by
    rw [Real.cosh_eq_tsum]
    exact (r.hasSum_cosh.summable).sum_le_tsum (Finset.range (d + 1))
      (fun k _hk => div_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _))
  calc
    ‖truncatedCosineSection d z x‖ ≤
        ∑ k ∈ Finset.range (d + 1),
          r ^ (2 * k) / ((2 * k).factorial : ℝ) := by
      unfold truncatedCosineSection
      calc
        ‖∑ k ∈ Finset.range (d + 1),
            (-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k) / (2 * k).factorial‖ ≤
            ∑ k ∈ Finset.range (d + 1),
              ‖(-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k) /
                (2 * k).factorial‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range (d + 1),
            r ^ (2 * k) / ((2 * k).factorial : ℝ) := by
          apply Finset.sum_le_sum
          intro k _hk
          simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
            Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
          dsimp [r]
          exact le_rfl
    _ ≤ Real.cosh r := hsum
    _ ≤ Real.exp r := by
      rw [Real.cosh_eq]
      have hneg : Real.exp (-r) ≤ Real.exp r := Real.exp_le_exp.mpr (by linarith)
      linarith
    _ = _ := rfl

/-- The odd companion enjoys the same degree-uniform exponential envelope. -/
theorem norm_truncatedSineCompanion_le_exp
    (d : ℕ) (z : ℂ) (x : ℝ) :
    ‖truncatedSineCompanion d z x‖ ≤ Real.exp (‖z‖ * |x|) := by
  let r : ℝ := ‖z‖ * |x|
  have hr : 0 ≤ r := mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hsum :
      ∑ k ∈ Finset.range d, r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) ≤
        Real.sinh r := by
    rw [Real.sinh_eq_tsum]
    exact (r.hasSum_sinh.summable).sum_le_tsum (Finset.range d)
      (fun k _hk => div_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _))
  calc
    ‖truncatedSineCompanion d z x‖ ≤
        ∑ k ∈ Finset.range d,
          r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
      unfold truncatedSineCompanion
      calc
        ‖∑ k ∈ Finset.range d,
            (-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k + 1) /
              (2 * k + 1).factorial‖ ≤
            ∑ k ∈ Finset.range d,
              ‖(-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k + 1) /
                (2 * k + 1).factorial‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range d,
            r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
          apply Finset.sum_le_sum
          intro k _hk
          simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
            Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
          dsimp [r]
          exact le_rfl
    _ ≤ Real.sinh r := hsum
    _ ≤ Real.exp r := by
      rw [Real.sinh_eq]
      have hneg : 0 < Real.exp (-r) := Real.exp_pos _
      linarith [Real.exp_pos r]
    _ = _ := rfl

/-- The spectral derivative of every finite cosine section has a degree-uniform exponential
envelope with the expected single source-coordinate factor. -/
theorem norm_truncatedCosineSectionDerivative_le
    (d : ℕ) (z : ℂ) (x : ℝ) :
    ‖truncatedCosineSectionDerivative d z x‖ ≤
      |x| * Real.exp (‖z‖ * |x|) := by
  let r : ℝ := ‖z‖ * |x|
  have hr : 0 ≤ r := mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hsum :
      ∑ k ∈ Finset.range d,
          r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) ≤ Real.sinh r := by
    rw [Real.sinh_eq_tsum]
    exact (r.hasSum_sinh.summable).sum_le_tsum (Finset.range d)
      (fun k _hk => div_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _))
  calc
    ‖truncatedCosineSectionDerivative d z x‖ ≤
        |x| * ∑ k ∈ Finset.range d,
          r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
      unfold truncatedCosineSectionDerivative
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
      calc
        ‖∑ k ∈ Finset.range d,
            (-1 : ℂ) ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℂ) *
              z ^ (2 * (k + 1) - 1) *
                ((x : ℂ) ^ (2 * (k + 1)) / (2 * (k + 1)).factorial)‖ ≤
            ∑ k ∈ Finset.range d,
              ‖(-1 : ℂ) ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℂ) *
                z ^ (2 * (k + 1) - 1) *
                  ((x : ℂ) ^ (2 * (k + 1)) / (2 * (k + 1)).factorial)‖ :=
          norm_sum_le _ _
        _ = |x| * ∑ k ∈ Finset.range d,
            r ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          rw [show 2 * (k + 1) = 2 * k + 2 by omega,
            show 2 * k + 2 - 1 = 2 * k + 1 by omega]
          simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
            Complex.norm_natCast, norm_div, Complex.norm_real, Real.norm_eq_abs]
          have hfac : (2 * k + 2).factorial =
              (2 * k + 2) * (2 * k + 1).factorial := by
            rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ]
          rw [hfac]
          push_cast
          have hk : (0 : ℝ) < 2 * k + 2 := by positivity
          field_simp
          dsimp [r]
          rw [mul_pow]
          ring
    _ ≤ |x| * Real.sinh r := by gcongr
    _ ≤ |x| * Real.exp r := by
      gcongr
      rw [Real.sinh_eq]
      have hneg : 0 < Real.exp (-r) := Real.exp_pos _
      linarith [Real.exp_pos r]
    _ = _ := rfl

/-- Explicit constant for arbitrary-rate decay of every derivative of the raw theta tail. -/
def thetaCuspTailDerivativeNatExpConstant (m p : ℕ) : ℝ :=
  let P := thetaCuspTailDerivativePolynomial m
  thetaCuspCoeffMass P *
    Real.exp (((p + P.natDegree + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi)) *
      ∑' n : ℕ,
        ((n + 1 : ℕ) : ℝ) ^ P.natDegree *
          Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)

/-- A polynomial Gaussian atom retains arbitrary natural exponential decay; its polynomial factor
is absorbed by the summable discrete Gaussian in the square index. -/
theorem exp_nat_mul_abs_thetaCuspPolynomialAtom_le_of_pos
    (P : ℝ[X]) (p : ℕ) {x : ℝ} (hx : 0 ≤ x) {q : ℕ} (hq : 0 < q) :
    Real.exp ((p : ℝ) * x) * |thetaCuspPolynomialAtom P q x| ≤
      thetaCuspCoeffMass P *
        Real.exp (((p + P.natDegree + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi)) *
          (q : ℝ) ^ P.natDegree *
            Real.exp (-(Real.pi / 2) * (q : ℝ) ^ 2) := by
  let y : ℝ := (q : ℝ) * Real.exp x
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hexp1 : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx
  have hy1 : 1 ≤ y := by
    dsimp [y]
    nlinarith [Real.exp_pos x]
  have heval := abs_eval_le_coeffMass_mul_pow P hy1
  have hbase := exp_nat_mul_abs_thetaCuspTailAtom_le (p + P.natDegree) hx hq
  simp only [thetaCuspPolynomialAtom, eval_one, mul_one, abs_mul,
    abs_of_pos (Real.exp_pos _)] at hbase ⊢
  change Real.exp ((p : ℝ) * x) *
      (Real.exp (x / 2) * |eval y P| * Real.exp (-Real.pi * y ^ 2)) ≤ _
  change Real.exp (((p + P.natDegree + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi)) *
      Real.exp (-(Real.pi / 2) * (q : ℝ) ^ 2) ≥
        Real.exp (((p + P.natDegree : ℕ) : ℝ) * x) *
          (Real.exp (x / 2) * Real.exp (-Real.pi * y ^ 2)) at hbase
  have hyPow : y ^ P.natDegree =
      (q : ℝ) ^ P.natDegree * Real.exp ((P.natDegree : ℝ) * x) := by
    dsimp [y]
    rw [mul_pow, ← Real.exp_nat_mul]
  rw [hyPow] at heval
  calc
    Real.exp ((p : ℝ) * x) *
        (Real.exp (x / 2) * |eval y P| * Real.exp (-Real.pi * y ^ 2)) ≤
      thetaCuspCoeffMass P * (q : ℝ) ^ P.natDegree *
        (Real.exp (((p + P.natDegree : ℕ) : ℝ) * x) *
          (Real.exp (x / 2) * Real.exp (-Real.pi * y ^ 2))) := by
      rw [show (((p + P.natDegree : ℕ) : ℝ)) =
          (p : ℝ) + (P.natDegree : ℝ) by norm_num,
        show ((p : ℝ) + (P.natDegree : ℝ)) * x =
          (p : ℝ) * x + (P.natDegree : ℝ) * x by ring,
        Real.exp_add]
      have hnon : 0 ≤ Real.exp ((p : ℝ) * x) * Real.exp (x / 2) *
          Real.exp (-Real.pi * y ^ 2) := by positivity
      nlinarith
    _ ≤ thetaCuspCoeffMass P * (q : ℝ) ^ P.natDegree *
        (Real.exp (((p + P.natDegree + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi)) *
          Real.exp (-(Real.pi / 2) * (q : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left hbase
      exact mul_nonneg (thetaCuspCoeffMass_nonneg P)
        (pow_nonneg (Nat.cast_nonneg q) _)
    _ = _ := by ring

/-- Every raw-tail derivative decays at every prescribed natural exponential rate.  In
particular this gives degree-uniform domination of `rho = 4 T''` against bounded spectral
exponential envelopes. -/
theorem abs_thetaCuspTailDerivative_le_nat_exp_neg
    (m p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |thetaCuspTailDerivative m x| ≤
      thetaCuspTailDerivativeNatExpConstant m p * Real.exp (-(p : ℝ) * x) := by
  let P : ℝ[X] := thetaCuspTailDerivativePolynomial m
  let a : ℕ → ℝ := fun n => thetaCuspPolynomialAtom P (n + 1) x
  let g : ℕ → ℝ := fun n =>
    ((n + 1 : ℕ) : ℝ) ^ P.natDegree *
      Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)
  let B : ℝ := thetaCuspCoeffMass P *
    Real.exp (((p + P.natDegree + 1 : ℕ) : ℝ) ^ 2 / (2 * Real.pi))
  have ha : Summable a := by
    simpa [a, P, thetaCuspTailDerivative] using summable_thetaCuspTailDerivative m x
  have hg : Summable g := by
    exact (summable_nat_add_iff 1).mpr
      (summable_pow_mul_exp_neg_nat_sq P.natDegree (by positivity : 0 < Real.pi / 2))
  have hag : Summable (fun n => Real.exp ((p : ℝ) * x) * |a n|) :=
    ha.norm.mul_left _
  have hBg : Summable (fun n => B * g n) := hg.mul_left _
  have hterm (n : ℕ) : Real.exp ((p : ℝ) * x) * |a n| ≤ B * g n := by
    dsimp [a, B, g, P]
    simpa only [mul_assoc] using
      exp_nat_mul_abs_thetaCuspPolynomialAtom_le_of_pos
        (thetaCuspTailDerivativePolynomial m) p hx (Nat.succ_pos n)
  have hsum : Real.exp ((p : ℝ) * x) * |∑' n, a n| ≤ B * ∑' n, g n := by
    calc
      Real.exp ((p : ℝ) * x) * |∑' n, a n| ≤
          Real.exp ((p : ℝ) * x) * ∑' n, |a n| := by
        gcongr
        exact norm_tsum_le_tsum_norm ha.norm
      _ = ∑' n, Real.exp ((p : ℝ) * x) * |a n| := by rw [tsum_mul_left]
      _ ≤ ∑' n, B * g n := hag.tsum_le_tsum hterm hBg
      _ = B * ∑' n, g n := by rw [tsum_mul_left]
  rw [thetaCuspTailDerivative]
  change |∑' n, a n| ≤ _
  calc
    |∑' n, a n| = Real.exp (-(p : ℝ) * x) *
        (Real.exp ((p : ℝ) * x) * |∑' n, a n|) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-(p : ℝ) * x) * (B * ∑' n, g n) := by gcongr
    _ = thetaCuspTailDerivativeNatExpConstant m p * Real.exp (-(p : ℝ) * x) := by
      simp [thetaCuspTailDerivativeNatExpConstant, B, P, g]
      ring

/-- Double integration by parts on a positive half-line, with all four endpoint values retained.
This abstract form is used for translated theta potentials: it prevents a seam term from being
silently lost when a reflected Haar packet is moved back to the positive source half-line. -/
theorem integral_Ioi_secondDerivative_mul_eq_boundary_add
    {a : ℝ} {f f' f'' : ℝ → ℂ} {g g' g'' : ℝ → ℂ}
    {A₁ B₁ A₂ B₂ : ℂ}
    (hf : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioi a, HasDerivAt f' (f'' x) x)
    (hg : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioi a, HasDerivAt g' (g'' x) x)
    (hgf'' : IntegrableOn (g * f'') (Ioi a))
    (hg'f' : IntegrableOn (g' * f') (Ioi a))
    (hg''f : IntegrableOn (g'' * f) (Ioi a))
    (hzero₁ : Tendsto (g * f') (𝓝[>] a) (𝓝 A₁))
    (hinfty₁ : Tendsto (g * f') atTop (𝓝 B₁))
    (hzero₂ : Tendsto (g' * f) (𝓝[>] a) (𝓝 A₂))
    (hinfty₂ : Tendsto (g' * f) atTop (𝓝 B₂)) :
    (∫ x : ℝ in Ioi a, f'' x * g x) =
      (B₁ - A₁) - (B₂ - A₂) +
        ∫ x : ℝ in Ioi a, f x * g'' x := by
  have hfirst := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    hg hf' hgf'' hg'f' hzero₁ hinfty₁
  have hsecond := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    hg' hf hg'f' hg''f hzero₂ hinfty₂
  rw [show (∫ x : ℝ in Ioi a, f'' x * g x) =
      ∫ x : ℝ in Ioi a, g x * f'' x by
        apply integral_congr_ae
        filter_upwards [] with x
        ring,
    hfirst, hsecond]
  have hcomm : (∫ x : ℝ in Ioi a, g'' x * f x) =
      ∫ x : ℝ in Ioi a, f x * g'' x := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hcomm]
  ring

end


end RHTower
