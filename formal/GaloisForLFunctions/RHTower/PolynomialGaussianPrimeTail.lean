import GaloisForLFunctions.RHTower.PolynomialGaussianFourierAperture
import GaloisForLFunctions.HTGeometry.RealDirichletSeries

/-!
# Route-U polynomial--Gaussian prime tail

This file closes C43-Y (24.138) with an exact arithmetic constant.  Under the universal
parabolic wedge

`t * (natDegree Q + 1) <= (log 2)^2 / 256`,

the coefficient-uniform Fourier aperture first loses half its Gaussian exponent.  Splitting the
remaining exponent once more produces both the first-frequency factor
`exp (-(log 2)^2 / (16t))` and a full `n^-2` at every arithmetic frequency `log n`.  The complete
prime tail is therefore controlled by the fixed, absolutely convergent right-half-plane mass

`sum_n vonMangoldt(n) n^-2`.

This avoids integer shell counting and proves summability of the literal absolute prime series.
No PNT, zero-free region, RH premise, coefficient bound, nonzero-polynomial premise, or numerical
computation enters.
-/

open scoped Real
open Real MeasureTheory ArithmeticFunction

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Universal degree--heat wedge in which the first prime frequency lies outside the translated
oscillator disk. Positivity and the closed endpoint inequality are encoded in the type. -/
def routeUPrimeGaussianWedge (Q : Polynomial ℝ) :=
  {t : ℝ // 0 < t ∧ t * (Q.natDegree + 1) ≤ Real.log 2 ^ 2 / 256}

/-- Forget the wedge bound while retaining positive heat time. -/
def routeUPrimeGaussianWedge.heat
    {Q : Polynomial ℝ} (t : routeUPrimeGaussianWedge Q) : {τ : ℝ // 0 < τ} :=
  ⟨t.1, t.property.1⟩

private theorem routeUPrimeGaussianWedge_sqrt_scale_le_log_two
    (Q : Polynomial ℝ) (t : routeUPrimeGaussianWedge Q) :
    16 * Real.sqrt Q.natDegree * Real.sqrt t.1 ≤ Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  apply (sq_le_sq₀ (by positivity) hlog.le).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg Q.natDegree),
    Real.sq_sqrt t.property.1.le]
  have hd : (Q.natDegree : ℝ) ≤ Q.natDegree + 1 :=
    le_add_of_nonneg_right zero_le_one
  calc
    16 ^ 2 * (Q.natDegree : ℝ) * t.1 ≤
        256 * (t.1 * (Q.natDegree + 1)) := by
      rw [show (16 : ℝ) ^ 2 = 256 by ring]
      have h := mul_le_mul_of_nonneg_left hd t.property.1.le
      nlinarith only [h]
    _ ≤ 256 * (Real.log 2 ^ 2 / 256) := by
      gcongr
      exact t.property.2
    _ = Real.log 2 ^ 2 := by ring

private theorem routeUPrimeGaussianWedge_translation_le
    (Q : Polynomial ℝ) (t : routeUPrimeGaussianWedge Q) {xi : ℝ}
    (hxi : Real.log 2 ≤ xi) :
    2 * Real.sqrt Q.natDegree * |xi| / Real.sqrt t.1 ≤
      xi ^ 2 / (8 * t.1) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hxi0 : 0 < xi := lt_of_lt_of_le hlog hxi
  have hs : 0 < Real.sqrt t.1 := Real.sqrt_pos.2 t.property.1
  have hs2 : Real.sqrt t.1 ^ 2 = t.1 := Real.sq_sqrt t.property.1.le
  have hscale : 16 * Real.sqrt Q.natDegree * Real.sqrt t.1 ≤ xi :=
    le_trans (routeUPrimeGaussianWedge_sqrt_scale_le_log_two Q t) hxi
  have hprod :
      16 * Real.sqrt Q.natDegree * Real.sqrt t.1 * xi ≤ xi ^ 2 := by
    nlinarith only [hscale, hxi0]
  rw [abs_of_pos hxi0]
  calc
    2 * Real.sqrt Q.natDegree * xi / Real.sqrt t.1 =
        (2 * Real.sqrt Q.natDegree * xi * Real.sqrt t.1) /
          (Real.sqrt t.1 ^ 2) := by
      field_simp [hs.ne']
    _ = (16 * Real.sqrt Q.natDegree * Real.sqrt t.1 * xi) /
          (8 * t.1) := by
      rw [hs2]
      ring
    _ ≤ xi ^ 2 / (8 * t.1) := by
      exact div_le_div_of_nonneg_right hprod
        (mul_nonneg (by positivity) t.property.1.le)

/-- In the parabolic wedge, every frequency beyond `log 2` receives a pure Gaussian Fourier
bound with half of the original exponent. -/
theorem norm_routeUPolynomialGaussianFourier_le_wedge
    (Q : Polynomial ℝ) (t : routeUPrimeGaussianWedge Q) {xi : ℝ}
    (hxi : Real.log 2 ≤ xi) :
    ‖routeUPolynomialGaussianFourier Q t.heat xi‖ ≤
      Real.exp (-(xi ^ 2 / (8 * t.1))) *
        routeUPolynomialGaussianMass Q t.heat := by
  have hraw := norm_routeUPolynomialGaussianFourier_le Q t.heat xi
  simp only [routeUPrimeGaussianWedge.heat] at hraw ⊢
  refine le_trans hraw ?_
  apply mul_le_mul_of_nonneg_right _ (routeUPolynomialGaussianMass_nonneg Q ⟨t.1, t.property.1⟩)
  rw [Real.exp_le_exp]
  have htrans := routeUPrimeGaussianWedge_translation_le Q t hxi
  calc
    -(xi ^ 2 / (4 * t.1)) +
          2 * Real.sqrt Q.natDegree * |xi| / Real.sqrt t.1 ≤
        -(xi ^ 2 / (4 * t.1)) + xi ^ 2 / (8 * t.1) := by
      simpa only [add_comm] using add_le_add_left htrans (-(xi ^ 2 / (4 * t.1)))
    _ = -(xi ^ 2 / (8 * t.1)) := by ring

private theorem routeUPrimeGaussianWedge_thirtytwo_heat_le_log_two
    (Q : Polynomial ℝ) (t : routeUPrimeGaussianWedge Q) :
    32 * t.1 ≤ Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogOne : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 from zero_lt_two)
    linarith only [h]
  have htMul : t.1 ≤ t.1 * (Q.natDegree + 1) := by
    have hd : (1 : ℝ) ≤ Q.natDegree + 1 :=
      le_add_of_nonneg_left (Nat.cast_nonneg Q.natDegree)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd t.property.1.le
  have ht : t.1 ≤ Real.log 2 ^ 2 / 256 := le_trans htMul t.property.2
  calc
    32 * t.1 ≤ 32 * (Real.log 2 ^ 2 / 256) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = Real.log 2 ^ 2 / 8 := by ring
    _ ≤ Real.log 2 := by
      nlinarith only [hlog, hlogOne]

private theorem routeUPrimeGaussianWedge_exp_tail_le
    (Q : Polynomial ℝ) (t : routeUPrimeGaussianWedge Q) {xi : ℝ}
    (hxi : Real.log 2 ≤ xi) :
    Real.exp (-(xi ^ 2 / (8 * t.1))) ≤
      Real.exp (-(Real.log 2 ^ 2 / (16 * t.1))) * Real.exp (-2 * xi) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hxi0 : 0 < xi := lt_of_lt_of_le hlog hxi
  have hsq : Real.log 2 ^ 2 ≤ xi ^ 2 :=
    (sq_le_sq₀ hlog.le hxi0.le).mpr hxi
  have hfirst : Real.log 2 ^ 2 / (16 * t.1) ≤ xi ^ 2 / (16 * t.1) :=
    div_le_div_of_nonneg_right hsq (mul_nonneg (by positivity) t.property.1.le)
  have hscale : 32 * t.1 ≤ xi :=
    le_trans (routeUPrimeGaussianWedge_thirtytwo_heat_le_log_two Q t) hxi
  have hprod : 32 * t.1 * xi ≤ xi ^ 2 := by
    nlinarith only [hscale, hxi0]
  have hsecond : 2 * xi ≤ xi ^ 2 / (16 * t.1) := by
    calc
      2 * xi = (32 * t.1 * xi) / (16 * t.1) := by
        field_simp [t.property.1.ne']
        ring
      _ ≤ xi ^ 2 / (16 * t.1) :=
        div_le_div_of_nonneg_right hprod (mul_nonneg (by positivity) t.property.1.le)
  rw [← Real.exp_add, Real.exp_le_exp]
  have hsum := add_le_add hfirst hsecond
  calc
    -(xi ^ 2 / (8 * t.1)) ≤
        -(Real.log 2 ^ 2 / (16 * t.1) + 2 * xi) := by
      apply neg_le_neg
      calc
        Real.log 2 ^ 2 / (16 * t.1) + 2 * xi ≤
            xi ^ 2 / (16 * t.1) + xi ^ 2 / (16 * t.1) := hsum
        _ = xi ^ 2 / (8 * t.1) := by ring
    _ = -(Real.log 2 ^ 2 / (16 * t.1)) + -2 * xi := by ring

private theorem routeUPrimeGaussianWedge_exp_log_nat_tail_le
    (Q : Polynomial ℝ) (t : routeUPrimeGaussianWedge Q) {n : ℕ} (hn : 2 ≤ n) :
    Real.exp (-(Real.log (n : ℝ) ^ 2 / (8 * t.1))) ≤
      Real.exp (-(Real.log 2 ^ 2 / (16 * t.1))) * (n : ℝ) ^ (-(2 : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le zero_lt_two hn)
  have hlog : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (show (0 : ℝ) < 2 from zero_lt_two) (by exact_mod_cast hn)
  have h := routeUPrimeGaussianWedge_exp_tail_le Q t hlog
  rw [Real.rpow_def_of_pos hnpos]
  convert h using 1
  ring

/-- Fixed unconditional arithmetic constant controlling the complete absolute prime tail. -/
def routeUVonMangoldtSquareMass : ℝ :=
  ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))

theorem routeUVonMangoldtSquareMass_nonneg : 0 ≤ routeUVonMangoldtSquareMass := by
  exact tsum_nonneg fun n =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Literal complete von-Mangoldt absolute tail of the native Route-U Fourier source. -/
def routeUPolynomialGaussianPrimeAbsoluteTail
    (Q : Polynomial ℝ) (t : routeUPrimeGaussianWedge Q) : ℝ :=
  ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    ‖routeUPolynomialGaussianFourier Q t.heat (Real.log n)‖

private theorem routeUPolynomialGaussianPrimeAbsoluteTail_term_le
    (Q : Polynomial ℝ) (t : routeUPrimeGaussianWedge Q) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        ‖routeUPolynomialGaussianFourier Q t.heat (Real.log n)‖ ≤
      (Real.exp (-(Real.log 2 ^ 2 / (16 * t.1))) *
          routeUPolynomialGaussianMass Q t.heat) *
        (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))) := by
  by_cases hn : 2 ≤ n
  · have hsqrtOne : (1 : ℝ) ≤ Real.sqrt n := by
      have hsqrtSq := Real.sq_sqrt (Nat.cast_nonneg n)
      have hsqrt0 := Real.sqrt_nonneg (n : ℝ)
      have hOneTwo : (1 : ℕ) ≤ 2 := Nat.succ_le_succ (Nat.zero_le 1)
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans hOneTwo hn)
      nlinarith only [hsqrtSq, hsqrt0, hnOne]
    have hcoeff : ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤
        ArithmeticFunction.vonMangoldt n :=
      div_le_self ArithmeticFunction.vonMangoldt_nonneg hsqrtOne
    have hfreq : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (show (0 : ℝ) < 2 from zero_lt_two) (by exact_mod_cast hn)
    have hfourier := norm_routeUPolynomialGaussianFourier_le_wedge Q t hfreq
    have hgauss := routeUPrimeGaussianWedge_exp_log_nat_tail_le Q t hn
    calc
      ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          ‖routeUPolynomialGaussianFourier Q t.heat (Real.log n)‖ ≤
        ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          (Real.exp (-(Real.log (n : ℝ) ^ 2 / (8 * t.1))) *
            routeUPolynomialGaussianMass Q t.heat) :=
        mul_le_mul_of_nonneg_left hfourier
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg n))
      _ ≤ ArithmeticFunction.vonMangoldt n *
          ((Real.exp (-(Real.log 2 ^ 2 / (16 * t.1))) * (n : ℝ) ^ (-(2 : ℝ))) *
            routeUPolynomialGaussianMass Q t.heat) := by
        exact mul_le_mul hcoeff
          (mul_le_mul_of_nonneg_right hgauss
            (routeUPolynomialGaussianMass_nonneg Q t.heat))
          (mul_nonneg (Real.exp_nonneg _)
            (routeUPolynomialGaussianMass_nonneg Q t.heat))
          ArithmeticFunction.vonMangoldt_nonneg
      _ = (Real.exp (-(Real.log 2 ^ 2 / (16 * t.1))) *
          routeUPolynomialGaussianMass Q t.heat) *
        (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))) := by ring
  · rcases n with _ | n
    · simp
    · rcases n with _ | n
      · simp
      · exact False.elim (hn
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))))

theorem summable_routeUPolynomialGaussianPrimeAbsoluteTail
    (Q : Polynomial ℝ) (t : routeUPrimeGaussianWedge Q) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      ‖routeUPolynomialGaussianFourier Q t.heat (Real.log n)‖) := by
  have hbase : Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))) :=
    summable_vonMangoldt_rpow (show (1 : ℝ) < 2 from one_lt_two)
  refine Summable.of_nonneg_of_le
      (f := fun n : ℕ =>
        (Real.exp (-(Real.log 2 ^ 2 / (16 * t.1))) *
          routeUPolynomialGaussianMass Q t.heat) *
            (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))))
      (fun n => mul_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg n)) (norm_nonneg _))
      (fun n => routeUPolynomialGaussianPrimeAbsoluteTail_term_le Q t n)
      ?_
  exact hbase.mul_left
    (Real.exp (-(Real.log 2 ^ 2 / (16 * t.1))) *
      routeUPolynomialGaussianMass Q t.heat)

/-- **Exact Route-U complete prime tail (PGPT.1 / C43-Y (24.138)).**

All analytic and summability obligations are discharged internally. The only inputs are a real
polynomial and a heat time whose type records the universal parabolic wedge. -/
theorem routeUPolynomialGaussianPrimeAbsoluteTail_le
    (Q : Polynomial ℝ) (t : routeUPrimeGaussianWedge Q) :
    routeUPolynomialGaussianPrimeAbsoluteTail Q t ≤
      routeUVonMangoldtSquareMass * routeUPolynomialGaussianMass Q t.heat *
        Real.exp (-(Real.log 2 ^ 2 / (16 * t.1))) := by
  let C : ℝ := Real.exp (-(Real.log 2 ^ 2 / (16 * t.1))) *
    routeUPolynomialGaussianMass Q t.heat
  let a : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))
  let b : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      ‖routeUPolynomialGaussianFourier Q t.heat (Real.log n)‖
  have ha : Summable a := by
    simpa only [a] using
      (summable_vonMangoldt_rpow (show (1 : ℝ) < 2 from one_lt_two))
  have hCa : Summable (fun n => C * a n) := ha.mul_left C
  have hb : Summable b := by
    simpa only [b] using summable_routeUPolynomialGaussianPrimeAbsoluteTail Q t
  have hba : ∀ n, b n ≤ C * a n := fun n => by
    simpa only [b, C, a] using routeUPolynomialGaussianPrimeAbsoluteTail_term_le Q t n
  have hsum := hb.tsum_le_tsum hba hCa
  rw [ha.tsum_mul_left C] at hsum
  change (∑' n, b n) ≤ routeUVonMangoldtSquareMass *
    routeUPolynomialGaussianMass Q t.heat *
      Real.exp (-(Real.log 2 ^ 2 / (16 * t.1)))
  calc
    (∑' n, b n) ≤ C * ∑' n, a n := hsum
    _ = routeUVonMangoldtSquareMass * routeUPolynomialGaussianMass Q t.heat *
        Real.exp (-(Real.log 2 ^ 2 / (16 * t.1))) := by
      simp only [C, a, routeUVonMangoldtSquareMass]
      ring

end RHTower
