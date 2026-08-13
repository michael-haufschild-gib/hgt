import GaloisForLFunctions.RHTower.XiPolynomialGaussianExplicitFormula

/-!
# Route-U global polynomial-Gaussian completed-source envelope

The translated-oscillator aperture admits a global completed-square estimate at arbitrary positive
heat time. At arithmetic frequencies this converts the entire half-density prime source into the
fixed, absolutely convergent von-Mangoldt mass at abscissa two. Combining that estimate with the
exact polynomial-Gaussian explicit formula gives an unconditional lower envelope for every
polynomial-square Xi heat trace.

No zero-location premise, coefficient bound, asymptotic input, or numerical computation enters.
-/

open scoped Real
open Real Complex MeasureTheory ArithmeticFunction

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

private theorem routeUGlobalFourierExponent_le
    (d : ℕ) (t : {t : ℝ // 0 < t}) (xi : ℝ) :
    -(xi ^ 2 / (4 * t.1)) +
        2 * Real.sqrt d * xi / Real.sqrt t.1 ≤
      8 * (d : ℝ) + 8 * t.1 - 2 * xi := by
  have hs : 0 < Real.sqrt t.1 := Real.sqrt_pos.2 t.property
  have hs2 : Real.sqrt t.1 ^ 2 = t.1 := Real.sq_sqrt t.property.le
  have hd2 : Real.sqrt (d : ℝ) ^ 2 = d :=
    Real.sq_sqrt (Nat.cast_nonneg d)
  have hsumsq :
      0 ≤ (xi - 8 * Real.sqrt d * Real.sqrt t.1) ^ 2 +
        (xi - 8 * t.1) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hcore :
      0 ≤ xi ^ 2 - 8 * Real.sqrt d * Real.sqrt t.1 * xi +
        32 * (d : ℝ) * t.1 + 32 * t.1 ^ 2 - 8 * t.1 * xi := by
    nlinarith only [hsumsq, hs2, hd2]
  have hgap :
      (8 * (d : ℝ) + 8 * t.1 - 2 * xi) -
          (-(xi ^ 2 / (4 * t.1)) +
            2 * Real.sqrt d * xi / Real.sqrt t.1) =
        (xi ^ 2 - 8 * Real.sqrt d * Real.sqrt t.1 * xi +
            32 * (d : ℝ) * t.1 + 32 * t.1 ^ 2 - 8 * t.1 * xi) /
          (4 * t.1) := by
    field_simp [t.property.ne', hs.ne']
    ring_nf
    rw [hs2]
    ring
  rw [← sub_nonneg, hgap]
  exact div_nonneg hcore (mul_nonneg (by norm_num) t.property.le)

/-- Literal complete von-Mangoldt absolute tail at arbitrary positive heat time. -/
def routeUPolynomialGaussianPrimeGlobalAbsoluteTail
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) : ℝ :=
  ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    ‖routeUPolynomialGaussianFourier Q t (Real.log n)‖

private theorem routeUPolynomialGaussianPrimeGlobalAbsoluteTail_term_le
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        ‖routeUPolynomialGaussianFourier Q t (Real.log n)‖ ≤
      (Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) *
          routeUPolynomialGaussianMass Q t) *
        (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))) := by
  by_cases hn : 2 ≤ n
  · have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le zero_lt_two hn)
    have hlog0 : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by
        exact_mod_cast (show (1 : ℕ) ≤ n from le_trans (by norm_num) hn))
    have hsqrtOne : (1 : ℝ) ≤ Real.sqrt n := by
      have hsqrtSq := Real.sq_sqrt (Nat.cast_nonneg n)
      have hsqrt0 := Real.sqrt_nonneg (n : ℝ)
      have hnOne : (1 : ℝ) ≤ n := by
        exact_mod_cast (show (1 : ℕ) ≤ n from le_trans (by norm_num) hn)
      nlinarith only [hsqrtSq, hsqrt0, hnOne]
    have hcoeff : ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤
        ArithmeticFunction.vonMangoldt n :=
      div_le_self ArithmeticFunction.vonMangoldt_nonneg hsqrtOne
    have hraw := norm_routeUPolynomialGaussianFourier_le Q t (Real.log n)
    rw [abs_of_nonneg hlog0] at hraw
    have hexponent := routeUGlobalFourierExponent_le Q.natDegree t (Real.log n)
    have hfourier :
        ‖routeUPolynomialGaussianFourier Q t (Real.log n)‖ ≤
          (Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) *
            (n : ℝ) ^ (-(2 : ℝ))) * routeUPolynomialGaussianMass Q t := by
      calc
        ‖routeUPolynomialGaussianFourier Q t (Real.log n)‖ ≤
            Real.exp (-(Real.log (n : ℝ) ^ 2 / (4 * t.1)) +
                2 * Real.sqrt Q.natDegree * Real.log n / Real.sqrt t.1) *
              routeUPolynomialGaussianMass Q t := hraw
        _ ≤ Real.exp (8 * (Q.natDegree : ℝ) + 8 * t.1 -
              2 * Real.log n) * routeUPolynomialGaussianMass Q t := by
            exact mul_le_mul_of_nonneg_right
              (Real.exp_le_exp.mpr hexponent)
              (routeUPolynomialGaussianMass_nonneg Q t)
        _ = (Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) *
              (n : ℝ) ^ (-(2 : ℝ))) * routeUPolynomialGaussianMass Q t := by
            rw [Real.rpow_def_of_pos hnpos, ← Real.exp_add]
            congr 2
            ring
    calc
      ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          ‖routeUPolynomialGaussianFourier Q t (Real.log n)‖ ≤
        ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          ((Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) *
            (n : ℝ) ^ (-(2 : ℝ))) * routeUPolynomialGaussianMass Q t) :=
        mul_le_mul_of_nonneg_left hfourier
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg n))
      _ ≤ ArithmeticFunction.vonMangoldt n *
          ((Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) *
            (n : ℝ) ^ (-(2 : ℝ))) * routeUPolynomialGaussianMass Q t) := by
        exact mul_le_mul_of_nonneg_right hcoeff
          (mul_nonneg
            (mul_nonneg (Real.exp_nonneg _)
              (Real.rpow_nonneg (Nat.cast_nonneg n) _))
            (routeUPolynomialGaussianMass_nonneg Q t))
      _ = (Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) *
          routeUPolynomialGaussianMass Q t) *
        (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))) := by ring
  · rcases n with _ | n
    · simp
    · rcases n with _ | n
      · simp
      · exact False.elim (hn
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))))

theorem summable_routeUPolynomialGaussianPrimeGlobalAbsoluteTail
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      ‖routeUPolynomialGaussianFourier Q t (Real.log n)‖) := by
  have hbase : Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))) :=
    summable_vonMangoldt_rpow (show (1 : ℝ) < 2 from one_lt_two)
  refine Summable.of_nonneg_of_le
      (f := fun n : ℕ =>
        (Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) *
          routeUPolynomialGaussianMass Q t) *
            (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))))
      (fun n => mul_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg n))
        (norm_nonneg _))
      (fun n => routeUPolynomialGaussianPrimeGlobalAbsoluteTail_term_le Q t n)
      ?_
  exact hbase.mul_left
    (Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) *
      routeUPolynomialGaussianMass Q t)

/-- Unrestricted complete prime tail, controlled by fixed Dirichlet mass and an explicit
degree--heat exponential cost. -/
theorem routeUPolynomialGaussianPrimeGlobalAbsoluteTail_le
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) :
    routeUPolynomialGaussianPrimeGlobalAbsoluteTail Q t ≤
      routeUVonMangoldtSquareMass * routeUPolynomialGaussianMass Q t *
        Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) := by
  let C : ℝ := Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) *
    routeUPolynomialGaussianMass Q t
  let a : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(2 : ℝ))
  let b : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      ‖routeUPolynomialGaussianFourier Q t (Real.log n)‖
  have ha : Summable a := by
    simpa only [a] using
      (summable_vonMangoldt_rpow (show (1 : ℝ) < 2 from one_lt_two))
  have hCa : Summable (fun n => C * a n) := ha.mul_left C
  have hb : Summable b := by
    simpa only [b] using
      summable_routeUPolynomialGaussianPrimeGlobalAbsoluteTail Q t
  have hba : ∀ n, b n ≤ C * a n := fun n => by
    simpa only [b, C, a] using
      routeUPolynomialGaussianPrimeGlobalAbsoluteTail_term_le Q t n
  have hsum := hb.tsum_le_tsum hba hCa
  rw [ha.tsum_mul_left C] at hsum
  change (∑' n, b n) ≤ routeUVonMangoldtSquareMass *
    routeUPolynomialGaussianMass Q t *
      Real.exp (8 * ((Q.natDegree : ℝ) + t.1))
  calc
    (∑' n, b n) ≤ C * ∑' n, a n := hsum
    _ = routeUVonMangoldtSquareMass * routeUPolynomialGaussianMass Q t *
        Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) := by
      simp only [C, a, routeUVonMangoldtSquareMass]
      ring

private theorem norm_LSeries_vonMangoldt_half_term_global
    (n : ℕ) :
    ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (1 / 2 : ℂ) n‖ = ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
  rcases n with _ | n
  · simp [LSeries.term_zero]
  · have hn : 0 < n + 1 := Nat.succ_pos n
    rw [LSeries.term_of_ne_zero hn.ne', norm_div, norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.norm_natCast_cpow_of_pos hn, Real.sqrt_eq_rpow]
    norm_num

/-- Real part of the exact prime source is bounded at every positive heat time. -/
theorem re_routeUPolynomialGaussianPrimeSource_le_globalAbsoluteTail
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) :
    (routeUPolynomialGaussianPrimeSource Q t).re ≤
      routeUPolynomialGaussianPrimeGlobalAbsoluteTail Q t := by
  have hsource := summable_routeUPolynomialGaussianPrimeSourceTerm Q t
  have hsourceRe := hsource.mapL Complex.reCLM
  rw [routeUPolynomialGaussianPrimeSource, Complex.re_tsum hsource]
  exact hsourceRe.tsum_le_tsum
    (fun n => by
      calc
        (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (1 / 2 : ℂ) n *
            routeUPolynomialGaussianFourier Q t (Real.log n)).re ≤
            ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (1 / 2 : ℂ) n *
                routeUPolynomialGaussianFourier Q t (Real.log n)‖ :=
          Complex.re_le_norm _
        _ = ArithmeticFunction.vonMangoldt n / Real.sqrt n *
              ‖routeUPolynomialGaussianFourier Q t (Real.log n)‖ := by
          rw [norm_mul, norm_LSeries_vonMangoldt_half_term_global])
    (summable_routeUPolynomialGaussianPrimeGlobalAbsoluteTail Q t)

private theorem integral_norm_routeUPolynomialGaussianDensity_mul_gammaHardyPhaseRate_ge_zero
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) :
    gammaHardyPhaseRate 0 * routeUPolynomialGaussianMass Q t ≤
      ∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t x‖ * gammaHardyPhaseRate x := by
  simpa using
    (integral_norm_routeUPolynomialGaussianDensity_mul_gammaHardyPhaseRate_ge
      Q t ⟨0, le_rfl⟩)

/-- **Global completed-source envelope (GSE.2).** Every polynomial-square Xi heat trace has an
unconditional lower bound at arbitrary positive heat time, with no zero-location premise. -/
theorem pi_mul_xiPolynomialGaussianHeatTraceReal_ge_globalEnvelope
    (Q : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) :
    (gammaHardyPhaseRate 0 - routeUVonMangoldtSquareMass *
        Real.exp (8 * ((Q.natDegree : ℝ) + t.1))) *
        routeUPolynomialGaussianMass Q t ≤
      Real.pi * xiPolynomialGaussianHeatTraceReal Q t.1 := by
  have hformula := pi_mul_xiPolynomialGaussianHeatTraceReal_eq_primeGamma Q t
  have hgamma :=
    integral_norm_routeUPolynomialGaussianDensity_mul_gammaHardyPhaseRate_ge_zero Q t
  have hsource := re_routeUPolynomialGaussianPrimeSource_le_globalAbsoluteTail Q t
  have htail := routeUPolynomialGaussianPrimeGlobalAbsoluteTail_le Q t
  have hprime :
      (routeUPolynomialGaussianPrimeSource Q t).re ≤
        routeUVonMangoldtSquareMass * routeUPolynomialGaussianMass Q t *
          Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) :=
    le_trans hsource htail
  have hpolar : 0 ≤
      2 * Real.pi * (Q.eval (-(1 / 4 : ℝ))) ^ 2 * Real.exp (t.1 / 4) := by
    positivity
  calc
    (gammaHardyPhaseRate 0 - routeUVonMangoldtSquareMass *
        Real.exp (8 * ((Q.natDegree : ℝ) + t.1))) *
        routeUPolynomialGaussianMass Q t =
      gammaHardyPhaseRate 0 * routeUPolynomialGaussianMass Q t -
        routeUVonMangoldtSquareMass * routeUPolynomialGaussianMass Q t *
          Real.exp (8 * ((Q.natDegree : ℝ) + t.1)) := by ring
    _ ≤ (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t x‖ *
          gammaHardyPhaseRate x) -
        (routeUPolynomialGaussianPrimeSource Q t).re :=
      sub_le_sub hgamma hprime
    _ ≤ (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t x‖ *
          gammaHardyPhaseRate x) +
        2 * Real.pi * (Q.eval (-(1 / 4 : ℝ))) ^ 2 * Real.exp (t.1 / 4) -
          (routeUPolynomialGaussianPrimeSource Q t).re := by
      linarith only [hpolar]
    _ = Real.pi * xiPolynomialGaussianHeatTraceReal Q t.1 := hformula.symm

end RHTower
