import GaloisForLFunctions.RHTower.PrimeTailReflectionFoldedSecondOrderResolvent
import GaloisForLFunctions.RHTower.BurnolCartierHeadEnergyStokesFlux
import GaloisForLFunctions.RHTower.CCMQuartetPaleyWiener
import GaloisForLFunctions.HTGeometry.HermitianWittEigenvalueReality

/-!
# Burnol current as a folded prime-tail Laplace port

The reflection-folded prime-tail monodromy supplies two independent source-pointed modes.  Their
fixed half-rate Laplace readings are exactly the two reciprocal Burnol head coefficients.  The
oriented Burnol current is therefore the normalized Lorentzian difference of these two genuine
source readings.

The file also applies the algebraic Witt-index-one theorem to the actual folded Cauchy doublet.  It
does not construct the still-missing coefficient-faithful Stokes landing and does not assume its
existence globally.
-/

open Complex MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-! ## Independent folded source modes -/

/-- The centered reflection parameter. -/
def routeRFoldedCenteredParameter (rho : ℂ) : ℂ := rho - 1 / 2

@[simp]
theorem routeRFoldedCenteredParameter_sq (rho : ℂ) :
    routeRFoldedCenteredParameter rho ^ 2 = primeFoldMu rho := rfl

/-- The even and odd monodromy modes are linearly independent whenever multiplicity is nonzero.
The proof reads their independent Dirichlet and Neumann source data. -/
theorem primeFoldEvenOddModes_linearIndependent
    {m : ℕ} (hm : m ≠ 0) (lam : ℂ) :
    LinearIndependent ℂ ![primeFoldEvenMode lam m, primeFoldOddMode lam m] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hq := primeFoldMonodromyCoefficient_ne_zero hm
  have hs : s = 0 := by
    have hzero := congrFun hst 0
    simpa [hq] using hzero
  refine ⟨hs, ?_⟩
  have htMode : t • primeFoldOddMode lam m = 0 := by
    simpa [hs] using hst
  by_contra ht
  have hmode : primeFoldOddMode lam m = 0 :=
    (smul_eq_zero.mp htMode).resolve_left ht
  exact primeFoldOddMode_ne_zero hm lam hmode

/-- Both independent modes solve the same folded equation with eigenvalue `primeFoldMu rho`. -/
theorem primeFoldEvenOddModes_common_secondOrder (rho : ℂ) (m : ℕ) :
    (∀ L : ℝ,
      deriv (deriv (primeFoldEvenMode (routeRFoldedCenteredParameter rho) m)) L =
        primeFoldMu rho * primeFoldEvenMode (routeRFoldedCenteredParameter rho) m L) ∧
    (∀ L : ℝ,
      deriv (deriv (primeFoldOddMode (routeRFoldedCenteredParameter rho) m)) L =
        primeFoldMu rho * primeFoldOddMode (routeRFoldedCenteredParameter rho) m L) := by
  constructor
  · intro L
    simpa using primeFoldEvenMode_secondDeriv (routeRFoldedCenteredParameter rho) m L
  · intro L
    simpa using primeFoldOddMode_secondDeriv (routeRFoldedCenteredParameter rho) m L

/-! ## Light-cone exponentials -/

/-- The forward light-cone combination is the positive exponential mode. -/
theorem primeFoldEvenMode_add_mul_oddMode
    (lam : ℂ) (m : ℕ) (L : ℝ) :
    primeFoldEvenMode lam m L + lam * primeFoldOddMode lam m L =
      primeFoldMonodromyCoefficient m * Complex.exp (lam * (L : ℂ)) := by
  rcases eq_or_ne lam 0 with rfl | hlam
  · simp [primeFoldEvenMode, primeFoldOddMode]
  · rw [primeFoldEvenMode, primeFoldOddMode_eq_of_ne_zero hlam]
    calc
      primeFoldMonodromyCoefficient m * Complex.cosh (lam * (L : ℂ)) +
          lam * (primeFoldMonodromyCoefficient m *
            (Complex.sinh (lam * (L : ℂ)) / lam)) =
          primeFoldMonodromyCoefficient m *
            (Complex.cosh (lam * (L : ℂ)) + Complex.sinh (lam * (L : ℂ))) := by
              field_simp
      _ = _ := by rw [Complex.cosh_add_sinh]

/-- The reflected light-cone combination is the negative exponential mode. -/
theorem primeFoldEvenMode_sub_mul_oddMode
    (lam : ℂ) (m : ℕ) (L : ℝ) :
    primeFoldEvenMode lam m L - lam * primeFoldOddMode lam m L =
      primeFoldMonodromyCoefficient m * Complex.exp (-lam * (L : ℂ)) := by
  rcases eq_or_ne lam 0 with rfl | hlam
  · simp [primeFoldEvenMode, primeFoldOddMode]
  · rw [primeFoldEvenMode, primeFoldOddMode_eq_of_ne_zero hlam]
    calc
      primeFoldMonodromyCoefficient m * Complex.cosh (lam * (L : ℂ)) -
          lam * (primeFoldMonodromyCoefficient m *
            (Complex.sinh (lam * (L : ℂ)) / lam)) =
          primeFoldMonodromyCoefficient m *
            (Complex.cosh (lam * (L : ℂ)) - Complex.sinh (lam * (L : ℂ))) := by
              field_simp
      _ = _ := by
        rw [Complex.cosh_sub_sinh]
        congr 2
        ring

/-! ## Genuine fixed half-rate Laplace port -/

/-- Weighted integrand of the fixed half-rate source Laplace port. -/
def routeRFoldedHalfLaplaceIntegrand (f : ℝ → ℂ) (L : ℝ) : ℂ :=
  Complex.exp (-((1 / 2 : ℂ) * (L : ℂ))) * f L

/-- Fixed source Laplace port at the critical half-rate. -/
def routeRFoldedHalfLaplacePort (f : ℝ → ℂ) : ℂ :=
  ∫ L : ℝ in Ioi 0, routeRFoldedHalfLaplaceIntegrand f L

theorem routeRFoldedHalfLaplaceIntegrand_add_lightCone
    (lam : ℂ) (m : ℕ) (L : ℝ) :
    routeRFoldedHalfLaplaceIntegrand
        (fun x => primeFoldEvenMode lam m x + lam * primeFoldOddMode lam m x) L =
      primeFoldMonodromyCoefficient m *
        Complex.exp (-(((1 / 2 : ℂ) - lam) * (L : ℂ))) := by
  rw [routeRFoldedHalfLaplaceIntegrand, primeFoldEvenMode_add_mul_oddMode]
  calc
    Complex.exp (-((1 / 2 : ℂ) * (L : ℂ))) *
        (primeFoldMonodromyCoefficient m * Complex.exp (lam * (L : ℂ))) =
      primeFoldMonodromyCoefficient m *
        (Complex.exp (-((1 / 2 : ℂ) * (L : ℂ))) *
          Complex.exp (lam * (L : ℂ))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      ring

theorem routeRFoldedHalfLaplaceIntegrand_sub_lightCone
    (lam : ℂ) (m : ℕ) (L : ℝ) :
    routeRFoldedHalfLaplaceIntegrand
        (fun x => primeFoldEvenMode lam m x - lam * primeFoldOddMode lam m x) L =
      primeFoldMonodromyCoefficient m *
        Complex.exp (-(((1 / 2 : ℂ) + lam) * (L : ℂ))) := by
  rw [routeRFoldedHalfLaplaceIntegrand, primeFoldEvenMode_sub_mul_oddMode]
  calc
    Complex.exp (-((1 / 2 : ℂ) * (L : ℂ))) *
        (primeFoldMonodromyCoefficient m * Complex.exp (-lam * (L : ℂ))) =
      primeFoldMonodromyCoefficient m *
        (Complex.exp (-((1 / 2 : ℂ) * (L : ℂ))) *
          Complex.exp (-lam * (L : ℂ))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      ring

theorem integrableOn_routeRFoldedHalfLaplaceIntegrand_add_lightCone
    {lam : ℂ} (hlam : |lam.re| < 1 / 2) (m : ℕ) :
    IntegrableOn
      (routeRFoldedHalfLaplaceIntegrand
        (fun x => primeFoldEvenMode lam m x + lam * primeFoldOddMode lam m x))
      (Ioi 0) := by
  have habs := abs_lt.mp hlam
  have hrate : 0 < (((1 / 2 : ℂ) - lam)).re := by
    simpa using (sub_pos.mpr habs.2 : 0 < (1 / 2 : ℝ) - lam.re)
  have hbase : IntegrableOn
      (fun L : ℝ => primeFoldMonodromyCoefficient m *
        Complex.exp (-(((1 / 2 : ℂ) - lam) * (L : ℂ)))) (Ioi 0) :=
    (GaloisForLFunctions.RHTower.integrableOn_Ioi_cexp_neg_mul hrate).const_mul
      (primeFoldMonodromyCoefficient m)
  exact hbase.congr_fun
    (fun L _ => (routeRFoldedHalfLaplaceIntegrand_add_lightCone lam m L).symm)
    measurableSet_Ioi

theorem integrableOn_routeRFoldedHalfLaplaceIntegrand_sub_lightCone
    {lam : ℂ} (hlam : |lam.re| < 1 / 2) (m : ℕ) :
    IntegrableOn
      (routeRFoldedHalfLaplaceIntegrand
        (fun x => primeFoldEvenMode lam m x - lam * primeFoldOddMode lam m x))
      (Ioi 0) := by
  have habs := abs_lt.mp hlam
  have hrate : 0 < (((1 / 2 : ℂ) + lam)).re := by
    have hpos : 0 < (1 / 2 : ℝ) + lam.re := by linarith [habs.1]
    simpa using hpos
  have hbase : IntegrableOn
      (fun L : ℝ => primeFoldMonodromyCoefficient m *
        Complex.exp (-(((1 / 2 : ℂ) + lam) * (L : ℂ)))) (Ioi 0) :=
    (GaloisForLFunctions.RHTower.integrableOn_Ioi_cexp_neg_mul hrate).const_mul
      (primeFoldMonodromyCoefficient m)
  exact hbase.congr_fun
    (fun L _ => (routeRFoldedHalfLaplaceIntegrand_sub_lightCone lam m L).symm)
    measurableSet_Ioi

/-- Exact forward light-cone Laplace reading. -/
theorem routeRFoldedHalfLaplacePort_add_lightCone
    {lam : ℂ} (hlam : |lam.re| < 1 / 2) (m : ℕ) :
    routeRFoldedHalfLaplacePort
        (fun L => primeFoldEvenMode lam m L + lam * primeFoldOddMode lam m L) =
      primeFoldMonodromyCoefficient m * ((1 / 2 : ℂ) - lam)⁻¹ := by
  have habs := abs_lt.mp hlam
  have hrate : 0 < (((1 / 2 : ℂ) - lam)).re := by
    simpa using (sub_pos.mpr habs.2 : 0 < (1 / 2 : ℝ) - lam.re)
  rw [routeRFoldedHalfLaplacePort,
    setIntegral_congr_fun measurableSet_Ioi
      (fun L _ => routeRFoldedHalfLaplaceIntegrand_add_lightCone lam m L),
    integral_const_mul,
    GaloisForLFunctions.RHTower.integral_Ioi_cexp_neg_mul hrate]

/-- Exact reflected light-cone Laplace reading. -/
theorem routeRFoldedHalfLaplacePort_sub_lightCone
    {lam : ℂ} (hlam : |lam.re| < 1 / 2) (m : ℕ) :
    routeRFoldedHalfLaplacePort
        (fun L => primeFoldEvenMode lam m L - lam * primeFoldOddMode lam m L) =
      primeFoldMonodromyCoefficient m * ((1 / 2 : ℂ) + lam)⁻¹ := by
  have habs := abs_lt.mp hlam
  have hrate : 0 < (((1 / 2 : ℂ) + lam)).re := by
    have hpos : 0 < (1 / 2 : ℝ) + lam.re := by linarith [habs.1]
    simpa using hpos
  rw [routeRFoldedHalfLaplacePort,
    setIntegral_congr_fun measurableSet_Ioi
      (fun L _ => routeRFoldedHalfLaplaceIntegrand_sub_lightCone lam m L),
    integral_const_mul,
    GaloisForLFunctions.RHTower.integral_Ioi_cexp_neg_mul hrate]

/-- Laplace reading of the even mode itself. -/
theorem routeRFoldedHalfLaplacePort_evenMode
    {lam : ℂ} (hlam : |lam.re| < 1 / 2) (m : ℕ) :
    routeRFoldedHalfLaplacePort (primeFoldEvenMode lam m) =
      primeFoldMonodromyCoefficient m * (1 / 2 : ℂ) /
        ((1 / 2 : ℂ) ^ 2 - lam ^ 2) := by
  have hp := integrableOn_routeRFoldedHalfLaplaceIntegrand_add_lightCone hlam m
  have hm := integrableOn_routeRFoldedHalfLaplaceIntegrand_sub_lightCone hlam m
  have hsum :
      routeRFoldedHalfLaplacePort
          (fun L => primeFoldEvenMode lam m L + lam * primeFoldOddMode lam m L) +
        routeRFoldedHalfLaplacePort
          (fun L => primeFoldEvenMode lam m L - lam * primeFoldOddMode lam m L) =
        (2 : ℂ) * routeRFoldedHalfLaplacePort (primeFoldEvenMode lam m) := by
    rw [routeRFoldedHalfLaplacePort, routeRFoldedHalfLaplacePort,
      routeRFoldedHalfLaplacePort, ← integral_add hp hm]
    rw [show
      (fun L =>
        routeRFoldedHalfLaplaceIntegrand
            (fun x => primeFoldEvenMode lam m x + lam * primeFoldOddMode lam m x) L +
          routeRFoldedHalfLaplaceIntegrand
            (fun x => primeFoldEvenMode lam m x - lam * primeFoldOddMode lam m x) L) =
        (fun L => (2 : ℂ) *
          routeRFoldedHalfLaplaceIntegrand (primeFoldEvenMode lam m) L) by
      funext L
      simp only [routeRFoldedHalfLaplaceIntegrand]
      ring]
    rw [integral_const_mul]
  rw [routeRFoldedHalfLaplacePort_add_lightCone hlam m,
    routeRFoldedHalfLaplacePort_sub_lightCone hlam m] at hsum
  have habs := abs_lt.mp hlam
  have hminus : (1 / 2 : ℂ) - lam ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simpa using (sub_ne_zero.mpr (ne_of_gt habs.2) : (1 / 2 : ℝ) - lam.re ≠ 0)
  have hplus : (1 / 2 : ℂ) + lam ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    have hpos : 0 < (1 / 2 : ℝ) + lam.re := by linarith [habs.1]
    simpa using hpos.ne'
  have hport : routeRFoldedHalfLaplacePort (primeFoldEvenMode lam m) =
      (primeFoldMonodromyCoefficient m * ((1 / 2 : ℂ) - lam)⁻¹ +
        primeFoldMonodromyCoefficient m * ((1 / 2 : ℂ) + lam)⁻¹) / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
    simpa [mul_comm] using hsum.symm
  rw [hport]
  have hden : (1 / 2 : ℂ) ^ 2 - lam ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hminus
  have hminusN : 1 - 2 * lam ≠ 0 := by
    intro h
    apply hminus
    linear_combination h / 2
  have hplusN : 1 + 2 * lam ≠ 0 := by
    intro h
    apply hplus
    linear_combination h / 2
  have hdenN : 1 - 2 ^ 2 * lam ^ 2 ≠ 0 := by
    intro h
    apply hden
    linear_combination h / 4
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp [hminusN, hplusN, hdenN]
  ring

/-- Laplace reading of the removable odd mode at the centered parameter `0`. -/
theorem routeRFoldedHalfLaplacePort_oddMode_zero (m : ℕ) :
    routeRFoldedHalfLaplacePort (primeFoldOddMode 0 m) =
      primeFoldMonodromyCoefficient m / (1 / 2 : ℂ) ^ 2 := by
  have hgamma := Complex.integral_cpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℂ)) (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hlinear :
      (∫ L : ℝ in Ioi 0,
        (L : ℂ) * Complex.exp (-((1 / 2 : ℂ) * (L : ℂ)))) = (4 : ℂ) := by
    calc
      (∫ L : ℝ in Ioi 0,
        (L : ℂ) * Complex.exp (-((1 / 2 : ℂ) * (L : ℂ)))) =
          ∫ L : ℝ in Ioi 0,
            (L : ℂ) ^ ((2 : ℂ) - 1) *
              Complex.exp (-(((1 / 2 : ℝ) : ℂ) * (L : ℂ))) := by
                apply setIntegral_congr_fun measurableSet_Ioi
                intro L _
                norm_num [Complex.cpow_one]
      _ = (4 : ℂ) := by
        rw [hgamma]
        rw [Complex.cpow_two]
        norm_num [Complex.Gamma_nat_eq_factorial]
  rw [routeRFoldedHalfLaplacePort]
  calc
    (∫ L : ℝ in Ioi 0,
      routeRFoldedHalfLaplaceIntegrand (primeFoldOddMode 0 m) L) =
        primeFoldMonodromyCoefficient m *
          ∫ L : ℝ in Ioi 0,
            (L : ℂ) * Complex.exp (-((1 / 2 : ℂ) * (L : ℂ))) := by
              rw [← integral_const_mul]
              apply setIntegral_congr_fun measurableSet_Ioi
              intro L _
              rw [routeRFoldedHalfLaplaceIntegrand, primeFoldOddMode_eq_of_zero]
              ring
    _ = _ := by rw [hlinear]; norm_num [div_eq_mul_inv]

/-- Laplace reading of the odd mode itself, including its removable centered value. -/
theorem routeRFoldedHalfLaplacePort_oddMode
    {lam : ℂ} (hlam : |lam.re| < 1 / 2) (m : ℕ) :
    routeRFoldedHalfLaplacePort (primeFoldOddMode lam m) =
      primeFoldMonodromyCoefficient m /
        ((1 / 2 : ℂ) ^ 2 - lam ^ 2) := by
  rcases eq_or_ne lam 0 with rfl | hne
  · simpa using routeRFoldedHalfLaplacePort_oddMode_zero m
  · have hp := integrableOn_routeRFoldedHalfLaplaceIntegrand_add_lightCone hlam m
    have hm := integrableOn_routeRFoldedHalfLaplaceIntegrand_sub_lightCone hlam m
    have hdiff :
        routeRFoldedHalfLaplacePort
            (fun L => primeFoldEvenMode lam m L + lam * primeFoldOddMode lam m L) -
          routeRFoldedHalfLaplacePort
            (fun L => primeFoldEvenMode lam m L - lam * primeFoldOddMode lam m L) =
          (2 * lam) * routeRFoldedHalfLaplacePort (primeFoldOddMode lam m) := by
      rw [routeRFoldedHalfLaplacePort, routeRFoldedHalfLaplacePort,
        routeRFoldedHalfLaplacePort, ← integral_sub hp hm]
      rw [show
        (fun L =>
          routeRFoldedHalfLaplaceIntegrand
              (fun x => primeFoldEvenMode lam m x + lam * primeFoldOddMode lam m x) L -
            routeRFoldedHalfLaplaceIntegrand
              (fun x => primeFoldEvenMode lam m x - lam * primeFoldOddMode lam m x) L) =
          (fun L => (2 * lam) *
            routeRFoldedHalfLaplaceIntegrand (primeFoldOddMode lam m) L) by
        funext L
        simp only [routeRFoldedHalfLaplaceIntegrand]
        ring]
      rw [integral_const_mul]
    rw [routeRFoldedHalfLaplacePort_add_lightCone hlam m,
      routeRFoldedHalfLaplacePort_sub_lightCone hlam m] at hdiff
    have habs := abs_lt.mp hlam
    have hminus : (1 / 2 : ℂ) - lam ≠ 0 := by
      apply ne_of_apply_ne Complex.re
      simpa using (sub_ne_zero.mpr (ne_of_gt habs.2) : (1 / 2 : ℝ) - lam.re ≠ 0)
    have hplus : (1 / 2 : ℂ) + lam ≠ 0 := by
      apply ne_of_apply_ne Complex.re
      have hpos : 0 < (1 / 2 : ℝ) + lam.re := by linarith [habs.1]
      simpa using hpos.ne'
    have hport : routeRFoldedHalfLaplacePort (primeFoldOddMode lam m) =
        (primeFoldMonodromyCoefficient m * ((1 / 2 : ℂ) - lam)⁻¹ -
          primeFoldMonodromyCoefficient m * ((1 / 2 : ℂ) + lam)⁻¹) /
          (2 * lam) := by
      apply (eq_div_iff (mul_ne_zero (by norm_num) hne)).2
      simpa [mul_comm] using hdiff.symm
    rw [hport]
    have hden : (1 / 2 : ℂ) ^ 2 - lam ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero hplus hminus
    have hminusN : 1 - 2 * lam ≠ 0 := by
      intro h
      apply hminus
      linear_combination h / 2
    have hplusN : 1 + 2 * lam ≠ 0 := by
      intro h
      apply hplus
      linear_combination h / 2
    have hdenN : 1 - 2 ^ 2 * lam ^ 2 ≠ 0 := by
      intro h
      apply hden
      linear_combination h / 4
    rw [inv_eq_one_div, inv_eq_one_div]
    field_simp [hne, hminusN, hplusN, hdenN]
    ring

/-! ## Landing on the Burnol heads and current -/

theorem abs_re_routeRFoldedCenteredParameter_lt_half
    {rho : ℂ} (hzero : 0 < rho.re) (hone : rho.re < 1) :
    |(routeRFoldedCenteredParameter rho).re| < 1 / 2 := by
  rw [routeRFoldedCenteredParameter, Complex.sub_re]
  have hhalf : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  rw [hhalf]
  rw [abs_lt]
  constructor <;> linarith

/-- Forward Burnol head as the fixed source Laplace reading. -/
theorem routeRFoldedHalfLaplacePort_forwardHead
    {rho : ℂ} (hzero : 0 < rho.re) (hone : rho.re < 1) (m : ℕ) :
    routeRFoldedHalfLaplacePort
        (fun L =>
          primeFoldEvenMode (routeRFoldedCenteredParameter rho) m L +
            routeRFoldedCenteredParameter rho *
              primeFoldOddMode (routeRFoldedCenteredParameter rho) m L) =
      primeFoldMonodromyCoefficient m / (1 - rho) := by
  rw [routeRFoldedHalfLaplacePort_add_lightCone
    (abs_re_routeRFoldedCenteredParameter_lt_half hzero hone) m]
  have hrate : (1 / 2 : ℂ) - routeRFoldedCenteredParameter rho = 1 - rho := by
    rw [routeRFoldedCenteredParameter]
    ring
  rw [hrate, div_eq_mul_inv]

/-- Reflected Burnol head as the fixed source Laplace reading. -/
theorem routeRFoldedHalfLaplacePort_reflectedHead
    {rho : ℂ} (hzero : 0 < rho.re) (hone : rho.re < 1) (m : ℕ) :
    routeRFoldedHalfLaplacePort
        (fun L =>
          primeFoldEvenMode (routeRFoldedCenteredParameter rho) m L -
            routeRFoldedCenteredParameter rho *
              primeFoldOddMode (routeRFoldedCenteredParameter rho) m L) =
      primeFoldMonodromyCoefficient m / rho := by
  rw [routeRFoldedHalfLaplacePort_sub_lightCone
    (abs_re_routeRFoldedCenteredParameter_lt_half hzero hone) m]
  have hrate : (1 / 2 : ℂ) + routeRFoldedCenteredParameter rho = rho := by
    rw [routeRFoldedCenteredParameter]
    ring
  rw [hrate, div_eq_mul_inv]

/-- Even folded-mode reading in the divisor coordinate. -/
theorem routeRFoldedHalfLaplacePort_evenMode_at
    {rho : ℂ} (hzero : 0 < rho.re) (hone : rho.re < 1) (m : ℕ) :
    routeRFoldedHalfLaplacePort
        (primeFoldEvenMode (routeRFoldedCenteredParameter rho) m) =
      primeFoldMonodromyCoefficient m * (1 / 2 : ℂ) /
        ((1 / 2 : ℂ) ^ 2 - primeFoldMu rho) := by
  simpa using routeRFoldedHalfLaplacePort_evenMode
    (abs_re_routeRFoldedCenteredParameter_lt_half hzero hone) m

/-- Odd folded-mode reading in the divisor coordinate. -/
theorem routeRFoldedHalfLaplacePort_oddMode_at
    {rho : ℂ} (hzero : 0 < rho.re) (hone : rho.re < 1) (m : ℕ) :
    routeRFoldedHalfLaplacePort
        (primeFoldOddMode (routeRFoldedCenteredParameter rho) m) =
      primeFoldMonodromyCoefficient m /
        ((1 / 2 : ℂ) ^ 2 - primeFoldMu rho) := by
  simpa using routeRFoldedHalfLaplacePort_oddMode
    (abs_re_routeRFoldedCenteredParameter_lt_half hzero hone) m

/-- Scaled exact identification of the Burnol current with the folded source Laplace port. -/
theorem norm_primeFoldMonodromyCoefficient_sq_mul_burnolFlux_eq_laplacePort
    {rho : ℂ} (hzero : 0 < rho.re) (hone : rho.re < 1) (m : ℕ) :
    ‖primeFoldMonodromyCoefficient m‖ ^ 2 * burnolCartierDividedShiftHeadFlux rho =
      ‖routeRFoldedHalfLaplacePort
          (fun L =>
            primeFoldEvenMode (routeRFoldedCenteredParameter rho) m L +
              routeRFoldedCenteredParameter rho *
                primeFoldOddMode (routeRFoldedCenteredParameter rho) m L)‖ ^ 2 -
        (Real.log 2) ^ 2 *
          ‖routeRFoldedHalfLaplacePort
            (fun L =>
              primeFoldEvenMode (routeRFoldedCenteredParameter rho) m L -
                routeRFoldedCenteredParameter rho *
                  primeFoldOddMode (routeRFoldedCenteredParameter rho) m L)‖ ^ 2 := by
  rw [routeRFoldedHalfLaplacePort_forwardHead hzero hone m,
    routeRFoldedHalfLaplacePort_reflectedHead hzero hone m]
  unfold burnolCartierDividedShiftHeadFlux
  rw [norm_div, norm_div, norm_inv, norm_inv]
  ring

/-- Exact normalized Lorentz-port formula for the Burnol current. -/
theorem burnolCartierDividedShiftHeadFlux_eq_foldedLaplacePort
    {rho : ℂ} (hzero : 0 < rho.re) (hone : rho.re < 1)
    {m : ℕ} (hm : m ≠ 0) :
    burnolCartierDividedShiftHeadFlux rho =
      ‖primeFoldMonodromyCoefficient m‖⁻¹ ^ 2 *
        (‖routeRFoldedHalfLaplacePort
            (fun L =>
              primeFoldEvenMode (routeRFoldedCenteredParameter rho) m L +
                routeRFoldedCenteredParameter rho *
                  primeFoldOddMode (routeRFoldedCenteredParameter rho) m L)‖ ^ 2 -
          (Real.log 2) ^ 2 *
            ‖routeRFoldedHalfLaplacePort
              (fun L =>
                primeFoldEvenMode (routeRFoldedCenteredParameter rho) m L -
                  routeRFoldedCenteredParameter rho *
                    primeFoldOddMode (routeRFoldedCenteredParameter rho) m L)‖ ^ 2) := by
  rw [← norm_primeFoldMonodromyCoefficient_sq_mul_burnolFlux_eq_laplacePort
    hzero hone m]
  have hq : ‖primeFoldMonodromyCoefficient m‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (primeFoldMonodromyCoefficient_ne_zero hm)
  field_simp

/-- Exact Cayley quotient of the two folded Laplace readings. -/
theorem routeRFoldedHalfLaplacePort_forward_div_reflected
    {rho : ℂ} (hzero : 0 < rho.re) (hone : rho.re < 1)
    {m : ℕ} (hm : m ≠ 0) :
    routeRFoldedHalfLaplacePort
          (fun L =>
            primeFoldEvenMode (routeRFoldedCenteredParameter rho) m L +
              routeRFoldedCenteredParameter rho *
                primeFoldOddMode (routeRFoldedCenteredParameter rho) m L) /
        routeRFoldedHalfLaplacePort
          (fun L =>
            primeFoldEvenMode (routeRFoldedCenteredParameter rho) m L -
              routeRFoldedCenteredParameter rho *
                primeFoldOddMode (routeRFoldedCenteredParameter rho) m L) =
      rho / (1 - rho) := by
  rw [routeRFoldedHalfLaplacePort_forwardHead hzero hone m,
    routeRFoldedHalfLaplacePort_reflectedHead hzero hone m]
  have hq := primeFoldMonodromyCoefficient_ne_zero hm
  have hrho : rho ≠ 0 := by
    intro h
    rw [h] at hzero
    norm_num at hzero
  have honeRho : 1 - rho ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    rw [← h] at hone
    norm_num at hone
  field_simp

/-- The Cayley port is expansive on the open right half-strip. -/
theorem one_lt_norm_routeRFoldedHalfLaplacePort_forward_div_reflected
    {rho : ℂ} (hright : 1 / 2 < rho.re) (hone : rho.re < 1)
    {m : ℕ} (hm : m ≠ 0) :
    1 < ‖routeRFoldedHalfLaplacePort
          (fun L =>
            primeFoldEvenMode (routeRFoldedCenteredParameter rho) m L +
              routeRFoldedCenteredParameter rho *
                primeFoldOddMode (routeRFoldedCenteredParameter rho) m L) /
        routeRFoldedHalfLaplacePort
          (fun L =>
            primeFoldEvenMode (routeRFoldedCenteredParameter rho) m L -
              routeRFoldedCenteredParameter rho *
                primeFoldOddMode (routeRFoldedCenteredParameter rho) m L)‖ := by
  have hzero : 0 < rho.re := lt_trans (by norm_num) hright
  rw [routeRFoldedHalfLaplacePort_forward_div_reflected hzero hone hm]
  have hgain := one_lt_norm_burnolCartierForwardHeadGain hright hone
  simpa [burnolCartierForwardHeadGain, norm_div, norm_conj] using hgain

/-- The Gamma weight `log 2` lies strictly below the right-half Cayley gain. -/
theorem log_two_lt_norm_routeRFoldedHalfLaplacePort_forward_div_reflected
    {rho : ℂ} (hright : 1 / 2 < rho.re) (hone : rho.re < 1)
    {m : ℕ} (hm : m ≠ 0) :
    Real.log 2 < ‖routeRFoldedHalfLaplacePort
          (fun L =>
            primeFoldEvenMode (routeRFoldedCenteredParameter rho) m L +
              routeRFoldedCenteredParameter rho *
                primeFoldOddMode (routeRFoldedCenteredParameter rho) m L) /
        routeRFoldedHalfLaplacePort
          (fun L =>
            primeFoldEvenMode (routeRFoldedCenteredParameter rho) m L -
              routeRFoldedCenteredParameter rho *
                primeFoldOddMode (routeRFoldedCenteredParameter rho) m L)‖ := by
  have hlog : Real.log 2 < 1 := by
    linarith [Real.log_two_lt_d9]
  exact lt_trans hlog
    (one_lt_norm_routeRFoldedHalfLaplacePort_forward_div_reflected hright hone hm)

/-! ## Finite Cauchy-faithful Witt landing consumer -/

open GaloisForLFunctions.HTGeometry

/-- Any coefficient-faithful landing of the two actual folded modes as a common eigenpair in a
Witt-index-one formally self-adjoint carrier forces the folded divisor parameter to be real. -/
theorem primeFoldMu_im_eq_zero_of_cauchyFaithfulWittLanding
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : ComplexSesquilinearForm V) (A : V →ₗ[ℂ] V)
    (hWitt : B.WittIndexAtMostOne) (hA : B.IsFormallySelfAdjoint A)
    (rho : ℂ) (m : ℕ) (T : (ℝ → ℂ) →ₗ[ℂ] V)
    (hfaithful : LinearIndependent ℂ
      ![T (primeFoldEvenMode (routeRFoldedCenteredParameter rho) m),
        T (primeFoldOddMode (routeRFoldedCenteredParameter rho) m)])
    (heven : A (T (primeFoldEvenMode (routeRFoldedCenteredParameter rho) m)) =
      primeFoldMu rho • T (primeFoldEvenMode (routeRFoldedCenteredParameter rho) m))
    (hodd : A (T (primeFoldOddMode (routeRFoldedCenteredParameter rho) m)) =
      primeFoldMu rho • T (primeFoldOddMode (routeRFoldedCenteredParameter rho) m)) :
    (primeFoldMu rho).im = 0 :=
  ComplexSesquilinearForm.common_eigenvalue_im_eq_zero_of_wittIndexAtMostOne
    B A hWitt hA hfaithful heven hodd

/-- Global injectivity is a sufficient, but not necessary, way to obtain the exact
Cauchy-faithfulness premise from the source-mode independence theorem. -/
theorem primeFoldMu_im_eq_zero_of_injectiveWittLanding
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : ComplexSesquilinearForm V) (A : V →ₗ[ℂ] V)
    (hWitt : B.WittIndexAtMostOne) (hA : B.IsFormallySelfAdjoint A)
    (rho : ℂ) {m : ℕ} (hm : m ≠ 0)
    (T : (ℝ → ℂ) →ₗ[ℂ] V) (hT : Function.Injective T)
    (heven : A (T (primeFoldEvenMode (routeRFoldedCenteredParameter rho) m)) =
      primeFoldMu rho • T (primeFoldEvenMode (routeRFoldedCenteredParameter rho) m))
    (hodd : A (T (primeFoldOddMode (routeRFoldedCenteredParameter rho) m)) =
      primeFoldMu rho • T (primeFoldOddMode (routeRFoldedCenteredParameter rho) m)) :
    (primeFoldMu rho).im = 0 := by
  have hsource := primeFoldEvenOddModes_linearIndependent hm
    (routeRFoldedCenteredParameter rho)
  have himages : LinearIndependent ℂ
      ![T (primeFoldEvenMode (routeRFoldedCenteredParameter rho) m),
        T (primeFoldOddMode (routeRFoldedCenteredParameter rho) m)] := by
    rw [LinearIndependent.pair_iff] at hsource ⊢
    intro s t hzero
    apply hsource s t
    apply hT
    simpa using hzero
  exact primeFoldMu_im_eq_zero_of_cauchyFaithfulWittLanding
    B A hWitt hA rho m T himages heven hodd

/-- Critical-line consequence of the finite Cauchy-faithful Witt landing. -/
theorem re_eq_half_of_cauchyFaithfulWittLanding
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : ComplexSesquilinearForm V) (A : V →ₗ[ℂ] V)
    (hWitt : B.WittIndexAtMostOne) (hA : B.IsFormallySelfAdjoint A)
    (rho : ℂ) (him : rho.im ≠ 0) (m : ℕ)
    (T : (ℝ → ℂ) →ₗ[ℂ] V)
    (hfaithful : LinearIndependent ℂ
      ![T (primeFoldEvenMode (routeRFoldedCenteredParameter rho) m),
        T (primeFoldOddMode (routeRFoldedCenteredParameter rho) m)])
    (heven : A (T (primeFoldEvenMode (routeRFoldedCenteredParameter rho) m)) =
      primeFoldMu rho • T (primeFoldEvenMode (routeRFoldedCenteredParameter rho) m))
    (hodd : A (T (primeFoldOddMode (routeRFoldedCenteredParameter rho) m)) =
      primeFoldMu rho • T (primeFoldOddMode (routeRFoldedCenteredParameter rho) m)) :
    rho.re = 1 / 2 :=
  re_eq_half_of_primeFoldMu_real him
    (primeFoldMu_im_eq_zero_of_cauchyFaithfulWittLanding
      B A hWitt hA rho m T hfaithful heven hodd)

/-- Critical-line consequence under the sufficient global-injectivity interface. -/
theorem re_eq_half_of_injectiveWittLanding
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : ComplexSesquilinearForm V) (A : V →ₗ[ℂ] V)
    (hWitt : B.WittIndexAtMostOne) (hA : B.IsFormallySelfAdjoint A)
    (rho : ℂ) (him : rho.im ≠ 0) {m : ℕ} (hm : m ≠ 0)
    (T : (ℝ → ℂ) →ₗ[ℂ] V) (hT : Function.Injective T)
    (heven : A (T (primeFoldEvenMode (routeRFoldedCenteredParameter rho) m)) =
      primeFoldMu rho • T (primeFoldEvenMode (routeRFoldedCenteredParameter rho) m))
    (hodd : A (T (primeFoldOddMode (routeRFoldedCenteredParameter rho) m)) =
      primeFoldMu rho • T (primeFoldOddMode (routeRFoldedCenteredParameter rho) m)) :
    rho.re = 1 / 2 :=
  re_eq_half_of_primeFoldMu_real him
    (primeFoldMu_im_eq_zero_of_injectiveWittLanding
      B A hWitt hA rho hm T hT heven hodd)

end RHTower
