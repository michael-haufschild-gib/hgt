import GaloisForLFunctions.RHTower.BurnolPrimeTailFoldedHalfLaplacePortRankOne

/-!
# Coefficient-faithful multi-rate ports for folded prime tails

The fixed half-rate Laplace port is rank one on a nontrivial folded doublet.
This module isolates the exact positive replacement: a literal Laplace port
at rate `a` reads the Cauchy coefficients through `a c₀ + c₁`; two distinct
rates recover both coefficients, provided both are in the strict integrability
region.  This is a source-data theorem only: it does not construct an
arithmetic realization of the two rates.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- Laplace integrand at arbitrary positive real rate. -/
def routeRFoldedLaplaceIntegrandAt (a : ℝ) (f : ℝ → ℂ) (L : ℝ) : ℂ :=
  Complex.exp (-((a : ℂ) * (L : ℂ))) * f L

/-- Literal folded Laplace port at arbitrary real rate. -/
def routeRFoldedLaplacePortAt (a : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ L : ℝ in Ioi 0, routeRFoldedLaplaceIntegrandAt a f L

theorem routeRFoldedLaplaceIntegrandAt_add_lightCone
    (a : ℝ) (lam : ℂ) (m : ℕ) (L : ℝ) :
    routeRFoldedLaplaceIntegrandAt a
        (fun x => primeFoldEvenMode lam m x + lam * primeFoldOddMode lam m x) L =
      primeFoldMonodromyCoefficient m *
        Complex.exp (-(((a : ℂ) - lam) * (L : ℂ))) := by
  rw [routeRFoldedLaplaceIntegrandAt, primeFoldEvenMode_add_mul_oddMode]
  calc
    Complex.exp (-((a : ℂ) * (L : ℂ))) *
        (primeFoldMonodromyCoefficient m * Complex.exp (lam * (L : ℂ))) =
      primeFoldMonodromyCoefficient m *
        (Complex.exp (-((a : ℂ) * (L : ℂ))) * Complex.exp (lam * (L : ℂ))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      ring

theorem routeRFoldedLaplaceIntegrandAt_sub_lightCone
    (a : ℝ) (lam : ℂ) (m : ℕ) (L : ℝ) :
    routeRFoldedLaplaceIntegrandAt a
        (fun x => primeFoldEvenMode lam m x - lam * primeFoldOddMode lam m x) L =
      primeFoldMonodromyCoefficient m *
        Complex.exp (-(((a : ℂ) + lam) * (L : ℂ))) := by
  rw [routeRFoldedLaplaceIntegrandAt, primeFoldEvenMode_sub_mul_oddMode]
  calc
    Complex.exp (-((a : ℂ) * (L : ℂ))) *
        (primeFoldMonodromyCoefficient m * Complex.exp (-lam * (L : ℂ))) =
      primeFoldMonodromyCoefficient m *
        (Complex.exp (-((a : ℂ) * (L : ℂ))) * Complex.exp (-lam * (L : ℂ))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      ring

theorem integrableOn_routeRFoldedLaplaceIntegrandAt_add_lightCone
    {a : ℝ} {lam : ℂ} (hlam : |lam.re| < a) (m : ℕ) :
    IntegrableOn
      (routeRFoldedLaplaceIntegrandAt a
        (fun x => primeFoldEvenMode lam m x + lam * primeFoldOddMode lam m x))
      (Ioi 0) := by
  have habs := abs_lt.mp hlam
  have hrate : 0 < (((a : ℂ) - lam)).re := by
    simpa using (sub_pos.mpr habs.2 : 0 < a - lam.re)
  have hbase : IntegrableOn (fun L : ℝ => primeFoldMonodromyCoefficient m *
      Complex.exp (-(((a : ℂ) - lam) * (L : ℂ)))) (Ioi 0) :=
    (GaloisForLFunctions.RHTower.integrableOn_Ioi_cexp_neg_mul hrate).const_mul
      (primeFoldMonodromyCoefficient m)
  exact hbase.congr_fun
    (fun L _ => (routeRFoldedLaplaceIntegrandAt_add_lightCone a lam m L).symm)
    measurableSet_Ioi

theorem integrableOn_routeRFoldedLaplaceIntegrandAt_sub_lightCone
    {a : ℝ} {lam : ℂ} (hlam : |lam.re| < a) (m : ℕ) :
    IntegrableOn
      (routeRFoldedLaplaceIntegrandAt a
        (fun x => primeFoldEvenMode lam m x - lam * primeFoldOddMode lam m x))
      (Ioi 0) := by
  have habs := abs_lt.mp hlam
  have hrate : 0 < (((a : ℂ) + lam)).re := by
    have hpos : 0 < a + lam.re := by linarith [habs.1]
    simpa using hpos
  have hbase : IntegrableOn (fun L : ℝ => primeFoldMonodromyCoefficient m *
      Complex.exp (-(((a : ℂ) + lam) * (L : ℂ)))) (Ioi 0) :=
    (GaloisForLFunctions.RHTower.integrableOn_Ioi_cexp_neg_mul hrate).const_mul
      (primeFoldMonodromyCoefficient m)
  exact hbase.congr_fun
    (fun L _ => (routeRFoldedLaplaceIntegrandAt_sub_lightCone a lam m L).symm)
    measurableSet_Ioi

theorem routeRFoldedLaplacePortAt_add_lightCone
    {a : ℝ} {lam : ℂ} (hlam : |lam.re| < a) (m : ℕ) :
    routeRFoldedLaplacePortAt a
        (fun L => primeFoldEvenMode lam m L + lam * primeFoldOddMode lam m L) =
      primeFoldMonodromyCoefficient m * ((a : ℂ) - lam)⁻¹ := by
  have habs := abs_lt.mp hlam
  have hrate : 0 < (((a : ℂ) - lam)).re := by
    simpa using (sub_pos.mpr habs.2 : 0 < a - lam.re)
  rw [routeRFoldedLaplacePortAt,
    setIntegral_congr_fun measurableSet_Ioi
      (fun L _ => routeRFoldedLaplaceIntegrandAt_add_lightCone a lam m L),
    integral_const_mul,
    GaloisForLFunctions.RHTower.integral_Ioi_cexp_neg_mul hrate]

theorem routeRFoldedLaplacePortAt_sub_lightCone
    {a : ℝ} {lam : ℂ} (hlam : |lam.re| < a) (m : ℕ) :
    routeRFoldedLaplacePortAt a
        (fun L => primeFoldEvenMode lam m L - lam * primeFoldOddMode lam m L) =
      primeFoldMonodromyCoefficient m * ((a : ℂ) + lam)⁻¹ := by
  have habs := abs_lt.mp hlam
  have hrate : 0 < (((a : ℂ) + lam)).re := by
    have hpos : 0 < a + lam.re := by linarith [habs.1]
    simpa using hpos
  rw [routeRFoldedLaplacePortAt,
    setIntegral_congr_fun measurableSet_Ioi
      (fun L _ => routeRFoldedLaplaceIntegrandAt_sub_lightCone a lam m L),
    integral_const_mul,
    GaloisForLFunctions.RHTower.integral_Ioi_cexp_neg_mul hrate]

theorem routeRFoldedLaplacePortAt_evenMode
    {a : ℝ} {lam : ℂ} (hlam : |lam.re| < a) (m : ℕ) :
    routeRFoldedLaplacePortAt a (primeFoldEvenMode lam m) =
      primeFoldMonodromyCoefficient m * (a : ℂ) /
        ((a : ℂ) ^ (2 : ℕ) - lam ^ (2 : ℕ)) := by
  have hp := integrableOn_routeRFoldedLaplaceIntegrandAt_add_lightCone hlam m
  have hm := integrableOn_routeRFoldedLaplaceIntegrandAt_sub_lightCone hlam m
  have hsum :
      routeRFoldedLaplacePortAt a
          (fun L => primeFoldEvenMode lam m L + lam * primeFoldOddMode lam m L) +
        routeRFoldedLaplacePortAt a
          (fun L => primeFoldEvenMode lam m L - lam * primeFoldOddMode lam m L) =
        (2 : ℂ) * routeRFoldedLaplacePortAt a (primeFoldEvenMode lam m) := by
    rw [routeRFoldedLaplacePortAt, routeRFoldedLaplacePortAt,
      routeRFoldedLaplacePortAt, ← integral_add hp hm]
    rw [show
      (fun L =>
        routeRFoldedLaplaceIntegrandAt a
            (fun x => primeFoldEvenMode lam m x + lam * primeFoldOddMode lam m x) L +
          routeRFoldedLaplaceIntegrandAt a
            (fun x => primeFoldEvenMode lam m x - lam * primeFoldOddMode lam m x) L) =
        (fun L => (2 : ℂ) *
          routeRFoldedLaplaceIntegrandAt a (primeFoldEvenMode lam m) L) by
      funext L
      simp only [routeRFoldedLaplaceIntegrandAt]
      ring]
    rw [integral_const_mul]
  rw [routeRFoldedLaplacePortAt_add_lightCone hlam m,
    routeRFoldedLaplacePortAt_sub_lightCone hlam m] at hsum
  have habs := abs_lt.mp hlam
  have hminus : (a : ℂ) - lam ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simpa using (sub_ne_zero.mpr (ne_of_gt habs.2) : a - lam.re ≠ 0)
  have hplus : (a : ℂ) + lam ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    have hpos : 0 < a + lam.re := by linarith [habs.1]
    simpa using hpos.ne'
  have hport : routeRFoldedLaplacePortAt a (primeFoldEvenMode lam m) =
      (primeFoldMonodromyCoefficient m * ((a : ℂ) - lam)⁻¹ +
        primeFoldMonodromyCoefficient m * ((a : ℂ) + lam)⁻¹) / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
    simpa [mul_comm] using hsum.symm
  rw [hport]
  have hden : (a : ℂ) ^ (2 : ℕ) - lam ^ (2 : ℕ) ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hminus
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp [hminus, hplus, hden]
  ring

theorem routeRFoldedLaplacePortAt_oddMode_zero
    {a : ℝ} (ha : 0 < a) (m : ℕ) :
    routeRFoldedLaplacePortAt a (primeFoldOddMode 0 m) =
      primeFoldMonodromyCoefficient m / (a : ℂ) ^ (2 : ℕ) := by
  have hgamma := Complex.integral_cpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℂ)) (r := a) (by norm_num) ha
  have hlinear :
      (∫ L : ℝ in Ioi 0,
        (L : ℂ) * Complex.exp (-((a : ℂ) * (L : ℂ)))) = (a : ℂ)⁻¹ ^ (2 : ℕ) := by
    calc
      (∫ L : ℝ in Ioi 0,
        (L : ℂ) * Complex.exp (-((a : ℂ) * (L : ℂ)))) =
          ∫ L : ℝ in Ioi 0,
            (L : ℂ) ^ ((2 : ℂ) - 1) *
              Complex.exp (-((a : ℂ) * (L : ℂ))) := by
                apply setIntegral_congr_fun measurableSet_Ioi
                intro L _
                norm_num [Complex.cpow_one]
      _ = (a : ℂ)⁻¹ ^ (2 : ℕ) := by
        rw [hgamma]
        rw [Complex.cpow_two]
        norm_num [Complex.Gamma_nat_eq_factorial]
  rw [routeRFoldedLaplacePortAt]
  calc
    (∫ L : ℝ in Ioi 0,
      routeRFoldedLaplaceIntegrandAt a (primeFoldOddMode 0 m) L) =
        primeFoldMonodromyCoefficient m *
          ∫ L : ℝ in Ioi 0,
            (L : ℂ) * Complex.exp (-((a : ℂ) * (L : ℂ))) := by
              rw [← integral_const_mul]
              apply setIntegral_congr_fun measurableSet_Ioi
              intro L _
              rw [routeRFoldedLaplaceIntegrandAt, primeFoldOddMode_eq_of_zero]
              ring
    _ = _ := by rw [hlinear]; field_simp

theorem routeRFoldedLaplacePortAt_oddMode
    {a : ℝ} {lam : ℂ} (hlam : |lam.re| < a) (m : ℕ) :
    routeRFoldedLaplacePortAt a (primeFoldOddMode lam m) =
      primeFoldMonodromyCoefficient m /
        ((a : ℂ) ^ (2 : ℕ) - lam ^ (2 : ℕ)) := by
  rcases eq_or_ne lam 0 with rfl | hne
  · have ha : 0 < a := lt_of_le_of_lt (abs_nonneg (0 : ℝ)) hlam
    simpa using routeRFoldedLaplacePortAt_oddMode_zero ha m
  · have hp := integrableOn_routeRFoldedLaplaceIntegrandAt_add_lightCone hlam m
    have hm := integrableOn_routeRFoldedLaplaceIntegrandAt_sub_lightCone hlam m
    have hdiff :
        routeRFoldedLaplacePortAt a
            (fun L => primeFoldEvenMode lam m L + lam * primeFoldOddMode lam m L) -
          routeRFoldedLaplacePortAt a
            (fun L => primeFoldEvenMode lam m L - lam * primeFoldOddMode lam m L) =
          (2 * lam) * routeRFoldedLaplacePortAt a (primeFoldOddMode lam m) := by
      rw [routeRFoldedLaplacePortAt, routeRFoldedLaplacePortAt,
        routeRFoldedLaplacePortAt, ← integral_sub hp hm]
      rw [show
        (fun L =>
          routeRFoldedLaplaceIntegrandAt a
              (fun x => primeFoldEvenMode lam m x + lam * primeFoldOddMode lam m x) L -
            routeRFoldedLaplaceIntegrandAt a
              (fun x => primeFoldEvenMode lam m x - lam * primeFoldOddMode lam m x) L) =
          (fun L => (2 * lam) *
            routeRFoldedLaplaceIntegrandAt a (primeFoldOddMode lam m) L) by
        funext L
        simp only [routeRFoldedLaplaceIntegrandAt]
        ring]
      rw [integral_const_mul]
    rw [routeRFoldedLaplacePortAt_add_lightCone hlam m,
      routeRFoldedLaplacePortAt_sub_lightCone hlam m] at hdiff
    have habs := abs_lt.mp hlam
    have hminus : (a : ℂ) - lam ≠ 0 := by
      apply ne_of_apply_ne Complex.re
      simpa using (sub_ne_zero.mpr (ne_of_gt habs.2) : a - lam.re ≠ 0)
    have hplus : (a : ℂ) + lam ≠ 0 := by
      apply ne_of_apply_ne Complex.re
      have hpos : 0 < a + lam.re := by linarith [habs.1]
      simpa using hpos.ne'
    have hport : routeRFoldedLaplacePortAt a (primeFoldOddMode lam m) =
        (primeFoldMonodromyCoefficient m * ((a : ℂ) - lam)⁻¹ -
          primeFoldMonodromyCoefficient m * ((a : ℂ) + lam)⁻¹) /
          (2 * lam) := by
      apply (eq_div_iff (mul_ne_zero (by norm_num) hne)).2
      simpa [mul_comm] using hdiff.symm
    rw [hport]
    have hden : (a : ℂ) ^ (2 : ℕ) - lam ^ (2 : ℕ) ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero hplus hminus
    rw [inv_eq_one_div, inv_eq_one_div]
    field_simp [hne, hminus, hplus, hden]
    ring

private theorem integrableOn_routeRFoldedLaplaceIntegrandAt_evenMode
    {a : ℝ} {lam : ℂ} (hlam : |lam.re| < a) (m : ℕ) :
    IntegrableOn (routeRFoldedLaplaceIntegrandAt a (primeFoldEvenMode lam m)) (Ioi 0) := by
  have hp := integrableOn_routeRFoldedLaplaceIntegrandAt_add_lightCone hlam m
  have hm := integrableOn_routeRFoldedLaplaceIntegrandAt_sub_lightCone hlam m
  have hsum := hp.add hm
  have hrewrite :
      (fun L : ℝ =>
        routeRFoldedLaplaceIntegrandAt a
          (fun x => primeFoldEvenMode lam m x + lam * primeFoldOddMode lam m x) L +
        routeRFoldedLaplaceIntegrandAt a
          (fun x => primeFoldEvenMode lam m x - lam * primeFoldOddMode lam m x) L) =
      fun L => (2 : ℂ) * routeRFoldedLaplaceIntegrandAt a (primeFoldEvenMode lam m) L := by
    funext L
    simp only [routeRFoldedLaplaceIntegrandAt]
    ring
  have htwice : IntegrableOn
      (fun L => (2 : ℂ) * routeRFoldedLaplaceIntegrandAt a (primeFoldEvenMode lam m) L)
      (Ioi 0) :=
    hsum.congr_fun (fun L _ => congrFun hrewrite L) measurableSet_Ioi
  apply Integrable.congr (htwice.const_mul (1 / 2 : ℂ))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with L _
  ring

private theorem integrableOn_routeRFoldedLaplaceIntegrandAt_oddMode
    {a : ℝ} {lam : ℂ} (hlam : |lam.re| < a) (m : ℕ) :
    IntegrableOn (routeRFoldedLaplaceIntegrandAt a (primeFoldOddMode lam m)) (Ioi 0) := by
  rcases eq_or_ne lam 0 with rfl | hlam0
  · have ha : 0 < a := lt_of_le_of_lt (abs_nonneg (0 : ℝ)) hlam
    have hbase := GaloisForLFunctions.RHTower.integrableOn_Ioi_cexp_neg_mul_linear_shift
      (w := (a : ℂ)) (by simpa using ha) (L := (0 : ℝ)) le_rfl
    apply Integrable.congr (hbase.const_mul (primeFoldMonodromyCoefficient m))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with L _
    rw [routeRFoldedLaplaceIntegrandAt, primeFoldOddMode_eq_of_zero]
    ring_nf
  · have hp := integrableOn_routeRFoldedLaplaceIntegrandAt_add_lightCone hlam m
    have hm := integrableOn_routeRFoldedLaplaceIntegrandAt_sub_lightCone hlam m
    have hsub := hp.sub hm
    have hrewrite :
        (fun L : ℝ =>
          routeRFoldedLaplaceIntegrandAt a
            (fun x => primeFoldEvenMode lam m x + lam * primeFoldOddMode lam m x) L -
          routeRFoldedLaplaceIntegrandAt a
            (fun x => primeFoldEvenMode lam m x - lam * primeFoldOddMode lam m x) L) =
        fun L => (2 * lam) * routeRFoldedLaplaceIntegrandAt a (primeFoldOddMode lam m) L := by
      funext L
      simp only [routeRFoldedLaplaceIntegrandAt]
      ring
    have htwice : IntegrableOn
        (fun L => (2 * lam) * routeRFoldedLaplaceIntegrandAt a (primeFoldOddMode lam m) L)
        (Ioi 0) :=
      hsub.congr_fun (fun L _ => congrFun hrewrite L) measurableSet_Ioi
    have htwo : (2 * lam : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hlam0
    apply Integrable.congr (htwice.const_mul (2 * lam)⁻¹)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with L _
    field_simp [hlam0]

theorem routeRFoldedLaplacePortAt_synthesis_eq
    {a : ℝ} {lam : ℂ} (hlam : |lam.re| < a) (m : ℕ) (c : ℂ × ℂ) :
    routeRFoldedLaplacePortAt a (primeFoldCauchySynthesis lam m c) =
      ((a : ℂ) * c.1 + c.2) * primeFoldMonodromyCoefficient m /
        ((a : ℂ) ^ (2 : ℕ) - lam ^ (2 : ℕ)) := by
  have he := integrableOn_routeRFoldedLaplaceIntegrandAt_evenMode hlam m
  have ho := integrableOn_routeRFoldedLaplaceIntegrandAt_oddMode hlam m
  have hlinear :
      routeRFoldedLaplacePortAt a (primeFoldCauchySynthesis lam m c) =
        c.1 * routeRFoldedLaplacePortAt a (primeFoldEvenMode lam m) +
          c.2 * routeRFoldedLaplacePortAt a (primeFoldOddMode lam m) := by
    rw [routeRFoldedLaplacePortAt, routeRFoldedLaplacePortAt,
      routeRFoldedLaplacePortAt]
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (he.const_mul c.1) (ho.const_mul c.2)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro L _
    simp only [primeFoldCauchySynthesis, routeRFoldedLaplaceIntegrandAt]
    ring
  rw [hlinear, routeRFoldedLaplacePortAt_evenMode hlam,
    routeRFoldedLaplacePortAt_oddMode hlam]
  ring

private theorem routeRFoldedLaplacePortAt_den_ne_zero
    {a : ℝ} {lam : ℂ} (hlam : |lam.re| < a) :
    (a : ℂ) ^ (2 : ℕ) - lam ^ (2 : ℕ) ≠ 0 := by
  have habs := abs_lt.mp hlam
  have hminus : (a : ℂ) - lam ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simpa using (sub_ne_zero.mpr (ne_of_gt habs.2) : a - lam.re ≠ 0)
  have hplus : (a : ℂ) + lam ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    have hpos : 0 < a + lam.re := by linarith [habs.1]
    simpa using hpos.ne'
  rw [sq_sub_sq]
  exact mul_ne_zero hplus hminus

/-- Two distinct strict-rate ports recover both Cauchy coefficients of every
nontrivial folded doublet. -/
theorem routeRFoldedLaplacePortAt_twoRate_injective
    {a b : ℝ} {lam : ℂ} (hlama : |lam.re| < a) (hlamb : |lam.re| < b)
    (hab : a ≠ b) {m : ℕ} (hm : m ≠ 0) :
    Function.Injective (fun c : ℂ × ℂ =>
      (routeRFoldedLaplacePortAt a (primeFoldCauchySynthesis lam m c),
        routeRFoldedLaplacePortAt b (primeFoldCauchySynthesis lam m c))) := by
  intro c d hcd
  have hdena := routeRFoldedLaplacePortAt_den_ne_zero hlama
  have hdenb := routeRFoldedLaplacePortAt_den_ne_zero hlamb
  have hcoeff : primeFoldMonodromyCoefficient m ≠ 0 :=
    primeFoldMonodromyCoefficient_ne_zero hm
  have ha := congrArg Prod.fst hcd
  have hb := congrArg Prod.snd hcd
  change routeRFoldedLaplacePortAt a (primeFoldCauchySynthesis lam m c) =
    routeRFoldedLaplacePortAt a (primeFoldCauchySynthesis lam m d) at ha
  change routeRFoldedLaplacePortAt b (primeFoldCauchySynthesis lam m c) =
    routeRFoldedLaplacePortAt b (primeFoldCauchySynthesis lam m d) at hb
  rw [routeRFoldedLaplacePortAt_synthesis_eq hlama,
    routeRFoldedLaplacePortAt_synthesis_eq hlama] at ha
  rw [routeRFoldedLaplacePortAt_synthesis_eq hlamb,
    routeRFoldedLaplacePortAt_synthesis_eq hlamb] at hb
  have haProd := congrArg (fun x : ℂ => x * ((a : ℂ) ^ (2 : ℕ) - lam ^ (2 : ℕ))) ha
  have hbProd := congrArg (fun x : ℂ => x * ((b : ℂ) ^ (2 : ℕ) - lam ^ (2 : ℕ))) hb
  simp only [div_mul_cancel₀ _ hdena] at haProd
  simp only [div_mul_cancel₀ _ hdenb] at hbProd
  have haLine : (a : ℂ) * c.1 + c.2 = (a : ℂ) * d.1 + d.2 :=
    mul_right_cancel₀ hcoeff haProd
  have hbLine : (b : ℂ) * c.1 + c.2 = (b : ℂ) * d.1 + d.2 :=
    mul_right_cancel₀ hcoeff hbProd
  have habc : (a : ℂ) - (b : ℂ) ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simpa using sub_ne_zero.mpr hab
  have hfirst : c.1 - d.1 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left habc
    linear_combination haLine - hbLine
  have hsecond : c.2 - d.2 = 0 := by
    linear_combination haLine - (a : ℂ) * hfirst
  apply Prod.ext
  · exact sub_eq_zero.mp hfirst
  · exact sub_eq_zero.mp hsecond

end RHTower
