import GaloisForLFunctions.RHTower.BurnolPrimeTailFoldedModeWittBridge
import GaloisForLFunctions.RHTower.CCMUnitRieszVolterraLaplace

/-!
# Exact rank-one compression of the folded prime-tail half-Laplace port

The two folded prime-tail monodromy modes have independent Cauchy data at the
source point.  The literal fixed half-rate Laplace/Burnol port, however,
compresses them to one scalar direction: its even-mode reading is exactly one
half of its odd-mode reading.  Thus this port cannot be the missing
coefficient-faithful Stokes landing.

The positive survivor is explicit.  Evaluation and first derivative at the
source point recover the two coefficients of every finite folded-mode
combination.  Any source-faithful landing must preserve an equivalent two-port
boundary datum before applying the self-adjoint Witt consumer.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Finite two-mode source synthesis from the folded monodromy Cauchy doublet. -/
def primeFoldCauchySynthesis (lam : ℂ) (m : ℕ) (c : ℂ × ℂ) : ℝ → ℂ :=
  fun L => c.1 * primeFoldEvenMode lam m L + c.2 * primeFoldOddMode lam m L

/-- The literal fixed half-rate port collapses the two independent folded modes to one
scalar direction. -/
theorem routeRFoldedHalfLaplacePort_evenMode_eq_half_oddMode
    {lam : ℂ} (hlam : |lam.re| < 1 / 2) (m : ℕ) :
    routeRFoldedHalfLaplacePort (primeFoldEvenMode lam m) =
      (1 / 2 : ℂ) * routeRFoldedHalfLaplacePort (primeFoldOddMode lam m) := by
  rw [routeRFoldedHalfLaplacePort_evenMode hlam m,
    routeRFoldedHalfLaplacePort_oddMode hlam m]
  ring

/-- Hence the fixed half-rate port is not coefficient-faithful on a nontrivial folded
monodromy doublet. -/
theorem exists_distinct_primeFoldModes_eq_halfLaplacePort
    {lam : ℂ} (hlam : |lam.re| < 1 / 2) {m : ℕ} (hm : m ≠ 0) :
    ∃ f g : ℝ → ℂ, f ≠ g ∧
      routeRFoldedHalfLaplacePort f = routeRFoldedHalfLaplacePort g := by
  refine ⟨primeFoldEvenMode lam m,
    fun L => (1 / 2 : ℂ) * primeFoldOddMode lam m L, ?_, ?_⟩
  · intro h
    have hzero := congrFun h 0
    rw [primeFoldEvenMode_zero, primeFoldOddMode_zero] at hzero
    norm_num at hzero
    exact (primeFoldMonodromyCoefficient_ne_zero hm) hzero
  · rw [routeRFoldedHalfLaplacePort_evenMode_eq_half_oddMode hlam m,
      routeRFoldedHalfLaplacePort]
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro L _
    simp only [routeRFoldedHalfLaplaceIntegrand]
    ring_nf

private theorem integrableOn_routeRFoldedHalfLaplaceIntegrand_evenMode
    {lam : ℂ} (hlam : |lam.re| < 1 / 2) (m : ℕ) :
    IntegrableOn
      (routeRFoldedHalfLaplaceIntegrand (primeFoldEvenMode lam m)) (Ioi 0) := by
  have hp := integrableOn_routeRFoldedHalfLaplaceIntegrand_add_lightCone hlam m
  have hm := integrableOn_routeRFoldedHalfLaplaceIntegrand_sub_lightCone hlam m
  have hsum := hp.add hm
  have hrewrite :
      (fun L : ℝ =>
        routeRFoldedHalfLaplaceIntegrand
          (fun x => primeFoldEvenMode lam m x + lam * primeFoldOddMode lam m x) L +
        routeRFoldedHalfLaplaceIntegrand
          (fun x => primeFoldEvenMode lam m x - lam * primeFoldOddMode lam m x) L) =
      fun L => (2 : ℂ) * routeRFoldedHalfLaplaceIntegrand (primeFoldEvenMode lam m) L := by
    funext L
    simp only [routeRFoldedHalfLaplaceIntegrand]
    ring
  have htwice : IntegrableOn
      (fun L => (2 : ℂ) * routeRFoldedHalfLaplaceIntegrand
        (primeFoldEvenMode lam m) L) (Ioi 0) :=
    hsum.congr_fun (fun L _ => congrFun hrewrite L) measurableSet_Ioi
  apply Integrable.congr (htwice.const_mul (1 / 2 : ℂ))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with L _
  ring

private theorem integrableOn_routeRFoldedHalfLaplaceIntegrand_oddMode
    {lam : ℂ} (hlam : |lam.re| < 1 / 2) (m : ℕ) :
    IntegrableOn
      (routeRFoldedHalfLaplaceIntegrand (primeFoldOddMode lam m)) (Ioi 0) := by
  rcases eq_or_ne lam 0 with rfl | hlam0
  · have hbase := GaloisForLFunctions.RHTower.integrableOn_Ioi_cexp_neg_mul_linear_shift
      (w := (1 / 2 : ℂ)) (by norm_num) (L := (0 : ℝ)) le_rfl
    apply Integrable.congr (hbase.const_mul (primeFoldMonodromyCoefficient m))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with L _
    rw [routeRFoldedHalfLaplaceIntegrand, primeFoldOddMode_eq_of_zero]
    norm_num
    ring
  · have hp := integrableOn_routeRFoldedHalfLaplaceIntegrand_add_lightCone hlam m
    have hm := integrableOn_routeRFoldedHalfLaplaceIntegrand_sub_lightCone hlam m
    have hsub := hp.sub hm
    have hrewrite :
        (fun L : ℝ =>
          routeRFoldedHalfLaplaceIntegrand
            (fun x => primeFoldEvenMode lam m x + lam * primeFoldOddMode lam m x) L -
          routeRFoldedHalfLaplaceIntegrand
            (fun x => primeFoldEvenMode lam m x - lam * primeFoldOddMode lam m x) L) =
        fun L => (2 * lam) * routeRFoldedHalfLaplaceIntegrand (primeFoldOddMode lam m) L := by
      funext L
      simp only [routeRFoldedHalfLaplaceIntegrand]
      ring
    have htwice : IntegrableOn
        (fun L => (2 * lam) * routeRFoldedHalfLaplaceIntegrand
          (primeFoldOddMode lam m) L) (Ioi 0) :=
      hsub.congr_fun (fun L _ => congrFun hrewrite L) measurableSet_Ioi
    have htwo : (2 * lam : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hlam0
    apply Integrable.congr (htwice.const_mul (2 * lam)⁻¹)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with L _
    field_simp [hlam0]

/-- Exact scalar factorization of the fixed half-rate port on every folded Cauchy doublet. -/
theorem routeRFoldedHalfLaplacePort_synthesis_eq
    {lam : ℂ} (hlam : |lam.re| < 1 / 2) (m : ℕ) (c : ℂ × ℂ) :
    routeRFoldedHalfLaplacePort (primeFoldCauchySynthesis lam m c) =
      (c.1 / 2 + c.2) * primeFoldMonodromyCoefficient m /
        ((1 / 2 : ℂ) ^ (2 : ℕ) - lam ^ (2 : ℕ)) := by
  have he := integrableOn_routeRFoldedHalfLaplaceIntegrand_evenMode hlam m
  have ho := integrableOn_routeRFoldedHalfLaplaceIntegrand_oddMode hlam m
  have hlinear :
      routeRFoldedHalfLaplacePort (primeFoldCauchySynthesis lam m c) =
        c.1 * routeRFoldedHalfLaplacePort (primeFoldEvenMode lam m) +
          c.2 * routeRFoldedHalfLaplacePort (primeFoldOddMode lam m) := by
    rw [routeRFoldedHalfLaplacePort, routeRFoldedHalfLaplacePort,
      routeRFoldedHalfLaplacePort]
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (he.const_mul c.1) (ho.const_mul c.2)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro L _
    simp only [primeFoldCauchySynthesis, routeRFoldedHalfLaplaceIntegrand]
    ring
  rw [hlinear, routeRFoldedHalfLaplacePort_evenMode hlam,
    routeRFoldedHalfLaplacePort_oddMode hlam]
  ring

/-- The fixed half-rate port loses exactly the coefficient line `c₁ / 2 + c₂ = 0`. -/
theorem routeRFoldedHalfLaplacePort_synthesis_eq_zero_iff
    {lam : ℂ} (hlam : |lam.re| < 1 / 2) {m : ℕ} (hm : m ≠ 0) (c : ℂ × ℂ) :
    routeRFoldedHalfLaplacePort (primeFoldCauchySynthesis lam m c) = 0 ↔
      c.1 / 2 + c.2 = 0 := by
  rw [routeRFoldedHalfLaplacePort_synthesis_eq hlam]
  have habs := abs_lt.mp hlam
  have hminus : (1 / 2 : ℂ) - lam ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simpa using (sub_ne_zero.mpr (ne_of_gt habs.2) : (1 / 2 : ℝ) - lam.re ≠ 0)
  have hplus : (1 / 2 : ℂ) + lam ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    have hpos : 0 < (1 / 2 : ℝ) + lam.re := by linarith [habs.1]
    simpa using hpos.ne'
  have hden : (1 / 2 : ℂ) ^ (2 : ℕ) - lam ^ (2 : ℕ) ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hminus
  have hcoeff : primeFoldMonodromyCoefficient m ≠ 0 :=
    primeFoldMonodromyCoefficient_ne_zero hm
  constructor
  · intro h
    have hprod : (c.1 / 2 + c.2) * primeFoldMonodromyCoefficient m = 0 := by
      calc
        (c.1 / 2 + c.2) * primeFoldMonodromyCoefficient m =
            ((c.1 / 2 + c.2) * primeFoldMonodromyCoefficient m /
              ((1 / 2 : ℂ) ^ (2 : ℕ) - lam ^ (2 : ℕ))) *
                ((1 / 2 : ℂ) ^ (2 : ℕ) - lam ^ (2 : ℕ)) :=
          (div_mul_cancel₀ _ hden).symm
        _ = 0 := by rw [h, zero_mul]
    exact (mul_eq_zero.mp hprod).resolve_right hcoeff
  · intro h
    rw [h]
    ring

/-- Source-point value of a folded two-mode synthesis reads its even coefficient. -/
theorem primeFoldCauchySynthesis_zero
    (lam : ℂ) (m : ℕ) (c : ℂ × ℂ) :
    primeFoldCauchySynthesis lam m c 0 =
      c.1 * primeFoldMonodromyCoefficient m := by
  simp [primeFoldCauchySynthesis, primeFoldEvenMode_zero,
    primeFoldOddMode_zero]

/-- Source-point first derivative of a folded two-mode synthesis reads its odd coefficient. -/
theorem primeFoldCauchySynthesis_hasDerivAt_zero
    (lam : ℂ) (m : ℕ) (c : ℂ × ℂ) :
    HasDerivAt (primeFoldCauchySynthesis lam m c)
      (c.2 * primeFoldMonodromyCoefficient m) 0 := by
  change HasDerivAt
    ((fun L => c.1 * primeFoldEvenMode lam m L) +
      fun L => c.2 * primeFoldOddMode lam m L)
    (c.2 * primeFoldMonodromyCoefficient m) 0
  simpa using
    ((primeFoldEvenMode_hasDerivAt_zero lam m).const_mul c.1).add
      ((primeFoldOddMode_hasDerivAt_zero lam m).const_mul c.2)

/-- The two literal source Cauchy ports recover both coefficients exactly. -/
theorem primeFoldCauchySynthesis_injective
    {m : ℕ} (hm : m ≠ 0) (lam : ℂ) :
    Function.Injective (primeFoldCauchySynthesis lam m) := by
  intro c d hcd
  apply Prod.ext
  · apply mul_right_cancel₀ (primeFoldMonodromyCoefficient_ne_zero hm)
    have hzero := congrFun hcd 0
    simpa only [primeFoldCauchySynthesis_zero] using hzero
  · apply mul_right_cancel₀ (primeFoldMonodromyCoefficient_ne_zero hm)
    have hderiv := congrArg (fun f : ℝ → ℂ => deriv f 0) hcd
    rw [(primeFoldCauchySynthesis_hasDerivAt_zero lam m c).deriv,
      (primeFoldCauchySynthesis_hasDerivAt_zero lam m d).deriv] at hderiv
    exact hderiv

end

end RHTower
