import GaloisForLFunctions.RHTower.PolynomialGaussianGammaRadialEnvelope
import GaloisForLFunctions.RHTower.PolynomialGaussianPrimeTail

/-!
# Route-U completed prime--Gamma wedge

This file closes C43-Y (24.139) before the explicit-formula landing.  The unique positive zero of
the exact Gamma Hardy-phase rate selects a canonical fixed radius.  One explicit positive aperture
is then the minimum of the existing Fourier wedge, a Gamma-leakage budget, and a complete-prime-tail
budget.

For every polynomial in this wedge, the exact Gamma integral minus the literal complete absolute
prime tail is at least one half of the positive Gamma rate at the canonical radius times native
mass.  For every nonzero polynomial the gap is strictly positive.  No mass division, numerical
computation, asymptotic premise, PNT, zero-free region, or RH hypothesis enters.
-/

open scoped Real
open Complex Real MeasureTheory Set

noncomputable section

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- A nonzero Route-U polynomial has strictly positive native polynomial--Gaussian mass. -/
theorem routeUPolynomialGaussianMass_pos
    (Q : {Q : Polynomial ℝ // Q ≠ 0}) (t : {t : ℝ // 0 < t}) :
    0 < routeUPolynomialGaussianMass Q.1 t := by
  rw [routeUPolynomialGaussianMass]
  have hEven : evenSquarePolynomial Q.1 ≠ 0 := by
    rw [evenSquarePolynomial, ← Polynomial.expand_eq_comp_X_pow]
    exact (Polynomial.expand_ne_zero (R := ℝ) (show 0 < 2 by norm_num)).2 Q.property
  obtain ⟨x, hx⟩ : ∃ x : ℝ, (evenSquarePolynomial Q.1).eval x ≠ 0 := by
    by_contra h
    have hzero : ∀ x : ℝ, (evenSquarePolynomial Q.1).eval x = 0 := by
      intro x
      exact not_ne_iff.mp (not_exists.mp h x)
    exact hEven (Polynomial.zero_of_eval_zero _ hzero)
  apply integral_pos_of_integrable_nonneg_nonzero
      (x := x)
      (by
        unfold routeUPolynomialGaussianDensity evenSquarePolynomial
        fun_prop)
      (integrable_norm_routeUPolynomialGaussianDensity Q.1 t)
      (fun _ => norm_nonneg _)
  rw [norm_ne_zero_iff]
  unfold routeUPolynomialGaussianDensity
  exact_mod_cast mul_ne_zero (pow_ne_zero 2 hx) (Real.exp_ne_zero _)

private theorem exp_neg_div_le_div {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    Real.exp (-(A / t)) ≤ t / A := by
  have hx : 0 < A / t := div_pos hA ht
  have hxexp : A / t ≤ Real.exp (A / t) :=
    le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp (A / t))
  have hmul := mul_le_mul_of_nonneg_right hxexp (Real.exp_nonneg (-(A / t)))
  have hprod : Real.exp (-(A / t)) * (A / t) ≤ 1 := by
    calc
      Real.exp (-(A / t)) * (A / t) =
          (A / t) * Real.exp (-(A / t)) := by ring
      _ ≤ Real.exp (A / t) * Real.exp (-(A / t)) := hmul
      _ = 1 := by rw [← Real.exp_add]; ring_nf; simp
  apply (le_div_iff₀ hA).2
  calc
    Real.exp (-(A / t)) * A =
        (Real.exp (-(A / t)) * (A / t)) * t := by field_simp
    _ ≤ 1 * t := mul_le_mul_of_nonneg_right hprod ht.le
    _ = t := one_mul t

/-- Canonical positive zero of the exact Gamma Hardy-phase rate. -/
def routeUCompletedPrimeGammaRoot : ℝ :=
  Classical.choose existsUnique_pos_gammaHardyPhaseRate_eq_zero

theorem routeUCompletedPrimeGammaRoot_pos : 0 < routeUCompletedPrimeGammaRoot :=
  (Classical.choose_spec existsUnique_pos_gammaHardyPhaseRate_eq_zero).1.1

theorem gammaHardyPhaseRate_routeUCompletedPrimeGammaRoot_eq_zero :
    gammaHardyPhaseRate routeUCompletedPrimeGammaRoot = 0 :=
  (Classical.choose_spec existsUnique_pos_gammaHardyPhaseRate_eq_zero).1.2

/-- Fixed radius one unit beyond the canonical Gamma-rate zero. -/
def routeUCompletedPrimeGammaRadius : ℝ := routeUCompletedPrimeGammaRoot + 1

theorem routeUCompletedPrimeGammaRadius_pos : 0 < routeUCompletedPrimeGammaRadius := by
  unfold routeUCompletedPrimeGammaRadius
  linarith [routeUCompletedPrimeGammaRoot_pos]

theorem gammaHardyPhaseRate_routeUCompletedPrimeGammaRadius_pos :
    0 < gammaHardyPhaseRate routeUCompletedPrimeGammaRadius := by
  have h := strictMonoOn_gammaHardyPhaseRate
    (Set.mem_Ici.mpr routeUCompletedPrimeGammaRoot_pos.le)
    (Set.mem_Ici.mpr routeUCompletedPrimeGammaRadius_pos.le)
    (show routeUCompletedPrimeGammaRoot < routeUCompletedPrimeGammaRadius by
      unfold routeUCompletedPrimeGammaRadius
      linarith)
  rw [gammaHardyPhaseRate_routeUCompletedPrimeGammaRoot_eq_zero] at h
  exact h

private theorem routeUCompletedPrimeGammaRadius_increment_pos :
    0 < gammaHardyPhaseRate routeUCompletedPrimeGammaRadius - gammaHardyPhaseRate 0 := by
  linarith [gammaHardyPhaseRate_routeUCompletedPrimeGammaRadius_pos,
    gammaHardyPhaseRate_zero_neg]

/-- Heat--degree budget making Gamma leakage at most one quarter of the canonical positive rate. -/
def routeUGammaLeakageBudget : ℝ :=
  (gammaHardyPhaseRate routeUCompletedPrimeGammaRadius /
    (72 * routeUCompletedPrimeGammaRadius *
      (gammaHardyPhaseRate routeUCompletedPrimeGammaRadius - gammaHardyPhaseRate 0))) ^ (2 : ℕ)

/-- Heat--degree budget making the complete absolute prime tail at most one quarter of the
canonical positive Gamma rate times mass. -/
def routeUPrimeSuppressionBudget : ℝ :=
  gammaHardyPhaseRate routeUCompletedPrimeGammaRadius * Real.log 2 ^ (2 : ℕ) /
    (64 * (routeUVonMangoldtSquareMass + 1))

/-- Canonical positive aperture simultaneously satisfying Fourier, Gamma, and prime budgets. -/
def routeUCompletedPrimeGammaAperture : ℝ :=
  min (Real.log 2 ^ (2 : ℕ) / 256)
    (min routeUGammaLeakageBudget routeUPrimeSuppressionBudget)

theorem routeUCompletedPrimeGammaAperture_pos :
    0 < routeUCompletedPrimeGammaAperture := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hC : 0 < routeUVonMangoldtSquareMass + 1 := by
    linarith [routeUVonMangoldtSquareMass_nonneg]
  have hLeak : 0 < routeUGammaLeakageBudget := by
    unfold routeUGammaLeakageBudget
    exact sq_pos_of_pos (div_pos gammaHardyPhaseRate_routeUCompletedPrimeGammaRadius_pos
      (mul_pos (mul_pos (by norm_num) routeUCompletedPrimeGammaRadius_pos)
        routeUCompletedPrimeGammaRadius_increment_pos))
  have hPrime : 0 < routeUPrimeSuppressionBudget := by
    unfold routeUPrimeSuppressionBudget
    exact div_pos
      (mul_pos gammaHardyPhaseRate_routeUCompletedPrimeGammaRadius_pos (sq_pos_of_pos hlog))
      (mul_pos (by norm_num) hC)
  unfold routeUCompletedPrimeGammaAperture
  exact lt_min (by positivity) (lt_min hLeak hPrime)

/-- Typed Route-U wedge on which the exact completed Gamma-minus-absolute-prime gap is positive. -/
def routeUCompletedPrimeGammaWedge (Q : Polynomial ℝ) :=
  {t : ℝ // 0 < t ∧
    t * (Q.natDegree + 1) ≤ routeUCompletedPrimeGammaAperture}

/-- Forget the completed wedge while retaining positive heat time. -/
def routeUCompletedPrimeGammaWedge.heat
    {Q : Polynomial ℝ} (t : routeUCompletedPrimeGammaWedge Q) : {τ : ℝ // 0 < τ} :=
  ⟨t.1, t.property.1⟩

/-- The completed wedge is contained in the universal prime Gaussian wedge. -/
def routeUCompletedPrimeGammaWedge.prime
    {Q : Polynomial ℝ} (t : routeUCompletedPrimeGammaWedge Q) :
    routeUPrimeGaussianWedge Q :=
  ⟨t.1, t.property.1, le_trans t.property.2 (min_le_left _ _)⟩

private theorem routeUGammaPenalty_le_quarter
    (Q : Polynomial ℝ) (t : routeUCompletedPrimeGammaWedge Q) :
    18 * routeUCompletedPrimeGammaRadius *
        (gammaHardyPhaseRate routeUCompletedPrimeGammaRadius - gammaHardyPhaseRate 0) *
        Real.sqrt (t.1 * (Q.natDegree + 1)) ≤
      gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 4 := by
  let B : ℝ := gammaHardyPhaseRate routeUCompletedPrimeGammaRadius /
    (72 * routeUCompletedPrimeGammaRadius *
      (gammaHardyPhaseRate routeUCompletedPrimeGammaRadius - gammaHardyPhaseRate 0))
  have hB : 0 < B := by
    dsimp only [B]
    exact div_pos gammaHardyPhaseRate_routeUCompletedPrimeGammaRadius_pos
      (mul_pos (mul_pos (by norm_num) routeUCompletedPrimeGammaRadius_pos)
        routeUCompletedPrimeGammaRadius_increment_pos)
  have hz : 0 ≤ t.1 * (Q.natDegree + 1) :=
    mul_nonneg t.property.1.le
      (add_nonneg (Nat.cast_nonneg Q.natDegree) zero_le_one)
  have hzle : t.1 * (Q.natDegree + 1) ≤ B ^ (2 : ℕ) := by
    calc
      t.1 * (Q.natDegree + 1) ≤ routeUCompletedPrimeGammaAperture := t.property.2
      _ ≤ routeUGammaLeakageBudget :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      _ = B ^ (2 : ℕ) := rfl
  have hsqrt : Real.sqrt (t.1 * (Q.natDegree + 1)) ≤ B := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hB.le).mp
    rw [Real.sq_sqrt hz]
    exact hzle
  calc
    18 * routeUCompletedPrimeGammaRadius *
          (gammaHardyPhaseRate routeUCompletedPrimeGammaRadius - gammaHardyPhaseRate 0) *
          Real.sqrt (t.1 * (Q.natDegree + 1)) ≤
        18 * routeUCompletedPrimeGammaRadius *
          (gammaHardyPhaseRate routeUCompletedPrimeGammaRadius - gammaHardyPhaseRate 0) * B := by
      exact mul_le_mul_of_nonneg_left hsqrt
        (mul_nonneg
          (mul_nonneg (by norm_num) routeUCompletedPrimeGammaRadius_pos.le)
          routeUCompletedPrimeGammaRadius_increment_pos.le)
    _ = gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 4 := by
      dsimp only [B]
      field_simp [routeUCompletedPrimeGammaRadius_pos.ne',
        routeUCompletedPrimeGammaRadius_increment_pos.ne']
      ring

private theorem routeUPrimeCoefficient_le_quarter
    (Q : Polynomial ℝ) (t : routeUCompletedPrimeGammaWedge Q) :
    routeUVonMangoldtSquareMass *
        Real.exp (-(Real.log 2 ^ (2 : ℕ) / (16 * t.1))) ≤
      gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 4 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogSq : 0 < Real.log 2 ^ (2 : ℕ) := sq_pos_of_pos hlog
  have hExpRaw := exp_neg_div_le_div
    (A := Real.log 2 ^ (2 : ℕ) / 16) (t := t.1) (div_pos hlogSq (by norm_num)) t.property.1
  have hExp : Real.exp (-(Real.log 2 ^ (2 : ℕ) / (16 * t.1))) ≤
      16 * t.1 / Real.log 2 ^ (2 : ℕ) := by
    convert hExpRaw using 1 <;> field_simp [hlog.ne']
  have htFactor : t.1 ≤ t.1 * (Q.natDegree + 1) := by
    have hOne : (1 : ℝ) ≤ Q.natDegree + 1 :=
      le_add_of_nonneg_left (Nat.cast_nonneg Q.natDegree)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hOne t.property.1.le
  have htBudget : t.1 ≤ routeUPrimeSuppressionBudget := by
    calc
      t.1 ≤ t.1 * (Q.natDegree + 1) := htFactor
      _ ≤ routeUCompletedPrimeGammaAperture := t.property.2
      _ ≤ routeUPrimeSuppressionBudget :=
        le_trans (min_le_right _ _) (min_le_right _ _)
  have hC : 0 ≤ routeUVonMangoldtSquareMass := routeUVonMangoldtSquareMass_nonneg
  have hCOne : 0 < routeUVonMangoldtSquareMass + 1 := by linarith
  have hLinearNonneg : 0 ≤ 16 * t.1 / Real.log 2 ^ (2 : ℕ) :=
    div_nonneg (mul_nonneg (by norm_num) t.property.1.le) hlogSq.le
  calc
    routeUVonMangoldtSquareMass *
          Real.exp (-(Real.log 2 ^ (2 : ℕ) / (16 * t.1))) ≤
        routeUVonMangoldtSquareMass * (16 * t.1 / Real.log 2 ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hExp hC
    _ ≤ (routeUVonMangoldtSquareMass + 1) *
          (16 * t.1 / Real.log 2 ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        hLinearNonneg
    _ ≤ (routeUVonMangoldtSquareMass + 1) *
          (16 * routeUPrimeSuppressionBudget / Real.log 2 ^ (2 : ℕ)) := by
      gcongr
    _ = gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 4 := by
      unfold routeUPrimeSuppressionBudget
      field_simp [hlog.ne', hCOne.ne']
      ring

/-- **Quantitative Route-U completed prime--Gamma wedge (CPGW.1 / C43-Y (24.139)).**

The exact Gamma integral dominates the literal complete absolute prime tail by a fixed positive
multiple of native mass.  The statement also covers the zero polynomial without division. -/
theorem routeUPolynomialGaussianCompletedPrimeGammaGap_ge
    (Q : Polynomial ℝ) (t : routeUCompletedPrimeGammaWedge Q) :
    gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 2 *
        routeUPolynomialGaussianMass Q t.heat ≤
      (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t.heat x‖ *
          gammaHardyPhaseRate x) -
        routeUPolynomialGaussianPrimeAbsoluteTail Q t.prime := by
  have hMass : 0 ≤ routeUPolynomialGaussianMass Q t.heat :=
    routeUPolynomialGaussianMass_nonneg Q t.heat
  have hGammaRaw :=
    integral_norm_routeUPolynomialGaussianDensity_mul_gammaHardyPhaseRate_ge
      Q t.heat
        (⟨routeUCompletedPrimeGammaRadius, routeUCompletedPrimeGammaRadius_pos.le⟩ :
          {R : ℝ // 0 ≤ R})
  have hGammaCoeff :
      3 * gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 4 ≤
        gammaHardyPhaseRate routeUCompletedPrimeGammaRadius -
          18 * routeUCompletedPrimeGammaRadius *
            (gammaHardyPhaseRate routeUCompletedPrimeGammaRadius - gammaHardyPhaseRate 0) *
            Real.sqrt (t.1 * (Q.natDegree + 1)) := by
    linarith [routeUGammaPenalty_le_quarter Q t]
  have hGamma :
      3 * gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 4 *
          routeUPolynomialGaussianMass Q t.heat ≤
        ∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t.heat x‖ *
          gammaHardyPhaseRate x := by
    refine le_trans (mul_le_mul_of_nonneg_right hGammaCoeff hMass) ?_
    simpa only [routeUCompletedPrimeGammaWedge.heat] using hGammaRaw
  have hPrimeRaw := routeUPolynomialGaussianPrimeAbsoluteTail_le Q t.prime
  have hPrime : routeUPolynomialGaussianPrimeAbsoluteTail Q t.prime ≤
      gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 4 *
        routeUPolynomialGaussianMass Q t.heat := by
    refine le_trans hPrimeRaw ?_
    calc
      routeUVonMangoldtSquareMass *
            routeUPolynomialGaussianMass Q t.prime.heat *
            Real.exp (-(Real.log 2 ^ (2 : ℕ) / (16 * t.prime.1))) =
          (routeUVonMangoldtSquareMass *
              Real.exp (-(Real.log 2 ^ (2 : ℕ) / (16 * t.1)))) *
            routeUPolynomialGaussianMass Q t.heat := by
        simp only [routeUCompletedPrimeGammaWedge.prime,
          routeUPrimeGaussianWedge.heat,
          routeUCompletedPrimeGammaWedge.heat]
        ring
      _ ≤ gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 4 *
          routeUPolynomialGaussianMass Q t.heat :=
        mul_le_mul_of_nonneg_right (routeUPrimeCoefficient_le_quarter Q t) hMass
  calc
    gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 2 *
          routeUPolynomialGaussianMass Q t.heat =
        3 * gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 4 *
            routeUPolynomialGaussianMass Q t.heat -
          gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 4 *
            routeUPolynomialGaussianMass Q t.heat := by ring
    _ ≤ (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t.heat x‖ *
          gammaHardyPhaseRate x) -
        routeUPolynomialGaussianPrimeAbsoluteTail Q t.prime :=
      sub_le_sub hGamma hPrime

/-- **Strict Route-U completed prime--Gamma wedge (CPGW.2 / C43-Y (24.139)).**

Nonzeroness of the polynomial and every analytic smallness condition are carried by input types;
the theorem has no hypotheses. -/
theorem routeUPolynomialGaussianCompletedPrimeGammaGap_pos
    (Q : {Q : Polynomial ℝ // Q ≠ 0})
    (t : routeUCompletedPrimeGammaWedge Q.1) :
    0 < (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q.1 t.heat x‖ *
          gammaHardyPhaseRate x) -
        routeUPolynomialGaussianPrimeAbsoluteTail Q.1 t.prime := by
  have hLower : 0 < gammaHardyPhaseRate routeUCompletedPrimeGammaRadius / 2 *
      routeUPolynomialGaussianMass Q.1 t.heat := by
    exact mul_pos
      (div_pos gammaHardyPhaseRate_routeUCompletedPrimeGammaRadius_pos (by norm_num))
      (routeUPolynomialGaussianMass_pos Q t.heat)
  exact lt_of_lt_of_le hLower
    (routeUPolynomialGaussianCompletedPrimeGammaGap_ge Q.1 t)

end RHTower
