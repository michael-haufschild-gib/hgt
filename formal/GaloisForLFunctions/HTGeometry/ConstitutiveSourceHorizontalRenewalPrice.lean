import GaloisForLFunctions.HTGeometry.ConstitutiveExtendedRenewalActionThreshold
import GaloisForLFunctions.HTGeometry.ConstitutiveSourceHorizontalGlobalRenewal

/-!
# Source-horizontal renewal price

This module specializes the local renewal wall to exact forward and reverse abelian apertures.
It proves the orientation-resolved coefficients and infinite total KL action without a finite-KL
premise on individual renewals.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real InformationTheory Set Filter Topology
open scoped ENNReal Topology
open _root_.RHTower

noncomputable section

/-- Exact forward orientation price: coefficient `c(2-a)/(2a)` and infinite total KL action. -/
theorem sourceHorizontalForward_orientationRenewalPrice
    (p : Nat.Primes) {a c : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hc : 0 < c)
    (nu : ℕ → Measure AbelianZetaGroupClass)
    (hnu : ∀ n, IsProbabilityMeasure (nu n))
    (hcurrent : ∀ n, c ≤
      (nu n).real (sourceHorizontalClassAperture p n) *
        sourceHorizontalPrimeAdaptiveJeffreysWork p (((n + 1 : ℕ) : ℝ) * a)) :
    ((c * (2 - a) / (2 * a) : ℝ) : EReal) ≤
        liminf (fun n =>
          ((klDiv (nu n)
            (classLaw
              (sourceHorizontalAbelianForwardParameters a ha0.le ha1).toAbelianZetaParameters) :
                ℝ≥0∞) : EReal)) atTop ∧
      ∑' n, klDiv (nu n)
        (classLaw
          (sourceHorizontalAbelianForwardParameters a ha0.le ha1).toAbelianZetaParameters) = ⊤ := by
  let theta := sourceHorizontalAbelianForwardParameters a ha0.le ha1
  let mu : ℕ → Measure AbelianZetaGroupClass := fun _ => classLaw theta.toAbelianZetaParameters
  let A : ℕ → Set AbelianZetaGroupClass := sourceHorizontalClassAperture p
  let W : ℕ → ℝ := fun n =>
    sourceHorizontalPrimeAdaptiveJeffreysWork p (((n + 1 : ℕ) : ℝ) * a)
  let C : ℝ := 2 * theta.ennNormalizer.toReal
  let beta : ℝ := (2 - a) * Real.log (p : ℝ)
  let K : ℝ := 2 * a * Real.log (p : ℝ)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hmu : ∀ n, IsProbabilityMeasure (mu n) := fun _ => inferInstance
  have hnormalizer : 0 < theta.ennNormalizer.toReal := ENNReal.toReal_pos
    (AbelianZetaConvergentParameters.ennNormalizer_ne_zero _)
    (ennNormalizer_ne_top _)
  have hC : 0 < C := mul_pos (by linarith) hnormalizer
  have hbeta : 0 < beta := mul_pos (by linarith) hlogp
  have hK : 0 < K := mul_pos (mul_pos (by linarith) ha0) hlogp
  have hmass : ∀ n, (mu n).real (A n) ≤
      C * Real.exp (-beta * ((n + 1 : ℕ) : ℝ)) := by
    intro n
    simpa [mu, A, C, beta, theta] using
      sourceHorizontalForwardClassAperture_real_le p n ha0.le ha1
  have hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ (1 : ℝ) := by
    intro n
    have h := sourceHorizontalPrimeAdaptiveJeffreysWork_le_linear p
      (u := ((n + 1 : ℕ) : ℝ) * a) (mul_nonneg (by positivity) ha0.le)
    rw [Real.rpow_one]
    dsimp [W, K]
    calc
      sourceHorizontalPrimeAdaptiveJeffreysWork p (((n + 1 : ℕ) : ℝ) * a) ≤
          2 * (((n + 1 : ℕ) : ℝ) * a) * Real.log (p : ℝ) := h
      _ = 2 * a * Real.log (p : ℝ) * ((n + 1 : ℕ) : ℝ) := by ring
  have hcurrent' : ∀ n, c ≤ (nu n).real (A n) * W n := by
    simpa [A, W] using hcurrent
  have hlim := exponentialAperture_polynomialCurrent_action_liminf_ennreal
    mu nu hmu hnu A (fun n => measurableSet_sourceHorizontalClassAperture p n)
    W C beta K c 1 hC hbeta hK hc hmass hwork hcurrent'
  have hsum := exponentialAperture_polynomialCurrent_action_eq_top_of_degree_le_two
    mu nu hmu hnu A (fun n => measurableSet_sourceHorizontalClassAperture p n)
    W C beta K c 1 hC hbeta hK hc hmass hwork hcurrent' (by linarith)
  have hcoeff : c * beta / K = c * (2 - a) / (2 * a) := by
    dsimp [beta, K]
    field_simp [ha0.ne', hlogp.ne']
  constructor
  · rw [hcoeff] at hlim
    simpa [mu] using hlim
  · simpa [mu] using hsum

/-- Exact reverse orientation price: coefficient `c/a` and infinite total KL action. -/
theorem sourceHorizontalReverse_orientationRenewalPrice
    (p : Nat.Primes) {a c : ℝ} (ha0 : 0 < a) (hc : 0 < c)
    (nu : ℕ → Measure AbelianZetaGroupClass)
    (hnu : ∀ n, IsProbabilityMeasure (nu n))
    (hcurrent : ∀ n, c ≤
      (nu n).real (sourceHorizontalClassAperture p n) *
        sourceHorizontalPrimeAdaptiveJeffreysWork p (((n + 1 : ℕ) : ℝ) * a)) :
    ((c / a : ℝ) : EReal) ≤
        liminf (fun n =>
          ((klDiv (nu n)
            (classLaw
              (sourceHorizontalAbelianReverseParameters a ha0.le).toAbelianZetaParameters) :
                ℝ≥0∞) : EReal)) atTop ∧
      ∑' n, klDiv (nu n)
        (classLaw
          (sourceHorizontalAbelianReverseParameters a ha0.le).toAbelianZetaParameters) = ⊤ := by
  let theta := sourceHorizontalAbelianReverseParameters a ha0.le
  let mu : ℕ → Measure AbelianZetaGroupClass := fun _ => classLaw theta.toAbelianZetaParameters
  let A : ℕ → Set AbelianZetaGroupClass := sourceHorizontalClassAperture p
  let W : ℕ → ℝ := fun n =>
    sourceHorizontalPrimeAdaptiveJeffreysWork p (((n + 1 : ℕ) : ℝ) * a)
  let C : ℝ := 2 * theta.ennNormalizer.toReal
  let beta : ℝ := 2 * Real.log (p : ℝ)
  let K : ℝ := 2 * a * Real.log (p : ℝ)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hmu : ∀ n, IsProbabilityMeasure (mu n) := fun _ => inferInstance
  have hnormalizer : 0 < theta.ennNormalizer.toReal := ENNReal.toReal_pos
    (AbelianZetaConvergentParameters.ennNormalizer_ne_zero _)
    (ennNormalizer_ne_top _)
  have hC : 0 < C := mul_pos (by linarith) hnormalizer
  have hbeta : 0 < beta := mul_pos (by linarith) hlogp
  have hK : 0 < K := mul_pos (mul_pos (by linarith) ha0) hlogp
  have hmass : ∀ n, (mu n).real (A n) ≤
      C * Real.exp (-beta * ((n + 1 : ℕ) : ℝ)) := by
    intro n
    simpa [mu, A, C, beta, theta] using
      sourceHorizontalReverseClassAperture_real_le p n ha0.le
  have hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ (1 : ℝ) := by
    intro n
    have h := sourceHorizontalPrimeAdaptiveJeffreysWork_le_linear p
      (u := ((n + 1 : ℕ) : ℝ) * a) (mul_nonneg (by positivity) ha0.le)
    rw [Real.rpow_one]
    dsimp [W, K]
    calc
      sourceHorizontalPrimeAdaptiveJeffreysWork p (((n + 1 : ℕ) : ℝ) * a) ≤
          2 * (((n + 1 : ℕ) : ℝ) * a) * Real.log (p : ℝ) := h
      _ = 2 * a * Real.log (p : ℝ) * ((n + 1 : ℕ) : ℝ) := by ring
  have hcurrent' : ∀ n, c ≤ (nu n).real (A n) * W n := by
    simpa [A, W] using hcurrent
  have hlim := exponentialAperture_polynomialCurrent_action_liminf_ennreal
    mu nu hmu hnu A (fun n => measurableSet_sourceHorizontalClassAperture p n)
    W C beta K c 1 hC hbeta hK hc hmass hwork hcurrent'
  have hsum := exponentialAperture_polynomialCurrent_action_eq_top_of_degree_le_two
    mu nu hmu hnu A (fun n => measurableSet_sourceHorizontalClassAperture p n)
    W C beta K c 1 hC hbeta hK hc hmass hwork hcurrent' (by linarith)
  have hcoeff : c * beta / K = c / a := by
    dsimp [beta, K]
    field_simp [ha0.ne', hlogp.ne']
  constructor
  · rw [hcoeff] at hlim
    simpa [mu] using hlim
  · simpa [mu] using hsum

end

end GaloisForLFunctions.HTGeometry
