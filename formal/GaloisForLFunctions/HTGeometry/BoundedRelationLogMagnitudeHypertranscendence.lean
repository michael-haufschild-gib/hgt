import GaloisForLFunctions.HTGeometry.BoundedRelationExponentialSurvival
import GaloisForLFunctions.HTGeometry.DATaylorLogRatioResonance
import GaloisForLFunctions.HTGeometry.LogSuperlacunaryDoubleExponentialFamily
import GaloisForLFunctions.HTGeometry.SuperexponentialGrowth

/-!
# Bounded-relation exponential hypertranscendence

This module closes the bounded-relation log-magnitude theorem.  Unconditional Mahler
normalization turns any nonzero complex formal differential relation into an integer relation of
positive jet degree, where bounded-relation exponential survival applies.  Superlinear
log-magnitude growth gives an infinite-radius scalar series, yielding the card's explicit entire
hypertranscendental function.
-/

open Filter PowerSeries MvPolynomial
open scoped Topology ENNReal

namespace GaloisForLFunctions

noncomputable section

/-- The exact exponential coefficient with algebraic phase `u n` and log-magnitude `b n`. -/
def boundedRelationExponentialCoeff (b : ℕ → ℝ) (u : ℕ → ℂ) (n : ℕ) : ℂ :=
  u n * Complex.exp (-(b n : ℂ))

/-- The prescribed unit phase does not change the exponential coefficient magnitude. -/
theorem norm_boundedRelationExponentialCoeff
    {b : ℕ → ℝ} {u : ℕ → ℂ} (huNorm : ∀ n, ‖u n‖ = 1) (n : ℕ) :
    ‖boundedRelationExponentialCoeff b u n‖ = Real.exp (-b n) := by
  rw [boundedRelationExponentialCoeff, norm_mul, huNorm, one_mul, Complex.norm_exp]
  simp

/-- Unit-phase exponential coefficients are nonzero. -/
theorem boundedRelationExponentialCoeff_ne_zero
    {b : ℕ → ℝ} {u : ℕ → ℂ} (huNorm : ∀ n, ‖u n‖ = 1) (n : ℕ) :
    boundedRelationExponentialCoeff b u n ≠ 0 := by
  apply mul_ne_zero
  · intro hu
    simpa [hu] using huNorm n
  · exact Complex.exp_ne_zero _

/-- Bounded-relation exponential coefficients survive every nonzero formal differential
polynomial after unconditional Mahler normalization. -/
theorem aeval_ne_zero_of_boundedRelation_exponential
    {b : ℕ → ℝ} {u : ℕ → ℂ} {F : PowerSeries ℂ}
    (hF : ∀ i, PowerSeries.coeff i F =
      u i * Complex.exp (-(b i : ℂ)))
    (hbAlg : ∀ i, IsAlgebraic ℚ (b i))
    (hconf : BoundedRelationConfinement b)
    (huAlg : ∀ i, IsAlgebraic ℚ (u i))
    (huNorm : ∀ i, ‖u i‖ = 1)
    {n : ℕ} (P : MvPolynomial (Fin (n + 2)) ℂ) (hP : P ≠ 0) :
    MvPolynomial.aeval (formalJets n F) P ≠ 0 := by
  intro hrel
  obtain ⟨n', Q, hQ, hQint, hQrel⟩ :=
    formal_mahler_integer_normalization hP hrel
  have hb : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-b i) := by
    intro i
    rw [hF, norm_mul, huNorm, one_mul, Complex.norm_exp]
    simp
  have hDpos := magnitudeMaxJetDegree_pos_of_integer_relation
    F hb Q hQ hQint hQrel
  have hu0 : ∀ i, u i ≠ 0 := by
    intro i hi
    simpa [hi] using huNorm i
  obtain ⟨N, hN⟩ := exists_coeff_ne_zero_of_boundedRelation_exponential
    hF hbAlg hconf huAlg hu0 Q hQint hDpos
  rw [hQrel, map_zero] at hN
  exact hN rfl

/-- A smooth function with the exact bounded-relation exponential Taylor coefficients is
hypertranscendental. -/
theorem hypertranscendental_of_boundedRelation_exponential_taylor
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ} {u : ℕ → ℂ}
    (hcoeff : ∀ i, PowerSeries.coeff i (taylorPS f) =
      u i * Complex.exp (-(b i : ℂ)))
    (hbAlg : ∀ i, IsAlgebraic ℚ (b i))
    (hconf : BoundedRelationConfinement b)
    (huAlg : ∀ i, IsAlgebraic ℚ (u i))
    (huNorm : ∀ i, ‖u i‖ = 1) :
    Hypertranscendental f := by
  apply hypertranscendental_of_aeval_survives hf
  intro n P hP
  exact aeval_ne_zero_of_boundedRelation_exponential
    hcoeff hbAlg hconf huAlg huNorm P hP

/-- The entire scalar-series carrier of a bounded-relation exponential coefficient family. -/
def boundedRelationExponentialFunction (b : ℕ → ℝ) (u : ℕ → ℂ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (boundedRelationExponentialCoeff b u)

/-- The analytic carrier is the card's ordinary scalar power-series sum. -/
theorem boundedRelationExponentialFunction_eq_tsum
    (b : ℕ → ℝ) (u : ℕ → ℂ) (z : ℂ) :
    boundedRelationExponentialFunction b u z =
      ∑' n, boundedRelationExponentialCoeff b u n * z ^ n := by
  simpa [boundedRelationExponentialFunction, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq
      (boundedRelationExponentialCoeff b u) z)

/-- Superlinear log-magnitude growth gives infinite convergence radius. -/
theorem boundedRelationExponentialSeries_radius_eq_top
    {b : ℕ → ℝ} {u : ℕ → ℂ}
    (hgrowth : Tendsto (fun n => b n / (n : ℝ)) atTop atTop)
    (huNorm : ∀ n, ‖u n‖ = 1) :
    (FormalMultilinearSeries.ofScalars ℂ
      (boundedRelationExponentialCoeff b u)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  by_cases hr : r = 0
  · subst r
    apply summable_of_hasFiniteSupport
    refine (Set.finite_singleton 0).subset ?_
    intro n hn
    simp only [Function.mem_support] at hn
    have hn0 : n = 0 := by
      by_contra hn0
      exact hn (by simp [hn0])
    simp [hn0]
  · have hrpos : 0 < (r : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
    simpa [FormalMultilinearSeries.ofScalars_norm,
      norm_boundedRelationExponentialCoeff huNorm,
      Real.norm_of_nonneg (Real.exp_nonneg _)] using
      (summable_exp_neg_mul_pow hgrowth hrpos)

/-- The bounded-relation exponential scalar series is entire. -/
theorem contDiff_boundedRelationExponentialFunction
    {b : ℕ → ℝ} {u : ℕ → ℂ}
    (hgrowth : Tendsto (fun n => b n / (n : ℝ)) atTop atTop)
    (huNorm : ∀ n, ‖u n‖ = 1) :
    ContDiff ℂ (⊤ : ℕ∞) (boundedRelationExponentialFunction b u) := by
  let p := FormalMultilinearSeries.ofScalars ℂ
    (boundedRelationExponentialCoeff b u)
  have hr : p.radius = ⊤ :=
    boundedRelationExponentialSeries_radius_eq_top hgrowth huNorm
  have hp : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by rw [hr]; simp)
  have ha : AnalyticOnNhd ℂ p.sum Set.univ := by
    simpa [hr] using hp.analyticOnNhd
  exact ha.contDiff

/-- The entire carrier has exactly the prescribed Taylor coefficients. -/
theorem taylorPS_boundedRelationExponentialFunction
    {b : ℕ → ℝ} {u : ℕ → ℂ}
    (hgrowth : Tendsto (fun n => b n / (n : ℝ)) atTop atTop)
    (huNorm : ∀ n, ‖u n‖ = 1) (n : ℕ) :
    PowerSeries.coeff n (taylorPS (boundedRelationExponentialFunction b u)) =
      boundedRelationExponentialCoeff b u n := by
  exact taylorPS_ofScalarsSum_of_radius_eq_top
    (boundedRelationExponentialCoeff b u)
    (boundedRelationExponentialSeries_radius_eq_top hgrowth huNorm) n

/-- The realized entire series has full Taylor support. -/
theorem taylorPS_boundedRelationExponentialFunction_coeff_ne_zero
    {b : ℕ → ℝ} {u : ℕ → ℂ}
    (hgrowth : Tendsto (fun n => b n / (n : ℝ)) atTop atTop)
    (huNorm : ∀ n, ‖u n‖ = 1) (n : ℕ) :
    PowerSeries.coeff n (taylorPS (boundedRelationExponentialFunction b u)) ≠ 0 := by
  rw [taylorPS_boundedRelationExponentialFunction hgrowth huNorm]
  exact boundedRelationExponentialCoeff_ne_zero huNorm n

/-- The card's entire bounded-relation log-magnitude series is hypertranscendental. -/
theorem hypertranscendental_boundedRelationExponentialFunction
    {b : ℕ → ℝ} {u : ℕ → ℂ}
    (_hbpos : ∀ n, 0 < b n)
    (hgrowth : Tendsto (fun n => b n / (n : ℝ)) atTop atTop)
    (hbAlg : ∀ n, IsAlgebraic ℚ (b n))
    (hconf : BoundedRelationConfinement b)
    (huAlg : ∀ n, IsAlgebraic ℚ (u n))
    (huNorm : ∀ n, ‖u n‖ = 1) :
    Hypertranscendental (boundedRelationExponentialFunction b u) := by
  apply hypertranscendental_of_boundedRelation_exponential_taylor
    (contDiff_boundedRelationExponentialFunction hgrowth huNorm)
    (b := b) (u := u)
  · intro n
    rw [taylorPS_boundedRelationExponentialFunction hgrowth huNorm]
    rfl
  · exact hbAlg
  · exact hconf
  · exact huAlg
  · exact huNorm

end

end GaloisForLFunctions
