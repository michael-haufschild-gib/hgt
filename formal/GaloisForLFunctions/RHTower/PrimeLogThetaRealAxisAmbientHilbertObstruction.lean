import GaloisForLFunctions.RHTower.PrimeLogThetaStripReporterBoundary
import GaloisForLFunctions.RHTower.PrimeLogThetaLowerClosedGraphLanding
import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeShiftJet
import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
# Real-axis ambient-Hilbert obstruction for the prime-log theta graph

The literal prime-log theta coefficient on the real axis has squared mass
`4 log(p)^4 / p`, which is not summable.  This file proves the stronger obstruction
needed for Route P's actual closed-graph problem.  It is not enough to observe that the
coefficient is not a source vector: a continuous functional on an ambient
source/output Hilbert product could in principle combine a source vector with a Hilbert-output
reader of the Laplace feature.

For the literal feature, however, the output reader divided by the real-axis coefficient has
squared norm at most `‖b‖² / (4 log(p)^3)` and therefore vanishes along the cofinite prime
filter.  A source vector plus such a relatively negligible term cannot equal the literal
reporter, because it would force a nonsummable lower bound on an `ℓ²` source vector.

Thus no ambient continuous Hilbert source/output functional realizes literal real-axis theta
evaluation on every finite-prime coordinate.  This does not rule out the required Route P
Calderón/distributional boundary morphism; it identifies its non-Hilbert necessity exactly.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal InnerProduct LinearPMap

namespace RHTower

noncomputable section

/-- The literal critical Laplace feature has exactly the critical prime mass as its squared
half-line Hilbert norm. -/
theorem norm_sq_primeLogCriticalLaplaceFeatureL2 (p : Nat.Primes) :
    ‖primeLogCriticalLaplaceFeatureL2 p‖ ^ 2 = Real.log (p : ℝ) / (p : ℝ) := by
  have hf : MemLp (primeLogCriticalLaplaceFeatureC p) 2
      (volume.restrict (Ioi (0 : ℝ))) :=
    (memLp_two_iff_integrable_sq_norm
      (continuous_primeLogCriticalLaplaceFeatureC p).aestronglyMeasurable.restrict).2
      (integrableOn_norm_sq_primeLogCriticalLaplaceFeatureC p)
  rw [primeLogCriticalLaplaceFeatureL2, Lp.norm_toLp]
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (f := primeLogCriticalLaplaceFeatureC p)
    (by norm_num) (by norm_num) hf]
  norm_num
  rw [show (∫ (a : ℝ), ‖primeLogCriticalLaplaceFeatureC p a‖ ^ 2 ∂volume.restrict (Ioi 0)) =
      ∫ a : ℝ in Ioi 0, primeLogCriticalLaplaceFeature p a ^ 2 by
    apply integral_congr_ae
    filter_upwards with a
    rw [primeLogCriticalLaplaceFeatureC, Complex.norm_real, Real.norm_eq_abs]
    rw [sq_abs]
  , integral_primeLogCriticalLaplaceFeature_sq]
  have hnonneg : 0 ≤ Real.log (p : ℝ) / (p : ℝ) := by positivity
  rw [ENNReal.toReal_ofReal]
  · rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]
  · positivity

/-- A real-axis reporter cannot be decomposed into a source-Hilbert vector plus a term that is
asymptotically negligible relative to its literal coefficient. -/
theorem no_source_plus_relative_negligible_primeLogTheta_realAxis
    (x : ℝ) (a o : Nat.Primes → ℂ)
    (ha : Memℓp a 2)
    (heq : ∀ p : Nat.Primes,
      primeLogThetaStripRealAxisReporter x p = a p + o p)
    (ho : Tendsto (fun p : Nat.Primes =>
      o p / primeLogThetaStripRealAxisReporter x p) cofinite (nhds 0)) : False := by
  have hsmall : ∀ᶠ p : Nat.Primes in cofinite,
      ‖o p / primeLogThetaStripRealAxisReporter x p‖ < (1 / 2 : ℝ) := by
    have hzero : Tendsto (fun p : Nat.Primes =>
        ‖o p / primeLogThetaStripRealAxisReporter x p‖) cofinite (nhds 0) := by
      simpa using ho.norm
    exact hzero.eventually_lt_const (by norm_num)
  have hbound : ∀ᶠ p : Nat.Primes in cofinite,
      ‖primeLogThetaStripRealAxisReporter x p‖ ^ 2 ≤ 4 * ‖a p‖ ^ 2 := by
    filter_upwards [hsmall] with p hp
    have hlog : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.2.one_lt)
    have hreportSq : 0 < ‖primeLogThetaStripRealAxisReporter x p‖ ^ 2 := by
      rw [norm_sq_primeLogThetaStripRealAxisReporter]
      have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
      positivity
    have hreportNe : primeLogThetaStripRealAxisReporter x p ≠ 0 := by
      intro hzero
      rw [hzero] at hreportSq
      norm_num at hreportSq
    have hreportPos : 0 < ‖primeLogThetaStripRealAxisReporter x p‖ :=
      norm_pos_iff.mpr hreportNe
    have hdiv : ‖o p‖ / ‖primeLogThetaStripRealAxisReporter x p‖ < 1 / 2 := by
      simpa only [norm_div] using hp
    have hoBound : ‖o p‖ < ‖primeLogThetaStripRealAxisReporter x p‖ / 2 := by
      have h := (div_lt_iff₀ hreportPos).mp hdiv
      nlinarith
    have htriangle : ‖primeLogThetaStripRealAxisReporter x p‖ ≤ ‖a p‖ + ‖o p‖ := by
      rw [heq p]
      exact norm_add_le _ _
    have haLower : ‖primeLogThetaStripRealAxisReporter x p‖ / 2 < ‖a p‖ := by
      linarith
    have haNonneg : 0 ≤ ‖a p‖ := norm_nonneg _
    nlinarith
  have hsumA : Summable (fun p : Nat.Primes => ‖a p‖ ^ 2) :=
    HTGeometry.ConstraintMotiveRelativity.memℓp_two_iff.mp ha
  have hsumFourA : Summable (fun p : Nat.Primes => 4 * ‖a p‖ ^ 2) :=
    hsumA.mul_left 4
  have hbad : {p : Nat.Primes |
      ¬ ‖primeLogThetaStripRealAxisReporter x p‖ ^ 2 ≤ 4 * ‖a p‖ ^ 2}.Finite :=
    Filter.eventually_cofinite.mp hbound
  let F : Finset Nat.Primes := hbad.toFinset
  let Fset : Set Nat.Primes := ↑F
  have htail : Summable (fun p : (Fsetᶜ : Set Nat.Primes) =>
      ‖primeLogThetaStripRealAxisReporter x p.1‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun p => sq_nonneg _)
      (fun p => ?_) (hsumFourA.subtype _)
    by_contra hnot
    apply p.2
    change p.1 ∈ F
    exact hbad.mem_toFinset.mpr hnot
  apply not_summable_norm_sq_primeLogThetaStripRealAxisReporter x
  apply Summable.add_compl (s := Fset) Summable.of_finite
  change Summable (fun p : (Fsetᶜ : Set Nat.Primes) =>
    ‖primeLogThetaStripRealAxisReporter x (p : Nat.Primes)‖ ^ 2)
  exact htail

/-- Any bounded Hilbert output reader applied to the literal Laplace feature is negligible
relative to the real-axis theta coefficient. -/
theorem tendsto_hilbertOutput_relative_primeLogTheta_realAxis_zero
    (x : ℝ) (b : primeLogCriticalHalfLineL2) :
    Tendsto (fun p : Nat.Primes =>
      inner ℂ b (primeLogCriticalLaplaceFeatureL2 p) /
        primeLogThetaStripRealAxisReporter x p) cofinite (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hbound : ∀ p : Nat.Primes,
      ‖inner ℂ b (primeLogCriticalLaplaceFeatureL2 p) /
        primeLogThetaStripRealAxisReporter x p‖ ^ 2 ≤
        ‖b‖ ^ 2 / (4 * Real.log (p : ℝ) ^ 3) := by
    intro p
    have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
    have hlog : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.2.one_lt)
    have hreportSq : 0 < ‖primeLogThetaStripRealAxisReporter x p‖ ^ 2 := by
      rw [norm_sq_primeLogThetaStripRealAxisReporter]
      positivity
    have hinner := norm_inner_le_norm (𝕜 := ℂ) b
      (primeLogCriticalLaplaceFeatureL2 p)
    have hinnerSq : ‖inner ℂ b (primeLogCriticalLaplaceFeatureL2 p)‖ ^ 2 ≤
        (‖b‖ * ‖primeLogCriticalLaplaceFeatureL2 p‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
    calc
      ‖inner ℂ b (primeLogCriticalLaplaceFeatureL2 p) /
          primeLogThetaStripRealAxisReporter x p‖ ^ 2 =
          ‖inner ℂ b (primeLogCriticalLaplaceFeatureL2 p)‖ ^ 2 /
            ‖primeLogThetaStripRealAxisReporter x p‖ ^ 2 := by
              rw [norm_div]
              ring
      _ ≤ (‖b‖ * ‖primeLogCriticalLaplaceFeatureL2 p‖) ^ 2 /
            ‖primeLogThetaStripRealAxisReporter x p‖ ^ 2 :=
          div_le_div_of_nonneg_right hinnerSq hreportSq.le
      _ = ‖b‖ ^ 2 / (4 * Real.log (p : ℝ) ^ 3) := by
          rw [show (‖b‖ * ‖primeLogCriticalLaplaceFeatureL2 p‖) ^ 2 =
              ‖b‖ ^ 2 * ‖primeLogCriticalLaplaceFeatureL2 p‖ ^ 2 by ring,
            norm_sq_primeLogCriticalLaplaceFeatureL2,
            norm_sq_primeLogThetaStripRealAxisReporter]
          field_simp [hp.ne', hlog.ne']
  have hlogTop : Tendsto (fun p : Nat.Primes => Real.log (p : ℝ))
      cofinite atTop :=
    GaloisForLFunctions.HTGeometry.tendsto_primeRealLog_cofinite_atTop
  have hinv : Tendsto (fun p : Nat.Primes => (Real.log (p : ℝ))⁻¹)
      cofinite (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlogTop
  have hdecay : Tendsto (fun p : Nat.Primes =>
      ‖b‖ ^ 2 / (4 * Real.log (p : ℝ) ^ 3)) cofinite (nhds 0) := by
    have hraw := (hinv.pow 3).const_mul (‖b‖ ^ 2 / 4)
    have hrawZero : Tendsto (fun p : Nat.Primes =>
        ‖b‖ ^ 2 / 4 * (Real.log (p : ℝ))⁻¹ ^ 3) cofinite (nhds 0) := by
      simpa using hraw
    apply hrawZero.congr'
    filter_upwards with p
    have hlog : Real.log (p : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
    field_simp [hlog]
  have hsquare : Tendsto (fun p : Nat.Primes =>
      ‖inner ℂ b (primeLogCriticalLaplaceFeatureL2 p) /
        primeLogThetaStripRealAxisReporter x p‖ ^ 2) cofinite (nhds 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hbound hdecay
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsquare
  have hsqrt' : Tendsto (fun p : Nat.Primes =>
      √(‖inner ℂ b (primeLogCriticalLaplaceFeatureL2 p) /
        primeLogThetaStripRealAxisReporter x p‖ ^ 2)) cofinite (nhds 0) := by
    have hfun : (fun p : Nat.Primes =>
        √(‖inner ℂ b (primeLogCriticalLaplaceFeatureL2 p) /
          primeLogThetaStripRealAxisReporter x p‖ ^ 2)) =
        (fun u : ℝ => √u) ∘ (fun p : Nat.Primes =>
          ‖inner ℂ b (primeLogCriticalLaplaceFeatureL2 p) /
            primeLogThetaStripRealAxisReporter x p‖ ^ 2) := by
      rfl
    rw [hfun]
    simpa only [Real.sqrt_zero] using hsqrt
  simpa only [Function.comp_apply, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsqrt'

/-- No ambient Hilbert source/output functional can recover the literal real-axis theta
reporter on all finite prime coordinates. -/
theorem no_ambientHilbertSourceOutput_primeLogTheta_realAxis
    (x : ℝ) (a : primeLogCriticalSourceL2) (b : primeLogCriticalHalfLineL2) :
    ¬ ∀ p : Nat.Primes,
      primeLogThetaStripRealAxisReporter x p =
        (a : Nat.Primes → ℂ) p + inner ℂ b (primeLogCriticalLaplaceFeatureL2 p) := by
  intro hfactor
  exact no_source_plus_relative_negligible_primeLogTheta_realAxis x
    (a : Nat.Primes → ℂ)
    (fun p => inner ℂ b (primeLogCriticalLaplaceFeatureL2 p)) a.2 hfactor
    (tendsto_hilbertOutput_relative_primeLogTheta_realAxis_zero x b)

/-- The literal one-prime vector belongs to the finite core of the critical Laplace synthesis. -/
def primeLogCriticalLaplacePrimeCore (p : Nat.Primes) :
    primeLogCriticalLaplaceSynthesis.domain :=
  ⟨HTGeometry.ConstraintMotiveRelativity.srcBasis p, by
    refine ⟨Finsupp.single p (1 : ℂ), ?_⟩
    rw [HTGeometry.ConstraintMotiveRelativity.srcEmb_single]
    simp⟩

/-- The synthesis of the literal one-prime core is its literal critical Laplace feature. -/
theorem primeLogCriticalLaplacePrimeCore_output (p : Nat.Primes) :
    primeLogCriticalLaplaceSynthesis (primeLogCriticalLaplacePrimeCore p) =
      primeLogCriticalLaplaceFeatureL2 p := by
  let hmem : HTGeometry.ConstraintMotiveRelativity.srcEmb (Finsupp.single p (1 : ℂ)) ∈
      LinearMap.range (HTGeometry.ConstraintMotiveRelativity.srcEmb (P := Nat.Primes)) :=
    ⟨Finsupp.single p (1 : ℂ), rfl⟩
  let q : primeLogCriticalLaplaceSynthesis.domain :=
    ⟨HTGeometry.ConstraintMotiveRelativity.srcEmb (Finsupp.single p (1 : ℂ)), hmem⟩
  have hq : q = primeLogCriticalLaplacePrimeCore p := by
    apply Subtype.ext
    change HTGeometry.ConstraintMotiveRelativity.srcEmb (Finsupp.single p (1 : ℂ)) =
      HTGeometry.ConstraintMotiveRelativity.srcBasis p
    rw [HTGeometry.ConstraintMotiveRelativity.srcEmb_single]
    simp
  rw [← hq]
  rw [primeLogCriticalLaplaceSynthesis_apply (Finsupp.single p (1 : ℂ)) hmem]
  rw [primeLogCriticalLaplaceMass_eq_sum]
  simp

/-- The literal one-prime graph point survives in the closed critical Laplace graph. -/
def primeLogCriticalLaplacePrimeGraphPoint (p : Nat.Primes) :
    primeLogCriticalLaplaceSynthesis.closure.graph :=
  primeLogCriticalLaplaceClosureCorePoint (primeLogCriticalLaplacePrimeCore p)

/-- The ambient coordinates of the literal one-prime closed-graph point. -/
theorem primeLogCriticalLaplacePrimeGraphPoint_val (p : Nat.Primes) :
    (primeLogCriticalLaplacePrimeGraphPoint p).1 =
      (HTGeometry.ConstraintMotiveRelativity.srcBasis p,
        primeLogCriticalLaplaceFeatureL2 p) := by
  change (HTGeometry.ConstraintMotiveRelativity.srcBasis p,
    primeLogCriticalLaplaceSynthesis (primeLogCriticalLaplacePrimeCore p)) = _
  rw [primeLogCriticalLaplacePrimeCore_output]

/-- **Continuous closed-graph no-go on the literal real axis.**

Every continuous complex-linear reader of the actual closed critical-Laplace graph extends to
the ambient Banach product by Hahn--Banach.  Restricting that extension to each coordinate axis
and applying Riesz separately produces precisely the source/output representation ruled out by
`no_ambientHilbertSourceOutput_primeLogTheta_realAxis`.  Consequently no such reader can recover
the literal real-axis theta reporter on all literal one-prime graph points.

The product is deliberately treated as a Banach product here, not falsely as a Hilbert product.
This is the full obstruction class of ordinary continuous graph readers; any surviving Route P
boundary object must leave this category (for example through a genuinely distributional or
Calderón-type boundary construction). -/
theorem no_continuousClosedGraphReader_primeLogTheta_realAxis
    (x : ℝ) (F : StrongDual ℂ primeLogCriticalLaplaceSynthesis.closure.graph) :
    ¬ ∀ p : Nat.Primes,
      F (primeLogCriticalLaplacePrimeGraphPoint p) =
        primeLogThetaStripRealAxisReporter x p := by
  intro hF
  obtain ⟨G, hG⟩ := StrongDual.exists_extension
    primeLogCriticalLaplaceSynthesis.closure.graph F
  let Gsrc : StrongDual ℂ primeLogCriticalSourceL2 :=
    G.comp (ContinuousLinearMap.inl ℂ primeLogCriticalSourceL2
      primeLogCriticalHalfLineL2)
  let Gout : StrongDual ℂ primeLogCriticalHalfLineL2 :=
    G.comp (ContinuousLinearMap.inr ℂ primeLogCriticalSourceL2
      primeLogCriticalHalfLineL2)
  let u : primeLogCriticalSourceL2 :=
    (InnerProductSpace.toDual ℂ primeLogCriticalSourceL2).symm Gsrc
  let b : primeLogCriticalHalfLineL2 :=
    (InnerProductSpace.toDual ℂ primeLogCriticalHalfLineL2).symm Gout
  let hu : Summable (fun p : Nat.Primes => ‖(u : Nat.Primes → ℂ) p‖ ^ 2) :=
    HTGeometry.ConstraintMotiveRelativity.memℓp_two_iff.mp u.2
  apply no_ambientHilbertSourceOutput_primeLogTheta_realAxis x
    (HTGeometry.ConstraintMotiveRelativity.portVec
      (fun p => (u : Nat.Primes → ℂ) p) hu) b
  intro p
  have hpair (s : primeLogCriticalSourceL2) (y : primeLogCriticalHalfLineL2) :
      G (s, y) = Gsrc s + Gout y := by
    change G (s, y) = G (s, 0) + G (0, y)
    rw [show (s, y) = (s, 0) + (0, y) by ext <;> simp, map_add]
  have hsrc (s : primeLogCriticalSourceL2) :
      Gsrc s = inner ℂ u s := by
    dsimp [u]
    rw [InnerProductSpace.toDual_symm_apply]
  have hout (y : primeLogCriticalHalfLineL2) :
      Gout y = inner ℂ b y := by
    dsimp [b]
    rw [InnerProductSpace.toDual_symm_apply]
  have hsource :
      inner ℂ u (HTGeometry.ConstraintMotiveRelativity.srcBasis p) =
        (starRingEnd ℂ) ((u : Nat.Primes → ℂ) p) := by
    rw [HTGeometry.ConstraintMotiveRelativity.srcBasis]
    rw [lp.inner_single_right]
    simp
  calc
    primeLogThetaStripRealAxisReporter x p =
        F (primeLogCriticalLaplacePrimeGraphPoint p) := (hF p).symm
    _ = G (primeLogCriticalLaplacePrimeGraphPoint p).1 := (hG _).symm
    _ = G (HTGeometry.ConstraintMotiveRelativity.srcBasis p,
        primeLogCriticalLaplaceFeatureL2 p) := by
      rw [primeLogCriticalLaplacePrimeGraphPoint_val]
    _ = Gsrc (HTGeometry.ConstraintMotiveRelativity.srcBasis p) +
        Gout (primeLogCriticalLaplaceFeatureL2 p) := hpair _ _
    _ = inner ℂ u (HTGeometry.ConstraintMotiveRelativity.srcBasis p) +
        inner ℂ b (primeLogCriticalLaplaceFeatureL2 p) := by rw [hsrc, hout]
    _ = (starRingEnd ℂ) ((u : Nat.Primes → ℂ) p) +
        inner ℂ b (primeLogCriticalLaplaceFeatureL2 p) := by rw [hsource]
    _ = (HTGeometry.ConstraintMotiveRelativity.portVec
          (fun p => (u : Nat.Primes → ℂ) p) hu : Nat.Primes → ℂ) p +
        inner ℂ b (primeLogCriticalLaplaceFeatureL2 p) := by
      rw [HTGeometry.ConstraintMotiveRelativity.portVec_apply]

end

end RHTower
