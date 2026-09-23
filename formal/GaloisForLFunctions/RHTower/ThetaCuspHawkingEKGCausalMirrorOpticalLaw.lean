import GaloisForLFunctions.RHTower.ThetaCuspHawkingEKGNonlinearTailSignNoGo
import GaloisForLFunctions.RHTower.ThetaCuspTiltedSchwartz
import GaloisForLFunctions.HTGeometry.ReflectionSplitIntegral
import GaloisForLFunctions.HTGeometry.BlockWindowFubini

/-!
# Causal-mirror optical law for the tilted theta EKG tail

The Bizoń--Chmaj--Rostworowski spherical Einstein--Klein--Gordon tail is causal: its
quadratic Einstein memory integrates derivative energy from retarded time `s` toward future
null infinity.  For the exponentially tilted theta packet this file also defines the advanced
time-reversed functional.  Theta reflection exchanges tilt `a` with `-a` and exchanges those
two causal orderings.

The resulting exact optical law is

`Gamma_R(a) + Gamma_R(-a)
    = -32 pi (integral k_a) (integral (k_a')^(2 : ℕ)) < 0`.

Thus genuine EKG dynamics fixes the entire reflection-even component of the cubic response in
the negative chamber.  Only the reflection-odd causal anomaly can distinguish a tilted sector
from its mirror.  KMS/passivity alone cannot reverse this coefficient-level conclusion.

`[SCOPE]` As in `ThetaCuspHawkingEKGNonlinearTailSignNoGo`, Lean formalizes the exact BCR
coefficient functional after inserting the theta packet.  It does not claim a Schwarzschild
or second-order Teukolsky coefficient identification.
-/

open MeasureTheory Set Filter Topology
open scoped SchwartzMap

noncomputable section

namespace RHTower

/-- Positive quadratic derivative-energy density of the tilted outgoing EKG generator. -/
def thetaCuspTiltedEKGDerivativeEnergyDensity (a u : ℝ) : ℝ :=
  deriv (thetaCuspTiltedSource a) u ^ (2 : ℕ)

/-- Retarded Einstein memory: derivative energy to the causal future of `s`. -/
def thetaCuspTiltedEKGRetardedDerivativeEnergy (a s : ℝ) : ℝ :=
  ∫ u in Ioi s, thetaCuspTiltedEKGDerivativeEnergyDensity a u

/-- Advanced/time-reversed Einstein memory: derivative energy to the causal past of `s`. -/
def thetaCuspTiltedEKGAdvancedDerivativeEnergy (a s : ℝ) : ℝ :=
  ∫ u in Iio s, thetaCuspTiltedEKGDerivativeEnergyDensity a u

/-- Ordered retarded theta/Einstein coupling mass. -/
def thetaCuspTiltedEKGRetardedTailMass (a : ℝ) : ℝ :=
  ∫ s : ℝ, thetaCuspTiltedSource a s *
    thetaCuspTiltedEKGRetardedDerivativeEnergy a s

/-- Ordered advanced theta/Einstein coupling mass. -/
def thetaCuspTiltedEKGAdvancedTailMass (a : ℝ) : ℝ :=
  ∫ s : ℝ, thetaCuspTiltedSource a s *
    thetaCuspTiltedEKGAdvancedDerivativeEnergy a s

/-- Retarded BCR cubic coefficient for the tilted theta packet. -/
def thetaCuspTiltedEKGRetardedTailCoefficient (a : ℝ) : ℝ :=
  (-32 * Real.pi) * thetaCuspTiltedEKGRetardedTailMass a

/-- Advanced/time-reversed BCR cubic coefficient for the tilted theta packet. -/
def thetaCuspTiltedEKGAdvancedTailCoefficient (a : ℝ) : ℝ :=
  (-32 * Real.pi) * thetaCuspTiltedEKGAdvancedTailMass a

/-- Reflection exchanges theta tilt with retarded-time reversal. -/
theorem thetaCuspTiltedSource_neg_tilt (a x : ℝ) :
    thetaCuspTiltedSource (-a) x = thetaCuspTiltedSource a (-x) := by
  unfold thetaCuspTiltedSource
  rw [thetaCuspFullSource_neg]
  congr 2
  ring

/-- The tilted source derivative is odd under simultaneous tilt/time reflection. -/
theorem deriv_thetaCuspTiltedSource_neg_tilt (a x : ℝ) :
    deriv (thetaCuspTiltedSource (-a)) x =
      -deriv (thetaCuspTiltedSource a) (-x) := by
  have hfun : thetaCuspTiltedSource (-a) =
      fun y : ℝ => thetaCuspTiltedSource a (-y) := by
    funext y
    exact thetaCuspTiltedSource_neg_tilt a y
  rw [hfun, deriv_comp_neg]

/-- Squaring removes the derivative orientation: reflected tilt reflects EKG energy density. -/
theorem thetaCuspTiltedEKGDerivativeEnergyDensity_neg_tilt (a x : ℝ) :
    thetaCuspTiltedEKGDerivativeEnergyDensity (-a) x =
      thetaCuspTiltedEKGDerivativeEnergyDensity a (-x) := by
  rw [thetaCuspTiltedEKGDerivativeEnergyDensity,
    thetaCuspTiltedEKGDerivativeEnergyDensity,
    deriv_thetaCuspTiltedSource_neg_tilt]
  ring

theorem continuous_deriv_thetaCuspTiltedSource (a : ℝ) :
    Continuous (deriv (thetaCuspTiltedSource a)) :=
  (contDiff_thetaCuspTiltedSource a).continuous_deriv (by simp)

theorem continuous_thetaCuspTiltedEKGDerivativeEnergyDensity (a : ℝ) :
    Continuous (thetaCuspTiltedEKGDerivativeEnergyDensity a) := by
  exact (continuous_deriv_thetaCuspTiltedSource a).pow 2

theorem integrable_thetaCuspTiltedSource {a : ℝ} (ha : |a| < 1) :
    Integrable (thetaCuspTiltedSource a) := by
  let source : 𝓢(ℝ, ℝ) := thetaCuspTiltedSchwartzReal a ha
  change Integrable (source : ℝ → ℝ)
  exact source.integrable

theorem integrable_abs_deriv_thetaCuspTiltedSource {a : ℝ} (ha : |a| < 1) :
    Integrable (fun x : ℝ => |deriv (thetaCuspTiltedSource a) x|) := by
  let source : 𝓢(ℝ, ℝ) := thetaCuspTiltedSchwartzReal a ha
  let sourceDeriv : 𝓢(ℝ, ℝ) := SchwartzMap.derivCLM ℝ ℝ source
  have h : Integrable (sourceDeriv : ℝ → ℝ) := sourceDeriv.integrable
  refine h.norm.congr ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  change |deriv (thetaCuspTiltedSource a) x| =
    |deriv (thetaCuspTiltedSource a) x|
  rfl

theorem abs_deriv_thetaCuspTiltedSource_le {a : ℝ} (ha : |a| < 1) (x : ℝ) :
    |deriv (thetaCuspTiltedSource a) x| ≤
      thetaCuspTiltedDerivativeConstant a 1 := by
  have h := weighted_iteratedDeriv_thetaCuspTiltedSource_le ha 0 1 x
  simpa [iteratedDeriv_one, Real.norm_eq_abs] using h

theorem integrable_thetaCuspTiltedEKGDerivativeEnergyDensity
    {a : ℝ} (ha : |a| < 1) :
    Integrable (thetaCuspTiltedEKGDerivativeEnergyDensity a) := by
  have hmajor := (integrable_abs_deriv_thetaCuspTiltedSource ha).const_mul
    (thetaCuspTiltedDerivativeConstant a 1)
  apply Integrable.mono hmajor
  · exact (continuous_thetaCuspTiltedEKGDerivativeEnergyDensity a).aestronglyMeasurable
  · filter_upwards with x
    have hC := thetaCuspTiltedDerivativeConstant_nonneg a 1
    have hdx := abs_deriv_thetaCuspTiltedSource_le ha x
    rw [thetaCuspTiltedEKGDerivativeEnergyDensity, Real.norm_eq_abs,
      Real.norm_eq_abs]
    change abs (deriv (thetaCuspTiltedSource a) x ^ (2 : ℕ)) ≤
      abs (thetaCuspTiltedDerivativeConstant a 1 *
        abs (deriv (thetaCuspTiltedSource a) x))
    rw [abs_pow, abs_mul, abs_of_nonneg hC, abs_abs]
    nlinarith [abs_nonneg (deriv (thetaCuspTiltedSource a) x)]

theorem thetaCuspTiltedEKGRetardedDerivativeEnergy_neg_tilt (a s : ℝ) :
    thetaCuspTiltedEKGRetardedDerivativeEnergy (-a) s =
      thetaCuspTiltedEKGAdvancedDerivativeEnergy a (-s) := by
  unfold thetaCuspTiltedEKGRetardedDerivativeEnergy
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun u _ => thetaCuspTiltedEKGDerivativeEnergyDensity_neg_tilt a u)]
  rw [integral_comp_neg_Ioi]
  unfold thetaCuspTiltedEKGAdvancedDerivativeEnergy
  exact (MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Iio_ae_eq_Iic : Iio (-s) =ᵐ[volume] Iic (-s))).symm

theorem thetaCuspTiltedEKGAdvancedDerivativeEnergy_neg_tilt (a s : ℝ) :
    thetaCuspTiltedEKGAdvancedDerivativeEnergy (-a) s =
      thetaCuspTiltedEKGRetardedDerivativeEnergy a (-s) := by
  simpa only [neg_neg] using
    (thetaCuspTiltedEKGRetardedDerivativeEnergy_neg_tilt (-a) (-s)).symm

/-- Past plus future derivative energy is the full Einstein quadratic source. -/
theorem thetaCuspTiltedEKGRetarded_add_advanced_eq_total
    {a : ℝ} (ha : |a| < 1) (s : ℝ) :
    thetaCuspTiltedEKGRetardedDerivativeEnergy a s +
      thetaCuspTiltedEKGAdvancedDerivativeEnergy a s =
        ∫ u : ℝ, thetaCuspTiltedEKGDerivativeEnergyDensity a u := by
  have hq := integrable_thetaCuspTiltedEKGDerivativeEnergyDensity ha
  have hsplit := MeasureTheory.integral_add_compl (s := Ioi s)
    measurableSet_Ioi hq
  have hcompl : (Ioi s)ᶜ = Iic s := by
    ext x
    simp
  rw [hcompl] at hsplit
  have hae : (∫ u in Iic s, thetaCuspTiltedEKGDerivativeEnergyDensity a u) =
      ∫ u in Iio s, thetaCuspTiltedEKGDerivativeEnergyDensity a u :=
    (MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Iio_ae_eq_Iic : Iio s =ᵐ[volume] Iic s)).symm
  rw [hae] at hsplit
  exact hsplit

theorem continuous_thetaCuspTiltedEKGRetardedDerivativeEnergy
    {a : ℝ} (ha : |a| < 1) :
    Continuous (thetaCuspTiltedEKGRetardedDerivativeEnergy a) := by
  let q := thetaCuspTiltedEKGDerivativeEnergyDensity a
  have hq : Integrable q := integrable_thetaCuspTiltedEKGDerivativeEnergyDensity ha
  have hrepr : thetaCuspTiltedEKGRetardedDerivativeEnergy a = fun s : ℝ =>
      (∫ u in Ioi 0, q u) - ∫ u in (0 : ℝ)..s, q u := by
    funext s
    have hsplit := intervalIntegral.integral_Ioi_sub_Ioi'
      (hq.integrableOn : IntegrableOn q (Ioi 0))
      (hq.integrableOn : IntegrableOn q (Ioi s))
    dsimp [thetaCuspTiltedEKGRetardedDerivativeEnergy]
    change (∫ u in Ioi s, q u) = _
    linarith
  rw [hrepr]
  exact continuous_const.sub (hq.continuous_primitive 0)

theorem continuous_thetaCuspTiltedEKGAdvancedDerivativeEnergy
    {a : ℝ} (ha : |a| < 1) :
    Continuous (thetaCuspTiltedEKGAdvancedDerivativeEnergy a) := by
  have hrepr : thetaCuspTiltedEKGAdvancedDerivativeEnergy a = fun s : ℝ =>
      (∫ u : ℝ, thetaCuspTiltedEKGDerivativeEnergyDensity a u) -
        thetaCuspTiltedEKGRetardedDerivativeEnergy a s := by
    funext s
    linarith [thetaCuspTiltedEKGRetarded_add_advanced_eq_total ha s]
  rw [hrepr]
  exact continuous_const.sub
    (continuous_thetaCuspTiltedEKGRetardedDerivativeEnergy ha)

theorem thetaCuspTiltedEKGRetardedDerivativeEnergy_nonneg (a s : ℝ) :
    0 ≤ thetaCuspTiltedEKGRetardedDerivativeEnergy a s := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro u _
  exact sq_nonneg _

theorem thetaCuspTiltedEKGAdvancedDerivativeEnergy_nonneg (a s : ℝ) :
    0 ≤ thetaCuspTiltedEKGAdvancedDerivativeEnergy a s := by
  apply setIntegral_nonneg measurableSet_Iio
  intro u _
  exact sq_nonneg _

theorem thetaCuspTiltedEKGRetardedDerivativeEnergy_le_total
    {a : ℝ} (ha : |a| < 1) (s : ℝ) :
    thetaCuspTiltedEKGRetardedDerivativeEnergy a s ≤
      ∫ u : ℝ, thetaCuspTiltedEKGDerivativeEnergyDensity a u := by
  linarith [thetaCuspTiltedEKGRetarded_add_advanced_eq_total ha s,
    thetaCuspTiltedEKGAdvancedDerivativeEnergy_nonneg a s]

theorem thetaCuspTiltedEKGAdvancedDerivativeEnergy_le_total
    {a : ℝ} (ha : |a| < 1) (s : ℝ) :
    thetaCuspTiltedEKGAdvancedDerivativeEnergy a s ≤
      ∫ u : ℝ, thetaCuspTiltedEKGDerivativeEnergyDensity a u := by
  linarith [thetaCuspTiltedEKGRetarded_add_advanced_eq_total ha s,
    thetaCuspTiltedEKGRetardedDerivativeEnergy_nonneg a s]

theorem thetaCuspTiltedSource_pos (a x : ℝ) :
    0 < thetaCuspTiltedSource a x := by
  unfold thetaCuspTiltedSource
  exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)

theorem integrable_thetaCuspTiltedEKGRetardedTailDensity
    {a : ℝ} (ha : |a| < 1) :
    Integrable (fun s : ℝ => thetaCuspTiltedSource a s *
      thetaCuspTiltedEKGRetardedDerivativeEnergy a s) := by
  let D := ∫ u : ℝ, thetaCuspTiltedEKGDerivativeEnergyDensity a u
  have hD : 0 ≤ D := integral_nonneg fun u => sq_nonneg _
  have hmajor := (integrable_thetaCuspTiltedSource ha).mul_const D
  apply Integrable.mono hmajor
  · exact ((contDiff_thetaCuspTiltedSource a).continuous.mul
      (continuous_thetaCuspTiltedEKGRetardedDerivativeEnergy ha)).aestronglyMeasurable
  · filter_upwards with s
    have hsource := thetaCuspTiltedSource_pos a s
    have hE := thetaCuspTiltedEKGRetardedDerivativeEnergy_nonneg a s
    have hEle := thetaCuspTiltedEKGRetardedDerivativeEnergy_le_total ha s
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hsource.le hE),
      abs_of_nonneg (mul_nonneg hsource.le hD)]
    exact mul_le_mul_of_nonneg_left hEle hsource.le

theorem integrable_thetaCuspTiltedEKGAdvancedTailDensity
    {a : ℝ} (ha : |a| < 1) :
    Integrable (fun s : ℝ => thetaCuspTiltedSource a s *
      thetaCuspTiltedEKGAdvancedDerivativeEnergy a s) := by
  let D := ∫ u : ℝ, thetaCuspTiltedEKGDerivativeEnergyDensity a u
  have hD : 0 ≤ D := integral_nonneg fun u => sq_nonneg _
  have hmajor := (integrable_thetaCuspTiltedSource ha).mul_const D
  apply Integrable.mono hmajor
  · exact ((contDiff_thetaCuspTiltedSource a).continuous.mul
      (continuous_thetaCuspTiltedEKGAdvancedDerivativeEnergy ha)).aestronglyMeasurable
  · filter_upwards with s
    have hsource := thetaCuspTiltedSource_pos a s
    have hE := thetaCuspTiltedEKGAdvancedDerivativeEnergy_nonneg a s
    have hEle := thetaCuspTiltedEKGAdvancedDerivativeEnergy_le_total ha s
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hsource.le hE),
      abs_of_nonneg (mul_nonneg hsource.le hD)]
    exact mul_le_mul_of_nonneg_left hEle hsource.le

/-- Time reflection converts the retarded mass at mirror tilt into the advanced mass. -/
theorem thetaCuspTiltedEKGRetardedTailMass_neg_tilt (a : ℝ) :
    thetaCuspTiltedEKGRetardedTailMass (-a) =
      thetaCuspTiltedEKGAdvancedTailMass a := by
  unfold thetaCuspTiltedEKGRetardedTailMass
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    measurableEmbedding_neg
    (fun s : ℝ => thetaCuspTiltedSource (-a) s *
      thetaCuspTiltedEKGRetardedDerivativeEnergy (-a) s)]
  unfold thetaCuspTiltedEKGAdvancedTailMass
  apply MeasureTheory.integral_congr_ae
  filter_upwards with s
  rw [thetaCuspTiltedSource_neg_tilt,
    thetaCuspTiltedEKGRetardedDerivativeEnergy_neg_tilt]
  simp

theorem thetaCuspTiltedEKGRetardedTailCoefficient_neg_tilt (a : ℝ) :
    thetaCuspTiltedEKGRetardedTailCoefficient (-a) =
      thetaCuspTiltedEKGAdvancedTailCoefficient a := by
  rw [thetaCuspTiltedEKGRetardedTailCoefficient,
    thetaCuspTiltedEKGAdvancedTailCoefficient,
    thetaCuspTiltedEKGRetardedTailMass_neg_tilt]

/-- Discrete causal order disappears from the sum: the two orderings factor into source mass
times total Einstein derivative energy. -/
theorem thetaCuspTiltedEKGRetarded_add_advanced_tailMass_factorization
    {a : ℝ} (ha : |a| < 1) :
    thetaCuspTiltedEKGRetardedTailMass a +
      thetaCuspTiltedEKGAdvancedTailMass a =
        (∫ s : ℝ, thetaCuspTiltedSource a s) *
          ∫ u : ℝ, thetaCuspTiltedEKGDerivativeEnergyDensity a u := by
  let D := ∫ u : ℝ, thetaCuspTiltedEKGDerivativeEnergyDensity a u
  have hret := integrable_thetaCuspTiltedEKGRetardedTailDensity ha
  have hadv := integrable_thetaCuspTiltedEKGAdvancedTailDensity ha
  unfold thetaCuspTiltedEKGRetardedTailMass thetaCuspTiltedEKGAdvancedTailMass
  rw [← MeasureTheory.integral_add hret hadv]
  calc
    (∫ s : ℝ, thetaCuspTiltedSource a s *
          thetaCuspTiltedEKGRetardedDerivativeEnergy a s +
        thetaCuspTiltedSource a s *
          thetaCuspTiltedEKGAdvancedDerivativeEnergy a s) =
        ∫ s : ℝ, thetaCuspTiltedSource a s * D := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with s
      rw [← mul_add, thetaCuspTiltedEKGRetarded_add_advanced_eq_total ha]
    _ = (∫ s : ℝ, thetaCuspTiltedSource a s) * D := by
      rw [MeasureTheory.integral_mul_const]

/-- Retarded ordered mass after Fubini: derivative energy is weighted by source mass lying in
its causal past. -/
theorem thetaCuspTiltedEKGRetardedTailMass_eq_pastSourceMass
    {a : ℝ} (ha : |a| < 1) :
    thetaCuspTiltedEKGRetardedTailMass a =
      ∫ u : ℝ, (∫ s in Iio u, thetaCuspTiltedSource a s) *
        thetaCuspTiltedEKGDerivativeEnergyDensity a u := by
  let F : ℝ → ℝ → ℝ := fun s u =>
    if s < u then thetaCuspTiltedSource a s *
      thetaCuspTiltedEKGDerivativeEnergyDensity a u else 0
  have hk := integrable_thetaCuspTiltedSource ha
  have hq := integrable_thetaCuspTiltedEKGDerivativeEnergyDensity ha
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume : Measure ℝ).prod volume) := by
    apply Measurable.aestronglyMeasurable
    dsimp [F, Function.uncurry]
    apply Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
    · exact ((contDiff_thetaCuspTiltedSource a).continuous.measurable.comp measurable_fst).mul
        ((continuous_thetaCuspTiltedEKGDerivativeEnergyDensity a).measurable.comp measurable_snd)
    · exact measurable_const
  have hbound : ∀ᵐ p ∂((volume : Measure ℝ).prod volume),
      ‖Function.uncurry F p‖ ≤
        thetaCuspTiltedSource a p.1 *
          thetaCuspTiltedEKGDerivativeEnergyDensity a p.2 := by
    filter_upwards with p
    dsimp [F, Function.uncurry]
    by_cases h : p.1 < p.2
    · rw [if_pos h]
      have hnonneg : 0 ≤ thetaCuspTiltedSource a p.1 *
          thetaCuspTiltedEKGDerivativeEnergyDensity a p.2 := by
        apply mul_nonneg (thetaCuspTiltedSource_pos a p.1).le
        unfold thetaCuspTiltedEKGDerivativeEnergyDensity
        exact sq_nonneg _
      rw [abs_of_nonneg hnonneg]
    · rw [if_neg h, abs_zero]
      exact mul_nonneg (thetaCuspTiltedSource_pos a p.1).le (sq_nonneg _)
  have hswap := GaloisForLFunctions.HTGeometry.integral_swap_of_dominated_prod
    hk hq hmeas hbound
  unfold thetaCuspTiltedEKGRetardedTailMass
  calc
    (∫ s : ℝ, thetaCuspTiltedSource a s *
      thetaCuspTiltedEKGRetardedDerivativeEnergy a s) =
        ∫ s : ℝ, ∫ u : ℝ, F s u := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with s
      dsimp [F]
      rw [thetaCuspTiltedEKGRetardedDerivativeEnergy]
      symm
      calc
        (∫ u : ℝ, if s < u then thetaCuspTiltedSource a s *
            thetaCuspTiltedEKGDerivativeEnergyDensity a u else 0) =
            ∫ u : ℝ, (Ioi s).indicator
              (fun u => thetaCuspTiltedSource a s *
                thetaCuspTiltedEKGDerivativeEnergyDensity a u) u := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with u
          by_cases hu : s < u <;> simp [hu]
        _ = ∫ u in Ioi s, thetaCuspTiltedSource a s *
            thetaCuspTiltedEKGDerivativeEnergyDensity a u :=
          MeasureTheory.integral_indicator measurableSet_Ioi
        _ = _ := by rw [MeasureTheory.integral_const_mul]
    _ = ∫ u : ℝ, ∫ s : ℝ, F s u := hswap
    _ = ∫ u : ℝ, (∫ s in Iio u, thetaCuspTiltedSource a s) *
        thetaCuspTiltedEKGDerivativeEnergyDensity a u := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      dsimp [F]
      calc
        (∫ s : ℝ, if s < u then thetaCuspTiltedSource a s *
            thetaCuspTiltedEKGDerivativeEnergyDensity a u else 0) =
            ∫ s : ℝ, (Iio u).indicator
              (fun s => thetaCuspTiltedSource a s *
                thetaCuspTiltedEKGDerivativeEnergyDensity a u) s := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with s
          by_cases hs : s < u <;> simp [hs]
        _ = ∫ s in Iio u, thetaCuspTiltedSource a s *
            thetaCuspTiltedEKGDerivativeEnergyDensity a u :=
          MeasureTheory.integral_indicator measurableSet_Iio
        _ = _ := by rw [MeasureTheory.integral_mul_const]

/-- Tilted source mass strictly before retarded time `u`. -/
def thetaCuspTiltedEKGPastSourceMass (a u : ℝ) : ℝ :=
  ∫ s in Iio u, thetaCuspTiltedSource a s

/-- Tilted source mass strictly after retarded time `u`. -/
def thetaCuspTiltedEKGFutureSourceMass (a u : ℝ) : ℝ :=
  ∫ s in Ioi u, thetaCuspTiltedSource a s

/-- Past-minus-future source imbalance sampled by the Einstein derivative energy. -/
def thetaCuspTiltedEKGSourceCausalImbalance (a u : ℝ) : ℝ :=
  thetaCuspTiltedEKGPastSourceMass a u -
    thetaCuspTiltedEKGFutureSourceMass a u

theorem thetaCuspTiltedEKGPast_add_future_sourceMass_eq_total
    {a : ℝ} (ha : |a| < 1) (u : ℝ) :
    thetaCuspTiltedEKGPastSourceMass a u +
      thetaCuspTiltedEKGFutureSourceMass a u =
        ∫ s : ℝ, thetaCuspTiltedSource a s := by
  have hk := integrable_thetaCuspTiltedSource ha
  have hsplit := MeasureTheory.integral_add_compl (s := Ioi u)
    measurableSet_Ioi hk
  have hcompl : (Ioi u)ᶜ = Iic u := by
    ext x
    simp
  rw [hcompl] at hsplit
  have hae : (∫ s in Iic u, thetaCuspTiltedSource a s) =
      ∫ s in Iio u, thetaCuspTiltedSource a s :=
    (MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Iio_ae_eq_Iic : Iio u =ᵐ[volume] Iic u)).symm
  rw [hae] at hsplit
  unfold thetaCuspTiltedEKGPastSourceMass thetaCuspTiltedEKGFutureSourceMass
  linarith

theorem continuous_thetaCuspTiltedEKGFutureSourceMass
    {a : ℝ} (ha : |a| < 1) :
    Continuous (thetaCuspTiltedEKGFutureSourceMass a) := by
  let k := thetaCuspTiltedSource a
  have hk : Integrable k := integrable_thetaCuspTiltedSource ha
  have hrepr : thetaCuspTiltedEKGFutureSourceMass a = fun u : ℝ =>
      (∫ s in Ioi 0, k s) - ∫ s in (0 : ℝ)..u, k s := by
    funext u
    have hsplit := intervalIntegral.integral_Ioi_sub_Ioi'
      (hk.integrableOn : IntegrableOn k (Ioi 0))
      (hk.integrableOn : IntegrableOn k (Ioi u))
    dsimp [thetaCuspTiltedEKGFutureSourceMass]
    change (∫ s in Ioi u, k s) = _
    linarith
  rw [hrepr]
  exact continuous_const.sub (hk.continuous_primitive 0)

theorem continuous_thetaCuspTiltedEKGPastSourceMass
    {a : ℝ} (ha : |a| < 1) :
    Continuous (thetaCuspTiltedEKGPastSourceMass a) := by
  have hrepr : thetaCuspTiltedEKGPastSourceMass a = fun u : ℝ =>
      (∫ s : ℝ, thetaCuspTiltedSource a s) -
        thetaCuspTiltedEKGFutureSourceMass a u := by
    funext u
    linarith [thetaCuspTiltedEKGPast_add_future_sourceMass_eq_total ha u]
  rw [hrepr]
  exact continuous_const.sub (continuous_thetaCuspTiltedEKGFutureSourceMass ha)

theorem continuous_thetaCuspTiltedEKGSourceCausalImbalance
    {a : ℝ} (ha : |a| < 1) :
    Continuous (thetaCuspTiltedEKGSourceCausalImbalance a) := by
  unfold thetaCuspTiltedEKGSourceCausalImbalance
  exact (continuous_thetaCuspTiltedEKGPastSourceMass ha).sub
    (continuous_thetaCuspTiltedEKGFutureSourceMass ha)

theorem thetaCuspTiltedEKGPastSourceMass_nonneg (a u : ℝ) :
    0 ≤ thetaCuspTiltedEKGPastSourceMass a u := by
  unfold thetaCuspTiltedEKGPastSourceMass
  exact setIntegral_nonneg measurableSet_Iio
    (fun s _ => (thetaCuspTiltedSource_pos a s).le)

theorem thetaCuspTiltedEKGFutureSourceMass_nonneg (a u : ℝ) :
    0 ≤ thetaCuspTiltedEKGFutureSourceMass a u := by
  unfold thetaCuspTiltedEKGFutureSourceMass
  exact setIntegral_nonneg measurableSet_Ioi
    (fun s _ => (thetaCuspTiltedSource_pos a s).le)

theorem abs_thetaCuspTiltedEKGSourceCausalImbalance_le_total
    {a : ℝ} (ha : |a| < 1) (u : ℝ) :
    |thetaCuspTiltedEKGSourceCausalImbalance a u| ≤
      ∫ s : ℝ, thetaCuspTiltedSource a s := by
  have hsplit := thetaCuspTiltedEKGPast_add_future_sourceMass_eq_total ha u
  have hp := thetaCuspTiltedEKGPastSourceMass_nonneg a u
  have hf := thetaCuspTiltedEKGFutureSourceMass_nonneg a u
  unfold thetaCuspTiltedEKGSourceCausalImbalance
  apply abs_le.mpr
  constructor <;> linarith

theorem integrable_thetaCuspTiltedEKGPastSourceMass_mul_energy
    {a : ℝ} (ha : |a| < 1) :
    Integrable (fun u : ℝ => thetaCuspTiltedEKGPastSourceMass a u *
      thetaCuspTiltedEKGDerivativeEnergyDensity a u) := by
  let K := ∫ s : ℝ, thetaCuspTiltedSource a s
  have hK : 0 ≤ K := integral_nonneg fun s => (thetaCuspTiltedSource_pos a s).le
  have hmajor := (integrable_thetaCuspTiltedEKGDerivativeEnergyDensity ha).const_mul K
  apply Integrable.mono hmajor
  · exact ((continuous_thetaCuspTiltedEKGPastSourceMass ha).mul
      (continuous_thetaCuspTiltedEKGDerivativeEnergyDensity a)).aestronglyMeasurable
  · filter_upwards with u
    have hp := thetaCuspTiltedEKGPastSourceMass_nonneg a u
    have hq : 0 ≤ thetaCuspTiltedEKGDerivativeEnergyDensity a u := by
      unfold thetaCuspTiltedEKGDerivativeEnergyDensity
      exact sq_nonneg _
    have hple : thetaCuspTiltedEKGPastSourceMass a u ≤ K := by
      linarith [thetaCuspTiltedEKGPast_add_future_sourceMass_eq_total ha u,
        thetaCuspTiltedEKGFutureSourceMass_nonneg a u]
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hp hq), abs_of_nonneg (mul_nonneg hK hq)]
    exact mul_le_mul_of_nonneg_right hple hq

theorem integrable_thetaCuspTiltedEKGSourceCausalImbalance_mul_energy
    {a : ℝ} (ha : |a| < 1) :
    Integrable (fun u : ℝ => thetaCuspTiltedEKGSourceCausalImbalance a u *
      thetaCuspTiltedEKGDerivativeEnergyDensity a u) := by
  let K := ∫ s : ℝ, thetaCuspTiltedSource a s
  have hK : 0 ≤ K := integral_nonneg fun s => (thetaCuspTiltedSource_pos a s).le
  have hmajor := (integrable_thetaCuspTiltedEKGDerivativeEnergyDensity ha).const_mul K
  apply Integrable.mono hmajor
  · exact ((continuous_thetaCuspTiltedEKGSourceCausalImbalance ha).mul
      (continuous_thetaCuspTiltedEKGDerivativeEnergyDensity a)).aestronglyMeasurable
  · filter_upwards with u
    have hq : 0 ≤ thetaCuspTiltedEKGDerivativeEnergyDensity a u := by
      unfold thetaCuspTiltedEKGDerivativeEnergyDensity
      exact sq_nonneg _
    have himb := abs_thetaCuspTiltedEKGSourceCausalImbalance_le_total ha u
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hq,
      abs_of_nonneg (mul_nonneg hK hq)]
    exact mul_le_mul_of_nonneg_right himb hq

/-- The reflection-odd mass is exactly derivative energy sampled against the source's causal
past-minus-future imbalance. -/
theorem thetaCuspTiltedEKGRetarded_sub_advanced_tailMass_eq_causalImbalance
    {a : ℝ} (ha : |a| < 1) :
    thetaCuspTiltedEKGRetardedTailMass a -
      thetaCuspTiltedEKGAdvancedTailMass a =
        ∫ u : ℝ, thetaCuspTiltedEKGSourceCausalImbalance a u *
          thetaCuspTiltedEKGDerivativeEnergyDensity a u := by
  let K := ∫ s : ℝ, thetaCuspTiltedSource a s
  let q := thetaCuspTiltedEKGDerivativeEnergyDensity a
  let P := thetaCuspTiltedEKGPastSourceMass a
  let B := thetaCuspTiltedEKGSourceCausalImbalance a
  have hfactor := thetaCuspTiltedEKGRetarded_add_advanced_tailMass_factorization ha
  have hret := thetaCuspTiltedEKGRetardedTailMass_eq_pastSourceMass ha
  change thetaCuspTiltedEKGRetardedTailMass a =
    ∫ u : ℝ, P u * q u at hret
  have hPq : Integrable (fun u : ℝ => P u * q u) :=
    integrable_thetaCuspTiltedEKGPastSourceMass_mul_energy ha
  have hKq : Integrable (fun u : ℝ => K * q u) :=
    (integrable_thetaCuspTiltedEKGDerivativeEnergyDensity ha).const_mul K
  have hIntegral : (∫ u : ℝ, B u * q u) =
      2 * (∫ u : ℝ, P u * q u) - K * ∫ u : ℝ, q u := by
    calc
      (∫ u : ℝ, B u * q u) =
          ∫ u : ℝ, 2 * (P u * q u) - K * q u := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with u
        dsimp [B, P, K, q]
        have hsplit := thetaCuspTiltedEKGPast_add_future_sourceMass_eq_total ha u
        unfold thetaCuspTiltedEKGSourceCausalImbalance
        calc
          (thetaCuspTiltedEKGPastSourceMass a u -
              thetaCuspTiltedEKGFutureSourceMass a u) *
                thetaCuspTiltedEKGDerivativeEnergyDensity a u =
            (2 * thetaCuspTiltedEKGPastSourceMass a u -
              (thetaCuspTiltedEKGPastSourceMass a u +
                thetaCuspTiltedEKGFutureSourceMass a u)) *
                  thetaCuspTiltedEKGDerivativeEnergyDensity a u := by ring
          _ = (2 * thetaCuspTiltedEKGPastSourceMass a u -
              ∫ s : ℝ, thetaCuspTiltedSource a s) *
                thetaCuspTiltedEKGDerivativeEnergyDensity a u := by rw [hsplit]
          _ = 2 * (thetaCuspTiltedEKGPastSourceMass a u *
                thetaCuspTiltedEKGDerivativeEnergyDensity a u) -
              (∫ s : ℝ, thetaCuspTiltedSource a s) *
                thetaCuspTiltedEKGDerivativeEnergyDensity a u := by ring
      _ = (∫ u : ℝ, 2 * (P u * q u)) - ∫ u : ℝ, K * q u := by
        rw [MeasureTheory.integral_sub (hPq.const_mul 2) hKq]
      _ = 2 * (∫ u : ℝ, P u * q u) - K * ∫ u : ℝ, q u := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  calc
    thetaCuspTiltedEKGRetardedTailMass a -
        thetaCuspTiltedEKGAdvancedTailMass a =
      2 * thetaCuspTiltedEKGRetardedTailMass a -
        (thetaCuspTiltedEKGRetardedTailMass a +
          thetaCuspTiltedEKGAdvancedTailMass a) := by ring
    _ = 2 * thetaCuspTiltedEKGRetardedTailMass a -
        K * ∫ u : ℝ, q u := by rw [hfactor]
    _ = 2 * (∫ u : ℝ, P u * q u) - K * ∫ u : ℝ, q u := by rw [hret]
    _ = ∫ u : ℝ, B u * q u := hIntegral.symm

theorem integral_thetaCuspTiltedSource_pos {a : ℝ} (ha : |a| < 1) :
    0 < ∫ s : ℝ, thetaCuspTiltedSource a s := by
  exact integral_pos_of_integrable_nonneg_nonzero
    (contDiff_thetaCuspTiltedSource a).continuous
    (integrable_thetaCuspTiltedSource ha)
    (fun x => (thetaCuspTiltedSource_pos a x).le)
    (thetaCuspTiltedSource_pos a 0).ne'

theorem deriv_thetaCuspTiltedSource_zero (a : ℝ) :
    deriv (thetaCuspTiltedSource a) 0 = a * thetaCuspFullSource 0 := by
  rw [← iteratedDeriv_one]
  rw [iteratedDeriv_thetaCuspTiltedSource]
  have hodd : iteratedDeriv 1 thetaCuspFullSource 0 = 0 :=
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (by decide)
  norm_num [Finset.sum_range_succ, hodd]

theorem exists_deriv_thetaCuspTiltedSource_ne_zero (a : ℝ) :
    ∃ x : ℝ, deriv (thetaCuspTiltedSource a) x ≠ 0 := by
  by_cases ha0 : a = 0
  · subst a
    obtain ⟨c, _, hc⟩ := exists_thetaCuspEKGSourceDeriv_ne_zero
    refine ⟨c, ?_⟩
    have hfun : thetaCuspTiltedSource 0 = thetaCuspFullSource := by
      funext x
      simp [thetaCuspTiltedSource]
    rw [hfun]
    simpa [HedenmalmThetaSource.sourceDeriv] using hc
  · refine ⟨0, ?_⟩
    rw [deriv_thetaCuspTiltedSource_zero]
    exact mul_ne_zero ha0 (thetaCuspFullSource_pos_all 0).ne'

theorem integral_thetaCuspTiltedEKGDerivativeEnergyDensity_pos
    {a : ℝ} (ha : |a| < 1) :
    0 < ∫ u : ℝ, thetaCuspTiltedEKGDerivativeEnergyDensity a u := by
  obtain ⟨x, hx⟩ := exists_deriv_thetaCuspTiltedSource_ne_zero a
  apply integral_pos_of_integrable_nonneg_nonzero
    (continuous_thetaCuspTiltedEKGDerivativeEnergyDensity a)
    (integrable_thetaCuspTiltedEKGDerivativeEnergyDensity ha)
    (fun u => sq_nonneg _)
  change deriv (thetaCuspTiltedSource a) x ^ (2 : ℕ) ≠ 0
  exact pow_ne_zero 2 hx

/-- **Exact causal-mirror EKG optical law.**  Mirror-sector retarded coefficients have a
strictly negative sum fixed by source mass and total derivative energy. -/
theorem thetaCuspTiltedEKGRetardedTailCoefficient_add_mirror_eq
    {a : ℝ} (ha : |a| < 1) :
    thetaCuspTiltedEKGRetardedTailCoefficient a +
      thetaCuspTiltedEKGRetardedTailCoefficient (-a) =
        (-32 * Real.pi) *
          ((∫ s : ℝ, thetaCuspTiltedSource a s) *
            ∫ u : ℝ, thetaCuspTiltedEKGDerivativeEnergyDensity a u) := by
  rw [thetaCuspTiltedEKGRetardedTailCoefficient_neg_tilt]
  unfold thetaCuspTiltedEKGRetardedTailCoefficient
    thetaCuspTiltedEKGAdvancedTailCoefficient
  calc
    (-32 * Real.pi) * thetaCuspTiltedEKGRetardedTailMass a +
        (-32 * Real.pi) * thetaCuspTiltedEKGAdvancedTailMass a =
      (-32 * Real.pi) *
        (thetaCuspTiltedEKGRetardedTailMass a +
          thetaCuspTiltedEKGAdvancedTailMass a) := by ring
    _ = _ := by
      rw [thetaCuspTiltedEKGRetarded_add_advanced_tailMass_factorization ha]

theorem thetaCuspTiltedEKGRetardedTailCoefficient_add_mirror_neg
    {a : ℝ} (ha : |a| < 1) :
    thetaCuspTiltedEKGRetardedTailCoefficient a +
      thetaCuspTiltedEKGRetardedTailCoefficient (-a) < 0 := by
  rw [thetaCuspTiltedEKGRetardedTailCoefficient_add_mirror_eq ha]
  have hmass := integral_thetaCuspTiltedSource_pos ha
  have henergy := integral_thetaCuspTiltedEKGDerivativeEnergyDensity_pos ha
  have hpi : 0 < 32 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  nlinarith [mul_pos hmass henergy]

/-- Reflection-odd part of the genuine retarded EKG response. -/
def thetaCuspTiltedEKGCausalMirrorAnomaly (a : ℝ) : ℝ :=
  thetaCuspTiltedEKGRetardedTailCoefficient a -
    thetaCuspTiltedEKGRetardedTailCoefficient (-a)

/-- Coefficient-level causal-incidence formula: the only reflection-sensitive EKG response is
the derivative-energy expectation of past-minus-future theta source mass. -/
theorem thetaCuspTiltedEKGCausalMirrorAnomaly_eq_causalImbalance
    {a : ℝ} (ha : |a| < 1) :
    thetaCuspTiltedEKGCausalMirrorAnomaly a =
      (-32 * Real.pi) *
        ∫ u : ℝ, thetaCuspTiltedEKGSourceCausalImbalance a u *
          thetaCuspTiltedEKGDerivativeEnergyDensity a u := by
  unfold thetaCuspTiltedEKGCausalMirrorAnomaly
  rw [thetaCuspTiltedEKGRetardedTailCoefficient_neg_tilt]
  unfold thetaCuspTiltedEKGRetardedTailCoefficient
    thetaCuspTiltedEKGAdvancedTailCoefficient
  rw [← mul_sub]
  rw [thetaCuspTiltedEKGRetarded_sub_advanced_tailMass_eq_causalImbalance ha]

theorem thetaCuspTiltedEKGCausalMirrorAnomaly_neg (a : ℝ) :
    thetaCuspTiltedEKGCausalMirrorAnomaly (-a) =
      -thetaCuspTiltedEKGCausalMirrorAnomaly a := by
  unfold thetaCuspTiltedEKGCausalMirrorAnomaly
  simp only [neg_neg]
  ring

theorem thetaCuspTiltedEKGCausalMirrorAnomaly_zero :
    thetaCuspTiltedEKGCausalMirrorAnomaly 0 = 0 := by
  unfold thetaCuspTiltedEKGCausalMirrorAnomaly
  simp

end RHTower
