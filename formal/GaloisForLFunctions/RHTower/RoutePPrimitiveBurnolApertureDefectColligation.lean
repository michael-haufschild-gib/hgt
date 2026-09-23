import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolApertureDampingSemigroup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Route P primitive Burnol aperture defect colligation

P-G187 identifies the sharp forward damping semigroup on the positive Burnol aperture ray. This
module constructs its exact missing energy channels. The translated tail has multiplier
`((u-c)/u)^(2 : ℕ)`; its complement splits into the interval deleted at the aperture boundary and a
positive tail cocycle. Their explicit square-root features satisfy an exact three-channel energy
identity for every continuous finite-energy datum.

On each primitive Euler Burnol feature, the two defect channels carry precisely
`(1-exp(-2c lambda))` times its P-G186 base mass. Summed over all primitive cells, defect mass plus
transported mass is exactly the fixed P-G181 source budget. Thus completion has a concrete finite
defect space to match: a Gamma--polar producer must identify or extend these channels before Gram
comparison, rather than postulate an abstract contraction after divisor expansion.
-/

open Complex Set MeasureTheory

namespace RHTower

noncomputable section

/-- Exact tail normal form of weighted-aperture damping energy. -/
theorem routePBurnolApertureEnergy_forwardDampingShift_eq_tail
    {c : ℝ} (hc : 0 ≤ c) (f : ℝ → ℂ) :
    routePBurnolApertureEnergy (routePBurnolForwardDampingShift c f) =
      ∫ u : ℝ in Ioi c,
        ((u - c) / u) ^ 2 * ‖f u‖ ^ 2 := by
  rw [routePBurnolApertureEnergy]
  calc
    (∫ L : ℝ in Ioi 0,
        ‖routePBurnolForwardDampingShift c f L‖ ^ 2) =
        ∫ L : ℝ in Ioi 0,
          (L / (L + c)) ^ 2 * ‖f (L + c)‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro L hL
      exact norm_sq_routePBurnolForwardDampingShift hc hL f
    _ = ∫ L : ℝ in Ioi 0,
          (((L + c) - c) / (L + c)) ^ 2 * ‖f (L + c)‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro L _hL
      ring_nf
    _ = ∫ u : ℝ in Ioi c,
          ((u - c) / u) ^ 2 * ‖f u‖ ^ 2 := by
      exact routePIntegral_Ioi_comp_add_eq
        (fun u : ℝ => ((u - c) / u) ^ 2 * ‖f u‖ ^ 2) c

/-- Energy lost by deleting the initial aperture interval. -/
def routePBurnolApertureBoundaryDefect (c : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Ioc (0 : ℝ) c).indicator f u

/-- The nonnegative tail weight left by the damping cocycle. -/
def routePBurnolApertureTailDefectWeight (c u : ℝ) : ℝ :=
  1 - ((u - c) / u) ^ 2

/-- Tail defect channel of the weighted aperture translation. -/
def routePBurnolApertureTailDefect (c : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Ioi c).indicator
    (fun u => ((Real.sqrt (routePBurnolApertureTailDefectWeight c u) : ℝ) : ℂ) * f u) u

theorem routePBurnolApertureTailDefectWeight_nonneg
    {c u : ℝ} (hc : 0 ≤ c) (hu : c < u) :
    0 ≤ routePBurnolApertureTailDefectWeight c u := by
  rw [routePBurnolApertureTailDefectWeight]
  have hu0 : 0 < u := lt_of_le_of_lt hc hu
  have hq0 : 0 ≤ (u - c) / u := div_nonneg (sub_nonneg.mpr hu.le) hu0.le
  have hq1 : (u - c) / u ≤ 1 := (div_le_one hu0).mpr (by linarith)
  nlinarith

theorem routePBurnolApertureTailDefectWeight_le_one
    {c u : ℝ} (_hc : 0 ≤ c) (_hu : c < u) :
    routePBurnolApertureTailDefectWeight c u ≤ 1 := by
  rw [routePBurnolApertureTailDefectWeight]
  exact sub_le_self _ (sq_nonneg _)

theorem routePBurnolApertureTailRatio_sq_le_one
    {c u : ℝ} (hc : 0 ≤ c) (hu : c < u) :
    ((u - c) / u) ^ 2 ≤ 1 := by
  have hu0 : 0 < u := lt_of_le_of_lt hc hu
  have hq0 : 0 ≤ (u - c) / u := div_nonneg (sub_nonneg.mpr hu.le) hu0.le
  have hq1 : (u - c) / u ≤ 1 := (div_le_one hu0).mpr (by linarith)
  nlinarith

theorem norm_sq_routePBurnolApertureTailDefect
    {c u : ℝ} (hc : 0 ≤ c) (hu : c < u) (f : ℝ → ℂ) :
    ‖routePBurnolApertureTailDefect c f u‖ ^ 2 =
      routePBurnolApertureTailDefectWeight c u * ‖f u‖ ^ 2 := by
  rw [routePBurnolApertureTailDefect, Set.indicator_of_mem (mem_Ioi.mpr hu),
    norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (routePBurnolApertureTailDefectWeight_nonneg hc hu)]

theorem routePBurnolApertureEnergy_boundaryDefect
    (c : ℝ) (f : ℝ → ℂ) :
    routePBurnolApertureEnergy (routePBurnolApertureBoundaryDefect c f) =
      ∫ u : ℝ in Ioc 0 c, ‖f u‖ ^ 2 := by
  rw [routePBurnolApertureEnergy]
  calc
    (∫ u : ℝ in Ioi 0,
        ‖routePBurnolApertureBoundaryDefect c f u‖ ^ 2) =
        ∫ u : ℝ in Ioi 0,
          (Ioc (0 : ℝ) c).indicator (fun u => ‖f u‖ ^ 2) u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _hu
      by_cases huc : u ∈ Ioc (0 : ℝ) c <;>
        simp [routePBurnolApertureBoundaryDefect, huc]
    _ = ∫ u : ℝ in Ioi (0 : ℝ) ∩ Ioc 0 c, ‖f u‖ ^ 2 := by
      exact setIntegral_indicator measurableSet_Ioc
    _ = ∫ u : ℝ in Ioc 0 c, ‖f u‖ ^ 2 := by
      rw [inter_eq_right.mpr Ioc_subset_Ioi_self]

theorem routePBurnolApertureEnergy_tailDefect
    {c : ℝ} (hc : 0 ≤ c) (f : ℝ → ℂ) :
    routePBurnolApertureEnergy (routePBurnolApertureTailDefect c f) =
      ∫ u : ℝ in Ioi c,
        routePBurnolApertureTailDefectWeight c u * ‖f u‖ ^ 2 := by
  have hsubset : Ioi c ⊆ Ioi (0 : ℝ) := by
    intro u hu
    exact mem_Ioi.mpr (lt_of_le_of_lt hc (mem_Ioi.mp hu))
  rw [routePBurnolApertureEnergy]
  calc
    (∫ u : ℝ in Ioi 0,
        ‖routePBurnolApertureTailDefect c f u‖ ^ 2) =
        ∫ u : ℝ in Ioi 0,
          (Ioi c).indicator
            (fun u => routePBurnolApertureTailDefectWeight c u * ‖f u‖ ^ 2) u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _hu
      by_cases huc : u ∈ Ioi c
      · rw [Set.indicator_of_mem huc]
        change ‖routePBurnolApertureTailDefect c f u‖ ^ 2 = _
        exact norm_sq_routePBurnolApertureTailDefect hc (mem_Ioi.mp huc) f
      · rw [Set.indicator_of_notMem huc]
        simp [routePBurnolApertureTailDefect, huc]
    _ = ∫ u : ℝ in Ioi (0 : ℝ) ∩ Ioi c,
          routePBurnolApertureTailDefectWeight c u * ‖f u‖ ^ 2 := by
      exact setIntegral_indicator measurableSet_Ioi
    _ = ∫ u : ℝ in Ioi c,
          routePBurnolApertureTailDefectWeight c u * ‖f u‖ ^ 2 := by
      rw [inter_eq_right.mpr hsubset]

/-- **P-G188.** Weighted aperture damping completes to an exact three-channel energy colligation:
transported tail, deleted boundary interval, and positive cocycle defect. -/
theorem routePBurnolApertureDamping_energy_colligation
    {c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℂ}
    (hfcont : Continuous f)
    (hf : IntegrableOn (fun u : ℝ => ‖f u‖ ^ 2) (Ioi 0)) :
    routePBurnolApertureEnergy (routePBurnolForwardDampingShift c f) +
        routePBurnolApertureEnergy (routePBurnolApertureBoundaryDefect c f) +
        routePBurnolApertureEnergy (routePBurnolApertureTailDefect c f) =
      routePBurnolApertureEnergy f := by
  let g : ℝ → ℝ := fun u => ‖f u‖ ^ 2
  have hsubset : Ioi c ⊆ Ioi (0 : ℝ) := by
    intro u hu
    exact mem_Ioi.mpr (lt_of_le_of_lt hc (mem_Ioi.mp hu))
  have hhead : IntegrableOn g (Ioc 0 c) :=
    hf.mono_set Ioc_subset_Ioi_self
  have htail : IntegrableOn g (Ioi c) :=
    hf.mono_set hsubset
  have htransport : IntegrableOn
      (fun u : ℝ => ((u - c) / u) ^ 2 * g u) (Ioi c) := by
    apply Integrable.mono' htail
    · have hm : Measurable (fun u : ℝ => ((u - c) / u) ^ 2 * g u) := by
        dsimp [g]
        fun_prop
      exact hm.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have hw := routePBurnolApertureTailRatio_sq_le_one hc (mem_Ioi.mp hu)
      nlinarith [sq_nonneg ‖f u‖]
  have hdefect : IntegrableOn
      (fun u : ℝ => routePBurnolApertureTailDefectWeight c u * g u) (Ioi c) := by
    apply Integrable.mono' htail
    · have hm : Measurable
          (fun u : ℝ => routePBurnolApertureTailDefectWeight c u * g u) := by
        dsimp [routePBurnolApertureTailDefectWeight, g]
        fun_prop
      exact hm.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hw0 := routePBurnolApertureTailDefectWeight_nonneg hc (mem_Ioi.mp hu)
      have hw1 := routePBurnolApertureTailDefectWeight_le_one hc (mem_Ioi.mp hu)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 (sq_nonneg _))]
      nlinarith [sq_nonneg ‖f u‖]
  have htailComplete :
      (∫ u : ℝ in Ioi c, ((u - c) / u) ^ 2 * g u) +
          ∫ u : ℝ in Ioi c,
            routePBurnolApertureTailDefectWeight c u * g u =
        ∫ u : ℝ in Ioi c, g u := by
    rw [← integral_add htransport hdefect]
    apply integral_congr_ae
    filter_upwards with u
    dsimp [routePBurnolApertureTailDefectWeight]
    ring_nf
  have hsplit :
      (∫ u : ℝ in Ioc 0 c, g u) + ∫ u : ℝ in Ioi c, g u =
        ∫ u : ℝ in Ioi 0, g u := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hhead htail,
      Ioc_union_Ioi_eq_Ioi hc]
  rw [routePBurnolApertureEnergy_forwardDampingShift_eq_tail hc,
    routePBurnolApertureEnergy_boundaryDefect,
    routePBurnolApertureEnergy_tailDefect hc,
    routePBurnolApertureEnergy]
  change (∫ u : ℝ in Ioi c, ((u - c) / u) ^ 2 * g u) +
      (∫ u : ℝ in Ioc 0 c, g u) +
      (∫ u : ℝ in Ioi c,
        routePBurnolApertureTailDefectWeight c u * g u) =
      ∫ u : ℝ in Ioi 0, g u
  calc
    (∫ u : ℝ in Ioi c, ((u - c) / u) ^ 2 * g u) +
        (∫ u : ℝ in Ioc 0 c, g u) +
        (∫ u : ℝ in Ioi c,
          routePBurnolApertureTailDefectWeight c u * g u) =
      (∫ u : ℝ in Ioc 0 c, g u) +
        ((∫ u : ℝ in Ioi c, ((u - c) / u) ^ 2 * g u) +
          ∫ u : ℝ in Ioi c,
            routePBurnolApertureTailDefectWeight c u * g u) := by ring
    _ = (∫ u : ℝ in Ioc 0 c, g u) + ∫ u : ℝ in Ioi c, g u := by
      rw [htailComplete]
    _ = ∫ u : ℝ in Ioi 0, g u := hsplit

theorem integrableOn_norm_sq_routePPrimitiveBurnolWindowFeature
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    IntegrableOn
      (fun u : ℝ => ‖routePPrimitiveBurnolWindowFeature pe kappa u‖ ^ 2)
      (Ioi 0) := by
  let A := finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe)
  let lambda := xiGammaEulerPrimitiveLogFrequency pe
  have hlambda : 0 < lambda := xiGammaEulerPrimitiveLogFrequency_pos pe
  have hbase : IntegrableOn
      (fun u : ℝ => u ^ 2 * Real.exp (-(2 * lambda) * u)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (2 : ℝ)) (p := (1 : ℝ)) (b := 2 * lambda)
      (by norm_num) (by norm_num) (by positivity)
    simpa [Real.rpow_two, Real.rpow_one] using h
  have hscaled : IntegrableOn
      (fun u : ℝ => ‖A‖ ^ 2 *
        (u ^ 2 * Real.exp (-(2 * lambda) * u))) (Ioi 0) :=
    hbase.const_mul (‖A‖ ^ 2)
  refine hscaled.congr_fun ?_ measurableSet_Ioi
  intro u hu
  have hu0 : 0 < u := mem_Ioi.mp hu
  have hexp : Real.exp (-(xiGammaEulerPrimitiveLogFrequency pe * u)) ^ 2 =
      Real.exp (-(2 * xiGammaEulerPrimitiveLogFrequency pe) * u) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring_nf
  symm
  change ‖routePPrimitiveBurnolWindowFeature pe kappa u‖ ^ 2 = _
  rw [routePPrimitiveBurnolWindowFeature,
    xiWardCubicBurnolWindowConormalFeature_eq,
    routePXiBaseConormalResidueFeature]
  dsimp [A, lambda]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hu0, Complex.norm_exp, mul_pow, mul_pow]
  simp [routePPrimitiveBurnolSpectralPoint, Complex.mul_re]
  rw [hexp]
  ring_nf
  simp

theorem continuous_routePPrimitiveBurnolWindowFeature
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    Continuous (routePPrimitiveBurnolWindowFeature pe kappa) := by
  rw [show routePPrimitiveBurnolWindowFeature pe kappa =
      fun u : ℝ =>
        finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
          routePXiBaseConormalResidueFeature
            (routePPrimitiveBurnolSpectralPoint pe kappa) u by
    funext u
    rw [routePPrimitiveBurnolWindowFeature,
      xiWardCubicBurnolWindowConormalFeature_eq]]
  unfold routePXiBaseConormalResidueFeature
  fun_prop

/-- Primitive mass carried by the two explicit aperture defect channels at time `c`. -/
def routePPrimitiveBurnolApertureDefectMass
    (c : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  (1 - Real.exp (-2 * c * xiGammaEulerPrimitiveLogFrequency pe)) *
    routePPrimitiveBaseCauchyCubicWeight pe

/-- On each primitive feature, the boundary and cocycle channels carry exactly the missing
semigroup energy. -/
theorem routePPrimitiveBurnolApertureDefect_energy_eq_mass
    {c : ℝ} (hc : 0 ≤ c) (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    routePBurnolApertureEnergy
        (routePBurnolApertureBoundaryDefect c
          (routePPrimitiveBurnolWindowFeature pe kappa)) +
      routePBurnolApertureEnergy
        (routePBurnolApertureTailDefect c
          (routePPrimitiveBurnolWindowFeature pe kappa)) =
      routePPrimitiveBurnolApertureDefectMass c pe := by
  have hcoll := routePBurnolApertureDamping_energy_colligation hc
    (continuous_routePPrimitiveBurnolWindowFeature pe kappa)
    (integrableOn_norm_sq_routePPrimitiveBurnolWindowFeature pe kappa)
  rw [routePBurnolApertureEnergy_forwardDampingShift_primitiveFeature_eq_baseMass
      hc pe kappa,
    routePBurnolApertureEnergy_primitiveFeature_eq_baseWeight] at hcoll
  rw [routePPrimitiveBurnolSemigroupBaseMass] at hcoll
  rw [routePPrimitiveBurnolApertureDefectMass]
  linarith

theorem routePPrimitiveBurnolApertureDefectMass_nonneg
    {c : ℝ} (hc : 0 ≤ c) (pe : Nat.Primes × ℕ) :
    0 ≤ routePPrimitiveBurnolApertureDefectMass c pe := by
  rw [routePPrimitiveBurnolApertureDefectMass]
  have hexp : Real.exp (-2 * c * xiGammaEulerPrimitiveLogFrequency pe) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hc)
      (xiGammaEulerPrimitiveLogFrequency_pos pe).le
  exact mul_nonneg (sub_nonneg.mpr hexp)
    (routePPrimitiveBaseCauchyCubicWeight_nonneg pe)

theorem routePPrimitiveBurnolApertureDefectMass_add_baseMass
    (c : ℝ) (pe : Nat.Primes × ℕ) :
    routePPrimitiveBurnolApertureDefectMass c pe +
      routePPrimitiveBurnolSemigroupBaseMass c pe =
      routePPrimitiveBaseCauchyCubicWeight pe := by
  rw [routePPrimitiveBurnolApertureDefectMass,
    routePPrimitiveBurnolSemigroupBaseMass]
  ring_nf

theorem summable_routePPrimitiveBurnolApertureDefectMass
    {c : ℝ} (hc : 0 ≤ c) :
    Summable (routePPrimitiveBurnolApertureDefectMass c) := by
  have hmass : Summable (routePPrimitiveBurnolSemigroupBaseMass c) :=
    (summable_routePPrimitiveBurnolSemigroupBaseMass_iff c).mpr hc
  have hsub := summable_routePPrimitiveBaseCauchyCubicWeight.sub hmass
  exact hsub.congr fun pe => by
    rw [routePPrimitiveBurnolApertureDefectMass,
      routePPrimitiveBurnolSemigroupBaseMass]
    ring_nf

/-- Globally, transported primitive mass plus explicit aperture-defect mass is exactly the fixed
P-G181/P-G186 source budget. -/
theorem tsum_routePPrimitiveBurnolApertureDefectMass_add_baseMass_eq_budget
    {c : ℝ} (hc : 0 ≤ c) :
    (∑' pe : Nat.Primes × ℕ,
        routePPrimitiveBurnolApertureDefectMass c pe) +
      ∑' pe : Nat.Primes × ℕ,
        routePPrimitiveBurnolSemigroupBaseMass c pe =
      routePPrimitiveBaseCauchyCubicTraceBudget := by
  have hdef := summable_routePPrimitiveBurnolApertureDefectMass hc
  have hmass : Summable (routePPrimitiveBurnolSemigroupBaseMass c) :=
    (summable_routePPrimitiveBurnolSemigroupBaseMass_iff c).mpr hc
  rw [← hdef.tsum_add hmass, routePPrimitiveBaseCauchyCubicTraceBudget]
  apply tsum_congr
  exact routePPrimitiveBurnolApertureDefectMass_add_baseMass c

end

end RHTower
