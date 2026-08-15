import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolWindowGramSquare
import GaloisForLFunctions.RHTower.RoutePPrimitiveBaseJointDampingWall
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Route P primitive Burnol aperture damping semigroup

P-G186 realizes the complete primitive base cube as a positive-aperture Burnol Gram. P-G185
independently finds the exact joint Dirichlet damping chamber. This module identifies their common
dynamical origin. The weighted aperture translation
`T c f L = L / (L + c) * f (L + c)` is a contraction semigroup for `c ≥ 0`; every universal Burnol
conormal feature is an eigenvector, and each primitive Euler feature has energy eigenvalue
`exp (-2 c lambda)`.

At primitive log frequency `lambda = log n`, aperture time is exactly joint damping `s = 2c`.
Consequently the dynamically damped Gram diagonal is literally P-G185's joint-damping weight and
is summable exactly for `c ≥ 0`. This wall is also operator-theoretically sharp: for every `c < 0`,
one explicit compactly supported finite-energy boundary datum acquires a nonintegrable
reciprocal-square pole at `L = -c`. Thus ordinary backward aperture transport cannot implement the
remaining completed-Xi boundary continuation; a dilation or additional completed defect channel is
mathematically forced.
-/

open Complex Set MeasureTheory

namespace RHTower

noncomputable section

/-- Forward weighted translation on the positive Burnol aperture ray. -/
def routePBurnolForwardDampingShift (c : ℝ) (f : ℝ → ℂ) (L : ℝ) : ℂ :=
  ((L / (L + c) : ℝ) : ℂ) * f (L + c)

theorem routePBurnolForwardDampingShift_zero (f : ℝ → ℂ) {L : ℝ} (hL : 0 < L) :
    routePBurnolForwardDampingShift 0 f L = f L := by
  rw [routePBurnolForwardDampingShift]
  norm_num [hL.ne']

theorem routePBurnolForwardDampingShift_add
    {c d L : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hL : 0 < L) (f : ℝ → ℂ) :
    routePBurnolForwardDampingShift c
        (routePBurnolForwardDampingShift d f) L =
      routePBurnolForwardDampingShift (c + d) f L := by
  have hLc : L + c ≠ 0 := by linarith
  have hLcd : L + (c + d) ≠ 0 := by linarith
  have hfrac :
      (((L / (L + c) : ℝ) : ℂ) * (((L + c) / (L + c + d) : ℝ) : ℂ)) =
        (((L / (L + (c + d)) : ℝ) : ℂ)) := by
    norm_cast
    rw [show L + c + d = L + (c + d) by ring_nf]
    field_simp [hLc, hLcd]
  rw [routePBurnolForwardDampingShift, routePBurnolForwardDampingShift,
    routePBurnolForwardDampingShift, ← mul_assoc, hfrac]
  congr 2
  simp [add_assoc]

/-- Every universal Burnol conormal feature is an eigenvector of forward weighted translation. -/
theorem routePBurnolForwardDampingShift_windowFeature
    {c L : ℝ} (hc : 0 ≤ c) (hL : 0 < L) (z : ℂ) :
    routePBurnolForwardDampingShift c
        (xiWardCubicBurnolWindowConormalFeature · z) L =
      Complex.exp (-((z - 1 / 2) * (c : ℂ))) *
        xiWardCubicBurnolWindowConormalFeature L z := by
  rw [routePBurnolForwardDampingShift,
    xiWardCubicBurnolWindowConormalFeature_eq,
    xiWardCubicBurnolWindowConormalFeature_eq,
    routePXiBaseConormalResidueFeature,
    routePXiBaseConormalResidueFeature]
  have hLc : L + c ≠ 0 := by linarith
  have hscale : (((L / (L + c) : ℝ) : ℂ) * (((L + c : ℝ) : ℂ))) = (L : ℂ) := by
    norm_cast
    field_simp [hLc]
  rw [show -((z - 1 / 2) * (((L + c : ℝ) : ℂ))) =
      -((z - 1 / 2) * (c : ℂ)) + -((z - 1 / 2) * (L : ℂ)) by
    push_cast
    ring_nf,
    Complex.exp_add]
  rw [← mul_assoc, hscale]
  ring_nf

/-- Primitive Euler window features diagonalize the semigroup at their exact complex log node. -/
theorem routePBurnolForwardDampingShift_primitiveFeature
    {c L : ℝ} (hc : 0 ≤ c) (hL : 0 < L)
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    routePBurnolForwardDampingShift c
        (routePPrimitiveBurnolWindowFeature pe kappa) L =
      Complex.exp (-((c : ℂ) *
        ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ)))) *
        routePPrimitiveBurnolWindowFeature pe kappa L := by
  let A := finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe)
  let z := routePPrimitiveBurnolSpectralPoint pe kappa
  have hshift :
      routePBurnolForwardDampingShift c
          (routePPrimitiveBurnolWindowFeature pe kappa) L =
        A * routePBurnolForwardDampingShift c
          (xiWardCubicBurnolWindowConormalFeature · z) L := by
    rw [routePBurnolForwardDampingShift,
      routePBurnolForwardDampingShift,
      routePPrimitiveBurnolWindowFeature]
    dsimp [A, z]
    ring_nf
  rw [hshift, routePBurnolForwardDampingShift_windowFeature hc hL,
    routePPrimitiveBurnolWindowFeature]
  dsimp [A, z]
  have hnode :
      (routePPrimitiveBurnolSpectralPoint pe kappa - 1 / 2) =
        (xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ) := by
    rw [routePPrimitiveBurnolSpectralPoint]
    push_cast
    ring_nf
  rw [hnode]
  ring_nf

/-- Squared aperture energy of a scalar radial feature. -/
def routePBurnolApertureEnergy (f : ℝ → ℂ) : ℝ :=
  ∫ L : ℝ in Ioi 0, ‖f L‖ ^ 2

theorem norm_sq_routePBurnolForwardDampingShift
    {c L : ℝ} (hc : 0 ≤ c) (hL : 0 < L) (f : ℝ → ℂ) :
    ‖routePBurnolForwardDampingShift c f L‖ ^ 2 =
      (L / (L + c)) ^ 2 * ‖f (L + c)‖ ^ 2 := by
  rw [routePBurnolForwardDampingShift, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hL.le (by linarith))]
  ring_nf

theorem routePBurnolForwardDampingShift_norm_sq_le
    {c L : ℝ} (hc : 0 ≤ c) (hL : 0 < L) (f : ℝ → ℂ) :
    ‖routePBurnolForwardDampingShift c f L‖ ^ 2 ≤ ‖f (L + c)‖ ^ 2 := by
  rw [norm_sq_routePBurnolForwardDampingShift hc hL]
  have hden : 0 < L + c := by linarith
  have hq0 : 0 ≤ L / (L + c) := div_nonneg hL.le hden.le
  have hq1 : L / (L + c) ≤ 1 := (div_le_one hden).2 (by linarith)
  have hq2 : (L / (L + c)) ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hq2 (sq_nonneg ‖f (L + c)‖)]

theorem routePIntegral_Ioi_comp_add_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (c : ℝ) :
    (∫ L : ℝ in Ioi 0, f (L + c)) = ∫ u : ℝ in Ioi c, f u := by
  rw [← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioi]
  let g : ℝ → E := (Ioi c).indicator f
  calc
    (∫ L : ℝ, (Ioi 0).indicator (fun L => f (L + c)) L) =
        ∫ L : ℝ, g (L + c) := by
      apply integral_congr_ae
      filter_upwards with L
      by_cases hL : L ∈ Ioi (0 : ℝ)
      · have hLc : L + c ∈ Ioi c := by simpa using add_lt_add_right hL c
        simp [g, hL, hLc]
      · have hLc : L + c ∉ Ioi c := by simpa using hL
        simp [g, hL, hLc]
    _ = ∫ u : ℝ, g u :=
      MeasureTheory.integral_add_right_eq_self g c
    _ = ∫ u : ℝ, (Ioi c).indicator f u := by rfl

/-- Forward damping is a contraction on positive-aperture squared energy. -/
theorem routePBurnolApertureEnergy_forwardDampingShift_le
    {c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℂ}
    (hfcont : Continuous f)
    (hf : IntegrableOn (fun L : ℝ => ‖f L‖ ^ 2) (Ioi 0)) :
    routePBurnolApertureEnergy (routePBurnolForwardDampingShift c f) ≤
      routePBurnolApertureEnergy f := by
  let g : ℝ → ℝ := fun L => ‖f L‖ ^ 2
  have hsub : Ioi c ⊆ Ioi (0 : ℝ) := by
    intro L hL
    exact mem_Ioi.mpr (lt_of_le_of_lt hc (mem_Ioi.mp hL))
  have htail : IntegrableOn g (Ioi c) := hf.mono_set hsub
  have hshift : IntegrableOn (fun L : ℝ => g (L + c)) (Ioi 0) := by
    have hmp : MeasurePreserving (fun L : ℝ => L + c) volume volume :=
      measurePreserving_add_right volume c
    rw [show Ioi (0 : ℝ) = (fun L : ℝ => L + c) ⁻¹' Ioi c by ext L; simp]
    exact (hmp.integrableOn_comp_preimage (measurableEmbedding_addRight c)).mpr htail
  have hmeas : AEStronglyMeasurable
      (fun L : ℝ => ‖routePBurnolForwardDampingShift c f L‖ ^ 2)
      (volume.restrict (Ioi 0)) := by
    have hm : Measurable
        (fun L : ℝ => ‖routePBurnolForwardDampingShift c f L‖ ^ 2) := by
      unfold routePBurnolForwardDampingShift
      measurability
    exact hm.aestronglyMeasurable.restrict
  have hshiftedInt : IntegrableOn
      (fun L : ℝ => ‖routePBurnolForwardDampingShift c f L‖ ^ 2) (Ioi 0) := by
    refine Integrable.mono' hshift hmeas ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with L hL
    simpa [g] using routePBurnolForwardDampingShift_norm_sq_le hc hL f
  have hmono :
      (∫ L : ℝ in Ioi 0,
          ‖routePBurnolForwardDampingShift c f L‖ ^ 2) ≤
        ∫ L : ℝ in Ioi 0, g (L + c) := by
    exact setIntegral_mono_on hshiftedInt hshift measurableSet_Ioi
      (fun L hL => routePBurnolForwardDampingShift_norm_sq_le hc hL f)
  have htailLe : (∫ u : ℝ in Ioi c, g u) ≤ ∫ u : ℝ in Ioi 0, g u := by
    exact setIntegral_mono_set hf
      (Filter.Eventually.of_forall fun L => sq_nonneg ‖f L‖)
      (Filter.Eventually.of_forall hsub)
  rw [routePBurnolApertureEnergy]
  refine hmono.trans ?_
  rw [routePIntegral_Ioi_comp_add_eq g c]
  exact htailLe

/-- Exact energy decay on every universal Burnol conormal eigenfeature. -/
theorem routePBurnolApertureEnergy_forwardDampingShift_windowFeature
    {c : ℝ} (hc : 0 ≤ c) {z : ℂ} :
    routePBurnolApertureEnergy
        (routePBurnolForwardDampingShift c
          (xiWardCubicBurnolWindowConormalFeature · z)) =
      Real.exp (-2 * c * (z.re - 1 / 2)) *
        routePBurnolApertureEnergy
          (xiWardCubicBurnolWindowConormalFeature · z) := by
  rw [routePBurnolApertureEnergy]
  calc
    (∫ L : ℝ in Ioi 0,
        ‖routePBurnolForwardDampingShift c
          (xiWardCubicBurnolWindowConormalFeature · z) L‖ ^ 2) =
        ∫ L : ℝ in Ioi 0,
          Real.exp (-2 * c * (z.re - 1 / 2)) *
            ‖xiWardCubicBurnolWindowConormalFeature L z‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro L hL
      change ‖routePBurnolForwardDampingShift c
          (xiWardCubicBurnolWindowConormalFeature · z) L‖ ^ 2 = _
      rw [routePBurnolForwardDampingShift_windowFeature hc hL]
      rw [norm_mul, Complex.norm_exp]
      have hre : (-((z - 1 / 2) * (c : ℂ))).re = -c * (z.re - 1 / 2) := by
        simp [Complex.mul_re]
        ring_nf
      rw [hre]
      have hexp : Real.exp (-c * (z.re - 1 / 2)) ^ 2 =
          Real.exp (-2 * c * (z.re - 1 / 2)) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring_nf
      rw [mul_pow, hexp]
    _ = Real.exp (-2 * c * (z.re - 1 / 2)) *
        ∫ L : ℝ in Ioi 0,
          ‖xiWardCubicBurnolWindowConormalFeature L z‖ ^ 2 := by
      rw [MeasureTheory.integral_const_mul]

/-- Primitive damping is exactly `exp(-2c lambda)` on energy, independently of ordinate. -/
theorem routePBurnolApertureEnergy_forwardDampingShift_primitiveFeature
    {c : ℝ} (hc : 0 ≤ c) (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    routePBurnolApertureEnergy
        (routePBurnolForwardDampingShift c
          (routePPrimitiveBurnolWindowFeature pe kappa)) =
      Real.exp (-2 * c * xiGammaEulerPrimitiveLogFrequency pe) *
        routePBurnolApertureEnergy
          (routePPrimitiveBurnolWindowFeature pe kappa) := by
  rw [routePBurnolApertureEnergy]
  calc
    (∫ L : ℝ in Ioi 0,
        ‖routePBurnolForwardDampingShift c
          (routePPrimitiveBurnolWindowFeature pe kappa) L‖ ^ 2) =
        ∫ L : ℝ in Ioi 0,
          Real.exp (-2 * c * xiGammaEulerPrimitiveLogFrequency pe) *
            ‖routePPrimitiveBurnolWindowFeature pe kappa L‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro L hL
      change ‖routePBurnolForwardDampingShift c
          (routePPrimitiveBurnolWindowFeature pe kappa) L‖ ^ 2 = _
      rw [routePBurnolForwardDampingShift_primitiveFeature hc hL]
      rw [norm_mul, Complex.norm_exp]
      simp [Complex.mul_re]
      have hexp : Real.exp (-(c * xiGammaEulerPrimitiveLogFrequency pe)) ^ 2 =
          Real.exp (-2 * c * xiGammaEulerPrimitiveLogFrequency pe) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring_nf
      rw [mul_pow, hexp]
      ring_nf
    _ = Real.exp (-2 * c * xiGammaEulerPrimitiveLogFrequency pe) *
        ∫ L : ℝ in Ioi 0,
          ‖routePPrimitiveBurnolWindowFeature pe kappa L‖ ^ 2 := by
      rw [MeasureTheory.integral_const_mul]

/-- Each primitive Burnol feature has exactly the corresponding P-G186 base Gram diagonal as its
positive-aperture energy. -/
theorem routePBurnolApertureEnergy_primitiveFeature_eq_baseWeight
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    routePBurnolApertureEnergy
        (routePPrimitiveBurnolWindowFeature pe kappa) =
      routePPrimitiveBaseCauchyCubicWeight pe := by
  let pe₁ : Fin 1 → Nat.Primes × ℕ := fun _ => pe
  let kappa₁ : Fin 1 → ℝ := fun _ => kappa
  have hcomplex :
      (∫ L : ℝ in Ioi 0,
        star (routePPrimitiveBurnolWindowFeature pe kappa L) *
          routePPrimitiveBurnolWindowFeature pe kappa L) =
        (routePPrimitiveBaseCauchyCubicWeight pe : ℂ) := by
    calc
      (∫ L : ℝ in Ioi 0,
        star (routePPrimitiveBurnolWindowFeature pe kappa L) *
          routePPrimitiveBurnolWindowFeature pe kappa L) =
          routePPrimitiveBurnolWindowGramMatrix pe₁ kappa₁ 0 0 := by rfl
      _ = routePPrimitiveBaseCauchyCubicKernelMatrix 1 pe₁ kappa₁ 0 0 := by
        rw [routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy]
      _ = (routePPrimitiveBaseCauchyCubicWeight pe : ℂ) := by
        simpa [pe₁] using
          routePPrimitiveBaseCauchyCubicKernelMatrix_diagonal
            (N := 1) (R := 1) (by norm_num) pe₁ kappa₁ 0
  have hcast :
      ((routePBurnolApertureEnergy
        (routePPrimitiveBurnolWindowFeature pe kappa) : ℝ) : ℂ) =
        ∫ L : ℝ in Ioi 0,
          star (routePPrimitiveBurnolWindowFeature pe kappa L) *
            routePPrimitiveBurnolWindowFeature pe kappa L := by
    rw [routePBurnolApertureEnergy, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with L
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [hcomplex] at hcast
  exact_mod_cast hcast

/-- Semigroup energy time `c` is exactly joint Dirichlet damping `s = 2c`. -/
theorem routePPrimitiveBurnolEnergyDampingFactor_eq_jointDampingPower
    (c : ℝ) (pe : Nat.Primes × ℕ) :
    Real.exp (-2 * c * xiGammaEulerPrimitiveLogFrequency pe) =
      (xiGammaEulerValuationNat pe : ℝ) ^ (-(2 * c)) := by
  have hnNat : xiGammaEulerValuationNat pe ≠ 0 := by
    unfold xiGammaEulerValuationNat
    exact pow_ne_zero _ pe.1.property.ne_zero
  have hn : 0 < (xiGammaEulerValuationNat pe : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hnNat
  rw [xiGammaEulerPrimitiveLogFrequency, Real.rpow_def_of_pos hn]
  congr 1
  ring_nf

/-- Base mass after aperture time `c`: the P-G186 Gram diagonal times its semigroup energy
eigenvalue. -/
def routePPrimitiveBurnolSemigroupBaseMass
    (c : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  routePPrimitiveBaseCauchyCubicWeight pe *
    Real.exp (-2 * c * xiGammaEulerPrimitiveLogFrequency pe)

/-- The dynamically damped feature energy is literally the semigroup base mass. -/
theorem routePBurnolApertureEnergy_forwardDampingShift_primitiveFeature_eq_baseMass
    {c : ℝ} (hc : 0 ≤ c) (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    routePBurnolApertureEnergy
        (routePBurnolForwardDampingShift c
          (routePPrimitiveBurnolWindowFeature pe kappa)) =
      routePPrimitiveBurnolSemigroupBaseMass c pe := by
  rw [routePBurnolApertureEnergy_forwardDampingShift_primitiveFeature hc,
    routePBurnolApertureEnergy_primitiveFeature_eq_baseWeight,
    routePPrimitiveBurnolSemigroupBaseMass]
  ring_nf

theorem routePPrimitiveBurnolSemigroupBaseMass_eq_jointDampingWeight
    (c : ℝ) (pe : Nat.Primes × ℕ) :
    routePPrimitiveBurnolSemigroupBaseMass c pe =
      routePPrimitiveBaseJointDampingWeight (2 * c) pe := by
  rw [routePPrimitiveBurnolSemigroupBaseMass,
    routePPrimitiveBaseJointDampingWeight,
    routePPrimitiveBurnolEnergyDampingFactor_eq_jointDampingPower]

/-- The semigroup-weighted primitive Gram diagonal is summable exactly at nonnegative aperture
time. This is the P-G185 wall in its source-window dynamical coordinate. -/
theorem summable_routePPrimitiveBurnolSemigroupBaseMass_iff
    (c : ℝ) :
    Summable (routePPrimitiveBurnolSemigroupBaseMass c) ↔ 0 ≤ c := by
  have hfun : routePPrimitiveBurnolSemigroupBaseMass c =
      routePPrimitiveBaseJointDampingWeight (2 * c) := by
    funext pe
    exact routePPrimitiveBurnolSemigroupBaseMass_eq_jointDampingWeight c pe
  rw [hfun, summable_routePPrimitiveBaseJointDampingWeight_iff]
  constructor <;> intro h <;> linarith

/-- The reciprocal-square singularity created at the translated aperture boundary is not locally
integrable. -/
theorem routeP_not_integrableOn_translated_inverseSquare (a : ℝ) :
    ¬ IntegrableOn (fun L : ℝ => (L - a) ^ (-2 : ℝ)) (Ioo a (a + 1)) := by
  intro h
  have hcomp : IntegrableOn
      ((fun L : ℝ => (L - a) ^ (-2 : ℝ)) ∘ fun x : ℝ => x + a)
      ((fun x : ℝ => x + a) ⁻¹' Ioo a (a + 1)) :=
    ((measurePreserving_add_right volume a).integrableOn_comp_preimage
      (measurableEmbedding_addRight a)).mpr h
  have hbase : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioo 0 1) := by
    simpa [Function.comp_def] using hcomp
  have hexponent : (-1 : ℝ) < -2 :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mp hbase
  norm_num at hexponent

/-- Compactly supported unit boundary datum used to expose the negative-time aperture pole. -/
def routePBurnolBackwardWallTest (u : ℝ) : ℂ :=
  (Ioo (0 : ℝ) 1).indicator (fun _ => 1) u

/-- The boundary-wall datum has finite positive-aperture squared energy. -/
theorem routePBurnolBackwardWallTest_integrable :
    IntegrableOn (fun u : ℝ => ‖routePBurnolBackwardWallTest u‖ ^ 2) (Ioi 0) := by
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 1) :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hind : Integrable ((Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hconst
  have heq : (fun u : ℝ => ‖routePBurnolBackwardWallTest u‖ ^ 2) =
      (Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
    funext u
    by_cases hu : u ∈ Ioo (0 : ℝ) 1 <;>
      simp [routePBurnolBackwardWallTest, hu]
  rw [heq]
  exact hind.integrableOn

theorem norm_sq_routePBurnolForwardDampingShift_backwardWallTest
    {c L : ℝ} (hL : L ∈ Ioo (-c) (-c + 1)) :
    ‖routePBurnolForwardDampingShift c routePBurnolBackwardWallTest L‖ ^ 2 =
      (L / (L + c)) ^ 2 := by
  have harg : L + c ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hL.1, hL.2]
  rw [routePBurnolForwardDampingShift]
  have htest : routePBurnolBackwardWallTest (L + c) = 1 := by
    simp [routePBurnolBackwardWallTest, harg]
  rw [htest, mul_one, norm_real, Real.norm_eq_abs, sq_abs]

/-- Every negative damping time sends one finite-energy boundary datum outside the positive-aperture
`L²` space. Hence the forward contraction semigroup has a sharp wall at time zero. -/
theorem routePBurnolForwardDampingShift_negative_not_integrable
    {c : ℝ} (hc : c < 0) :
    ¬ IntegrableOn
      (fun L : ℝ =>
        ‖routePBurnolForwardDampingShift c routePBurnolBackwardWallTest L‖ ^ 2)
      (Ioi 0) := by
  intro hout
  let a : ℝ := -c
  have ha : 0 < a := by dsimp [a]; linarith
  have hsubset : Ioo a (a + 1) ⊆ Ioi (0 : ℝ) := by
    intro L hL
    exact mem_Ioi.mpr (ha.trans hL.1)
  have hlocal : IntegrableOn
      (fun L : ℝ =>
        ‖routePBurnolForwardDampingShift c routePBurnolBackwardWallTest L‖ ^ 2)
      (Ioo a (a + 1)) :=
    hout.mono_set hsubset
  have hscaled : IntegrableOn
      (fun L : ℝ => (a ^ 2)⁻¹ *
        ‖routePBurnolForwardDampingShift c routePBurnolBackwardWallTest L‖ ^ 2)
      (Ioo a (a + 1)) :=
    hlocal.const_mul (a ^ 2)⁻¹
  have htarget : IntegrableOn
      (fun L : ℝ => (L - a) ^ (-2 : ℝ)) (Ioo a (a + 1)) := by
    apply Integrable.mono' hscaled
    · have hm : Measurable (fun L : ℝ => (L - a) ^ (-2 : ℝ)) := by
        fun_prop
      exact hm.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with L hL
      have hx : 0 < L - a := by linarith [hL.1]
      have ha0 : a ≠ 0 := ha.ne'
      have hx0 : L - a ≠ 0 := hx.ne'
      have hinterval : L ∈ Ioo (-c) (-c + 1) := by
        simpa [a] using hL
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hx.le (-2 : ℝ)),
        norm_sq_routePBurnolForwardDampingShift_backwardWallTest hinterval]
      have hden : L + c = L - a := by dsimp [a]; ring_nf
      rw [hden]
      have hrpow : (L - a) ^ (-2 : ℝ) = ((L - a) ^ 2)⁻¹ := by
        rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
          Real.rpow_neg hx.le, Real.rpow_two]
      rw [hrpow]
      field_simp
      nlinarith [sq_nonneg (L - a), sq_nonneg a]
  exact routeP_not_integrableOn_translated_inverseSquare a htarget

end

end RHTower
