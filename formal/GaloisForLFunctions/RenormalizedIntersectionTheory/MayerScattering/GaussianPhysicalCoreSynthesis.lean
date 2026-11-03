import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.PhysicalCoreSpectralBounds
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.PhysicalCoresHaveFiniteHeckeCuspEnergy
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.WindowWeilCorePackets
import GaloisForLFunctions.RHTower.WeilPositivityConductorObstruction
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery

/-! Gaussian damping makes the actual resonance cores summable in upper Haar square energy.
The same height damping respects the coefficient reflection; removing it recovers the complete
Weil form. Convergence alone supplies no positivity of that form. -/

set_option autoImplicit false

noncomputable section
open Complex Set MeasureTheory Filter Topology Zeta23
open scoped lp ENNReal ComplexConjugate
open GaloisForLFunctions
open CohomologyOfWindowsOfSpecZ ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry
open ArithmeticPolarization SpacingScaleHarmonicAnalysis


namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

private theorem gaussian_weight_majorant {ε : ℝ} (hε : 0 < ε) (B : ℝ) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y ≥ 0,
      Real.exp (-ε * y ^ 2) * (1 + y) ^ N * Real.exp (B * y) ≤ K / (1 + y ^ 2) := by
  let D : ℝ := B + (N + 2 : ℕ)
  refine ⟨Real.exp (D ^ 2 / (4 * ε)), (Real.exp_pos _).le, fun y hy => ?_⟩
  have hpow (n : ℕ) : (1 + y) ^ n ≤ Real.exp ((n : ℝ) * y) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Nat.cast_succ, add_mul, one_mul, Real.exp_add]
      exact mul_le_mul ih (by simpa only [add_comm] using Real.add_one_le_exp y)
        (by linarith : 0 ≤ 1 + y) (Real.exp_pos _).le
  have hpoly : (1 + y ^ 2) * (1 + y) ^ N ≤ (1 + y) ^ (N + 2) := by
    rw [pow_add, pow_two]
    nlinarith only [pow_nonneg (show 0 ≤ 1 + y by linarith) N,
      mul_nonneg hy (pow_nonneg (show 0 ≤ 1 + y by linarith) N)]
  have hquad : -ε * y ^ 2 + D * y ≤ D ^ 2 / (4 * ε) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * ε)).mpr
    nlinarith only [sq_nonneg (2 * ε * y - D)]
  apply (le_div_iff₀ (by positivity : 0 < 1 + y ^ 2)).mpr
  calc
    _ = ((1 + y ^ 2) * (1 + y) ^ N) * Real.exp (-ε * y ^ 2 + B * y) := by
      rw [Real.exp_add]
      ring
    _ ≤ (1 + y) ^ (N + 2) * Real.exp (-ε * y ^ 2 + B * y) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ ≤ Real.exp ((N + 2 : ℕ) * y) * Real.exp (-ε * y ^ 2 + B * y) :=
      mul_le_mul_of_nonneg_right (hpow (N + 2)) (Real.exp_pos _).le
    _ = Real.exp (-ε * y ^ 2 + D * y) := by rw [← Real.exp_add]; congr 1; dsimp [D]; ring
    _ ≤ _ := Real.exp_le_exp.mpr hquad






private theorem upperMayer_height_weight_summable :
    Summable (fun s : upperMayerResonances => 1 / (1 + s.1.im ^ 2)) := by
  have hsum := RHTower.summable_zetaZeroConfig.comp_injective upperMayerZero_injective
  refine Summable.of_nonneg_of_le (fun s => by positivity) (fun s => ?_) (hsum.mul_left 5)
  have hm : (1 : ℝ) ≤ zetaZeroConfig.mult (upperMayerZero s) := by
    exact_mod_cast zetaZeroConfig.one_le_mult _ (upperMayerZero s).2
  have hr0 := s.2.2.1
  have hr1 := s.2.2.2.1
  have he : Complex.normSq (gammaOf (upperMayerZero s)) =
      (2 * s.1.im) ^ 2 + (2 * s.1.re - 1 / 2) ^ 2 := by
    simp [upperMayerZero, gammaOf, Complex.div_I, Complex.normSq_apply]
    ring
  have hd : 1 + Complex.normSq (gammaOf (upperMayerZero s)) ≤ 5 * (1 + s.1.im ^ 2) := by
    rw [he]
    nlinarith only [sq_nonneg s.1.im, mul_nonneg hr0.le (show 0 ≤ 1 / 2 - s.1.re by linarith)]
  have hden : 0 < 1 + Complex.normSq (gammaOf (upperMayerZero s)) := by
    have := Complex.normSq_nonneg (gammaOf (upperMayerZero s))
    linarith
  change 1 / (1 + s.1.im ^ 2) ≤
    5 * ((zetaZeroConfig.mult (upperMayerZero s) : ℝ) /
      (1 + Complex.normSq (gammaOf (upperMayerZero s))))
  calc
    _ ≤ 5 / (1 + Complex.normSq (gammaOf (upperMayerZero s))) := by
      apply (div_le_div_iff₀ (by positivity) hden).mpr
      simpa only [one_mul] using hd
    _ ≤ _ := by rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith) hden.le

/-- Every positive Gaussian dominates polynomial-exponential growth over the actual resonances. -/
theorem upperMayer_gaussian_growth_summable {ε : ℝ} (hε : 0 < ε) (B : ℝ) (N : ℕ) :
    Summable (fun s : upperMayerResonances =>
      Real.exp (-ε * s.1.im ^ 2) * (1 + s.1.im) ^ N * Real.exp (B * s.1.im)) := by
  obtain ⟨K, hK, hb⟩ := gaussian_weight_majorant hε B N
  refine Summable.of_nonneg_of_le (fun s => by have hy := s.2.1; positivity) (fun s => ?_)
    (upperMayer_height_weight_summable.mul_left K)
  simpa only [mul_one_div] using hb s.1.im s.2.1.le

/-- The actual core divided by `√a`; Lebesgue square energy is its Haar square energy. -/
def physicalCoreColumnFun (s : upperMayerResonances) (a : ℝ) : ℂ :=
  mayerPeriodCore s.1 a / (Real.sqrt a : ℂ)

private theorem physicalCoreColumnFun_norm_sq (s : upperMayerResonances) {a : ℝ}
    (ha : 0 < a) : ‖physicalCoreColumnFun s a‖ ^ 2 = ‖mayerPeriodCore s.1 a‖ ^ 2 / a := by
  rw [physicalCoreColumnFun, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt ha.le]

private theorem physicalCoreColumnFun_memLp (s : upperMayerResonances) :
    MemLp (physicalCoreColumnFun s) 2 (volume.restrict (Ioi (1 : ℝ))) := by
  have hm : Measurable (physicalCoreColumnFun s) := by
    unfold physicalCoreColumnFun
    exact (mayerPeriodCore_measurable s.2.1).div (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hi := (lewisHeckeWord_mayerPeriodCore_finite_cusp_energy
    s.2.2.1 s.2.2.2.1 s.2.1 []).1
  simp only [lewisHeckeWord] at hi
  refine hi.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  exact (physicalCoreColumnFun_norm_sq s (zero_lt_one.trans ha)).symm

/-- Actual resonance core as an element of upper Haar `L²`, represented in Lebesgue `L²`. -/
def physicalCoreColumn (s : upperMayerResonances) : Lp ℂ 2 (volume.restrict (Ioi (1 : ℝ))) :=
  (physicalCoreColumnFun_memLp s).toLp (physicalCoreColumnFun s)

private theorem physicalCoreColumn_norm_sq (s : upperMayerResonances) :
    ‖physicalCoreColumn s‖ ^ 2 = ∫ a in Ioi (1 : ℝ), ‖mayerPeriodCore s.1 a‖ ^ 2 / a := by
  have hn : ‖physicalCoreColumn s‖ ^ 2 =
      ∫ a in Ioi (1 : ℝ), ‖physicalCoreColumn s a‖ ^ 2 := by
    rw [Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable _),
      lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal)) (by norm_num) (by norm_num)
        (Lp.aestronglyMeasurable _)]
    norm_num [← Real.sqrt_eq_rpow]
    rw [Real.sq_sqrt]
    exact integral_nonneg fun a => sq_nonneg _
  rw [hn]
  apply integral_congr_ae
  filter_upwards [(physicalCoreColumnFun_memLp s).coeFn_toLp,
    ae_restrict_mem measurableSet_Ioi] with a ha ha1
  rw [show physicalCoreColumn s a = physicalCoreColumnFun s a from ha]
  exact physicalCoreColumnFun_norm_sq s (zero_lt_one.trans ha1)

private theorem physicalCoreColumn_norm_le (s : upperMayerResonances) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a > 0, ‖mayerPeriodCore s.1 a‖ ≤ C * a ^ (-s.1.re)) :
    ‖physicalCoreColumn s‖ ≤ 11 * C * (1 + s.1.im) := by
  have hr : 0 < s.1.re := s.2.2.1
  have hp : -2 * s.1.re - 1 < -1 := by linarith
  have hmajor : IntegrableOn (fun a : ℝ => C ^ 2 * a ^ (-2 * s.1.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hp zero_lt_one).const_mul _
  have hi := (lewisHeckeWord_mayerPeriodCore_finite_cusp_energy
    s.2.2.1 s.2.2.2.1 s.2.1 []).1
  simp only [lewisHeckeWord] at hi
  have hsq : ‖physicalCoreColumn s‖ ^ 2 ≤ C ^ 2 / (2 * s.1.re) := by
    rw [physicalCoreColumn_norm_sq]
    calc
      _ ≤ ∫ a in Ioi (1 : ℝ), C ^ 2 * a ^ (-2 * s.1.re - 1) := by
        apply setIntegral_mono_on hi hmajor measurableSet_Ioi
        intro a ha
        have ha0 : 0 < a := zero_lt_one.trans ha
        have hpow : (a ^ (-s.1.re)) ^ 2 / a = a ^ (-2 * s.1.re - 1) := by
          rw [← Real.rpow_natCast (a ^ (-s.1.re)) 2, ← Real.rpow_mul ha0.le,
            div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add ha0]
          congr 1
          norm_num
          ring
        calc
          _ ≤ (C * a ^ (-s.1.re)) ^ 2 / a :=
            div_le_div_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg _) (hb a ha0) 2) ha0.le
          _ = _ := by rw [mul_pow, mul_div_assoc, hpow]
      _ = _ := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt hp zero_lt_one]
        simp only [Real.one_rpow]
        field_simp
        ring
  have hrec := mul_le_mul_of_nonneg_left (upperMayerResonance_reciprocal_bound s).2
    (sq_nonneg C)
  have hy := s.2.1
  have hsq' : ‖physicalCoreColumn s‖ ^ 2 ≤ (11 * C * (1 + s.1.im)) ^ 2 := by
    have hpoly : 116 * s.1.im ≤ (11 * (1 + s.1.im)) ^ 2 := by
      nlinarith only [sq_nonneg s.1.im, hy.le]
    have hh := mul_le_mul_of_nonneg_left hpoly (sq_nonneg C)
    calc
      _ ≤ C ^ 2 / (2 * s.1.re) := hsq
      _ = C ^ 2 * (1 / (2 * s.1.re)) := by ring
      _ ≤ C ^ 2 * (116 * s.1.im) := hrec
      _ ≤ C ^ 2 * (11 * (1 + s.1.im)) ^ 2 := hh
      _ = _ := by ring
  have hright : 0 ≤ 11 * C * (1 + s.1.im) := by positivity
  nlinarith only [hsq', norm_nonneg (physicalCoreColumn s), hright]

/-- Gaussian-regularized synthesis of the actual cores from existing zero coordinates. -/
def gaussianPhysicalCore (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (a : ℝ) : ℂ :=
  ∑' s : upperMayerResonances,
    (Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s) * mayerPeriodCore s.1 a

private theorem norm_gaussianPhysicalColumn_summable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    Summable (fun s : upperMayerResonances =>
      ‖((Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s)) • physicalCoreColumn s‖) := by
  obtain ⟨C, N, hC, hb⟩ := upperMayerCore_growth_bound
  have hsum := (upperMayer_gaussian_growth_summable hε (Real.pi / 2) (N + 1)).mul_left
    (11 * C * ‖x‖)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s => ?_) hsum
  have hy := s.2.1
  have hcoef := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) x (upperMayerZero s)
  have hcol := physicalCoreColumn_norm_le s
    (show 0 ≤ C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2) by positivity)
    (hb s)
  rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ (Real.exp (-ε * s.1.im ^ 2) * ‖x‖) *
        (11 * (C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2)) * (1 + s.1.im)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcoef (Real.exp_pos _).le) hcol
        (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [pow_succ, show Real.pi / 2 * s.1.im = Real.pi * s.1.im / 2 by ring]
      ring

/-- Every positive Gaussian parameter gives an absolutely convergent actual-core series
in upper Haar `L²`. The coefficient vector is the existing CWS zero space. -/
theorem gaussianPhysicalColumn_summable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    Summable (fun s : upperMayerResonances =>
      ((Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s)) • physicalCoreColumn s) :=
  (norm_gaussianPhysicalColumn_summable hε x).of_norm

private theorem physicalCore_pointwise_growth_bound (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : upperMayerResonances,
      ‖mayerPeriodCore s.1 a‖ ≤ C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2) := by
  obtain ⟨C, N, hC, hb⟩ := upperMayerCore_growth_bound
  refine ⟨C * (1 + a⁻¹), N, by positivity, fun s => ?_⟩
  have hy := s.2.1
  have hp : a ^ (-s.1.re) ≤ 1 + a⁻¹ := by
    by_cases ha1 : 1 ≤ a
    · have hh : a ^ (-s.1.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha1 (by linarith [s.2.2.1])
      exact hh.trans (by have := inv_nonneg.mpr ha.le; linarith)
    · have hh : a ^ (-s.1.re) ≤ a ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge ha (not_le.mp ha1).le (by linarith [s.2.2.2.1])
      rw [Real.rpow_neg_one] at hh
      linarith only [hh]
  calc
    _ ≤ (C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2)) * (1 + a⁻¹) :=
      (hb s a ha).trans (mul_le_mul_of_nonneg_left hp (by positivity))
    _ = _ := by ring

/-- At every positive physical coordinate, Gaussian synthesis converges absolutely. -/
theorem gaussianPhysicalCore_summable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) {a : ℝ} (ha : 0 < a) :
    Summable (fun s : upperMayerResonances =>
      ‖(Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s) * mayerPeriodCore s.1 a‖) := by
  obtain ⟨C, N, hC, hb⟩ := physicalCore_pointwise_growth_bound a ha
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s => ?_)
    ((upperMayer_gaussian_growth_summable hε (Real.pi / 2) N).mul_left (C * ‖x‖))
  have hy := s.2.1
  have hcoef := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) x (upperMayerZero s)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ (Real.exp (-ε * s.1.im ^ 2) * ‖x‖) *
        (C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcoef (Real.exp_pos _).le) (hb s)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [show Real.pi / 2 * s.1.im = Real.pi * s.1.im / 2 by ring]; ring

/-- Summability of the positive height weight makes the upper resonance set countable. -/
theorem upperMayerResonances_countable : Countable upperMayerResonances := by
  apply countable_univ_iff.mp
  refine upperMayer_height_weight_summable.countable_support.mono ?_
  intro s _
  change 1 / (1 + s.1.im ^ 2) ≠ 0
  positivity

/-- The norm-convergent sum represents the literal pointwise core series. -/
theorem gaussianPhysicalCore_eq_Lp_tsum {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    (fun a => (∑' s : upperMayerResonances,
      ((Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s)) • physicalCoreColumn s) a)
      =ᵐ[volume.restrict (Ioi (1 : ℝ))]
      fun a => gaussianPhysicalCore ε x a / (Real.sqrt a : ℂ) := by
  letI := upperMayerResonances_countable
  have hcoe := Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr
    (norm_gaussianPhysicalColumn_summable hε x))
  have hterm : ∀ᵐ a ∂volume.restrict (Ioi (1 : ℝ)), ∀ s : upperMayerResonances,
      (((Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s)) • physicalCoreColumn s) a =
        (Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s) *
          (mayerPeriodCore s.1 a / (Real.sqrt a : ℂ)) := by
    apply ae_all_iff.mpr
    intro s
    filter_upwards [Lp.coeFn_smul ((Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s))
        (physicalCoreColumn s), (physicalCoreColumnFun_memLp s).coeFn_toLp] with a ha hb
    rw [ha]
    change ((Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s)) * physicalCoreColumn s a = _
    rw [show physicalCoreColumn s a = physicalCoreColumnFun s a from hb]
    rfl
  filter_upwards [hcoe, hterm] with a ha hb
  rw [ha, gaussianPhysicalCore, ← tsum_div_const]
  exact tsum_congr fun s => (hb s).trans (by ring)

/-- The actual Gaussian sum has finite upper Haar square energy. -/
theorem gaussianPhysicalCore_finite_haar_energy {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    IntegrableOn (fun a : ℝ => ‖gaussianPhysicalCore ε x a‖ ^ 2 / a) (Ioi 1) := by
  have hm := (memLp_congr_ae (gaussianPhysicalCore_eq_Lp_tsum hε x)).mp (Lp.memLp _)
  have hi := (memLp_two_iff_integrable_sq_norm hm.1).mp hm
  refine hi.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    div_pow, Real.sq_sqrt (zero_lt_one.trans ha).le]

private theorem window_upper_sum_summable {A : ℝ} (H : windowTests A) :
    Summable (fun s : upperMayerResonances =>
      zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1)) := by
  have h := summable_Wsummand zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig
    (cx_contDiff H.2.contDiff) (cx_hasCompactSupport H.2.hasCompactSupport)
    (cx_contDiff H.2.contDiff) (cx_hasCompactSupport H.2.hasCompactSupport)
  exact h.comp_injective (i := upperMayerZero) upperMayerZero_injective

/-- Gaussian-damped reflection pairing, using the same coefficients as physical synthesis. -/
def gaussianWindowWeilEnergy {A : ℝ} (ε : ℝ) (H : windowTests A) : ℝ :=
  2 * (∑' s : upperMayerResonances,
    (Real.exp (-2 * ε * s.1.im ^ 2) : ℂ) *
      zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1)).re

private theorem window_reflected_coordinate_product {A : ℝ} (H : windowTests A)
    (s : upperMayerResonances) :
    windowZeroMap A H (upperMayerZero s) *
      conj (windowZeroMap A H (upperMayerZero (reflectUpperResonance s))) =
      zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1) := by
  rw [upperMayerZero_reflect]
  have hm := zetaZeroConfig.mult_reflect (upperMayerZero s : ℂ) (upperMayerZero s).2
  have hsq : (Real.sqrt (zetaZeroConfig.mult (upperMayerZero s)) : ℂ) *
      (Real.sqrt (zetaZeroConfig.mult (upperMayerZero s)) : ℂ) =
      (zetaZeroConfig.mult (upperMayerZero s) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  change zeroCoord zetaZeroConfig (cx H) (upperMayerZero s) *
    conj (zeroCoord zetaZeroConfig (cx H) (reflectCarrier zetaZeroConfig (upperMayerZero s))) =
      zetaZeroConfig.Wsummand (cx H) (cx H) (upperMayerZero s)
  simp only [zeroCoord, reflectCarrier, hm, gammaOf_reflect, map_mul,
    Complex.conj_ofReal, ZeroConfig.Wsummand]
  linear_combination (paperFT (cx H) (gammaOf (upperMayerZero s)) *
    conj (paperFT (cx H) (conj (gammaOf (upperMayerZero s))))) * hsq

/-- Height damping commutes with the PM reflection and gives exactly the damped Weil summand. -/
theorem gaussian_window_reflection_product {A : ℝ} (ε : ℝ) (H : windowTests A)
    (s : upperMayerResonances) :
    ((Real.exp (-ε * s.1.im ^ 2) : ℂ) * windowZeroMap A H (upperMayerZero s)) *
      conj ((Real.exp (-ε * (reflectUpperResonance s).1.im ^ 2) : ℂ) *
        windowZeroMap A H (upperMayerZero (reflectUpperResonance s))) =
      (Real.exp (-2 * ε * s.1.im ^ 2) : ℂ) *
        zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1) := by
  have him : (reflectUpperResonance s).1.im = s.1.im := by
    simp [reflectUpperResonance_coe, riemannMayerReflect]
  rw [him, map_mul, Complex.conj_ofReal]
  calc
    _ = ((Real.exp (-ε * s.1.im ^ 2) : ℂ) * (Real.exp (-ε * s.1.im ^ 2) : ℂ)) *
        (windowZeroMap A H (upperMayerZero s) *
          conj (windowZeroMap A H (upperMayerZero (reflectUpperResonance s)))) := by ring
    _ = _ := by
      rw [window_reflected_coordinate_product, ← Complex.ofReal_mul, ← Real.exp_add,
        show -ε * s.1.im ^ 2 + -ε * s.1.im ^ 2 = -2 * ε * s.1.im ^ 2 by ring]

/-- The damped reflection sum is absolutely convergent for every nonnegative parameter. -/
theorem gaussianWindowWeilEnergy_summable {A : ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (H : windowTests A) :
    Summable (fun s : upperMayerResonances => (Real.exp (-2 * ε * s.1.im ^ 2) : ℂ) *
      zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1)) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s => ?_)
    (window_upper_sum_summable H).norm
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hε (sq_nonneg s.1.im)]))

/-- Removing Gaussian damping recovers the complete Weil form, with all multiplicities
and both half planes. This is convergence of the signed reflection pairing. -/
theorem tendsto_gaussianWindowWeilEnergy {A : ℝ} (H : windowTests A) :
    Tendsto (fun ε : ℝ => gaussianWindowWeilEnergy ε H) (𝓝[≥] 0) (𝓝 (weilQuad H)) := by
  have hlim : Tendsto (fun ε : ℝ => ∑' s : upperMayerResonances,
      (Real.exp (-2 * ε * s.1.im ^ 2) : ℂ) *
        zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1)) (𝓝[≥] 0)
      (𝓝 (∑' s : upperMayerResonances, zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1))) := by
    apply tendsto_tsum_of_dominated_convergence (window_upper_sum_summable H).norm
    · intro s
      have hc : Continuous (fun ε : ℝ =>
          (Real.exp (-2 * ε * s.1.im ^ 2) : ℂ) *
            zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1)) := by fun_prop
      simpa only [mul_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using
        (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε s
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (Real.exp_le_one_iff.mpr (by
          have hε0 : 0 ≤ ε := hε
          nlinarith only [mul_nonneg hε0 (sq_nonneg s.1.im)]))
  rw [weilQuad_eq_twice_upperMayer_sum]
  exact tendsto_const_nhds.mul (Complex.continuous_re.continuousAt.tendsto.comp hlim)

#print axioms gaussianPhysicalCore_summable
#print axioms gaussianPhysicalColumn_summable
#print axioms gaussianPhysicalCore_finite_haar_energy
#print axioms gaussian_window_reflection_product
#print axioms tendsto_gaussianWindowWeilEnergy

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
