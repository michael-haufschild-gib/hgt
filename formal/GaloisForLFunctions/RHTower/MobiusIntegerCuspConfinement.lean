/-
Exact integer-cutoff localization of Möbius Gamma--Hankel energy and covariance.

For every r > 1 and delta > 0, energy below (N+1)^(-2) tends to zero,
while energy above delta converges to the integrable infinite-source exterior.
Consequently, covariance minus the intervening moving-layer energy converges.
This theorem locates possible escape; it neither excludes escape nor proves RH.
-/
import GaloisForLFunctions.RHTower.MobiusLaplaceMellinPlancherelBridge

open Filter Topology Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

def finiteLaplaceEnergyDensity (a : ℕ → ℝ) (N : ℕ) (r x : ℝ) : ℝ :=
  x ^ (r - 1) * finiteRealLaplacePencil a N x ^ 2

def finiteLaplaceCuspEnergy (a : ℕ → ℝ) (N : ℕ) (r eta : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..eta, finiteLaplaceEnergyDensity a N r x

def integerCuspLowerScale (N : ℕ) : ℝ := ((N : ℝ) + 1) ^ (-2 : ℝ)

theorem continuous_finiteRealLaplacePencil (a : ℕ → ℝ) (N : ℕ) :
    Continuous (finiteRealLaplacePencil a N) := by
  unfold finiteRealLaplacePencil
  fun_prop

theorem continuous_finiteLaplaceEnergyDensity (a : ℕ → ℝ) (N : ℕ)
    {r : ℝ} (hr : 1 < r) : Continuous (finiteLaplaceEnergyDensity a N r) :=
  (Real.continuous_rpow_const (by linarith : 0 ≤ r - 1)).mul
    ((continuous_finiteRealLaplacePencil a N).pow 2)

theorem finiteLaplaceEnergyDensity_nonneg (a : ℕ → ℝ) (N : ℕ) (r : ℝ)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ finiteLaplaceEnergyDensity a N r x :=
  mul_nonneg (Real.rpow_nonneg hx _) (sq_nonneg _)

theorem abs_finiteRealLaplacePencil_le_cutoff (a : ℕ → ℝ)
    (ha : ∀ n, |a n| ≤ 1) (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |finiteRealLaplacePencil a N x| ≤ N := by
  unfold finiteRealLaplacePencil
  calc
    _ ≤ ∑ n ∈ Finset.range N, |a n * Real.exp (-((n + 1 : ℕ) : ℝ) * x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul (ha n) (Real.exp_le_one_iff.mpr (by
        rw [neg_mul]
        exact neg_nonpos.mpr (mul_nonneg (by positivity) hx)))
        (Real.exp_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = _ := by simp

/-- Exact polynomial small-scale envelope, with no arithmetic cancellation premise. -/
theorem finiteLaplaceCuspEnergy_le (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1)
    (N : ℕ) {r eta : ℝ} (hr : 1 < r) (heta : 0 ≤ eta) :
    finiteLaplaceCuspEnergy a N r eta ≤ (N : ℝ) ^ 2 * eta ^ r / r := by
  have hr0 : 0 < r := by linarith
  have hcont := continuous_finiteLaplaceEnergyDensity a N hr
  calc
    _ ≤ ∫ x in (0 : ℝ)..eta, x ^ (r - 1) * (N : ℝ) ^ 2 := by
      apply intervalIntegral.integral_mono_on (μ := volume) heta
        (hcont.intervalIntegrable _ _)
        (((Real.continuous_rpow_const (by linarith : 0 ≤ r - 1)).mul_const _).intervalIntegrable _ _)
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.1 _)
      have hb := abs_finiteRealLaplacePencil_le_cutoff a ha N hx.1
      nlinarith [sq_abs (finiteRealLaplacePencil a N x), abs_nonneg (finiteRealLaplacePencil a N x)]
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, integral_rpow (Or.inl (by linarith))]
      simp only [sub_add_cancel, Real.zero_rpow hr0.ne', sub_zero]
      ring

theorem integerCuspLowerScale_pos (N : ℕ) : 0 < integerCuspLowerScale N :=
  Real.rpow_pos_of_pos (by positivity) _

theorem tendsto_integerCuspLowerScale :
    Tendsto integerCuspLowerScale atTop (nhds 0) := by
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-- Every bounded-coefficient integer prefix has vanishing *unnormalized* energy
below `(N+1)^(-2)` on every strict-right energy exponent. -/
theorem tendsto_finiteLaplaceCuspEnergy_ultraviolet_zero
    (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1) {r : ℝ} (hr : 1 < r) :
    Tendsto (fun N => finiteLaplaceCuspEnergy a N r (integerCuspLowerScale N)) atTop (nhds 0) := by
  have hg : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (-(2 * r - 2)) / r)
      atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < 2 * r - 2)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)).div_const r
  apply squeeze_zero (fun N => ?_) (fun N => ?_) hg
  · exact intervalIntegral.integral_nonneg (integerCuspLowerScale_pos N).le
      (fun x hx => finiteLaplaceEnergyDensity_nonneg a N r hx.1)
  · have hb := finiteLaplaceCuspEnergy_le a ha N hr (integerCuspLowerScale_pos N).le
    calc
      _ ≤ (N : ℝ) ^ 2 * integerCuspLowerScale N ^ r / r := hb
      _ ≤ ((N : ℝ) + 1) ^ 2 * integerCuspLowerScale N ^ r / r := by
        apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ r)
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (integerCuspLowerScale_pos N).le r)
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
      _ = _ := by
        unfold integerCuspLowerScale
        rw [← Real.rpow_natCast ((N : ℝ) + 1) 2,
          ← Real.rpow_mul (by positivity), ← Real.rpow_add (by positivity)]
        congr 2
        ring

def laplaceDilationEnvelope (delta : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-(n : ℝ) * delta)

theorem summable_laplaceDilationEnvelope {delta : ℝ} (hdelta : 0 < delta) :
    Summable (fun n : ℕ => Real.exp (-(n : ℝ) * delta)) := by
  have h := summable_geometric_of_lt_one (Real.exp_nonneg (-delta))
    (Real.exp_lt_one_iff.mpr (by linarith : -delta < 0))
  apply h.congr
  intro n
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem abs_finiteRealLaplacePencil_le_dilationEnvelope
    (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1) (N : ℕ)
    {delta x : ℝ} (hdelta : 0 < delta) (hx : delta ≤ x) :
    |finiteRealLaplacePencil a N x| ≤ Real.exp (-x) * laplaceDilationEnvelope delta := by
  unfold finiteRealLaplacePencil
  calc
    _ ≤ ∑ n ∈ Finset.range N, |a n * Real.exp (-((n + 1 : ℕ) : ℝ) * x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N, Real.exp (-x) * Real.exp (-(n : ℝ) * delta) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-((n + 1 : ℕ) : ℝ) * x) ≤
          Real.exp (-x) * Real.exp (-(n : ℝ) * delta) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      exact (mul_le_mul_of_nonneg_right (ha n) (Real.exp_nonneg _)).trans (by simpa using he)
    _ ≤ ∑' n : ℕ, Real.exp (-x) * Real.exp (-(n : ℝ) * delta) :=
      ((summable_laplaceDilationEnvelope hdelta).mul_left _).sum_le_tsum _
        (fun n hn => by positivity)
    _ = _ := by rw [tsum_mul_left]; rfl

def finiteLaplaceExteriorEnergy (a : ℕ → ℝ) (N : ℕ) (r delta : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi delta, finiteLaplaceEnergyDensity a N r x

theorem finiteLaplaceEnergyDensity_le_exteriorEnvelope
    (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1) (N : ℕ) (r : ℝ)
    {delta x : ℝ} (hdelta : 0 < delta) (hx : delta ≤ x) :
    finiteLaplaceEnergyDensity a N r x ≤
      laplaceDilationEnvelope delta ^ 2 * (x ^ (r - 1) * Real.exp (-(2 * x))) := by
  have hb := abs_finiteRealLaplacePencil_le_dilationEnvelope a ha N hdelta hx
  have he0 : 0 ≤ Real.exp (-x) * laplaceDilationEnvelope delta := (abs_nonneg _).trans hb
  have hs : finiteRealLaplacePencil a N x ^ 2 ≤
      laplaceDilationEnvelope delta ^ 2 * Real.exp (-(2 * x)) := by
    have heq : (Real.exp (-x) * laplaceDilationEnvelope delta) ^ 2 =
        laplaceDilationEnvelope delta ^ 2 * Real.exp (-(2 * x)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      ring_nf
    rw [← heq, ← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) he0).mpr hb
  have hm := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg (hdelta.le.trans hx) (r - 1))
  simpa only [finiteLaplaceEnergyDensity, mul_left_comm] using hm

theorem integrableOn_laplaceExteriorEnvelope (delta : ℝ) {r : ℝ} (hr : 1 < r) :
    IntegrableOn (fun x : ℝ => laplaceDilationEnvelope delta ^ 2 *
      (x ^ (r - 1) * Real.exp (-(2 * x)))) (Ioi 0) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ (r - 1) * Real.exp (-(2 * x))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := r - 1) (b := 2)
        (by linarith) (by norm_num) (by norm_num))
  exact hint.const_mul _

theorem finiteLaplaceExteriorEnergy_le (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1)
    (N : ℕ) {r delta : ℝ} (hr : 1 < r) (hdelta : 0 < delta) :
    finiteLaplaceExteriorEnergy a N r delta ≤
      laplaceDilationEnvelope delta ^ 2 * ((1 / 2 : ℝ) ^ r * Real.Gamma r) := by
  have hr0 : 0 < r := by linarith
  have hsub : Ioi delta ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hdelta.le
  have henv := integrableOn_laplaceExteriorEnvelope delta hr
  calc
    _ ≤ ∫ x : ℝ in Ioi delta,
        laplaceDilationEnvelope delta ^ 2 * (x ^ (r - 1) * Real.exp (-(2 * x))) := by
      apply setIntegral_mono_on
        ((integrableOn_finiteRealLaplacePencil_sq a N hr0).mono_set hsub)
        (henv.mono_set hsub) measurableSet_Ioi
      intro x hx
      exact finiteLaplaceEnergyDensity_le_exteriorEnvelope a ha N r hdelta hx.le
    _ ≤ ∫ x : ℝ in Ioi (0 : ℝ),
        laplaceDilationEnvelope delta ^ 2 * (x ^ (r - 1) * Real.exp (-(2 * x))) := by
      apply setIntegral_mono_set henv _ hsub.eventuallyLE
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_nonneg _))
    _ = _ := by
      rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hr0 (by norm_num)]

theorem finiteLaplaceEnergy_split (a : ℕ → ℝ) (N : ℕ)
    {r delta : ℝ} (hr : 1 < r) (hdelta : 0 < delta) (eta : ℝ) :
    finiteGammaHankelEnergy a N r = finiteLaplaceCuspEnergy a N r eta +
      (∫ x in eta..delta, finiteLaplaceEnergyDensity a N r x) +
      finiteLaplaceExteriorEnergy a N r delta := by
  have hcont := continuous_finiteLaplaceEnergyDensity a N hr
  have hint := integrableOn_finiteRealLaplacePencil_sq a N (by linarith : 0 < r)
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint.mono_set (show Ioc 0 delta ⊆ Ioi (0 : ℝ) from fun x hx => hx.1))
    (hint.mono_set (Ioi_subset_Ioi hdelta.le))
  rw [Ioc_union_Ioi_eq_Ioi hdelta.le, integral_finiteRealLaplacePencil_sq a N (by linarith)] at hsplit
  rw [finiteLaplaceCuspEnergy, intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 eta) (hcont.intervalIntegrable eta delta),
    intervalIntegral.integral_of_le hdelta.le]
  exact hsplit

theorem abs_shiftedMobiusRealCoefficient_le_one (n : ℕ) :
    |shiftedMobiusRealCoefficient n| ≤ 1 := by
  unfold shiftedMobiusRealCoefficient
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n + 1)

def mobiusLaplaceExteriorEnergy (r delta : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi delta, x ^ (r - 1) * ‖mobiusDiscreteLaplaceTransform x‖ ^ 2

theorem tendsto_finiteMobiusEnergyDensity (r : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N => finiteLaplaceEnergyDensity shiftedMobiusRealCoefficient N r x) atTop
      (nhds (x ^ (r - 1) * ‖mobiusDiscreteLaplaceTransform x‖ ^ 2)) := by
  have h := ((tendsto_mobiusDiscreteLaplaceFiniteSection_atTop hx).norm.pow 2).const_mul
    (x ^ (r - 1))
  simpa only [mobiusDiscreteLaplaceFiniteSection_eq_finiteMobiusLaplacePencil,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, finiteMobiusLaplacePencil,
    finiteLaplaceEnergyDensity] using h

/-- The limiting exterior is genuinely integrable, not a totalized integral. -/
theorem integrableOn_mobiusLaplaceExteriorEnergy {r delta : ℝ}
    (hr : 1 < r) (hdelta : 0 < delta) :
    IntegrableOn (fun x : ℝ => x ^ (r - 1) * ‖mobiusDiscreteLaplaceTransform x‖ ^ 2)
      (Ioi delta) := by
  have hsub : Ioi delta ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hdelta.le
  have hcont : ContinuousOn (fun x : ℝ => x ^ (r - 1) * ‖mobiusDiscreteLaplaceTransform x‖ ^ 2)
      (Ioi delta) :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ r - 1)).continuousOn.mul
      ((continuousOn_mobiusDiscreteLaplaceTransform.mono hsub).norm.pow 2)
  apply ((integrableOn_laplaceExteriorEnvelope delta hr).mono_set hsub).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hdelta.trans hx
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (sq_nonneg _))]
  exact le_of_tendsto (tendsto_finiteMobiusEnergyDensity r hx0)
    (Filter.Eventually.of_forall (fun N => finiteLaplaceEnergyDensity_le_exteriorEnvelope
      _ abs_shiftedMobiusRealCoefficient_le_one N r hdelta hx.le))

/-- Every fixed positive-scale exterior converges without RH. -/
theorem tendsto_finiteMobiusLaplaceExteriorEnergy {r delta : ℝ}
    (hr : 1 < r) (hdelta : 0 < delta) :
    Tendsto (fun N => finiteLaplaceExteriorEnergy shiftedMobiusRealCoefficient N r delta)
      atTop (nhds (mobiusLaplaceExteriorEnergy r delta)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x => laplaceDilationEnvelope delta ^ 2 * (x ^ (r - 1) * Real.exp (-(2 * x))))
  · intro N
    exact (continuous_finiteLaplaceEnergyDensity shiftedMobiusRealCoefficient N hr).aestronglyMeasurable
  · exact (integrableOn_laplaceExteriorEnvelope delta hr).mono_set (Ioi_subset_Ioi hdelta.le)
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_of_nonneg (finiteLaplaceEnergyDensity_nonneg _ _ _ (hdelta.le.trans hx.le))]
    exact finiteLaplaceEnergyDensity_le_exteriorEnvelope _ abs_shiftedMobiusRealCoefficient_le_one
      N r hdelta hx.le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact tendsto_finiteMobiusEnergyDensity r (hdelta.trans hx)

def finiteMobiusMovingCuspEnergy (N : ℕ) (r delta : ℝ) : ℝ :=
  ∫ x in (integerCuspLowerScale N)..delta,
    finiteLaplaceEnergyDensity shiftedMobiusRealCoefficient N r x

/-- Exact unconditional localization: the part outside the moving integer cusp
converges to the actual positive-scale exterior of the infinite source. -/
theorem tendsto_mobiusEnergy_sub_movingCusp {r delta : ℝ}
    (hr : 1 < r) (hdelta : 0 < delta) :
    Tendsto (fun N => finiteMobiusGammaHankelEnergy N r - finiteMobiusMovingCuspEnergy N r delta)
      atTop (nhds (mobiusLaplaceExteriorEnergy r delta)) := by
  have h := (tendsto_finiteLaplaceCuspEnergy_ultraviolet_zero shiftedMobiusRealCoefficient
    abs_shiftedMobiusRealCoefficient_le_one hr).add (tendsto_finiteMobiusLaplaceExteriorEnergy hr hdelta)
  simp only [zero_add] at h
  apply h.congr
  intro N
  have hs := finiteLaplaceEnergy_split shiftedMobiusRealCoefficient N hr hdelta (integerCuspLowerScale N)
  change finiteLaplaceCuspEnergy shiftedMobiusRealCoefficient N r (integerCuspLowerScale N) +
    finiteLaplaceExteriorEnergy shiftedMobiusRealCoefficient N r delta =
    finiteGammaHankelEnergy shiftedMobiusRealCoefficient N r -
      ∫ x in (integerCuspLowerScale N)..delta,
        finiteLaplaceEnergyDensity shiftedMobiusRealCoefficient N r x
  linarith

/-- If energy escapes, its normalized mass is asymptotically all in the moving
cusp. The hypothesis is an escape test, not an assumed RH estimate. -/
theorem tendsto_mobiusMovingCusp_energy_ratio_one {r delta : ℝ}
    (hr : 1 < r) (hdelta : 0 < delta)
    (hescape : Tendsto (fun N => finiteMobiusGammaHankelEnergy N r) atTop atTop) :
    Tendsto (fun N => finiteMobiusMovingCuspEnergy N r delta / finiteMobiusGammaHankelEnergy N r)
      atTop (nhds 1) := by
  have hzero := (tendsto_mobiusEnergy_sub_movingCusp hr hdelta).div_atTop hescape
  have h := (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) from tendsto_const_nhds).sub hzero
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [hescape.eventually_gt_atTop 0] with N hN
  field_simp
  ring

def mobiusGammaHankelDiagonalLimit (r : ℝ) : ℝ :=
  ∑' n : ℕ, Real.Gamma r * (shiftedMobiusRealCoefficient n ^ 2 /
    (((2 * (n + 1) : ℕ) : ℝ) ^ r))

theorem summable_mobiusGammaHankelDiagonal {r : ℝ} (hr : 1 < r) :
    Summable (fun n : ℕ => Real.Gamma r * (shiftedMobiusRealCoefficient n ^ 2 /
      (((2 * (n + 1) : ℕ) : ℝ) ^ r))) := by
  apply summable_of_sum_range_le (c := ∑' n : ℕ, mobiusGammaHankelDiagonalMajorant r n)
  · intro n
    exact mul_nonneg (Real.Gamma_pos_of_pos (by linarith : 0 < r)).le (by positivity)
  · intro N
    simpa only [finiteMobiusGammaHankelDiagonalEnergy, Finset.mul_sum] using
      finiteMobiusGammaHankelDiagonalEnergy_le_tsum N hr

theorem tendsto_finiteMobiusGammaHankelDiagonalEnergy {r : ℝ} (hr : 1 < r) :
    Tendsto (fun N => finiteMobiusGammaHankelDiagonalEnergy N r) atTop
      (nhds (mobiusGammaHankelDiagonalLimit r)) := by
  simpa only [finiteMobiusGammaHankelDiagonalEnergy, Finset.mul_sum,
    mobiusGammaHankelDiagonalLimit] using
    (summable_mobiusGammaHankelDiagonal hr).hasSum.tendsto_sum_nat

/-- The actual signed covariance differs from the moving cusp energy by a
convergent, unconditionally defined quantity. No covariance bound is assumed. -/
theorem tendsto_mobiusCovariance_sub_movingCusp {r delta : ℝ}
    (hr : 1 < r) (hdelta : 0 < delta) :
    Tendsto (fun N => finiteMobiusGammaHankelOffDiagonalCovariance N r -
      finiteMobiusMovingCuspEnergy N r delta) atTop
      (nhds (mobiusLaplaceExteriorEnergy r delta - mobiusGammaHankelDiagonalLimit r)) := by
  have h := (tendsto_mobiusEnergy_sub_movingCusp hr hdelta).sub
    (tendsto_finiteMobiusGammaHankelDiagonalEnergy hr)
  apply h.congr
  intro N
  unfold finiteMobiusGammaHankelOffDiagonalCovariance
  ring

end RHTower
