import GaloisForLFunctions.HTGeometry.PrimePoissonProductState
import GaloisForLFunctions.HTGeometry.BoundedCoeffPowerSeries
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Poisson-weighted bounded Euler series on a finite torus

The positive circle Poisson kernel transports to the unit additive circle.
Absolute coefficient summability justifies its Fourier pairing term by term.
The exponent identity recovers exactly the truncated-valuation coefficients;
finite product integration gives the full Poisson/Euler density coefficient,
including its subtracted Poisson product. All statements concern finite prime
sets; no infinite product or conditional-series rearrangement is used.
-/

open Complex MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate ENNReal

noncomputable section
namespace RHTower.WeilSingularArithmetic

private def unitCircleEquiv : UnitAddCircle ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero

def additivePoissonKernel (a : CirclePoissonParameter) : C(UnitAddCircle, ℝ) :=
  ⟨fun x => poissonKernel 0 (a : ℂ) (unitCircleEquiv x : ℂ),
    (continuous_circlePoissonDensity_real a).comp unitCircleEquiv.continuous⟩

theorem additivePoissonKernel_pos (a : CirclePoissonParameter) (x : UnitAddCircle) :
    0 < additivePoissonKernel a x := by
  have ha : ‖(a : ℂ)‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using a.2
  have hn : ‖(unitCircleEquiv x : ℂ)‖ = 1 := Circle.norm_coe _
  have hne : (unitCircleEquiv x : ℂ) - (a : ℂ) ≠ 0 := by
    intro he
    have heq := sub_eq_zero.mp he
    rw [← heq, hn] at ha
    exact (lt_irrefl 1) ha
  change 0 < poissonKernel 0 (a : ℂ) (unitCircleEquiv x : ℂ)
  rw [poissonKernel_def]
  simp only [sub_zero, hn, one_pow]
  exact div_pos (by nlinarith [norm_nonneg (a : ℂ)]) (sq_pos_of_pos (norm_pos_iff.mpr hne))

private theorem fourier_circleEquiv (q : ℤ) (x : UnitAddCircle) :
    fourier q x = (unitCircleEquiv x : ℂ) ^ q := by
  rw [fourier_apply, AddCircle.toCircle_zsmul]
  change (AddCircle.toCircle x : ℂ) ^ q = _
  rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
  rfl

theorem integral_additivePoissonKernel_fourier (a : CirclePoissonParameter) (q : ℤ) :
    (∫ x : UnitAddCircle, (additivePoissonKernel a x : ℂ) * fourier q x) =
      circlePoissonFourierMoment a q := by
  have hdens : AEMeasurable (circlePoissonDensity a) circleLebesgue :=
    (ENNReal.continuous_ofReal.comp (continuous_circlePoissonDensity_real a)).measurable.aemeasurable
  have htop : ∀ᵐ z ∂circleLebesgue, circlePoissonDensity a z < ∞ :=
    Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top
  have hbase := integral_circlePoissonMeasure_coe_zpow a q
  rw [circlePoissonMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hdens htop] at hbase
  have hpoint (z : Circle) : (circlePoissonDensity a z).toReal • (z : ℂ) ^ q =
      (poissonKernel 0 (a : ℂ) (z : ℂ) : ℂ) * (z : ℂ) ^ q := by
    rw [circlePoissonDensity, ENNReal.toReal_ofReal (circlePoissonDensity_nonneg a z)]
    simp only [Complex.real_smul]
  simp_rw [hpoint] at hbase
  have hc : Continuous (fun z : Circle => (poissonKernel 0 (a : ℂ) (z : ℂ) : ℂ) * (z : ℂ) ^ q) := by
    have he (z : Circle) : (z : ℂ) ^ q = fourier q (unitCircleEquiv.symm z) := by
      rw [fourier_circleEquiv, unitCircleEquiv.apply_symm_apply]
    simp_rw [he]
    exact (Complex.continuous_ofReal.comp (continuous_circlePoissonDensity_real a)).mul
      ((fourier q).continuous.comp unitCircleEquiv.symm.continuous)
  change (∫ z : Circle, (poissonKernel 0 (a : ℂ) (z : ℂ) : ℂ) * (z : ℂ) ^ q
    ∂(Measure.map unitCircleEquiv AddCircle.haarAddCircle)) = _ at hbase
  rw [integral_map unitCircleEquiv.continuous.aemeasurable hc.aestronglyMeasurable] at hbase
  have hv : (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  rw [hv] at hbase
  change (∫ x : UnitAddCircle, (poissonKernel 0 (a : ℂ) (unitCircleEquiv x : ℂ) : ℂ) * fourier q x) = _
  simpa only [circlePoissonFourierMoment, ← fourier_circleEquiv] using hbase

theorem continuous_boundedFun_fourier {a : ℕ → ℂ} {C r : ℝ}
    (ha : ∀ k, ‖a k‖ ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun x : UnitAddCircle => boundedFun a ((r : ℂ) * fourier 1 x)) := by
  apply (differentiableOn_boundedFun ha).continuousOn.comp_continuous
    (continuous_const.mul (fourier 1).continuous)
  intro x
  change ((r : ℂ) * fourier 1 x) ∈ Metric.ball 0 1
  simpa only [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr0, fourier_apply, Circle.norm_coe, mul_one] using hr1

def realPoissonParameter (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) : CirclePoissonParameter :=
  ⟨(r : ℂ), by simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr0] using hr1⟩

theorem integral_realPoissonKernel_fourier {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (q : ℤ) :
    (∫ x : UnitAddCircle, (additivePoissonKernel (realPoissonParameter r hr0 hr1) x : ℂ) * fourier q x) =
      (r : ℂ) ^ q.natAbs := by
  rw [integral_additivePoissonKernel_fourier]
  cases q <;> simp [circlePoissonFourierMoment, realPoissonParameter]

theorem integral_poissonKernel_summable_fourier (a : CirclePoissonParameter)
    {b : ℕ → ℂ} (hb : Summable (fun k => ‖b k‖)) (q : ℤ) :
    (∫ x : UnitAddCircle, (additivePoissonKernel a x : ℂ) *
      (∑' k : ℕ, b k * fourier (k : ℤ) x) * fourier q x) =
        ∑' k : ℕ, b k * circlePoissonFourierMoment a ((k : ℤ) + q) := by
  letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simpa using (inferInstance : IsProbabilityMeasure (AddCircle.haarAddCircle : Measure UnitAddCircle))
  let F : ℕ → UnitAddCircle → ℂ := fun k x =>
    b k * ((additivePoissonKernel a x : ℂ) * fourier ((k : ℤ) + q) x)
  have hc (k : ℕ) : Continuous (F k) :=
    continuous_const.mul ((Complex.continuous_ofReal.comp (additivePoissonKernel a).continuous).mul
      (fourier ((k : ℤ) + q)).continuous)
  have hi (k : ℕ) : Integrable (F k) :=
    (hc k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnorm (k : ℕ) (x : UnitAddCircle) : ‖F k x‖ ≤ ‖b k‖ * ‖additivePoissonKernel a‖ := by
    change ‖b k * ((additivePoissonKernel a x : ℂ) * fourier ((k : ℤ) + q) x)‖ ≤ _
    simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left ((additivePoissonKernel a).norm_coe_le_norm x) (norm_nonneg _)
  have hsum : Summable (fun k : ℕ => ∫ x : UnitAddCircle, ‖F k x‖) := by
    apply (hb.mul_right ‖additivePoissonKernel a‖).of_nonneg_of_le
      (fun k => integral_nonneg fun x => norm_nonneg _) fun k => ?_
    calc
      _ ≤ ∫ _ : UnitAddCircle, ‖b k‖ * ‖additivePoissonKernel a‖ :=
        integral_mono (hi k).norm (integrable_const _) (hnorm k)
      _ = _ := by simp
  have hpoint (x : UnitAddCircle) : (additivePoissonKernel a x : ℂ) *
      (∑' k : ℕ, b k * fourier (k : ℤ) x) * fourier q x = ∑' k, F k x := by
    rw [← tsum_mul_left, ← tsum_mul_right]
    apply tsum_congr
    intro k
    change (additivePoissonKernel a x : ℂ) * (b k * fourier (k : ℤ) x) * fourier q x =
      b k * ((additivePoissonKernel a x : ℂ) * fourier ((k : ℤ) + q) x)
    rw [fourier_add]
    ring
  simp_rw [hpoint]
  rw [← integral_tsum_of_summable_integral_norm hi hsum]
  apply tsum_congr
  intro k
  change (∫ x : UnitAddCircle, b k * ((additivePoissonKernel a x : ℂ) * fourier ((k : ℤ) + q) x)) = _
  rw [integral_const_mul, integral_additivePoissonKernel_fourier]

theorem integral_poissonKernel_boundedFun_fourier {a : ℕ → ℂ} {C r : ℝ}
    (ha : ∀ k, ‖a k‖ ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1) (j : ℤ) :
    (∫ x : UnitAddCircle, (additivePoissonKernel (realPoissonParameter r hr0 hr1) x : ℂ) *
      boundedFun a ((r : ℂ) * fourier 1 x) * fourier (-j) x) =
        ∑' k : ℕ, a k * (r : ℂ) ^ k * (r : ℂ) ^ ((k : ℤ) - j).natAbs := by
  have hr : ‖(r : ℂ)‖ < 1 := by simpa [abs_of_nonneg hr0] using hr1
  have hs : Summable (fun k : ℕ => ‖a k * (r : ℂ) ^ k‖) := (summable_boundedTerms ha hr).norm
  have he (x : UnitAddCircle) : boundedFun a ((r : ℂ) * fourier 1 x) =
      ∑' k : ℕ, (a k * (r : ℂ) ^ k) * fourier (k : ℤ) x := by
    unfold boundedFun
    apply tsum_congr
    intro k
    simp only [fourier_circleEquiv, zpow_one, zpow_natCast, mul_pow, mul_assoc]
  simp_rw [he]
  rw [integral_poissonKernel_summable_fourier _ hs]
  apply tsum_congr
  intro k
  have hm := integral_realPoissonKernel_fourier hr0 hr1 ((k : ℤ) - j)
  rw [integral_additivePoissonKernel_fourier] at hm
  simpa only [sub_eq_add_neg] using congrArg (fun z => a k * (r : ℂ) ^ k * z) hm

private theorem poisson_exponent_balance (k : ℕ) (j : ℤ) :
    k + ((k : ℤ) - j).natAbs = j.natAbs + 2 * (k - min k j.toNat) := by
  cases j with
  | ofNat n =>
    change k + ((k : ℤ) - (n : ℤ)).natAbs = n + 2 * (k - min k n)
    rcases le_total k n with hkn | hnk
    · rw [Int.natAbs_natCast_sub_natCast_of_le hkn]
      omega
    · rw [Int.natAbs_natCast_sub_natCast_of_ge hnk]
      omega
  | negSucc n =>
    change k + ((k : ℤ) - Int.negSucc n).natAbs = (n + 1) + 2 * (k - min k 0)
    have he : (k : ℤ) - Int.negSucc n = ((k + n + 1 : ℕ) : ℤ) := by omega
    rw [he, Int.natAbs_natCast]
    omega

theorem integral_poissonKernel_boundedFun_exact {a : ℕ → ℂ} {C r : ℝ}
    (ha : ∀ k, ‖a k‖ ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1) (j : ℤ) :
    (∫ x : UnitAddCircle, (additivePoissonKernel (realPoissonParameter r hr0 hr1) x : ℂ) *
      boundedFun a ((r : ℂ) * fourier 1 x) * fourier (-j) x) =
        (r : ℂ) ^ j.natAbs *
          ∑' k : ℕ, a k * ((r : ℂ) ^ 2) ^ (k - min k j.toNat) := by
  rw [integral_poissonKernel_boundedFun_fourier ha hr0 hr1, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [mul_assoc, ← pow_add, poisson_exponent_balance, pow_add, pow_mul]
  ring

def finitePoissonEulerDensity {ι : Type*} [Fintype ι]
    (a : ι → ℕ → ℂ) (r : ι → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    (c : ℂ) (x : UnitAddTorus ι) : ℂ :=
  (∏ i, (additivePoissonKernel (realPoissonParameter (r i) (hr0 i) (hr1 i)) (x i) : ℂ)) *
    (c * (∏ i, boundedFun (a i) ((r i : ℂ) * fourier 1 (x i))) - 1)

theorem continuous_finitePoissonEulerDensity {ι : Type*} [Fintype ι]
    {a : ι → ℕ → ℂ} {C : ι → ℝ} (ha : ∀ i k, ‖a i k‖ ≤ C i)
    (r : ι → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) (c : ℂ) :
    Continuous (finitePoissonEulerDensity a r hr0 hr1 c) := by
  apply Continuous.mul
  · exact continuous_finsetProd _ fun i _ =>
      (Complex.continuous_ofReal.comp
        (additivePoissonKernel (realPoissonParameter (r i) (hr0 i) (hr1 i))).continuous).comp
          (continuous_apply i)
  · exact (continuous_const.mul (continuous_finsetProd _ fun i _ =>
      (continuous_boundedFun_fourier (ha i) (hr0 i) (hr1 i)).comp
        (continuous_apply i))).sub continuous_const

/-- The full finite-dimensional Fourier coefficient, including the subtracted
Poisson product. No limiting Euler product is used. -/
theorem integral_finitePoissonEulerDensity_character {ι : Type*} [Fintype ι]
    {a : ι → ℕ → ℂ} {C : ι → ℝ} (ha : ∀ i k, ‖a i k‖ ≤ C i)
    (r : ι → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) (c : ℂ) (g : ι → ℤ) :
    (∫ x : UnitAddTorus ι, finitePoissonEulerDensity a r hr0 hr1 c x * UnitAddTorus.mFourier (-g) x) =
      (∏ i, (r i : ℂ) ^ (g i).natAbs) *
        (c * (∏ i, ∑' k : ℕ, a i k * ((r i : ℂ) ^ 2) ^ (k - min k (g i).toNat)) - 1) := by
  let K (i : ι) := additivePoissonKernel (realPoissonParameter (r i) (hr0 i) (hr1 i))
  let L (i : ι) (x : UnitAddCircle) := boundedFun (a i) ((r i : ℂ) * fourier 1 x)
  let F (x : UnitAddTorus ι) := (∏ i, (K i (x i) : ℂ) * L i (x i)) * UnitAddTorus.mFourier (-g) x
  let G (x : UnitAddTorus ι) := (∏ i, (K i (x i) : ℂ)) * UnitAddTorus.mFourier (-g) x
  have hF : Continuous F :=
    (continuous_finsetProd _ fun i _ =>
      ((Complex.continuous_ofReal.comp (K i).continuous).mul
        (continuous_boundedFun_fourier (ha i) (hr0 i) (hr1 i))).comp
          (continuous_apply i)).mul (UnitAddTorus.mFourier (-g)).continuous
  have hG : Continuous G :=
    (continuous_finsetProd _ fun i _ =>
      (Complex.continuous_ofReal.comp (K i).continuous).comp
        (continuous_apply i)).mul (UnitAddTorus.mFourier (-g)).continuous
  have hiF : Integrable F := hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiG : Integrable G := hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfirst : (∫ x : UnitAddTorus ι, F x) =
      (∏ i, (r i : ℂ) ^ (g i).natAbs) *
        ∏ i, ∑' k : ℕ, a i k * ((r i : ℂ) ^ 2) ^ (k - min k (g i).toNat) := by
    have he : F = fun x : UnitAddTorus ι => ∏ i, (K i (x i) : ℂ) * L i (x i) * fourier (-(g i)) (x i) := by
      funext x
      simp only [F, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, Finset.prod_mul_distrib]
    rw [he]
    change (∫ x : ι → UnitAddCircle, ∏ i, (K i (x i) : ℂ) * L i (x i) * fourier (-(g i)) (x i)) = _
    rw [integral_fintype_prod_volume_eq_prod
      (fun i (x : UnitAddCircle) => (K i x : ℂ) * L i x * fourier (-(g i)) x), ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact integral_poissonKernel_boundedFun_exact (ha i) (hr0 i) (hr1 i) (g i)
  have hsecond : (∫ x : UnitAddTorus ι, G x) = ∏ i, (r i : ℂ) ^ (g i).natAbs := by
    have he : G = fun x : UnitAddTorus ι => ∏ i, (K i (x i) : ℂ) * fourier (-(g i)) (x i) := by
      funext x
      simp only [G, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, Finset.prod_mul_distrib]
    rw [he]
    change (∫ x : ι → UnitAddCircle, ∏ i, (K i (x i) : ℂ) * fourier (-(g i)) (x i)) = _
    rw [integral_fintype_prod_volume_eq_prod
      (fun i (x : UnitAddCircle) => (K i x : ℂ) * fourier (-(g i)) x)]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [Int.natAbs_neg] using integral_realPoissonKernel_fourier (hr0 i) (hr1 i) (-(g i))
  have he : (fun x : UnitAddTorus ι => finitePoissonEulerDensity a r hr0 hr1 c x * UnitAddTorus.mFourier (-g) x) =
      fun x => c * F x - G x := by
    funext x
    simp only [finitePoissonEulerDensity, F, G, K, L, Finset.prod_mul_distrib]
    ring
  rw [he, integral_sub (hiF.const_mul c) hiG, integral_const_mul, hfirst, hsecond]
  ring

end RHTower.WeilSingularArithmetic
