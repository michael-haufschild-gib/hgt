import GaloisForLFunctions.HTGeometry.HardyLeakageRankOne
import GaloisForLFunctions.HTGeometry.NestedExhaustionCayleyLimit

/-!
# Operator-norm continuity of one-dimensional Hardy model spaces

Szegő kernels vary continuously in `H²(D)` as their disk node varies.  Writing the
orthogonal projection onto their span as a scaled rank-one transport then upgrades
this to operator-norm continuity of the corresponding model-space projections.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem hardyFun_hardyKernel {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    hardyFun (hardyKernel hb) a = (1 - (starRingEnd ℂ) b * a)⁻¹ := by
  rw [hardyFun]
  change (∑' n : ℕ, ((starRingEnd ℂ) b) ^ n * a ^ n) = _
  simp_rw [← mul_pow]
  exact tsum_geometric_of_norm_lt_one (by
    rw [norm_mul, RCLike.norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg b])

theorem inner_hardyKernel_hardyKernel {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    (inner ℂ (hardyKernel ha) (hardyKernel hb) : ℂ) =
      (1 - (starRingEnd ℂ) b * a)⁻¹ := by
  rw [inner_hardyKernel ha]
  exact hardyFun_hardyKernel ha hb

theorem norm_sq_hardyKernel {a : ℂ} (ha : ‖a‖ < 1) :
    ‖hardyKernel ha‖ ^ (2 : ℕ) = (1 - ‖a‖ ^ (2 : ℕ))⁻¹ := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    inner_hardyKernel_hardyKernel ha ha]
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  change ((1 - ((‖a‖ ^ (2 : ℕ) : ℝ) : ℂ))⁻¹).re = (1 - ‖a‖ ^ (2 : ℕ))⁻¹
  rw [Complex.inv_re]
  simp only [Complex.sub_re, one_re, ofReal_re, Complex.normSq_apply,
    Complex.sub_im, one_im, ofReal_im, sub_zero]
  have hx : 1 - ‖a‖ ^ (2 : ℕ) ≠ 0 := by nlinarith [norm_nonneg a]
  field_simp
  ring

/-- Szegő kernels are norm-continuous in their disk node. -/
theorem tendsto_hardyKernel
    {ι : Type*} {l : Filter ι} (u : ι → ℂ) (hu : ∀ i, ‖u i‖ < 1)
    {a : ℂ} (ha : ‖a‖ < 1) (h : Tendsto u l (𝓝 a)) :
    Tendsto (fun i => hardyKernel (hu i)) l (𝓝 (hardyKernel ha)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto
      (fun i => ‖hardyKernel (hu i) - hardyKernel ha‖ ^ (2 : ℕ)) l (𝓝 0) := by
    have hformula : ∀ i,
        ‖hardyKernel (hu i) - hardyKernel ha‖ ^ (2 : ℕ) =
          (1 - ‖u i‖ ^ (2 : ℕ))⁻¹ -
            2 * Complex.re ((1 - (starRingEnd ℂ) a * u i)⁻¹) +
              (1 - ‖a‖ ^ (2 : ℕ))⁻¹ := by
      intro i
      rw [norm_sub_sq (𝕜 := ℂ), norm_sq_hardyKernel (hu i), norm_sq_hardyKernel ha,
        inner_hardyKernel_hardyKernel (hu i) ha]
      rfl
    have hcont : ContinuousAt (fun z : ℂ =>
        (1 - ‖z‖ ^ (2 : ℕ))⁻¹ -
          2 * Complex.re ((1 - (starRingEnd ℂ) a * z)⁻¹) +
            (1 - ‖a‖ ^ (2 : ℕ))⁻¹) a := by
      have hreal : ContinuousAt (fun z : ℂ => 1 - ‖z‖ ^ (2 : ℕ)) a := by fun_prop
      have hreal0 : 1 - ‖a‖ ^ (2 : ℕ) ≠ 0 := by nlinarith [norm_nonneg a]
      have hcplx : ContinuousAt
          (fun z : ℂ => 1 - (starRingEnd ℂ) a * z) a := by fun_prop
      have hcplx0 : 1 - (starRingEnd ℂ) a * a ≠ 0 :=
        blaschke_denom_ne_zero (by nlinarith [norm_nonneg a])
      have hre : ContinuousAt
          (fun z : ℂ => Complex.re ((1 - (starRingEnd ℂ) a * z)⁻¹)) a := by
        convert Complex.continuous_re.continuousAt.comp (hcplx.inv₀ hcplx0) using 1
        ext z
        rfl
      exact ((hreal.inv₀ hreal0).sub (hre.const_mul 2)).add continuousAt_const
    have hlim := hcont.tendsto.comp h
    have hzero :
        (1 - ‖a‖ ^ (2 : ℕ))⁻¹ -
          2 * Complex.re ((1 - (starRingEnd ℂ) a * a)⁻¹) +
            (1 - ‖a‖ ^ (2 : ℕ))⁻¹ = 0 := by
      rw [← inner_hardyKernel_hardyKernel ha ha]
      have hinner : Complex.re
          (inner ℂ (hardyKernel ha) (hardyKernel ha)) = ‖hardyKernel ha‖ ^ (2 : ℕ) := by
        change RCLike.re (inner ℂ (hardyKernel ha) (hardyKernel ha)) = _
        exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (hardyKernel ha)).symm
      rw [hinner, norm_sq_hardyKernel ha]
      ring
    rw [hzero] at hlim
    simpa only [Function.comp_apply] using
      hlim.congr' (Filter.Eventually.of_forall fun i => (hformula i).symm)
  have hsqrt := hsq.sqrt
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt

theorem modelSpace_starProjection_eq_rankOneTransport {a : ℂ} (ha : ‖a‖ < 1) :
    (modelSpace ha).starProjection =
      ((((‖hardyKernel ha‖ ^ (2 : ℕ) : ℝ) : ℂ))⁻¹) •
        rankOneTransport (𝕜 := ℂ) (hardyKernel ha) (hardyKernel ha) := by
  apply ContinuousLinearMap.ext
  intro f
  change (ℂ ∙ hardyKernel ha).starProjection f = _
  rw [Submodule.starProjection_singleton, smul_apply,
    rankOneTransport_apply, smul_smul]
  congr 1
  rw [div_eq_inv_mul]
  rfl

/-- One-dimensional Hardy model-space projections vary in operator norm. -/
theorem tendsto_modelSpace_starProjection
    {ι : Type*} {l : Filter ι} (u : ι → ℂ) (hu : ∀ i, ‖u i‖ < 1)
    {a : ℂ} (ha : ‖a‖ < 1) (h : Tendsto u l (𝓝 a)) :
    Tendsto (fun i => (modelSpace (hu i)).starProjection) l
      (𝓝 (modelSpace ha).starProjection) := by
  have hk : Tendsto (fun i => hardyKernel (hu i)) l (𝓝 (hardyKernel ha)) :=
    tendsto_hardyKernel u hu ha h
  have hc : Tendsto
      (fun i => ((((‖hardyKernel (hu i)‖ ^ (2 : ℕ) : ℝ) : ℂ))⁻¹)) l
      (𝓝 ((((‖hardyKernel ha‖ ^ (2 : ℕ) : ℝ) : ℂ))⁻¹)) := by
    have hne : (((‖hardyKernel ha‖ ^ (2 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr (hardyKernel_ne_zero ha))
    have hnorm : Tendsto (fun i => ‖hardyKernel (hu i)‖) l
        (𝓝 ‖hardyKernel ha‖) := hk.norm
    have hpow := hnorm.pow 2
    have hcast : Tendsto
        (fun i => (((‖hardyKernel (hu i)‖ ^ (2 : ℕ) : ℝ) : ℂ))) l
        (𝓝 (((‖hardyKernel ha‖ ^ (2 : ℕ) : ℝ) : ℂ))) := by
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp hpow
    exact hcast.inv₀ hne
  have hrank : Tendsto
      (fun i => rankOneTransport (𝕜 := ℂ) (hardyKernel (hu i)) (hardyKernel (hu i))) l
      (𝓝 (rankOneTransport (𝕜 := ℂ) (hardyKernel ha) (hardyKernel ha))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact tendsto_opNorm_rankOneTransport_two hk hk
  have hprod := hc.smul hrank
  rw [← modelSpace_starProjection_eq_rankOneTransport ha] at hprod
  exact hprod.congr' (Filter.Eventually.of_forall fun i =>
    (modelSpace_starProjection_eq_rankOneTransport (hu i)).symm)

end GaloisForLFunctions.HTGeometry
