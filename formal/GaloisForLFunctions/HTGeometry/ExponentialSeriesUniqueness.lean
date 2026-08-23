import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

/-!
# Uniqueness of exponential-series coefficients

An absolutely convergent series `Σ c_i e^{iγ_i t}` with pairwise distinct real frequencies that
vanishes for every real `t` has all coefficients zero.  This is the Bohr--Fourier uniqueness
statement in the only generality the arithmetic applications need, and it is proved here without
any almost-periodicity theory.

The frequency `γ_j` is extracted by the mean value over `[-T, T]`.  Its kernel is
`(2T)^{-1} ∫ e^{ixt} dt`, bounded by `1` because the integrand is unimodular, and bounded by
`(T|x|)^{-1}` off the diagonal because the antiderivative is bounded by `2/|x|`.  Absolute
convergence lets the mean value pass inside the sum, and dominated convergence for series sends the
result to `c_j`.
-/

open MeasureTheory Set Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The normalized Dirichlet kernel of the Bohr mean value. -/
def bohrSincKernel (T x : ℝ) : ℂ :=
  ((1 / (2 * T) : ℝ) : ℂ) * ∫ t in Set.Ioc (-T) T, Complex.exp (I * (x : ℂ) * (t : ℂ))

theorem volume_Ioc_symm {T : ℝ} (hT : 0 ≤ T) :
    volume.real (Set.Ioc (-T) T) = 2 * T := by
  show (volume (Set.Ioc (-T) T)).toReal = 2 * T
  rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  ring

theorem bohrSincKernel_zero {T : ℝ} (hT : 0 < T) : bohrSincKernel T 0 = 1 := by
  have hfun : ∀ t : ℝ, Complex.exp (I * ((0 : ℝ) : ℂ) * (t : ℂ)) = 1 := by
    intro t
    simp
  rw [bohrSincKernel, MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun t : ℝ => hfun t))]
  rw [MeasureTheory.setIntegral_const, volume_Ioc_symm hT.le, Complex.real_smul, mul_one]
  push_cast
  field_simp
  rw [div_self (by simpa using ne_of_gt hT : ((T : ℝ) : ℂ) ≠ 0)]

theorem norm_bohrSincKernel_le_one {T : ℝ} (hT : 0 < T) (x : ℝ) :
    ‖bohrSincKernel T x‖ ≤ 1 := by
  have hbd : ‖∫ t in Set.Ioc (-T) T, Complex.exp (I * (x : ℂ) * (t : ℂ))‖ ≤ 2 * T := by
    have h1 : ∀ t : ℝ, ‖Complex.exp (I * (x : ℂ) * (t : ℂ))‖ ≤ 1 := by
      intro t
      rw [Complex.norm_exp]
      have hre : (I * (x : ℂ) * (t : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, Real.exp_zero]
    have h2 := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Ioc (-T) T) (C := 1)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
      (fun t _ => h1 t)
    rw [volume_Ioc_symm hT.le] at h2
    linarith
  rw [bohrSincKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
  exact hbd

theorem bohrSincKernel_eq {T x : ℝ} (hT : 0 < T) (hx : x ≠ 0) :
    bohrSincKernel T x
      = ((1 / (2 * T) : ℝ) : ℂ) *
        ((Complex.exp (I * (x : ℂ) * (T : ℂ)) - Complex.exp (I * (x : ℂ) * ((-T : ℝ) : ℂ)))
          / (I * (x : ℂ))) := by
  have hne : (I * (x : ℂ)) ≠ 0 := by
    refine mul_ne_zero Complex.I_ne_zero ?_
    simpa using hx
  have hle : (-T : ℝ) ≤ T := by linarith
  rw [bohrSincKernel, ← intervalIntegral.integral_of_le hle]
  congr 1
  rw [← integral_exp_mul_complex hne]

theorem norm_bohrSincKernel_le_inv {T x : ℝ} (hT : 0 < T) (hx : x ≠ 0) :
    ‖bohrSincKernel T x‖ ≤ 1 / (T * |x|) := by
  have hxn : (0 : ℝ) < |x| := abs_pos.mpr hx
  have hnum : ‖Complex.exp (I * (x : ℂ) * (T : ℂ))
      - Complex.exp (I * (x : ℂ) * ((-T : ℝ) : ℂ))‖ ≤ 2 := by
    have h1 : ∀ s : ℝ, ‖Complex.exp (I * (x : ℂ) * (s : ℂ))‖ = 1 := by
      intro s
      rw [Complex.norm_exp]
      have hre : (I * (x : ℂ) * (s : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, Real.exp_zero]
    calc ‖Complex.exp (I * (x : ℂ) * (T : ℂ))
        - Complex.exp (I * (x : ℂ) * ((-T : ℝ) : ℂ))‖
        ≤ ‖Complex.exp (I * (x : ℂ) * (T : ℂ))‖
          + ‖Complex.exp (I * (x : ℂ) * ((-T : ℝ) : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by rw [h1 T, h1 (-T)]; norm_num
  have hden : ‖I * (x : ℂ)‖ = |x| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [bohrSincKernel_eq hT hx, norm_mul, norm_div, hden, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc (1 / (2 * T)) * (‖Complex.exp (I * (x : ℂ) * (T : ℂ))
        - Complex.exp (I * (x : ℂ) * ((-T : ℝ) : ℂ))‖ / |x|)
      ≤ (1 / (2 * T)) * (2 / |x|) := by gcongr
    _ = 1 / (T * |x|) := by
        field_simp

theorem tendsto_bohrSincKernel {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun T : ℝ => bohrSincKernel T x) atTop (nhds 0) := by
  have hxn : (0 : ℝ) < |x| := abs_pos.mpr hx
  refine squeeze_zero_norm' (a := fun T : ℝ => 1 / (T * |x|)) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact norm_bohrSincKernel_le_inv hT hx
  · have hmul : Tendsto (fun T : ℝ => T * |x|) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hxn tendsto_id
    exact (tendsto_inv_atTop_zero.comp hmul).congr
      (fun T => by rw [Function.comp_apply, one_div])

/-! ## Uniqueness of the coefficients of an absolutely convergent exponential series -/

theorem norm_cis_mul (x t : ℝ) : ‖Complex.exp (I * (x : ℂ) * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (I * (x : ℂ) * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

theorem integrable_cis_on_Ioc (x T : ℝ) :
    IntegrableOn (fun t : ℝ => Complex.exp (I * (x : ℂ) * (t : ℂ))) (Set.Ioc (-T) T) volume := by
  have hcont : Continuous fun t : ℝ => Complex.exp (I * (x : ℂ) * (t : ℂ)) := by fun_prop
  exact hcont.integrableOn_Ioc

/-- **Uniqueness of exponential-series coefficients.**  An absolutely convergent series of
exponentials with pairwise distinct real frequencies that vanishes identically has zero
coefficients.  The frequency is extracted by the mean value over `[-T, T]`, whose kernel is
bounded by `1` and decays like `1/(T|x|)` off the diagonal. -/
theorem coeff_eq_zero_of_tsum_cis_eq_zero {ι : Type*} [Countable ι] {γ : ι → ℝ}
    (hinj : Function.Injective γ) {c : ι → ℂ} (hc : Summable (fun i => ‖c i‖))
    (h : ∀ t : ℝ, ∑' i, c i * Complex.exp (I * ((γ i : ℝ) : ℂ) * (t : ℂ)) = 0) (j : ι) :
    c j = 0 := by
  classical
  set g : ℝ → ℂ := fun T => ∑' i, c i * bohrSincKernel T (γ i - γ j) with hg
  have hzero : ∀ T : ℝ, 0 < T → g T = 0 := by
    intro T hT
    have hTne' : ((T : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hT
    have hTne : (2 * (T : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hTne'
    have hTc : ((1 / (2 * T) : ℝ) : ℂ) = (2 * (T : ℂ))⁻¹ := by
      push_cast
      rw [one_div]
    set μ : Measure ℝ := volume.restrict (Set.Ioc (-T) T) with hμ
    set F : ι → ℝ → ℂ := fun i t =>
      c i * Complex.exp (I * ((γ i - γ j : ℝ) : ℂ) * (t : ℂ)) with hF
    have hint : ∀ i, Integrable (F i) μ := fun i =>
      (integrable_cis_on_Ioc (γ i - γ j) T).const_mul (c i)
    have hnorm : ∀ i, (∫ t, ‖F i t‖ ∂μ) = ‖c i‖ * (2 * T) := by
      intro i
      have hfun : ∀ t : ℝ, ‖F i t‖ = ‖c i‖ := by
        intro t
        show ‖c i * Complex.exp (I * ((γ i - γ j : ℝ) : ℂ) * (t : ℂ))‖ = ‖c i‖
        rw [norm_mul, norm_cis_mul, mul_one]
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hfun), hμ,
        MeasureTheory.setIntegral_const, smul_eq_mul, volume_Ioc_symm hT.le]
      exact mul_comm _ _
    have hsummable : Summable fun i => ∫ t, ‖F i t‖ ∂μ :=
      (hc.mul_right (2 * T)).congr fun i => (hnorm i).symm
    have hsum := MeasureTheory.integral_tsum_of_summable_integral_norm hint hsummable
    have hterm : ∀ i, (∫ t, F i t ∂μ)
        = 2 * (T : ℂ) * (c i * bohrSincKernel T (γ i - γ j)) := by
      intro i
      have hL : (∫ t, F i t ∂μ)
          = c i * ∫ t in Set.Ioc (-T) T,
              Complex.exp (I * ((γ i - γ j : ℝ) : ℂ) * (t : ℂ)) := by
        rw [hμ]
        exact MeasureTheory.integral_const_mul _ _
      have hR : 2 * (T : ℂ) * (c i * bohrSincKernel T (γ i - γ j))
          = c i * ∫ t in Set.Ioc (-T) T,
              Complex.exp (I * ((γ i - γ j : ℝ) : ℂ) * (t : ℂ)) := by
        rw [bohrSincKernel, hTc]
        field_simp
      rw [hL, hR]
    have hpt : ∀ t : ℝ, (∑' i, F i t) = 0 := by
      intro t
      have hexp : ∀ i, F i t = (c i * Complex.exp (I * ((γ i : ℝ) : ℂ) * (t : ℂ)))
          * Complex.exp (-(I * ((γ j : ℝ) : ℂ) * (t : ℂ))) := by
        intro i
        show c i * Complex.exp (I * ((γ i - γ j : ℝ) : ℂ) * (t : ℂ))
          = (c i * Complex.exp (I * ((γ i : ℝ) : ℂ) * (t : ℂ)))
            * Complex.exp (-(I * ((γ j : ℝ) : ℂ) * (t : ℂ)))
        have hE : Complex.exp (I * ((γ i - γ j : ℝ) : ℂ) * (t : ℂ))
            = Complex.exp (I * ((γ i : ℝ) : ℂ) * (t : ℂ))
              * Complex.exp (-(I * ((γ j : ℝ) : ℂ) * (t : ℂ))) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [hE]
        ring
      rw [tsum_congr hexp, tsum_mul_right, h t, zero_mul]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_zero] at hsum
    have hsum2 : (∑' i, 2 * (T : ℂ) * (c i * bohrSincKernel T (γ i - γ j))) = 0 := by
      rw [← hsum]
      exact (tsum_congr hterm).symm
    rw [tsum_mul_left] at hsum2
    rw [hg]
    exact (mul_eq_zero.mp hsum2).resolve_left hTne
  have hlim : Tendsto g atTop (nhds (c j)) := by
    have hbound : ∀ᶠ T : ℝ in atTop, ∀ i,
        ‖c i * bohrSincKernel T (γ i - γ j)‖ ≤ ‖c i‖ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT i
      rw [norm_mul]
      have := norm_bohrSincKernel_le_one hT (γ i - γ j)
      nlinarith [norm_nonneg (c i), norm_nonneg (bohrSincKernel T (γ i - γ j))]
    have hpt : ∀ i, Tendsto (fun T : ℝ => c i * bohrSincKernel T (γ i - γ j)) atTop
        (nhds (if i = j then c i else 0)) := by
      intro i
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        have heq : ∀ᶠ T : ℝ in atTop, c i * bohrSincKernel T (γ i - γ i) = c i := by
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
          rw [sub_self, bohrSincKernel_zero hT, mul_one]
        exact Tendsto.congr' (Filter.EventuallyEq.symm heq) tendsto_const_nhds
      · rw [if_neg hij]
        have hne : γ i - γ j ≠ 0 := by
          intro hz
          exact hij (hinj (sub_eq_zero.mp hz))
        have := (tendsto_bohrSincKernel hne).const_mul (c i)
        simpa using this
    have hlim2 := tendsto_tsum_of_dominated_convergence hc hpt hbound
    rw [tsum_ite_eq j] at hlim2
    exact hlim2
  have : c j = 0 := by
    have hconst : Tendsto g atTop (nhds 0) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      exact (hzero T hT).symm
    exact tendsto_nhds_unique hlim hconst
  exact this


end GaloisForLFunctions.HTGeometry
