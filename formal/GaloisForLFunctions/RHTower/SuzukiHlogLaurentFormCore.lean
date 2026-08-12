import GaloisForLFunctions.RHTower.SuzukiHlogMollifiedFormCore
import GaloisForLFunctions.RHTower.SuzukiHlogApertureModeGrowth
import GaloisForLFunctions.RHTower.PeriodicFourierCubicDecay
import GaloisForLFunctions.HTGeometry.IntegerSeriesBounds
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Laurent-polynomial form core for the CCM logarithmic aperture form

This module completes Connes--Consani (2021), Lemma `core`, in the literal weighted form norm.
It proves:

* mollified inward vectors have support strictly inside the aperture;
* their periodic Fourier coefficients have cubic decay;
* the logarithmic form norms of zero-extended modes grow slowly enough for absolute form-norm
  summability;
* the resulting Fourier series sums to the original smooth vector in the complete form domain;
* finite Laurent polynomials are therefore dense in the full form domain.

The endpoint is stronger than ordinary `L²` density: convergence is in
`L²(ℝ, (1 + log⁺|ξ|) dξ)`, the exact closed quadratic-form norm used by the source.
-/

open MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal

noncomputable section

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- Radius containing the entire support of a mollified inward vector. -/
def suzukiHlogMollifiedSupportRadius
    (a : SuzukiPositiveAperture) (n m : ℕ) : ℝ :=
  a.1 / suzukiHlogInwardScale n + suzukiHlogMollifierWidth a n m

theorem suzukiHlogMollifiedSupportRadius_lt
    (a : SuzukiPositiveAperture) (n m : ℕ) :
    suzukiHlogMollifiedSupportRadius a n m < a.1 := by
  unfold suzukiHlogMollifiedSupportRadius
  have h := suzukiHlogMollifierWidth_lt_gap a n m
  unfold suzukiHlogInwardGap at h
  linarith

theorem support_suzukiHlogMollifiedTime_subset_strictRadius
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    Function.support (suzukiHlogMollifiedTime a n m f) ⊆
      Icc (-suzukiHlogMollifiedSupportRadius a n m)
        (suzukiHlogMollifiedSupportRadius a n m) := by
  intro x hx
  have hxsum := MeasureTheory.support_convolution_subset
    (ContinuousLinearMap.mul ℝ ℂ) hx
  rcases hxsum with ⟨y, hy, z, hz, rfl⟩
  have hy' := support_complexBumpMollifier_subset
    (suzukiHlogMollifierWidth_pos a n m) hy
  have hz' := support_suzukiHlogInwardCutoffRep_subset a n f hz
  unfold suzukiHlogMollifiedSupportRadius
  constructor <;> linarith [hy'.1, hy'.2, hz'.1, hz'.2]

theorem tsupport_suzukiHlogMollifiedTime_subset_interior
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    tsupport (suzukiHlogMollifiedTime a n m f) ⊆ Ioo (-a.1) a.1 := by
  have hclosed : IsClosed
      (Icc (-suzukiHlogMollifiedSupportRadius a n m)
        (suzukiHlogMollifiedSupportRadius a n m)) := isClosed_Icc
  have hclosure : tsupport (suzukiHlogMollifiedTime a n m f) ⊆
      Icc (-suzukiHlogMollifiedSupportRadius a n m)
        (suzukiHlogMollifiedSupportRadius a n m) :=
    closure_minimal
      (support_suzukiHlogMollifiedTime_subset_strictRadius a n m f) hclosed
  intro x hx
  have hx' := hclosure hx
  have hr := suzukiHlogMollifiedSupportRadius_lt a n m
  exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩

/-- Smooth form vectors whose time representative is supported strictly inside the aperture. -/
def suzukiHlogInteriorSmoothCore (a : SuzukiPositiveAperture) :
    Set (SuzukiHlogFormDomain a) :=
  {q | ∃ (g : ℝ → ℂ) (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g)
      (hgsupp : HasCompactSupport g),
      tsupport g ⊆ Ioo (-a.1) a.1 ∧
      suzukiHlogFormEmbedding a q = suzukiComplexTestL2 g hgdiff hgsupp}

theorem suzukiHlogMollifiedFormVector_mem_interiorSmoothCore
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    suzukiHlogMollifiedFormVector a n m f ∈ suzukiHlogInteriorSmoothCore a := by
  exact ⟨suzukiHlogMollifiedTime a n m f,
    contDiff_suzukiHlogMollifiedTime a n m f,
    hasCompactSupport_suzukiHlogMollifiedTime a n m f,
    tsupport_suzukiHlogMollifiedTime_subset_interior a n m f,
    suzukiHlogFormEmbedding_mollifiedFormVector a n m f⟩

theorem suzukiHlogFormInwardDilate_mem_closure_interiorSmoothCore
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SuzukiHlogFormDomain a) :
    suzukiHlogFormInwardDilate a n f ∈ closure (suzukiHlogInteriorSmoothCore a) :=
  mem_closure_of_tendsto (suzukiHlogMollifiedFormVector_tendsto_inward a n f)
    (Filter.Eventually.of_forall
      (fun m => suzukiHlogMollifiedFormVector_mem_interiorSmoothCore a n m f))

/-- Strict-interior smooth tests are already dense in the complete weighted form domain. -/
theorem dense_suzukiHlogInteriorSmoothCore (a : SuzukiPositiveAperture) :
    Dense (suzukiHlogInteriorSmoothCore a) := by
  intro f
  exact isClosed_closure.mem_of_tendsto (suzukiHlogFormInwardDilate_tendsto a f)
    (Filter.Eventually.of_forall
      (fun n => suzukiHlogFormInwardDilate_mem_closure_interiorSmoothCore a n f))

/-! ## Periodic endpoint jets and coefficient decay -/

theorem eq_zero_of_notMem_tsupport {g : ℝ → ℂ} {x : ℝ}
    (hx : x ∉ tsupport g) : g x = 0 := by
  by_contra hne
  exact hx (subset_closure (Function.mem_support.mpr hne))

theorem aperture_endpoints_notMem_tsupport
    {a : ℝ} {g : ℝ → ℂ} (hsupp : tsupport g ⊆ Ioo (-a) a) :
    -a ∉ tsupport g ∧ a ∉ tsupport g := by
  constructor
  · intro h
    exact lt_irrefl _ (hsupp h).1
  · intro h
    exact lt_irrefl _ (hsupp h).2

theorem aperture_endpoint_jets_zero
    {a : ℝ} {g : ℝ → ℂ} (hsupp : tsupport g ⊆ Ioo (-a) a) :
    g (-a) = 0 ∧ g a = 0 ∧
      deriv g (-a) = 0 ∧ deriv g a = 0 ∧
      deriv (deriv g) (-a) = 0 ∧ deriv (deriv g) a = 0 := by
  rcases aperture_endpoints_notMem_tsupport hsupp with ⟨hleft, hright⟩
  have hleft' : -a ∉ tsupport (deriv g) :=
    fun h => hleft (tsupport_deriv_subset h)
  have hright' : a ∉ tsupport (deriv g) :=
    fun h => hright (tsupport_deriv_subset h)
  exact ⟨eq_zero_of_notMem_tsupport hleft,
    eq_zero_of_notMem_tsupport hright,
    deriv_of_notMem_tsupport hleft,
    deriv_of_notMem_tsupport hright,
    deriv_of_notMem_tsupport hleft',
    deriv_of_notMem_tsupport hright'⟩

/-- A strict-interior smooth aperture function has cubic Fourier-coefficient decay. -/
theorem exists_fourierCoeffOn_cubic_bound
    (a : SuzukiPositiveAperture) {g : ℝ → ℂ}
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g)
    (hginterior : tsupport g ⊆ Ioo (-a.1) a.1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℤ, k ≠ 0 →
      ‖fourierCoeffOn (by linarith [a.2] : -a.1 < a.1) g k‖ ≤
        C * (1 / |(k : ℝ)| ^ 3) := by
  have hg1 : Differentiable ℝ g := hgdiff.differentiable (by simp)
  have hgd1 : ContDiff ℝ (⊤ : ℕ∞) (deriv g) :=
    (contDiff_infty_iff_deriv.mp hgdiff).2
  have hg2 : Differentiable ℝ (deriv g) := hgd1.differentiable (by simp)
  have hgd2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv g)) :=
    (contDiff_infty_iff_deriv.mp hgd1).2
  have hg3 : Differentiable ℝ (deriv (deriv g)) := hgd2.differentiable (by simp)
  have hgd3 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv (deriv g))) :=
    (contDiff_infty_iff_deriv.mp hgd2).2
  obtain ⟨B, hB⟩ := hgd3.continuous.bounded_above_of_compact_support
    hgsupp.deriv.deriv.deriv
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (deriv (deriv (deriv g)) 0)) (hB 0)
  let C : ℝ := ((2 * a.1) / (2 * Real.pi)) ^ 3 * B
  have hfactor0 : 0 ≤ ((2 * a.1) / (2 * Real.pi)) ^ 3 := by
    exact pow_nonneg (div_nonneg (mul_nonneg (by norm_num) a.2.le)
      (mul_nonneg (by norm_num) Real.pi_pos.le)) _
  refine ⟨C, mul_nonneg hfactor0 hB0, fun k hk => ?_⟩
  rcases aperture_endpoint_jets_zero hginterior with
    ⟨hgLeft, hgRight, hg1Left, hg1Right, hg2Left, hg2Right⟩
  have hraw := GaloisForLFunctions.RHTower.norm_fourierCoeffOn_le_of_periodic_three
    (a := -a.1) (b := a.1) (f := g) (f' := deriv g)
    (f'' := deriv (deriv g)) (f''' := deriv (deriv (deriv g)))
    (C := B) (by linarith [a.2])
    (fun x _ => hg1.differentiableAt.hasDerivAt)
    (fun x _ => hg2.differentiableAt.hasDerivAt)
    (fun x _ => hg3.differentiableAt.hasDerivAt)
    (hgd1.continuous.intervalIntegrable (-a.1) a.1)
    (hgd2.continuous.intervalIntegrable (-a.1) a.1)
    (hgd3.continuous.intervalIntegrable (-a.1) a.1) hB
    (by rw [hgRight, hgLeft])
    (by rw [hg1Right, hg1Left])
    (by rw [hg2Right, hg2Left]) hk
  calc
    ‖fourierCoeffOn (by linarith [a.2] : -a.1 < a.1) g k‖
        ≤ ((a.1 - -a.1) / (2 * Real.pi)) ^ 3 * B *
            (1 / |(k : ℝ)| ^ 3) := hraw
    _ = C * (1 / |(k : ℝ)| ^ 3) := by
      rw [show a.1 - -a.1 = 2 * a.1 by ring]

/-! ## Absolute summability in the weighted form norm -/

theorem summable_one_add_abs_mul_inv_abs_cube :
    Summable (fun k : ℤ => (1 + |(k : ℝ)|) * (1 / |(k : ℝ)| ^ 3)) := by
  have hbase : Summable (fun k : ℤ => 2 * (1 / (k : ℝ) ^ 2)) :=
    ((Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity) (by positivity))
    (fun k => ?_) hbase
  by_cases hk : k = 0
  · simp [hk]
  · have hkreal : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have habs : (1 : ℝ) ≤ |(k : ℝ)| := by
      rcases lt_or_gt_of_ne hk with hkneg | hkpos
      · have hkone : k ≤ -1 := by omega
        rw [abs_of_nonpos (by exact_mod_cast hkneg.le)]
        exact_mod_cast (show (1 : ℤ) ≤ -k by omega)
      · rw [abs_of_pos (by exact_mod_cast hkpos)]
        exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    have habs0 : 0 < |(k : ℝ)| := abs_pos.mpr hkreal
    have hlin : 1 + |(k : ℝ)| ≤ 2 * |(k : ℝ)| := by linarith
    rw [show (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 by rw [sq_abs]]
    calc
      (1 + |(k : ℝ)|) * (1 / |(k : ℝ)| ^ 3)
          ≤ (2 * |(k : ℝ)|) * (1 / |(k : ℝ)| ^ 3) := by
        gcongr
      _ = 2 * (1 / |(k : ℝ)| ^ 2) := by
        field_simp

/-- Linear majorant for the norm of the integer aperture modes.  The preceding squared estimate
is logarithmic; this deliberately coarser bound is convenient for summing against cubic Fourier
coefficient decay. -/
theorem norm_suzukiIntegerApertureModeFormVector_le
    (a : SuzukiPositiveAperture) (k : ℤ) :
    ‖suzukiApertureModeFormVector a
        (Real.pi * (k : ℝ) / a.1)‖ ≤
      (2 + |(Real.pi / a.1) / (2 * Real.pi)|) *
        (1 + |(k : ℝ)|) * ‖suzukiApertureModeFormVector a 0‖ := by
  let κ : ℝ := Real.pi * (k : ℝ) / a.1
  let A : ℝ := 1 + suzukiLogWeight (κ / (2 * Real.pi))
  have hA1 : 1 ≤ A := by
    unfold A
    linarith [suzukiLogWeight_nonneg (κ / (2 * Real.pi))]
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  have hsq : ‖suzukiApertureModeFormVector a κ‖ ^ 2 ≤
      (A * ‖suzukiApertureModeFormVector a 0‖) ^ 2 := by
    calc
      ‖suzukiApertureModeFormVector a κ‖ ^ 2
          ≤ A * ‖suzukiApertureModeFormVector a 0‖ ^ 2 :=
        norm_sq_suzukiApertureModeFormVector_le a κ
      _ ≤ (A * ‖suzukiApertureModeFormVector a 0‖) ^ 2 := by
        have hn := norm_nonneg (suzukiApertureModeFormVector a 0)
        nlinarith
  have hnormA : ‖suzukiApertureModeFormVector a κ‖ ≤
      A * ‖suzukiApertureModeFormVector a 0‖ :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hA0 (norm_nonneg _))).mp hsq
  let d : ℝ := |(Real.pi / a.1) / (2 * Real.pi)|
  have hd0 : 0 ≤ d := abs_nonneg _
  have halpha : κ / (2 * Real.pi) =
      ((Real.pi / a.1) / (2 * Real.pi)) * (k : ℝ) := by
    unfold κ
    field_simp [a.2.ne', Real.pi_ne_zero]
  have hAle : A ≤ (2 + d) * (1 + |(k : ℝ)|) := by
    have hw := suzukiLogWeight_le_one_add_abs (κ / (2 * Real.pi))
    calc
      A = 1 + suzukiLogWeight (κ / (2 * Real.pi)) := rfl
      _ ≤ 2 + |κ / (2 * Real.pi)| := by
        linarith
      _ = 2 + d * |(k : ℝ)| := by
        rw [halpha, abs_mul]
      _ ≤ (2 + d) * (1 + |(k : ℝ)|) := by
        nlinarith [hd0, abs_nonneg (k : ℝ)]
  calc
    ‖suzukiApertureModeFormVector a
        (Real.pi * (k : ℝ) / a.1)‖ =
        ‖suzukiApertureModeFormVector a κ‖ := rfl
    _ ≤ A * ‖suzukiApertureModeFormVector a 0‖ := hnormA
    _ ≤ ((2 + d) * (1 + |(k : ℝ)|)) *
        ‖suzukiApertureModeFormVector a 0‖ :=
      mul_le_mul_of_nonneg_right hAle (norm_nonneg _)
    _ = (2 + |(Real.pi / a.1) / (2 * Real.pi)|) *
        (1 + |(k : ℝ)|) * ‖suzukiApertureModeFormVector a 0‖ := rfl

/-- The `k`-th Laurent/Fourier coefficient realized as a genuine weighted form-domain vector. -/
def suzukiHlogLaurentTerm
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ) (k : ℤ) :
    SuzukiHlogFormDomain a :=
  fourierCoeffOn (by linarith [a.2] : -a.1 < a.1) g k •
    suzukiApertureModeFormVector a (Real.pi * (k : ℝ) / a.1)

/-- Cubic coefficient decay absorbs aperture-mode growth, so the Laurent series converges
absolutely in the exact weighted form norm. -/
theorem summable_norm_suzukiHlogLaurentTerm
    (a : SuzukiPositiveAperture) {g : ℝ → ℂ}
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g)
    (hginterior : tsupport g ⊆ Ioo (-a.1) a.1) :
    Summable (fun k : ℤ => ‖suzukiHlogLaurentTerm a g k‖) := by
  obtain ⟨C, hC0, hcoeff⟩ :=
    exists_fourierCoeffOn_cubic_bound a hgdiff hgsupp hginterior
  let D : ℝ := (2 + |(Real.pi / a.1) / (2 * Real.pi)|) *
    ‖suzukiApertureModeFormVector a 0‖
  have hD0 : 0 ≤ D := by
    unfold D
    positivity
  have hmajor : Summable (fun k : ℤ =>
      (C * D) * ((1 + |(k : ℝ)|) * (1 / |(k : ℝ)| ^ 3))) :=
    summable_one_add_abs_mul_inv_abs_cube.mul_left (C * D)
  refine Summable.of_norm_bounded_eventually hmajor ?_
  have hcof : ({(0 : ℤ)}ᶜ : Set ℤ) ∈ Filter.cofinite := by
    rw [Filter.mem_cofinite, compl_compl]
    exact Set.finite_singleton 0
  filter_upwards [hcof] with k hk
  have hcoeffk := hcoeff k (by simpa using hk)
  have hmode := norm_suzukiIntegerApertureModeFormVector_le a k
  have hcoeffNonneg : 0 ≤ C * (1 / |(k : ℝ)| ^ 3) :=
    mul_nonneg hC0 (by positivity)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg (suzukiHlogLaurentTerm a g k))]
  unfold suzukiHlogLaurentTerm
  rw [norm_smul]
  calc
    ‖fourierCoeffOn (by linarith [a.2] : -a.1 < a.1) g k‖ *
        ‖suzukiApertureModeFormVector a (Real.pi * (k : ℝ) / a.1)‖
        ≤ (C * (1 / |(k : ℝ)| ^ 3)) *
          ‖suzukiApertureModeFormVector a (Real.pi * (k : ℝ) / a.1)‖ :=
      mul_le_mul_of_nonneg_right hcoeffk (norm_nonneg _)
    _ ≤ (C * (1 / |(k : ℝ)| ^ 3)) *
        ((2 + |(Real.pi / a.1) / (2 * Real.pi)|) *
          (1 + |(k : ℝ)|) * ‖suzukiApertureModeFormVector a 0‖) :=
      mul_le_mul_of_nonneg_left hmode hcoeffNonneg
    _ = (C * D) * ((1 + |(k : ℝ)|) * (1 / |(k : ℝ)| ^ 3)) := by
      unfold D
      ring

/-! ## Identification of the form-norm sum -/

theorem suzukiIntegerApertureModeCutoff_eq_circleFourier
    (a : SuzukiPositiveAperture) (k : ℤ) {x : ℝ}
    (hx : x ∈ Icc (-a.1) a.1) :
    suzukiApertureModeCutoff a.1 (Real.pi * (k : ℝ) / a.1) x =
      fourier k ((x : ℝ) : AddCircle (a.1 - -a.1)) := by
  rw [suzukiApertureModeCutoff, indicator_of_mem hx, fourier_coe_apply]
  unfold suzukiApertureMode
  congr 1
  push_cast
  field_simp [a.2.ne']
  ring

theorem suzukiHlogFormEmbedding_laurentTerm_coeFn
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ) (k : ℤ) :
    (suzukiHlogFormEmbedding a (suzukiHlogLaurentTerm a g k) : ℝ → ℂ) =ᵐ[volume]
      fun x => fourierCoeffOn (by linarith [a.2] : -a.1 < a.1) g k *
        suzukiApertureModeCutoff a.1 (Real.pi * (k : ℝ) / a.1) x := by
  rw [suzukiHlogLaurentTerm, map_smul]
  filter_upwards [MeasureTheory.Lp.coeFn_smul
      (fourierCoeffOn (by linarith [a.2] : -a.1 < a.1) g k)
      (suzukiHlogFormEmbedding a
        (suzukiApertureModeFormVector a (Real.pi * (k : ℝ) / a.1))),
    suzukiHlogFormEmbedding_apertureModeFormVector_coeFn a
      (Real.pi * (k : ℝ) / a.1)] with x hsmul hmode
  rw [hsmul]
  change fourierCoeffOn (by linarith [a.2] : -a.1 < a.1) g k *
      (suzukiHlogFormEmbedding a
        (suzukiApertureModeFormVector a (Real.pi * (k : ℝ) / a.1)) : ℝ → ℂ) x = _
  rw [hmode]

/-- Pointwise Fourier inversion for a strict-interior smooth aperture test. -/
theorem hasSum_fourier_interiorSmooth
    (a : SuzukiPositiveAperture) {g : ℝ → ℂ}
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g)
    (hginterior : tsupport g ⊆ Ioo (-a.1) a.1)
    {x : ℝ} (hx : x ∈ Ioc (-a.1) a.1) :
    HasSum (fun k : ℤ =>
      fourierCoeffOn (by linarith [a.2] : -a.1 < a.1) g k *
        fourier k ((x : ℝ) : AddCircle (a.1 - -a.1))) (g x) := by
  have hg1 : Differentiable ℝ g := hgdiff.differentiable (by simp)
  have hgd1 : ContDiff ℝ (⊤ : ℕ∞) (deriv g) :=
    (contDiff_infty_iff_deriv.mp hgdiff).2
  have hg2 : Differentiable ℝ (deriv g) := hgd1.differentiable (by simp)
  have hgd2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv g)) :=
    (contDiff_infty_iff_deriv.mp hgd1).2
  obtain ⟨B, hB⟩ := hgd2.continuous.bounded_above_of_compact_support
    hgsupp.deriv.deriv
  rcases aperture_endpoint_jets_zero hginterior with
    ⟨hgLeft, hgRight, hg1Left, hg1Right, _, _⟩
  exact GaloisForLFunctions.RHTower.hasSum_fourier_of_periodic_two
    (a := -a.1) (b := a.1) (f := g) (f' := deriv g)
    (f'' := deriv (deriv g)) (C := B) (by linarith [a.2])
    (fun y _ => hg1.differentiableAt.hasDerivAt)
    (fun y _ => hg2.differentiableAt.hasDerivAt)
    (hgd1.continuous.intervalIntegrable (-a.1) a.1)
    (hgd2.continuous.intervalIntegrable (-a.1) a.1) hB
    (by rw [hgRight, hgLeft])
    (by rw [hg1Right, hg1Left]) hx

/-- Almost-everywhere physical-side sum of the absolutely form-convergent Laurent series. -/
theorem ae_hasSum_suzukiHlogFormEmbedding_laurentTerm
    (a : SuzukiPositiveAperture) {g : ℝ → ℂ}
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g)
    (hginterior : tsupport g ⊆ Ioo (-a.1) a.1) :
    ∀ᵐ x : ℝ, HasSum (fun k : ℤ =>
      (suzukiHlogFormEmbedding a (suzukiHlogLaurentTerm a g k) : ℝ → ℂ) x) (g x) := by
  have hterm : ∀ᵐ x : ℝ, ∀ k : ℤ,
      (suzukiHlogFormEmbedding a (suzukiHlogLaurentTerm a g k) : ℝ → ℂ) x =
        fourierCoeffOn (by linarith [a.2] : -a.1 < a.1) g k *
          suzukiApertureModeCutoff a.1 (Real.pi * (k : ℝ) / a.1) x :=
    ae_all_iff.mpr fun k => suzukiHlogFormEmbedding_laurentTerm_coeFn a g k
  filter_upwards [hterm, (volume : Measure ℝ).ae_ne (-a.1)] with x htermx hxleft
  by_cases hx : x ∈ Ioc (-a.1) a.1
  · have hsource := hasSum_fourier_interiorSmooth a hgdiff hgsupp hginterior hx
    refine hsource.congr_fun fun k => ?_
    rw [htermx k]
    exact congrArg (fun z : ℂ =>
      fourierCoeffOn (by linarith [a.2] : -a.1 < a.1) g k * z)
      (suzukiIntegerApertureModeCutoff_eq_circleFourier a k
        ⟨le_of_lt hx.1, hx.2⟩)
  · have hxOutside : x ∉ Icc (-a.1) a.1 := by
      rw [mem_Icc, not_and_or]
      rw [mem_Ioc, not_and_or] at hx
      rcases hx with hx | hx
      · have hlt : x < -a.1 :=
          lt_of_le_of_ne (le_of_not_gt hx) hxleft
        exact Or.inl (not_le_of_gt hlt)
      · exact Or.inr hx
    have hgzero : g x = 0 := by
      apply eq_zero_of_notMem_tsupport
      intro hxsupp
      have hxin := hginterior hxsupp
      exact hxOutside ⟨hxin.1.le, hxin.2.le⟩
    rw [hgzero]
    refine (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℂ)) 0).congr_fun fun k => ?_
    rw [htermx k, suzukiApertureModeCutoff, indicator_of_notMem hxOutside, mul_zero]

theorem summable_suzukiHlogLaurentTerm
    (a : SuzukiPositiveAperture) {g : ℝ → ℂ}
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g)
    (hginterior : tsupport g ⊆ Ioo (-a.1) a.1) :
    Summable (suzukiHlogLaurentTerm a g) :=
  (summable_norm_suzukiHlogLaurentTerm a hgdiff hgsupp hginterior).of_norm

/-- The form-norm Laurent series sums to the unique form vector represented by `g`. -/
theorem tsum_suzukiHlogLaurentTerm_eq
    (a : SuzukiPositiveAperture) {g : ℝ → ℂ}
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g)
    (hginterior : tsupport g ⊆ Ioo (-a.1) a.1)
    (q : SuzukiHlogFormDomain a)
    (hq : suzukiHlogFormEmbedding a q = suzukiComplexTestL2 g hgdiff hgsupp) :
    ∑' k : ℤ, suzukiHlogLaurentTerm a g k = q := by
  let term : ℤ → SuzukiHlogFormDomain a := suzukiHlogLaurentTerm a g
  let embedded : ℤ → SoninL2 := fun k => suzukiHlogFormEmbedding a (term k)
  have hnormTerm : Summable (fun k : ℤ => ‖term k‖) :=
    summable_norm_suzukiHlogLaurentTerm a hgdiff hgsupp hginterior
  have hnormEmbedded : Summable (fun k : ℤ => ‖embedded k‖) := by
    have hmajor : Summable (fun k : ℤ =>
        ‖suzukiHlogFormEmbedding a‖ * ‖term k‖) :=
      hnormTerm.mul_left ‖suzukiHlogFormEmbedding a‖
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hmajor
    exact (suzukiHlogFormEmbedding a).le_opNorm (term k)
  have henorm : (∑' k : ℤ, ‖embedded k‖ₑ) ≠ ⊤ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hnormEmbedded
  have hpointLp := MeasureTheory.Lp.hasSum_coeFn_tsum henorm
  have hpointSource := ae_hasSum_suzukiHlogFormEmbedding_laurentTerm
    a hgdiff hgsupp hginterior
  have hcoe : ((∑' k : ℤ, embedded k : SoninL2) : ℝ → ℂ) =ᵐ[volume] g := by
    filter_upwards [hpointLp, hpointSource] with x hlp hsource
    exact hlp.unique hsource
  have hmap : suzukiHlogFormEmbedding a (∑' k : ℤ, term k) =
      ∑' k : ℤ, embedded k := by
    exact (suzukiHlogFormEmbedding a).map_tsum
      ((summable_suzukiHlogLaurentTerm a hgdiff hgsupp hginterior))
  have hqcoe : (suzukiHlogFormEmbedding a q : ℝ → ℂ) =ᵐ[volume] g := by
    rw [hq]
    exact suzukiComplexTestL2_coeFn g hgdiff hgsupp
  apply suzukiHlogFormEmbedding_injective a
  rw [hmap]
  apply Lp.ext
  exact hcoe.trans hqcoe.symm

/-! ## Finite Laurent polynomials and the form-core theorem -/

/-- Algebraic Laurent polynomials in the aperture character, realized in the complete weighted
form domain. -/
def suzukiHlogLaurentSubmodule (a : SuzukiPositiveAperture) :
    Submodule ℂ (SuzukiHlogFormDomain a) :=
  Submodule.span ℂ (Set.range fun k : ℤ =>
    suzukiApertureModeFormVector a (Real.pi * (k : ℝ) / a.1))

theorem suzukiIntegerApertureModeFormVector_mem_laurentSubmodule
    (a : SuzukiPositiveAperture) (k : ℤ) :
    suzukiApertureModeFormVector a (Real.pi * (k : ℝ) / a.1) ∈
      suzukiHlogLaurentSubmodule a :=
  Submodule.subset_span ⟨k, rfl⟩

theorem suzukiHlogLaurentTerm_mem_laurentSubmodule
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ) (k : ℤ) :
    suzukiHlogLaurentTerm a g k ∈ suzukiHlogLaurentSubmodule a :=
  (suzukiHlogLaurentSubmodule a).smul_mem _
    (suzukiIntegerApertureModeFormVector_mem_laurentSubmodule a k)

/-- Symmetric finite Laurent truncations converge in the exact weighted form norm. -/
theorem tendsto_suzukiHlogSymmetricLaurentPartialSum
    (a : SuzukiPositiveAperture) {g : ℝ → ℂ}
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g)
    (hginterior : tsupport g ⊆ Ioo (-a.1) a.1)
    (q : SuzukiHlogFormDomain a)
    (hq : suzukiHlogFormEmbedding a q = suzukiComplexTestL2 g hgdiff hgsupp) :
    Tendsto (fun N : ℕ =>
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), suzukiHlogLaurentTerm a g k)
      atTop (nhds q) := by
  have hsum : HasSum (suzukiHlogLaurentTerm a g) q := by
    have h := (summable_suzukiHlogLaurentTerm a hgdiff hgsupp hginterior).hasSum
    rw [tsum_suzukiHlogLaurentTerm_eq a hgdiff hgsupp hginterior q hq] at h
    exact h
  have hbands := GaloisForLFunctions.tendsto_finsetIcc_atTop
    (b := fun N : ℕ => N) tendsto_id
  convert hsum.comp hbands using 1
  funext N
  rfl

theorem interiorSmoothCore_subset_closure_laurentSubmodule
    (a : SuzukiPositiveAperture) :
    suzukiHlogInteriorSmoothCore a ⊆
      closure (suzukiHlogLaurentSubmodule a : Set (SuzukiHlogFormDomain a)) := by
  intro q hq
  rcases hq with ⟨g, hgdiff, hgsupp, hginterior, hqembed⟩
  have hmem : (∑' k : ℤ, suzukiHlogLaurentTerm a g k) ∈
      (suzukiHlogLaurentSubmodule a).topologicalClosure :=
    tsum_mem (Submodule.isClosed_topologicalClosure (suzukiHlogLaurentSubmodule a))
      (fun k => by
        change suzukiHlogLaurentTerm a g k ∈
          closure (suzukiHlogLaurentSubmodule a : Set (SuzukiHlogFormDomain a))
        exact subset_closure (suzukiHlogLaurentTerm_mem_laurentSubmodule a g k))
  rw [tsum_suzukiHlogLaurentTerm_eq a hgdiff hgsupp hginterior q hqembed] at hmem
  exact hmem

/-- **Connes--Consani (2021), Lemma `core`, literal weighted theorem.**

Finite Laurent polynomials in `U(x)=exp(πix/a)` are dense in the complete aperture-supported
`H^log` form domain.  Equivalently, they form a core for the closed logarithmic quadratic form;
all convergence here is in the form norm, not merely in ordinary `L²`. -/
theorem dense_suzukiHlogLaurentSubmodule (a : SuzukiPositiveAperture) :
    Dense (suzukiHlogLaurentSubmodule a : Set (SuzukiHlogFormDomain a)) := by
  intro q
  have hsubset : closure (suzukiHlogInteriorSmoothCore a) ⊆
      closure (suzukiHlogLaurentSubmodule a : Set (SuzukiHlogFormDomain a)) :=
    closure_minimal (interiorSmoothCore_subset_closure_laurentSubmodule a) isClosed_closure
  exact hsubset (dense_suzukiHlogInteriorSmoothCore a q)

/-- Source-language alias: the Laurent algebra `ℂ[U,U⁻¹]` is a form core. -/
theorem ccmLaurentPolynomials_formCore (a : SuzukiPositiveAperture) :
    closure (suzukiHlogLaurentSubmodule a : Set (SuzukiHlogFormDomain a)) = Set.univ :=
  (dense_iff_closure_eq.mp (dense_suzukiHlogLaurentSubmodule a))

end RHTower

end
