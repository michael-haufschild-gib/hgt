import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalBounds
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62HorizontalDecay

/-!
# Chen--Gupta--Li Lemma 6.2: principal horizontal contour edges

The all-order uniform Mellin estimate absorbs the existential polynomial degree
of the principal Euler--zeta strip envelope.  Above the shifted unit-height
threshold, the literal principal integrand is uniformly `O(|Im(s)|⁻²)`.
-/

open Complex MeasureTheory Filter Set Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

noncomputable def cglLemma62PrincipalLStripBudget (Q : CGLPositiveModulus) : ℝ :=
  Classical.choose (cglLemma62_exists_bound_principalLFunction_strip Q)

noncomputable def cglLemma62PrincipalLStripDegree (Q : CGLPositiveModulus) : ℕ :=
  Classical.choose (Classical.choose_spec
    (cglLemma62_exists_bound_principalLFunction_strip Q))

private theorem cglLemma62PrincipalLStripBudget_pos (Q : CGLPositiveModulus) :
    0 < cglLemma62PrincipalLStripBudget Q :=
  (Classical.choose_spec (Classical.choose_spec
    (cglLemma62_exists_bound_principalLFunction_strip Q))).1

private theorem cglLemma62PrincipalLStripBudget_bound
    (Q : CGLPositiveModulus) (x v : ℝ)
    (hxlo : (-1 : ℝ) ≤ x) (hxhi : x ≤ 2) (hv : 1 ≤ |v|) :
    ‖DirichletCharacter.LFunctionTrivChar Q.value ((x : ℂ) + (v : ℂ) * I)‖ ≤
      cglLemma62PrincipalLStripBudget Q * (1 + |v|) ^
        cglLemma62PrincipalLStripDegree Q :=
  (Classical.choose_spec (Classical.choose_spec
    (cglLemma62_exists_bound_principalLFunction_strip Q))).2 x v hxlo hxhi hv

private theorem cglLemma62_principal_shifted_one_add_absPow_le
    (t y : ℝ) (n : ℕ) :
    (1 + |y - t|) ^ n ≤ (1 + |t|) ^ n * (1 + |y|) ^ n := by
  have hbase : 1 + |y - t| ≤ (1 + |t|) * (1 + |y|) := by
    rw [abs_sub_comm]
    have htri : |t - y| ≤ |t| + |y| := by
      calc
        |t - y| = |t + (-y)| := by rw [sub_eq_add_neg]
        _ ≤ |t| + |-y| := abs_add_le _ _
        _ = |t| + |y| := by rw [abs_neg]
    nlinarith [abs_nonneg t, abs_nonneg y]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + |y - t|) hbase n
  rw [mul_pow] at hpow
  exact hpow

private theorem cglLemma62_one_add_abs_pow_le_two_mul_abs
    (y : ℝ) (n : ℕ) (hy : 1 ≤ |y|) :
    (1 + |y|) ^ n ≤ 2 ^ n * |y| ^ n := by
  have hbase : 1 + |y| ≤ 2 * |y| := by linarith
  calc
    (1 + |y|) ^ n ≤ (2 * |y|) ^ n :=
      pow_le_pow_left₀ (by positivity) hbase n
    _ = 2 ^ n * |y| ^ n := mul_pow _ _ n

private theorem cglLemma62_principalHorizontal_point_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t y x : ℝ)
    (hxlo : -1 ≤ x) (hxhi : x ≤ 2)
    (hy : 1 ≤ |y|) (hyt : 1 ≤ |y - t|) :
    ‖cglLemma62PrincipalContourIntegrand w N Q t ((x : ℂ) + (y : ℂ) * I)‖ ≤
      (2 ^ cglLemma62PrincipalLStripDegree Q * (N.value : ℝ) ^ (2 : ℝ) *
        cglLemma62PrincipalLStripBudget Q * (1 + |t|) ^ cglLemma62PrincipalLStripDegree Q *
        cglLemma62MellinFirstShiftUniformBudget w (cglLemma62PrincipalLStripDegree Q + 2)) /
        |y| ^ 2 := by
  let n := cglLemma62PrincipalLStripDegree Q
  have hNpos : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  have hNone : 1 ≤ (N.value : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt N.positive))
  have hypos : 0 < |y| := lt_of_lt_of_le zero_lt_one hy
  have hE : 0 ≤ cglLemma62PrincipalLStripBudget Q :=
    (cglLemma62PrincipalLStripBudget_pos Q).le
  have hB : 0 ≤ cglLemma62MellinFirstShiftUniformBudget w (n + 2) := by
    dsimp [cglLemma62MellinFirstShiftUniformBudget]
    apply integral_nonneg
    intro u
    unfold deningerMeyerUniformStripMajorant
    positivity
  have hT : 0 ≤ (1 + |t|) ^ n := by positivity
  have hNtwo : 0 ≤ (N.value : ℝ) ^ (2 : ℝ) := by positivity
  let sigma : CGLLemma62FirstShiftAbscissa := ⟨x, hxlo, hxhi⟩
  have hkernel0 := cglLemma62_mellinTransform_firstShift_uniformAllOrderDecay
    w (n + 2) sigma y
  have hkernel : ‖cglLemma62MellinTransform w ((x : ℂ) + (y : ℂ) * I)‖ ≤
      cglLemma62MellinFirstShiftUniformBudget w (n + 2) / |y| ^ (n + 2) := by
    apply (le_div_iff₀ (pow_pos hypos (n + 2))).mpr
    simpa [sigma, mul_comm] using hkernel0
  have hL0 := cglLemma62PrincipalLStripBudget_bound Q x (y - t) hxlo hxhi hyt
  have hL : ‖DirichletCharacter.LFunctionTrivChar Q.value
      (((x : ℂ) + (y : ℂ) * I) - (t : ℂ) * I)‖ ≤
      cglLemma62PrincipalLStripBudget Q * (1 + |t|) ^ n * (1 + |y|) ^ n := by
    have harg : ((x : ℂ) + ((y - t : ℝ) : ℂ) * I) =
        ((x : ℂ) + (y : ℂ) * I) - (t : ℂ) * I := by
      push_cast
      ring
    rw [harg] at hL0
    calc
      _ ≤ cglLemma62PrincipalLStripBudget Q * (1 + |y - t|) ^ n := hL0
      _ ≤ cglLemma62PrincipalLStripBudget Q * ((1 + |t|) ^ n * (1 + |y|) ^ n) :=
        mul_le_mul_of_nonneg_left
          (cglLemma62_principal_shifted_one_add_absPow_le t y n) hE
      _ = _ := by ring
  have hNpow : (N.value : ℝ) ^ x ≤ (N.value : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNone hxhi
  have hpoly := cglLemma62_one_add_abs_pow_le_two_mul_abs y n hy
  unfold cglLemma62PrincipalContourIntegrand
  have hNcast : (N.value : ℂ) = ((N.value : ℝ) : ℂ) := by norm_cast
  rw [norm_mul, norm_mul, hNcast,
    Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  rw [hre]
  calc
    ‖cglLemma62MellinTransform w (↑x + ↑y * I)‖ * (N.value : ℝ) ^ x *
        ‖DirichletCharacter.LFunctionTrivChar Q.value (↑x + ↑y * I - ↑t * I)‖ ≤
      (cglLemma62MellinFirstShiftUniformBudget w (n + 2) / |y| ^ (n + 2)) *
        (N.value : ℝ) ^ x *
        ‖DirichletCharacter.LFunctionTrivChar Q.value (↑x + ↑y * I - ↑t * I)‖ := by
          gcongr
    _ ≤ (cglLemma62MellinFirstShiftUniformBudget w (n + 2) / |y| ^ (n + 2)) *
        (N.value : ℝ) ^ (2 : ℝ) *
        ‖DirichletCharacter.LFunctionTrivChar Q.value (↑x + ↑y * I - ↑t * I)‖ := by
          gcongr
    _ ≤ (cglLemma62MellinFirstShiftUniformBudget w (n + 2) / |y| ^ (n + 2)) *
        (N.value : ℝ) ^ (2 : ℝ) *
        (cglLemma62PrincipalLStripBudget Q * (1 + |t|) ^ n * (1 + |y|) ^ n) := by
          gcongr
    _ ≤ (cglLemma62MellinFirstShiftUniformBudget w (n + 2) / |y| ^ (n + 2)) *
        (N.value : ℝ) ^ (2 : ℝ) *
        (cglLemma62PrincipalLStripBudget Q * (1 + |t|) ^ n * (2 ^ n * |y| ^ n)) := by
          gcongr
    _ = (2 ^ n * (N.value : ℝ) ^ (2 : ℝ) * cglLemma62PrincipalLStripBudget Q *
        (1 + |t|) ^ n * cglLemma62MellinFirstShiftUniformBudget w (n + 2)) /
        |y| ^ 2 := by
          field_simp [ne_of_gt hypos]
          have hp : |y| ^ n * |y| ^ 2 = |y| ^ (n + 2) :=
            (pow_add |y| n 2).symm
          calc
            _ = cglLemma62MellinFirstShiftUniformBudget w (n + 2) *
                cglLemma62PrincipalLStripBudget Q * (|y| ^ n * |y| ^ 2) := by ring
            _ = cglLemma62MellinFirstShiftUniformBudget w (n + 2) *
                cglLemma62PrincipalLStripBudget Q * |y| ^ (n + 2) := by rw [hp]
            _ = _ := by ring

/-- The upper horizontal side of CGL's principal first-shift rectangle
vanishes without caller-supplied analytic premises. -/
theorem cglLemma62_principalContourIntegrand_horizontal_top
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) :
    Tendsto (fun y : ℝ =>
      ∫ x in (-1 : ℝ)..2,
        cglLemma62PrincipalContourIntegrand w N Q t ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) := by
  let n := cglLemma62PrincipalLStripDegree Q
  let C : ℝ := 2 ^ n * (N.value : ℝ) ^ (2 : ℝ) *
    cglLemma62PrincipalLStripBudget Q * (1 + |t|) ^ n *
    cglLemma62MellinFirstShiftUniformBudget w (n + 2)
  have hdecay : Tendsto (fun y : ℝ => C / y ^ 2) atTop (𝓝 0) := by
    have hpow : Tendsto (fun y : ℝ => y ^ (-(2 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have hscaled : Tendsto (fun y : ℝ => C * y ^ (-(2 : ℝ))) atTop (𝓝 0) := by
      simpa using hpow.const_mul C
    refine Filter.Tendsto.congr' ?_ hscaled
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    rw [Real.rpow_neg hy, Real.rpow_two, div_eq_mul_inv]
  apply GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
    (M := fun y : ℝ => C / y ^ 2) (hgt := fun y : ℝ => y)
  · filter_upwards [eventually_ge_atTop (|t| + 1)] with y hy x hx
    have hx' : x ∈ Icc (-1 : ℝ) 2 := by
      simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] using (uIoc_subset_uIcc hx)
    have hyabs : 1 ≤ |y| := by
      rw [abs_of_nonneg (by linarith [abs_nonneg t] : 0 ≤ y)]
      linarith [abs_nonneg t]
    have hyt : 1 ≤ |y - t| := by
      calc
        1 ≤ y - |t| := by linarith
        _ ≤ y - t := sub_le_sub_left (le_abs_self t) y
        _ ≤ |y - t| := le_abs_self _
    have hpoint := cglLemma62_principalHorizontal_point_bound w N Q t y x
      hx'.1 hx'.2 hyabs hyt
    simpa [C, n, abs_of_nonneg (by linarith [abs_nonneg t] : 0 ≤ y)] using hpoint
  · exact hdecay

/-- The lower horizontal side of CGL's principal first-shift rectangle
vanishes without caller-supplied analytic premises. -/
theorem cglLemma62_principalContourIntegrand_horizontal_bottom
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) :
    Tendsto (fun y : ℝ =>
      ∫ x in (-1 : ℝ)..2,
        cglLemma62PrincipalContourIntegrand w N Q t ((x : ℂ) + (y : ℂ) * I))
      atBot (𝓝 0) := by
  let n := cglLemma62PrincipalLStripDegree Q
  let C : ℝ := 2 ^ n * (N.value : ℝ) ^ (2 : ℝ) *
    cglLemma62PrincipalLStripBudget Q * (1 + |t|) ^ n *
    cglLemma62MellinFirstShiftUniformBudget w (n + 2)
  have hdecay : Tendsto (fun y : ℝ => C / y ^ 2) atTop (𝓝 0) := by
    have hpow : Tendsto (fun y : ℝ => y ^ (-(2 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have hscaled : Tendsto (fun y : ℝ => C * y ^ (-(2 : ℝ))) atTop (𝓝 0) := by
      simpa using hpow.const_mul C
    refine Filter.Tendsto.congr' ?_ hscaled
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    rw [Real.rpow_neg hy, Real.rpow_two, div_eq_mul_inv]
  have hneg : Tendsto (fun y : ℝ =>
      ∫ x in (-1 : ℝ)..2,
        cglLemma62PrincipalContourIntegrand w N Q t ((x : ℂ) + ((-y : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
    apply GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (M := fun y : ℝ => C / y ^ 2) (hgt := fun y : ℝ => -y)
    · filter_upwards [eventually_ge_atTop (|t| + 1)] with y hy x hx
      have hx' : x ∈ Icc (-1 : ℝ) 2 := by
        simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] using (uIoc_subset_uIcc hx)
      have hyabs : 1 ≤ |-y| := by
        rw [abs_neg, abs_of_nonneg (by linarith [abs_nonneg t] : 0 ≤ y)]
        linarith [abs_nonneg t]
      have hyt : 1 ≤ |-y - t| := by
        rw [show -y - t = -(y + t) by ring, abs_neg]
        calc
          1 ≤ y - |t| := by linarith
          _ ≤ y + t := by linarith [neg_abs_le t]
          _ ≤ |y + t| := le_abs_self _
      have hpoint := cglLemma62_principalHorizontal_point_bound w N Q t (-y) x
        hx'.1 hx'.2 hyabs hyt
      simpa [C, n, abs_neg, abs_of_nonneg (by linarith [abs_nonneg t] : 0 ≤ y)] using hpoint
    · exact hdecay
  refine Filter.Tendsto.congr' ?_ (hneg.comp tendsto_neg_atBot_atTop)
  filter_upwards with y
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with x
  intro _
  congr 1
  push_cast
  ring

end

end RHTower
