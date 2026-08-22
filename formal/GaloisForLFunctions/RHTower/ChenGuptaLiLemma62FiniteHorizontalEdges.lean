import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FiniteBounds
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62HorizontalDecay

/-!
# Chen--Gupta--Li Lemma 6.2: finite reflected horizontal contour edges

The literal finite reflected integrand is `O(|Im(s)|⁻²)` uniformly across
CGL's pole-free displacement strip.  This absorbs the quadratic primitive
functional-factor growth using fourth-order uniform Mellin decay and proves
the two horizontal sides vanish.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- Certified points on the horizontal sides of CGL's finite reflected
rectangle.  Every source-side and height condition is retained as data. -/
structure CGLLemma62FiniteHorizontalPoint (t : ℝ) where
  x : ℝ
  y : ℝ
  lower : (-1 : ℝ) ≤ x
  upper : x ≤ 1 / 2
  y_large : 1 ≤ |y|
  shifted_large : 2 ≤ |y - t|

private theorem cglLemma62_finite_shifted_one_add_absPow_le
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

private theorem cglLemma62_finite_one_add_abs_pow_le_two_mul_abs
    (y : ℝ) (n : ℕ) (hy : 1 ≤ |y|) :
    (1 + |y|) ^ n ≤ 2 ^ n * |y| ^ n := by
  have hbase : 1 + |y| ≤ 2 * |y| := by linarith
  calc
    (1 + |y|) ^ n ≤ (2 * |y|) ^ n :=
      pow_le_pow_left₀ (by positivity) hbase n
    _ = 2 ^ n * |y| ^ n := mul_pow _ _ n

/-- A closed uniform `O(|y|⁻²)` envelope for CGL's literal finite reflected
integrand.  The fixed height gap keeps the primitive factor in its proven
high strip, while the source's finite Euler and Dirichlet factors stay bounded.
-/
theorem cglLemma62_finiteContour_horizontal_point_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : CGLLemma62FiniteHorizontalPoint t,
      ‖cglLemma62FiniteContourIntegrand w N B t M
        ((p.x : ℂ) + (p.y : ℂ) * I)‖ ≤ C / |p.y| ^ 2 := by
  rcases cglLemma62_primitiveFunctionalFactor_highHeight_bound B.primitive with
    ⟨A, hA, hA_bound⟩
  let K := cglLemma62MellinFirstShiftUniformBudget w 4
  let E := cglLemma62EulerCorrectionBudget B
  let C : ℝ := K * (N.value : ℝ) ^ (2 : ℝ) * A * E * (M + 1) *
    (1 + |t|) ^ 2 * 2 ^ 2
  let z0 : CGLLemma62HighStripPoint :=
    ⟨(-1 : ℂ) + (2 : ℂ) * I, by simp, by norm_num, by norm_num⟩
  have hE0 := cglLemma62EulerCorrectionAt_highStrip_norm_le B z0
  have hEnonneg : 0 ≤ E := by
    dsimp [E]
    exact le_trans (norm_nonneg _) hE0
  have hK : 0 ≤ K := by
    dsimp [K, cglLemma62MellinFirstShiftUniformBudget]
    apply integral_nonneg
    intro u
    unfold deningerMeyerUniformStripMajorant
    positivity
  have hNtwo : 0 ≤ (N.value : ℝ) ^ (2 : ℝ) := by positivity
  have hM : 0 ≤ (M + 1 : ℝ) := by positivity
  have ht : 0 ≤ (1 + |t|) ^ 2 := by positivity
  have htwo : 0 ≤ (2 : ℝ) ^ 2 := by positivity
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro p
    let s : ℂ := (p.x : ℂ) + (p.y : ℂ) * I
    let z : CGLLemma62HighStripPoint := ⟨s - (t : ℂ) * I, by
      dsimp [s]
      simp
      exact p.lower, by
      dsimp [s]
      simp
      norm_num at p ⊢
      exact p.upper, by
      dsimp [s]
      simp
      exact p.shifted_large⟩
    let sigma : CGLLemma62FirstShiftAbscissa := ⟨p.x, p.lower, by
      linarith [p.upper]⟩
    let d : CGLLemma62NonnegativePoint := ⟨1 - s + (t : ℂ) * I, by
      dsimp [s]
      simp
      linarith [p.upper]⟩
    have hypos : 0 < |p.y| := lt_of_lt_of_le zero_lt_one p.y_large
    have hK : 0 ≤ K := by
      dsimp [K, cglLemma62MellinFirstShiftUniformBudget]
      apply integral_nonneg
      intro u
      unfold deningerMeyerUniformStripMajorant
      positivity
    have hkernel0 := cglLemma62_mellinTransform_firstShift_uniformAllOrderDecay w 4 sigma p.y
    have hkernel : ‖cglLemma62MellinTransform w s‖ ≤ K / |p.y| ^ 4 := by
      apply (le_div_iff₀ (pow_pos hypos 4)).mpr
      simpa [s, sigma, K, mul_comm] using hkernel0
    have hNraw := cglLemma62_lengthPower_highStrip_norm_le N z
    have hN : ‖(N.value : ℂ) ^ s‖ ≤ (N.value : ℝ) ^ (2 : ℝ) := by
      rw [show ‖(N.value : ℂ) ^ s‖ = ‖(N.value : ℂ) ^ z.value‖ by
        rw [Complex.norm_natCast_cpow_of_pos N.positive,
          Complex.norm_natCast_cpow_of_pos N.positive]
        congr 1
        dsimp [z, s]
        simp]
      exact hNraw
    have hP0 := hA_bound z
    have hquad : (p.y - t) ^ 2 ≤ (1 + |t|) ^ 2 * (1 + |p.y|) ^ 2 := by
      calc
        (p.y - t) ^ 2 = |p.y - t| ^ 2 := by rw [sq_abs]
        _ ≤ (1 + |p.y - t|) ^ 2 := by
          gcongr
          linarith [abs_nonneg (p.y - t)]
        _ ≤ (1 + |t|) ^ 2 * (1 + |p.y|) ^ 2 :=
          cglLemma62_finite_shifted_one_add_absPow_le t p.y 2
    have hP : ‖cglLemma62PrimitiveFunctionalFactor B.primitive
        (s - (t : ℂ) * I)‖ ≤ A * (1 + |t|) ^ 2 * (1 + |p.y|) ^ 2 := by
      calc
        _ = ‖cglLemma62PrimitiveFunctionalFactor B.primitive z.value‖ := by rfl
        _ ≤ A * z.value.im ^ 2 := hP0
        _ = A * (p.y - t) ^ 2 := by
          congr 2
          dsimp [z, s]
          simp
        _ ≤ A * ((1 + |t|) ^ 2 * (1 + |p.y|) ^ 2) :=
          mul_le_mul_of_nonneg_left hquad hA
        _ = _ := by ring
    have hE0 := cglLemma62EulerCorrectionAt_highStrip_norm_le B z
    have hE : ‖cglLemma62EulerCorrectionAt B (s - (t : ℂ) * I)‖ ≤ E := by
      simpa [z, E] using hE0
    have hEnonneg : 0 ≤ E := le_trans (norm_nonneg _) hE
    have hD0 := cglLemma62_dirichletHead_norm_le B M d
    have hD : ‖cglLemma62DirichletHead B.character⁻¹ M (1 - s + (t : ℂ) * I)‖ ≤ M + 1 := by
      simpa [d] using hD0
    have hpoly := cglLemma62_finite_one_add_abs_pow_le_two_mul_abs p.y 2 p.y_large
    change ‖cglLemma62FiniteContourIntegrand w N B t M s‖ ≤ C / |p.y| ^ 2
    unfold cglLemma62FiniteContourIntegrand
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    calc
      ‖cglLemma62MellinTransform w s‖ * ‖(N.value : ℂ) ^ s‖ *
          ‖cglLemma62PrimitiveFunctionalFactor B.primitive (s - ↑t * I)‖ *
          ‖cglLemma62EulerCorrectionAt B (s - ↑t * I)‖ *
          ‖cglLemma62DirichletHead B.character⁻¹ M (1 - s + ↑t * I)‖ ≤
        (K / |p.y| ^ 4) * (N.value : ℝ) ^ (2 : ℝ) *
          (A * (1 + |t|) ^ 2 * (1 + |p.y|) ^ 2) * E * (M + 1) := by
            gcongr
      _ ≤ (K / |p.y| ^ 4) * (N.value : ℝ) ^ (2 : ℝ) *
          (A * (1 + |t|) ^ 2 * (2 ^ 2 * |p.y| ^ 2)) * E * (M + 1) := by
            gcongr
      _ = C / |p.y| ^ 2 := by
        dsimp [C]
        field_simp [ne_of_gt hypos]

/-- The upper horizontal side of CGL's pole-free finite reflected rectangle
vanishes using the exact finite-contour factorization. -/
theorem cglLemma62_finiteContourIntegrand_horizontal_top
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) :
    Tendsto (fun y : ℝ =>
      ∫ x in (-1 : ℝ)..(1 / 2 : ℝ),
        cglLemma62FiniteContourIntegrand w N B t M ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) := by
  rcases cglLemma62_finiteContour_horizontal_point_bound w N B t M with ⟨C, hC, hpoint⟩
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
  · filter_upwards [eventually_ge_atTop (|t| + 2)] with y hy x hx
    have hx' : x ∈ Icc (-1 : ℝ) (1 / 2 : ℝ) := by
      have hleft : (-1 : ℝ) ≤ 1 / 2 := by norm_num
      have hx'' := uIoc_subset_uIcc hx
      rw [uIcc_of_le hleft] at hx''
      exact hx''
    have hyabs : 1 ≤ |y| := by
      rw [abs_of_nonneg (by linarith [abs_nonneg t] : 0 ≤ y)]
      linarith [abs_nonneg t]
    have hyt : 2 ≤ |y - t| := by
      calc
        2 ≤ y - |t| := by linarith
        _ ≤ y - t := sub_le_sub_left (le_abs_self t) y
        _ ≤ |y - t| := le_abs_self _
    let p : CGLLemma62FiniteHorizontalPoint t :=
      ⟨x, y, hx'.1, hx'.2, hyabs, hyt⟩
    have h := hpoint p
    simpa [p, abs_of_nonneg (by linarith [abs_nonneg t] : 0 ≤ y)] using h
  · exact hdecay

/-- The lower horizontal side of CGL's pole-free finite reflected rectangle
vanishes using the exact finite-contour factorization. -/
theorem cglLemma62_finiteContourIntegrand_horizontal_bottom
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) :
    Tendsto (fun y : ℝ =>
      ∫ x in (-1 : ℝ)..(1 / 2 : ℝ),
        cglLemma62FiniteContourIntegrand w N B t M ((x : ℂ) + (y : ℂ) * I))
      atBot (𝓝 0) := by
  rcases cglLemma62_finiteContour_horizontal_point_bound w N B t M with ⟨C, hC, hpoint⟩
  have hdecay : Tendsto (fun y : ℝ => C / y ^ 2) atTop (𝓝 0) := by
    have hpow : Tendsto (fun y : ℝ => y ^ (-(2 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have hscaled : Tendsto (fun y : ℝ => C * y ^ (-(2 : ℝ))) atTop (𝓝 0) := by
      simpa using hpow.const_mul C
    refine Filter.Tendsto.congr' ?_ hscaled
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    rw [Real.rpow_neg hy, Real.rpow_two, div_eq_mul_inv]
  have hneg : Tendsto (fun y : ℝ =>
      ∫ x in (-1 : ℝ)..(1 / 2 : ℝ),
        cglLemma62FiniteContourIntegrand w N B t M ((x : ℂ) + ((-y : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
    apply GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (M := fun y : ℝ => C / y ^ 2) (hgt := fun y : ℝ => -y)
    · filter_upwards [eventually_ge_atTop (|t| + 2)] with y hy x hx
      have hx' : x ∈ Icc (-1 : ℝ) (1 / 2 : ℝ) := by
        have hleft : (-1 : ℝ) ≤ 1 / 2 := by norm_num
        have hx'' := uIoc_subset_uIcc hx
        rw [uIcc_of_le hleft] at hx''
        exact hx''
      have hyabs : 1 ≤ |-y| := by
        rw [abs_neg, abs_of_nonneg (by linarith [abs_nonneg t] : 0 ≤ y)]
        linarith [abs_nonneg t]
      have hyt : 2 ≤ |-y - t| := by
        rw [show -y - t = -(y + t) by ring, abs_neg]
        calc
          2 ≤ y - |t| := by linarith
          _ ≤ y + t := by linarith [neg_abs_le t]
          _ ≤ |y + t| := le_abs_self _
      let p : CGLLemma62FiniteHorizontalPoint t :=
        ⟨x, -y, hx'.1, hx'.2, hyabs, hyt⟩
      have h := hpoint p
      simpa [p, abs_neg, abs_of_nonneg (by linarith [abs_nonneg t] : 0 ≤ y)] using h
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
