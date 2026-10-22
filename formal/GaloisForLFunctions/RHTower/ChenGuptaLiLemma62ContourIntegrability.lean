import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62ContourBounds
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62MellinKernel

/-!
# Chen--Gupta--Li Lemma 6.2: first-shift vertical integrability

This module supplies the two vertical `L¹` certificates required for CGL's
first displacement from `Re(s)=2` to `Re(s)=-1` in the nonprincipal branch.
The right line uses absolute convergence; the left line combines the induced
cubic strip bound with every polynomial moment of the compact Mellin kernel.
-/

open Complex MeasureTheory Filter Set

noncomputable section

namespace RHTower

/-- The unnormalized Mellin integrand in CGL equation (6.3), before its
first contour shift. -/
def cglLemma62ContourIntegrand (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (s : ℂ) : ℂ :=
  cglLemma62MellinTransform w s * (N.value : ℂ) ^ s *
    DirichletCharacter.LFunction B.character (s - (t : ℂ) * I)

private theorem cglLemma62_kernel_one_add_abs_cube_integrable
    (w : CGLRealSmoothBump) (σ : ℝ) :
    Integrable (fun v : ℝ => (1 + |v|) ^ 3 *
      ‖cglLemma62MellinTransform w ((σ : ℂ) + (v : ℂ) * I)‖) := by
  have h0 := cglLemma62_mellinTransform_vertical_integrable_absPow_norm w σ 0
  have h3 := cglLemma62_mellinTransform_vertical_integrable_absPow_norm w σ 3
  have h0' : Integrable (fun v : ℝ =>
      ‖cglLemma62MellinTransform w ((σ : ℂ) + (v : ℂ) * I)‖) := by
    simpa using h0
  have hsum := (h0'.add h3).const_mul (4 : ℝ)
  refine Integrable.mono' hsum ?_ ?_
  · have hdiff : Differentiable ℂ (cglLemma62MellinTransform w) := fun s =>
      (cglLemma62_mellinTransform_analyticOnNhd w s (mem_univ s)).differentiableAt
    have hline : Continuous (fun v : ℝ => (σ : ℂ) + (v : ℂ) * I) := by fun_prop
    have hweight : Continuous (fun v : ℝ => (1 + |v|) ^ 3) :=
      (continuous_const.add continuous_abs).pow _
    exact (hweight.mul ((hdiff.continuous.comp hline).norm)).aestronglyMeasurable
  filter_upwards with v
  have hnonneg : 0 ≤ |v| := abs_nonneg v
  have hfac : 0 ≤ (|v| - 1) ^ 2 * (|v| + 1) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hcub : (1 + |v|) ^ 3 ≤ 4 * (1 + |v| ^ 3) := by
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg (by positivity) _) (norm_nonneg _))]
  calc
    (1 + |v|) ^ 3 * ‖cglLemma62MellinTransform w ((σ : ℂ) + (v : ℂ) * I)‖ ≤
        (4 * (1 + |v| ^ 3)) *
          ‖cglLemma62MellinTransform w ((σ : ℂ) + (v : ℂ) * I)‖ :=
      mul_le_mul_of_nonneg_right hcub (norm_nonneg _)
    _ = 4 * (‖cglLemma62MellinTransform w ((σ : ℂ) + (v : ℂ) * I)‖ +
        |v| ^ 3 * ‖cglLemma62MellinTransform w ((σ : ℂ) + (v : ℂ) * I)‖) := by ring

theorem cglLemma62_shifted_cubic_le
    (t v : ℝ) :
    (2 + |v - t|) ^ 3 ≤ (2 + |t|) ^ 3 * (1 + |v|) ^ 3 := by
  have hbase : 2 + |v - t| ≤ (2 + |t|) * (1 + |v|) := by
    rw [abs_sub_comm]
    calc
      2 + |t - v| ≤ 2 + (|t| + |v|) := by
        gcongr
        simpa using (abs_sub_le t 0 v)
      _ ≤ (2 + |t|) * (1 + |v|) := by
        nlinarith [abs_nonneg t, abs_nonneg v]
  calc
    (2 + |v - t|) ^ 3 ≤ ((2 + |t|) * (1 + |v|)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hbase 3
    _ = (2 + |t|) ^ 3 * (1 + |v|) ^ 3 := mul_pow _ _ 3

/-- The left vertical edge in the nonprincipal CGL first shift is absolutely
integrable, with all polynomial growth and decay obligations closed. -/
theorem cglLemma62_nonprincipalContourIntegrand_left_integrable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) :
    Integrable (fun v : ℝ =>
      cglLemma62ContourIntegrand w N B t ((-1 : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨E, hE, hLbound⟩ := cglLemma62_exists_bound_inducedLFunction_strip B
  let Hline : ℝ → ℂ := fun v =>
    cglLemma62MellinTransform w ((-1 : ℂ) + (v : ℂ) * I)
  have hkernel := cglLemma62_kernel_one_add_abs_cube_integrable w (-1 : ℝ)
  have hkernel' : Integrable (fun v : ℝ => (1 + |v|) ^ 3 * ‖Hline v‖) := by
    apply hkernel.congr
    filter_upwards with v
    congr 3
    norm_num
  have hNpos : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  have hHdiff : Differentiable ℂ (cglLemma62MellinTransform w) := fun s =>
    (cglLemma62_mellinTransform_analyticOnNhd w s (mem_univ s)).differentiableAt
  have hline : Continuous (fun v : ℝ => (-1 : ℂ) + (v : ℂ) * I) := by fun_prop
  have hpow : Continuous (fun v : ℝ => (N.value : ℂ) ^
      ((-1 : ℂ) + (v : ℂ) * I)) :=
    Continuous.const_cpow hline (Or.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.positive)))
  have hLcont : Continuous (DirichletCharacter.LFunction B.character) :=
    (DirichletCharacter.differentiable_LFunction B.nonprincipal).continuous
  have hLarg : Continuous (fun v : ℝ =>
      ((-1 : ℂ) + (v : ℂ) * I) - (t : ℂ) * I) := by fun_prop
  have hmeas : AEStronglyMeasurable (fun v : ℝ =>
      cglLemma62ContourIntegrand w N B t ((-1 : ℂ) + (v : ℂ) * I)) := by
    unfold cglLemma62ContourIntegrand
    exact ((hHdiff.continuous.comp hline).mul hpow).mul
      (hLcont.comp hLarg) |>.aestronglyMeasurable
  refine Integrable.mono' (hkernel'.const_mul ((N.value : ℝ) ^ (-1 : ℝ) *
    E * (2 + |t|) ^ 3)) hmeas ?_
  filter_upwards with v
  have hL : ‖DirichletCharacter.LFunction B.character
      (((-1 : ℂ) + (v : ℂ) * I) - (t : ℂ) * I)‖ ≤
      E * (2 + |v - t|) ^ 3 := by
    convert hLbound (v - t) (-1 : ℝ) (by norm_num) (by norm_num) using 1
    all_goals
      push_cast
      ring_nf
  have hshift := cglLemma62_shifted_cubic_le t v
  have hL' : ‖DirichletCharacter.LFunction B.character
      (((-1 : ℂ) + (v : ℂ) * I) - (t : ℂ) * I)‖ ≤
      E * (2 + |t|) ^ 3 * (1 + |v|) ^ 3 := by
    calc
      _ ≤ E * (2 + |v - t|) ^ 3 := hL
      _ ≤ E * ((2 + |t|) ^ 3 * (1 + |v|) ^ 3) :=
        mul_le_mul_of_nonneg_left hshift hE.le
      _ = _ := by ring
  change ‖Hline v * (N.value : ℂ) ^ ((-1 : ℂ) + (v : ℂ) * I) *
      DirichletCharacter.LFunction B.character
        (((-1 : ℂ) + (v : ℂ) * I - (t : ℂ) * I))‖ ≤ _
  have hNcast : (N.value : ℂ) = ((N.value : ℝ) : ℂ) := by norm_cast
  rw [norm_mul, norm_mul, hNcast,
    Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
  have hre : ((-1 : ℂ) + (v : ℂ) * I).re = (-1 : ℝ) := by simp
  rw [hre]
  calc
    ‖Hline v‖ * (N.value : ℝ) ^ (-1 : ℝ) *
        ‖DirichletCharacter.LFunction B.character
          (((-1 : ℂ) + (v : ℂ) * I - (t : ℂ) * I))‖ ≤
      ‖Hline v‖ * (N.value : ℝ) ^ (-1 : ℝ) *
        (E * (2 + |t|) ^ 3 * (1 + |v|) ^ 3) := by
          refine mul_le_mul_of_nonneg_left hL' ?_
          positivity
    _ = ((N.value : ℝ) ^ (-1 : ℝ) * E * (2 + |t|) ^ 3) *
        ((1 + |v|) ^ 3 * ‖Hline v‖) := by ring

/-- The initial right vertical edge in the nonprincipal CGL first shift is
absolutely integrable by the closed `Re(s)=2` Dirichlet-series bound. -/
theorem cglLemma62_nonprincipalContourIntegrand_right_integrable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) :
    Integrable (fun v : ℝ =>
      cglLemma62ContourIntegrand w N B t ((2 : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C, hC, hLbound⟩ := exists_bound_LFunction_of_two_le_re B.character
  let Hline : ℝ → ℂ := fun v =>
    cglLemma62MellinTransform w ((2 : ℂ) + (v : ℂ) * I)
  have hH : Integrable Hline := by
    change Integrable (fun v : ℝ =>
      cglLemma62MellinTransform w ((2 : ℂ) + (v : ℂ) * I))
    exact cglLemma62_mellinTransform_verticalIntegrable w 2
  have hNpos : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  have hHdiff : Differentiable ℂ (cglLemma62MellinTransform w) := fun s =>
    (cglLemma62_mellinTransform_analyticOnNhd w s (mem_univ s)).differentiableAt
  have hline : Continuous (fun v : ℝ => (2 : ℂ) + (v : ℂ) * I) := by fun_prop
  have hpow : Continuous (fun v : ℝ => (N.value : ℂ) ^
      ((2 : ℂ) + (v : ℂ) * I)) :=
    Continuous.const_cpow hline (Or.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.positive)))
  have hLcont : Continuous (DirichletCharacter.LFunction B.character) :=
    (DirichletCharacter.differentiable_LFunction B.nonprincipal).continuous
  have hLarg : Continuous (fun v : ℝ =>
      ((2 : ℂ) + (v : ℂ) * I) - (t : ℂ) * I) := by fun_prop
  have hmeas : AEStronglyMeasurable (fun v : ℝ =>
      cglLemma62ContourIntegrand w N B t ((2 : ℂ) + (v : ℂ) * I)) := by
    unfold cglLemma62ContourIntegrand
    exact ((hHdiff.continuous.comp hline).mul hpow).mul
      (hLcont.comp hLarg) |>.aestronglyMeasurable
  refine Integrable.mono' (hH.norm.const_mul ((N.value : ℝ) ^ (2 : ℝ) * C)) hmeas ?_
  filter_upwards with v
  have hL : ‖DirichletCharacter.LFunction B.character
      (((2 : ℂ) + (v : ℂ) * I) - (t : ℂ) * I)‖ ≤ C := by
    apply hLbound
    simp
  change ‖Hline v * (N.value : ℂ) ^ ((2 : ℂ) + (v : ℂ) * I) *
      DirichletCharacter.LFunction B.character
        (((2 : ℂ) + (v : ℂ) * I - (t : ℂ) * I))‖ ≤ _
  have hNcast : (N.value : ℂ) = ((N.value : ℝ) : ℂ) := by norm_cast
  rw [norm_mul, norm_mul, hNcast,
    Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
  have hre : ((2 : ℂ) + (v : ℂ) * I).re = (2 : ℝ) := by simp
  rw [hre]
  calc
    ‖Hline v‖ * (N.value : ℝ) ^ (2 : ℝ) *
        ‖DirichletCharacter.LFunction B.character
          (((2 : ℂ) + (v : ℂ) * I - (t : ℂ) * I))‖ ≤
      ‖Hline v‖ * (N.value : ℝ) ^ (2 : ℝ) * C := by
        refine mul_le_mul_of_nonneg_left hL ?_
        positivity
    _ = ((N.value : ℝ) ^ (2 : ℝ) * C) * ‖Hline v‖ := by ring

end RHTower
