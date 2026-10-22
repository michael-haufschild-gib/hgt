import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailStripEuler
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailStripDirichlet

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

structure CGLLemma62TailHorizontalPoint (d : CGLLemma62TailContourDepth) (t : ℝ) where
  x : ℝ
  y : ℝ
  lower : -2 * (d.value : ℝ) ≤ x
  upper : x ≤ -1
  y_large : 1 ≤ |y|
  shifted_large : 2 ≤ |y - t|

private theorem cgl_tail_shifted_one_add_abs_pow_le (t y : ℝ) (n : ℕ) :
    (1 + |y - t|) ^ n ≤ (1 + |t|) ^ n * (1 + |y|) ^ n :=
  cglLemma62_finite_shifted_one_add_absPow_le t y n

private theorem cgl_tail_one_add_abs_pow_le (y : ℝ) (n : ℕ) (hy : 1≤|y|) :
    (1+|y|)^n ≤ 2^n*|y|^n := by
  have hbase : 1+|y| ≤ 2*|y| := by linarith
  calc (1+|y|)^n ≤ (2*|y|)^n := pow_le_pow_left₀ (by positivity) hbase n
       _ = _ := mul_pow _ _ n

theorem cglLemma62_tailContour_horizontal_point_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : CGLLemma62TailHorizontalPoint d t,
      ‖cglLemma62TailContourIntegrand w N B t M.value
        ((p.x : ℂ) + (p.y : ℂ) * I)‖ ≤ C / |p.y|^(2 : ℕ) := by
  rcases cglLemma62_primitiveFunctionalFactor_tail_strip_high_bound B.primitive d with
    ⟨A,hA,hA_bound⟩
  let K := cglLemma62TailMellinUniformBudget w d (2*d.value+3)
  let E := cglLemma62TailEulerCorrectionBudget B d
  let D : ℝ := (M.value : ℝ)^(-(1:ℝ))
  let C : ℝ := K*A*E*D*(1+|t|)^(2*d.value+1)*2^(2*d.value+1)
  let z0 : CGLLemma62TailEulerStripPoint d := ⟨(-1:ℂ), by
    simp
    have hd : (1:ℝ) ≤ d.value := by exact_mod_cast d.positive
    linarith, by simp⟩
  have hE0 := cglLemma62EulerCorrectionAt_tail_strip_norm_le B d z0
  have hE : 0≤E := le_trans (norm_nonneg _) hE0
  have hK : 0≤K := by
    dsimp [K,cglLemma62TailMellinUniformBudget]
    apply integral_nonneg
    intro u
    unfold deningerMeyerBoundedMellinMajorant
    apply Finset.sum_nonneg
    intro k hk
    positivity
  have hD : 0≤D := by
    dsimp [D]
    have hMone : (1 : ℝ) ≤ M.value := by exact_mod_cast M.one_le
    have hM : (0 : ℝ) ≤ M.value := by linarith
    exact Real.rpow_nonneg hM _
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro p
  let s : ℂ := (p.x : ℂ) + (p.y : ℂ)*I
  let mp : CGLLemma62TailMellinPoint d := ⟨p.x,p.y,p.lower,p.upper⟩
  let fp : CGLLemma62TailFunctionalStripHighPoint d := {
    value := s-(t:ℂ)*I
    lower := by dsimp [s]; simp; linarith [p.lower]
    upper := by dsimp [s]; simp; exact p.upper
    high := by dsimp [s]; simp; exact p.shifted_large }
  let ep : CGLLemma62TailEulerStripPoint d := {
    value := s-(t:ℂ)*I
    lower := by dsimp [s]; simp; linarith [p.lower]
    upper := by dsimp [s]; simp; exact p.upper }
  let rp : CGLLemma62TailRightStripPoint := ⟨1-s+(t:ℂ)*I, by
    dsimp [s]; simp; linarith [p.upper]⟩
  have hypos : 0 < |p.y| := lt_of_lt_of_le zero_lt_one p.y_large
  have hkernel0 := cglLemma62_mellinTransform_tail_uniformAllOrderDecay w d (2*d.value+3) mp
  have hkernel : ‖cglLemma62MellinTransform w s‖ ≤ K / |p.y|^(2*d.value+3) := by
    apply (le_div_iff₀ (pow_pos hypos _)).mpr
    simpa [K,s,mp,mul_comm] using hkernel0
  have hN0 := cglLemma62_lengthPower_tail_norm_le_one N d mp
  have hN : ‖(N.value:ℂ)^s‖ ≤ 1 := by simpa [s,mp] using hN0
  have hP0 := hA_bound fp
  have hP : ‖cglLemma62PrimitiveFunctionalFactor B.primitive (s-(t:ℂ)*I)‖ ≤
      A*(1+|t|)^(2*d.value+1)*(1+|p.y|)^(2*d.value+1) := by
    calc
      _ = ‖cglLemma62PrimitiveFunctionalFactor B.primitive fp.value‖ := by rfl
      _ ≤ A*(1+|fp.value.im|)^(2*d.value+1) := hP0
      _ = A*(1+|p.y-t|)^(2*d.value+1) := by
        congr 2
        dsimp [fp,s]
        simp
      _ ≤ A*((1+|t|)^(2*d.value+1)*(1+|p.y|)^(2*d.value+1)) := by
        gcongr
        exact cgl_tail_shifted_one_add_abs_pow_le t p.y _
      _ = _ := by ring
  have hE0 := cglLemma62EulerCorrectionAt_tail_strip_norm_le B d ep
  have hEcorr : ‖cglLemma62EulerCorrectionAt B (s-(t:ℂ)*I)‖ ≤ E := by simpa [E,ep] using hE0
  have hD0 := cglLemma62_tail_dirichletTail_norm_le B M rp
  have htail : ‖cglLemma62DirichletTail B.character⁻¹ M.value
      ⟨1-s+(t:ℂ)*I, by dsimp [s]; simp; linarith [p.upper]⟩‖ ≤ D := by
    simpa [D,rp] using hD0
  have htail_eq := cglLemma62_lfunction_sub_head_eq_tail B M.value
    (⟨1-s+(t:ℂ)*I, by dsimp [s]; simp; linarith [p.upper]⟩ : CGLAbsoluteConvergencePoint)
  have htail_contour : ‖DirichletCharacter.LFunction B.character⁻¹ (1-s+(t:ℂ)*I) -
      cglLemma62DirichletHead B.character⁻¹ M.value (1-s+(t:ℂ)*I)‖ ≤ D := by
    rw [htail_eq]
    exact htail
  have hpoly := cgl_tail_one_add_abs_pow_le p.y (2*d.value+1) p.y_large
  change ‖cglLemma62TailContourIntegrand w N B t M.value s‖ ≤ C/|p.y|^(2 : ℕ)
  unfold cglLemma62TailContourIntegrand
  rw [norm_mul,norm_mul,norm_mul,norm_mul]
  calc
    ‖cglLemma62MellinTransform w s‖ * ‖(N.value:ℂ)^s‖ *
        ‖cglLemma62PrimitiveFunctionalFactor B.primitive (s-↑t*I)‖ *
        ‖cglLemma62EulerCorrectionAt B (s-↑t*I)‖ *
        ‖DirichletCharacter.LFunction B.character⁻¹ (1-s+↑t*I) -
          cglLemma62DirichletHead B.character⁻¹ M.value (1-s+↑t*I)‖ ≤
      (K/|p.y|^(2*d.value+3))*1*
        (A*(1+|t|)^(2*d.value+1)*(1+|p.y|)^(2*d.value+1))*E*D := by
          gcongr
    _ ≤ (K/|p.y|^(2*d.value+3))*1*
        (A*(1+|t|)^(2*d.value+1)*(2^(2*d.value+1)*|p.y|^(2*d.value+1)))*E*D := by gcongr
    _ = C/|p.y|^(2 : ℕ) := by
      dsimp [C]
      field_simp [ne_of_gt hypos]
      calc
        K * A * |p.y| ^ (2 * d.value + 1) * E * D * |p.y| ^ 2 =
            K * (|p.y| ^ (2 * d.value + 1) * |p.y| ^ 2) * A * E * D := by ring
        _ = K * |p.y| ^ ((2 * d.value + 1) + 2) * A * E * D := by rw [← pow_add]
        _ = K * |p.y| ^ (2 * d.value + 3) * A * E * D := by
          congr 3

/-- The upper horizontal side of CGL's tail rectangle vanishes. -/
theorem cglLemma62_tailContour_horizontal_top
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) :
    Tendsto (fun y : ℝ =>
      ∫ x in (-2 * (d.value : ℝ))..(-1 : ℝ),
        cglLemma62TailContourIntegrand w N B t M.value ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) := by
  rcases cglLemma62_tailContour_horizontal_point_bound w N B t M d with ⟨C,hC,hpoint⟩
  have hdecay : Tendsto (fun y : ℝ => C / y^(2 : ℕ)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun y : ℝ => y ^ (-(2:ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have hscaled : Tendsto (fun y : ℝ => C*y^(-(2:ℝ))) atTop (𝓝 0) := by
      simpa using hpow.const_mul C
    refine Filter.Tendsto.congr' ?_ hscaled
    filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    rw [Real.rpow_neg hy, Real.rpow_two, div_eq_mul_inv]
  apply GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
    (M := fun y : ℝ => C/y^(2 : ℕ)) (hgt := fun y : ℝ => y)
  · filter_upwards [eventually_ge_atTop (|t|+2)] with y hy x hx
    have hleft : -2*(d.value:ℝ) ≤ (-1:ℝ) := by
      have hd : (1:ℝ) ≤ d.value := by exact_mod_cast d.positive
      linarith
    have hx' : x ∈ Icc (-2*(d.value:ℝ)) (-1:ℝ) := by
      have := uIoc_subset_uIcc hx
      rw [uIcc_of_le hleft] at this
      exact this
    have hyabs : 1 ≤ |y| := by
      rw [abs_of_nonneg (by linarith [abs_nonneg t] : 0≤y)]
      linarith [abs_nonneg t]
    have hyt : 2 ≤ |y-t| := by
      calc 2 ≤ y-|t| := by linarith
           _ ≤ y-t := sub_le_sub_left (le_abs_self t) y
           _ ≤ |y-t| := le_abs_self _
    let p : CGLLemma62TailHorizontalPoint d t := ⟨x,y,hx'.1,hx'.2,hyabs,hyt⟩
    have h := hpoint p
    simpa [p,abs_of_nonneg (by linarith [abs_nonneg t] : 0≤y)] using h
  · exact hdecay

/-- The lower horizontal side of CGL's tail rectangle vanishes. -/
theorem cglLemma62_tailContour_horizontal_bottom
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) :
    Tendsto (fun y : ℝ =>
      ∫ x in (-2 * (d.value : ℝ))..(-1 : ℝ),
        cglLemma62TailContourIntegrand w N B t M.value ((x : ℂ) + (y : ℂ) * I))
      atBot (𝓝 0) := by
  rcases cglLemma62_tailContour_horizontal_point_bound w N B t M d with ⟨C,hC,hpoint⟩
  have hdecay : Tendsto (fun y : ℝ => C/y^(2 : ℕ)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun y : ℝ => y ^ (-(2:ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have hscaled : Tendsto (fun y : ℝ => C*y^(-(2:ℝ))) atTop (𝓝 0) := by
      simpa using hpow.const_mul C
    refine Filter.Tendsto.congr' ?_ hscaled
    filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    rw [Real.rpow_neg hy, Real.rpow_two, div_eq_mul_inv]
  have hneg : Tendsto (fun y : ℝ =>
      ∫ x in (-2 * (d.value : ℝ))..(-1 : ℝ),
        cglLemma62TailContourIntegrand w N B t M.value ((x : ℂ) + ((-y:ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
    apply GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (M := fun y : ℝ => C/y^(2 : ℕ)) (hgt := fun y : ℝ => -y)
    · filter_upwards [eventually_ge_atTop (|t|+2)] with y hy x hx
      have hleft : -2*(d.value:ℝ) ≤ (-1:ℝ) := by
        have hd : (1:ℝ) ≤ d.value := by exact_mod_cast d.positive
        linarith
      have hx' : x ∈ Icc (-2*(d.value:ℝ)) (-1:ℝ) := by
        have := uIoc_subset_uIcc hx
        rw [uIcc_of_le hleft] at this
        exact this
      have hyabs : 1 ≤ |-y| := by
        rw [abs_neg,abs_of_nonneg (by linarith [abs_nonneg t] : 0≤y)]
        linarith [abs_nonneg t]
      have hyt : 2 ≤ |-y-t| := by
        rw [show -y-t = -(y+t) by ring,abs_neg]
        calc 2 ≤ y-|t| := by linarith
             _ ≤ y+t := by linarith [neg_abs_le t]
             _ ≤ |y+t| := le_abs_self _
      let p : CGLLemma62TailHorizontalPoint d t := ⟨x,-y,hx'.1,hx'.2,hyabs,hyt⟩
      have h := hpoint p
      simpa [p,abs_neg,abs_of_nonneg (by linarith [abs_nonneg t] : 0≤y)] using h
    · exact hdecay
  refine Filter.Tendsto.congr' ?_ (hneg.comp tendsto_neg_atBot_atTop)
  filter_upwards with y
  simp only [Function.comp_apply, neg_neg]

end

end RHTower
