import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceHorizonEndpointBounds

/-! A common nonvanishing horizon neighborhood for the actual Gauss factor. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem gauss_parameter_neighborhood (w chi : ℂ) (hw : w.im ≠ 0) :
    ∃ R B δ : ℝ, 0 < R ∧ R ≤ 1 ∧ 0 < B ∧ 0 < δ ∧
      ∀ u ∈ ball w R, ‖gaussA u chi‖ ≤ B ∧ ‖gaussB u chi‖ ≤ B ∧ ‖gaussC u‖ ≤ B ∧ δ ≤ |u.im| := by
  let B := ‖gaussA w chi‖+‖gaussB w chi‖+‖gaussC w‖+1
  let δ := |w.im|/2
  have hδ : 0 < δ := div_pos (abs_pos.mpr hw) (by norm_num)
  have hA : ∀ᶠ u in 𝓝 w, ‖gaussA u chi‖ < B :=
    (show ContinuousAt (fun u => ‖gaussA u chi‖) w by unfold gaussA; fun_prop).eventually_lt
      continuousAt_const (by dsimp [B]; linarith [norm_nonneg (gaussB w chi),norm_nonneg (gaussC w)])
  have hB : ∀ᶠ u in 𝓝 w, ‖gaussB u chi‖ < B :=
    (show ContinuousAt (fun u => ‖gaussB u chi‖) w by unfold gaussB; fun_prop).eventually_lt
      continuousAt_const (by dsimp [B]; linarith [norm_nonneg (gaussA w chi),norm_nonneg (gaussC w)])
  have hC : ∀ᶠ u in 𝓝 w, ‖gaussC u‖ < B :=
    (show ContinuousAt (fun u => ‖gaussC u‖) w by unfold gaussC; fun_prop).eventually_lt
      continuousAt_const (by dsimp [B]; linarith [norm_nonneg (gaussA w chi),norm_nonneg (gaussB w chi)])
  have hi : ∀ᶠ u : ℂ in 𝓝 w, δ < |u.im| := continuousAt_const.eventually_lt
    (by fun_prop) (by dsimp [δ]; linarith [abs_pos.mpr hw])
  obtain ⟨R,hR,hall⟩ := Metric.eventually_nhds_iff.mp (hA.and (hB.and (hC.and hi)))
  refine ⟨min R 1,B,δ,lt_min hR (by norm_num),min_le_right _ _,by dsimp [B]; positivity,hδ,?_⟩
  intro u hu
  obtain ⟨ha,hb,hc,hd⟩ := hall ((mem_ball.mp hu).trans_le (min_le_left _ _))
  exact ⟨ha.le,hb.le,hc.le,hd.le⟩

/-- The original Gauss factor has one linear endpoint bound for a whole frequency neighborhood. -/
theorem horizonGauss_uniform_first_bound (w chi : ℂ) (hw : w.im ≠ 0)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ u ∈ ball w R, ∀ z ∈ Icc (0:ℝ) b,
      ‖gaussFactor u chi false (z:ℂ)-1‖ ≤ C*z := by
  obtain ⟨R,B,δ,hR,_,hB,hδ,hp⟩ := gauss_parameter_neighborhood w chi hw
  obtain ⟨N,hN⟩ := exists_nat_ge (B+1)
  have hsep (u : ℂ) (hu : u ∈ ball w R) (j : ℕ) : δ ≤ ‖gaussC u+j‖ := by
    have hh := Complex.abs_im_le_norm (gaussC u+j)
    simp only [gaussC,Complex.add_im,Complex.one_im,Complex.natCast_im,zero_add,add_zero] at hh
    exact (hp u hu).2.2.2.trans hh
  let C := ∑' n, gaussParameterMajorant B δ N (n+1)*b^n
  have hC : 0 ≤ C := by
    apply tsum_nonneg
    intro n
    exact mul_nonneg ((norm_nonneg _).trans (gaussParameterMajorant_bound hB hδ
      (hp w (mem_ball_self hR)).1 (hp w (mem_ball_self hR)).2.1
      (hp w (mem_ball_self hR)).2.2.1 (hsep w (mem_ball_self hR)) N hN (n+1))) (pow_nonneg hb.le _)
  refine ⟨R,C,hR,hC,?_⟩
  intro u hu z hz
  have hn : ‖(z:ℂ)‖ ≤ b := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz.1] using hz.2
  have hh := hypergeometric_sub_one_bound hB hδ hb hb1 (hp u hu).1 (hp u hu).2.1
    (hp u hu).2.2.1 (hsep u hu) N hN hn
  simpa only [ordinaryHypergeometric,gaussFactor,radialSeries,Bool.false_eq_true,↓reduceIte,horizonSeries,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz.1] using hh

/-- One actual horizon neighborhood has a uniform inverse bound, without an assumed nonvanishing mode. -/
theorem horizonGauss_uniform_nonzero (w chi : ℂ) (hw : w.im ≠ 0) :
    ∃ R b C : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1/2 ∧ 0 ≤ C ∧
      ∀ u ∈ ball w R, ∀ z ∈ Icc (0:ℝ) b,
        ‖gaussFactor u chi false (z:ℂ)-1‖ ≤ C*z ∧
        1/2 ≤ ‖gaussFactor u chi false (z:ℂ)‖ ∧
        ‖gaussFactor u chi false (z:ℂ)‖ ≤ 3/2 := by
  obtain ⟨R,C,hR,hC,hbound⟩ := horizonGauss_uniform_first_bound w chi hw
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  let b := min (1/2:ℝ) (1/(2*(C+1)))
  have hb : 0 < b := lt_min (by norm_num) (by positivity)
  have hbhalf : b ≤ 1/2 := min_le_left _ _
  have hCb : C*b ≤ 1/2 := by
    have hb' : b ≤ 1/(2*(C+1)) := min_le_right _ _
    have hm := (le_div_iff₀ (by positivity : 0 < 2*(C+1))).mp hb'
    nlinarith
  refine ⟨R,b,C,hR,hb,hbhalf,hC,?_⟩
  intro u hu z hz
  have he := hbound u hu z ⟨hz.1,hz.2.trans hbhalf⟩
  have hh : ‖gaussFactor u chi false (z:ℂ)-1‖ ≤ 1/2 :=
    he.trans ((mul_le_mul_of_nonneg_left hz.2 hC).trans hCb)
  have hlo := norm_sub_norm_le (1:ℂ) (gaussFactor u chi false (z:ℂ))
  have hup := norm_sub_norm_le (gaussFactor u chi false (z:ℂ)) (1:ℂ)
  rw [norm_one,norm_sub_rev] at hlo
  rw [norm_one] at hup
  exact ⟨he,by linarith,by linarith⟩

end
end RHTower.D4BMLaplaceRadial
