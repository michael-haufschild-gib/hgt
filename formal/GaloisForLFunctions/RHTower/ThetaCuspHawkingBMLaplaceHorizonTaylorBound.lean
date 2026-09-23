import GaloisForLFunctions.HTGeometry.HypergeometricTaylorEndpointBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceHorizonGaussBound

/-! The original horizon mode's exact first coefficient and uniform quadratic frequency-family remainder. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Quantitative parameter separation on an actual nonreal frequency neighborhood. -/
theorem horizonGauss_parameter_neighborhood (w chi : ℂ) (hw : w.im ≠ 0) :
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

/-- The literal linear Taylor coefficient of the horizon Gauss series. -/
def horizonGaussFirstCoefficient (w chi : ℂ) : ℂ :=
  ordinaryHypergeometricCoefficient (gaussA w chi) (gaussB w chi) (gaussC w) 1

theorem horizonGaussFirstCoefficient_eq (w chi : ℂ) :
    horizonGaussFirstCoefficient w chi=gaussA w chi*gaussB w chi/gaussC w := by
  simp [horizonGaussFirstCoefficient,ordinaryHypergeometricCoefficient,ascPochhammer_one,div_eq_mul_inv]

/-- Its parameter dependence is analytic through the physical connection zeros. -/
theorem horizonGaussFirstCoefficient_analyticAt (w chi : ℂ) (hw : w.im ≠ 0) :
    AnalyticAt ℂ (fun u => horizonGaussFirstCoefficient u chi) w := by
  have hc : gaussC w ≠ 0 := by
    intro h; apply hw
    have hi := congrArg Complex.im h
    simpa only [gaussC,Complex.add_im,Complex.one_im,zero_add,Complex.zero_im] using hi
  simp_rw [horizonGaussFirstCoefficient_eq]
  exact ((show AnalyticAt ℂ (fun u => gaussA u chi) w by unfold gaussA; fun_prop).mul
    (show AnalyticAt ℂ (fun u => gaussB u chi) w by unfold gaussB; fun_prop)).div
      (show AnalyticAt ℂ gaussC w by unfold gaussC; fun_prop) hc

/-- A common frequency neighborhood bounds the actual linear coefficient and the full quadratic remainder. -/
theorem horizonGauss_uniform_second_bound (w chi : ℂ) (hw : w.im ≠ 0)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∃ R C L : ℝ, 0 < R ∧ 0 ≤ C ∧ 0 ≤ L ∧
      ∀ u ∈ ball w R, ‖horizonGaussFirstCoefficient u chi‖ ≤ L ∧
        ∀ z ∈ Icc (0:ℝ) b,
          ‖gaussFactor u chi false (z:ℂ)-1-horizonGaussFirstCoefficient u chi*(z:ℂ)‖ ≤ C*z^(2 : ℕ) := by
  obtain ⟨R,B,δ,hR,_,hB,hδ,hp⟩ := horizonGauss_parameter_neighborhood w chi hw
  obtain ⟨N,hN⟩ := exists_nat_ge (B+1)
  have hsep (u : ℂ) (hu : u ∈ ball w R) (j : ℕ) : δ ≤ ‖gaussC u+j‖ := by
    have hh := Complex.abs_im_le_norm (gaussC u+j)
    simp only [gaussC,Complex.add_im,Complex.one_im,Complex.natCast_im,zero_add,add_zero] at hh
    exact (hp u hu).2.2.2.trans hh
  have hcoef (u : ℂ) (hu : u ∈ ball w R) := gaussParameterMajorant_bound hB hδ
    (hp u hu).1 (hp u hu).2.1 (hp u hu).2.2.1 (hsep u hu) N hN
  have hnonneg (n : ℕ) : 0 ≤ gaussParameterMajorant B δ N n :=
    (norm_nonneg _).trans (hcoef w (mem_ball_self hR) n)
  let C := ∑' n, gaussParameterMajorant B δ N (n+2)*b^n
  have hC : 0 ≤ C := tsum_nonneg (fun n => mul_nonneg (hnonneg _) (pow_nonneg hb.le _))
  refine ⟨R,C,gaussParameterMajorant B δ N 1,hR,hC,hnonneg 1,?_⟩
  intro u hu
  refine ⟨hcoef u hu 1,?_⟩
  intro z hz
  have hn : ‖(z:ℂ)‖ ≤ b := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz.1] using hz.2
  have hh := hypergeometric_second_endpoint_bound hB hδ hb hb1 (hp u hu).1 (hp u hu).2.1
    (hp u hu).2.2.1 (hsep u hu) N hN hn
  simpa only [ordinaryHypergeometric,gaussFactor,radialSeries,Bool.false_eq_true,↓reduceIte,horizonSeries,
    horizonGaussFirstCoefficient,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz.1] using hh

/-- At either original fundamental connection root the derived first coefficient is exactly minus one half. -/
theorem horizonGaussFirstCoefficient_fundamental (w chi : ℂ) (hw : w.im ≠ 0)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) :
    horizonGaussFirstCoefficient w chi=-(1/2:ℂ) := by
  have hc : gaussC w ≠ 0 := by
    intro h; apply hw
    have hi := congrArg Complex.im h
    simpa only [gaussC,Complex.add_im,Complex.one_im,zero_add,Complex.zero_im] using hi
  rw [horizonGaussFirstCoefficient_eq]
  apply (div_eq_iff hc).mpr
  rcases hf with rfl|rfl <;> dsimp [gaussA,gaussB,gaussC] <;> ring

end
end RHTower.D4BMLaplaceRadial
