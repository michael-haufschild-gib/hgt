import GaloisForLFunctions.HTGeometry.HypergeometricParameterHolomorphy
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSolutions

/-! Frequency holomorphy of the original BM Gauss factors across the physical QNM range. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem parameter_bounds (w chi u : ℂ) (hu : ‖u-w‖ < 1) :
    ‖gaussA u chi‖ ≤ 3*‖w‖+‖chi‖+10 ∧
    ‖gaussB u chi‖ ≤ 3*‖w‖+‖chi‖+10 ∧
    ‖gaussC u‖ ≤ 3*‖w‖+‖chi‖+10 ∧
    ‖gaussC u-gaussA u chi‖ ≤ 3*‖w‖+‖chi‖+10 ∧
    ‖gaussC u-gaussB u chi‖ ≤ 3*‖w‖+‖chi‖+10 := by
  have hu' : ‖u‖ ≤ ‖w‖+1 := by
    have h := norm_add_le (u-w) w
    rw [sub_add_cancel] at h
    linarith
  have ha : ‖gaussA u chi‖ ≤ 1/4+‖u‖/2+‖chi‖/2 := by
    unfold gaussA
    calc
      _ ≤ ‖(1/4:ℂ)+u/2‖+‖Complex.I*chi/2‖ := norm_add_le _ _
      _ ≤ ‖(1/4:ℂ)‖+‖u/2‖+‖Complex.I*chi/2‖ := add_le_add (norm_add_le _ _) (le_refl _)
      _ = _ := by norm_num [norm_div,norm_mul]
  have hb : ‖gaussB u chi‖ ≤ 1/4+‖u‖/2+‖chi‖/2 := by
    unfold gaussB
    calc
      _ ≤ ‖(1/4:ℂ)+u/2‖+‖Complex.I*chi/2‖ := norm_sub_le _ _
      _ ≤ ‖(1/4:ℂ)‖+‖u/2‖+‖Complex.I*chi/2‖ := add_le_add (norm_add_le _ _) (le_refl _)
      _ = _ := by norm_num [norm_div,norm_mul]
  have hc : ‖gaussC u‖ ≤ 1+‖u‖ := by simpa [gaussC] using norm_add_le (1:ℂ) u
  have hca := norm_sub_le (gaussC u) (gaussA u chi)
  have hcb := norm_sub_le (gaussC u) (gaussB u chi)
  have hw := norm_nonneg w
  have hchi := norm_nonneg chi
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Horizon Gauss series is holomorphic in independent frequency off the real axis;
no numerator nonvanishing condition excludes its terminating QNM specializations. -/
theorem horizonGauss_frequency_differentiableAt (w chi z : ℂ) (hw : w.im ≠ 0)
    (hz : ‖z‖ < 1) : DifferentiableAt ℂ (fun u => gaussFactor u chi false z) w := by
  let R : ℝ := min 1 (|w.im|/2)
  let B : ℝ := 3*‖w‖+‖chi‖+10
  have hδ : 0 < |w.im|/2 := div_pos (abs_pos.mpr hw) (by norm_num)
  have hR : 0 < R := lt_min (by norm_num) hδ
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound (u : ℂ) (hu : u ∈ Metric.ball w R) :
      ‖gaussA u chi‖ ≤ B ∧ ‖gaussB u chi‖ ≤ B ∧ ‖gaussC u‖ ≤ B := by
    have hn : ‖u-w‖ < 1 := by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hu).trans_le (min_le_left _ _)
    obtain ⟨ha,hb,hc,-⟩ := parameter_bounds w chi u hn
    exact ⟨ha,hb,hc⟩
  have hsep (u : ℂ) (hu : u ∈ Metric.ball w R) (j : ℕ) : |w.im|/2 ≤ ‖gaussC u+j‖ := by
    have hn : ‖u-w‖ < |w.im|/2 := by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hu).trans_le (min_le_right _ _)
    have hi : |u.im-w.im| < |w.im|/2 := (Complex.abs_im_le_norm (u-w)).trans_lt hn
    have ht := abs_sub_abs_le_abs_sub w.im u.im
    rw [abs_sub_comm w.im u.im] at ht
    have hn' := Complex.abs_im_le_norm (gaussC u+j)
    simp only [gaussC,Complex.add_im,Complex.one_im,Complex.natCast_im,zero_add,add_zero] at hn'
    change |w.im|/2 ≤ ‖1+u+j‖
    linarith
  have hf := hypergeometric_family_differentiableAt (fun u => gaussA u chi)
    (fun u => gaussB u chi) gaussC w z R B (|w.im|/2) hR hB hδ
    (by intros; unfold gaussA; fun_prop) (by intros; unfold gaussB; fun_prop)
    (by intros; unfold gaussC; fun_prop) hbound hsep hz
  simpa only [gaussFactor,radialSeries,Bool.false_eq_true,↓reduceIte,horizonSeries,
    ordinaryHypergeometric] using hf

/-- The original normalizable Gauss series is entire in independent frequency,
including the terminating QNM parameters. -/
theorem outerGauss_frequency_differentiableAt (w chi z : ℂ) (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun u => gaussFactor u chi true z) w := by
  let B : ℝ := 3*‖w‖+‖chi‖+10
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound (u : ℂ) (hu : u ∈ Metric.ball w 1) :
      ‖gaussC u-gaussA u chi‖ ≤ B ∧ ‖gaussC u-gaussB u chi‖ ≤ B ∧ ‖(3/2:ℂ)‖ ≤ B := by
    obtain ⟨-,-,-,ha,hb⟩ := parameter_bounds w chi u (by simpa only [dist_eq_norm] using Metric.mem_ball.mp hu)
    refine ⟨ha,hb,?_⟩
    norm_num [B,norm_div]
    have hw := norm_nonneg w
    have hchi := norm_nonneg chi
    linarith
  have hsep (u : ℂ) (_hu : u ∈ Metric.ball w 1) (j : ℕ) : (1:ℝ) ≤ ‖(3/2:ℂ)+j‖ := by
    have h := Complex.re_le_norm ((3/2:ℂ)+j)
    norm_num at h
    have hn : (0:ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hf := hypergeometric_family_differentiableAt (fun u => gaussC u-gaussA u chi)
    (fun u => gaussC u-gaussB u chi) (fun _ => (3/2:ℂ)) w z 1 B 1
    (by norm_num) hB (by norm_num)
    (by intros; unfold gaussC gaussA; fun_prop) (by intros; unfold gaussC gaussB; fun_prop)
    (by intros; fun_prop) hbound hsep hz
  simpa only [gaussFactor,radialSeries,↓reduceIte,outerSeries,ordinaryHypergeometric] using hf

end
end RHTower.D4BMLaplaceRadial
