import GaloisForLFunctions.HTGeometry.HypergeometricEndpointBounds
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceSourceEndpoint

/-! Uniform outer-endpoint bounds for the original Gauss branch and literal source. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The original outer Gauss sum is uniformly bounded on a closed smaller radial disk
and a frequency ball, without a chamber or nontermination assumption. -/
theorem outerGauss_uniform_bound (w chi : ℂ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ ball w 1, ∀ z : ℂ, ‖z‖ ≤ r → ‖gaussFactor u chi true z‖ ≤ C := by
  obtain ⟨A,hA⟩ := (isCompact_closedBall w 1).exists_bound_of_continuousOn
    (show Continuous (fun u => gaussC u-gaussA u chi) by unfold gaussC gaussA; fun_prop).continuousOn
  obtain ⟨D,hD⟩ := (isCompact_closedBall w 1).exists_bound_of_continuousOn
    (show Continuous (fun u => gaussC u-gaussB u chi) by unfold gaussC gaussB; fun_prop).continuousOn
  let B := max A 0+max D 0+2
  have hB : 0 < B := by dsimp [B]; positivity
  have ha (u : ℂ) (hu : u ∈ ball w 1) : ‖gaussC u-gaussA u chi‖ ≤ B := by
    have hh := hA u (ball_subset_closedBall hu)
    dsimp [B]
    linarith [le_max_left A 0,le_max_right D 0]
  have hb (u : ℂ) (hu : u ∈ ball w 1) : ‖gaussC u-gaussB u chi‖ ≤ B := by
    have hh := hD u (ball_subset_closedBall hu)
    dsimp [B]
    linarith [le_max_left D 0,le_max_right A 0]
  have hc : ‖(3/2:ℂ)‖ ≤ B := by
    norm_num [norm_div,B]
    linarith [le_max_right A 0,le_max_right D 0]
  have hsep (j : ℕ) : (1:ℝ) ≤ ‖(3/2:ℂ)+j‖ := by
    have hh := Complex.re_le_norm ((3/2:ℂ)+j)
    norm_num at hh
    linarith [Nat.cast_nonneg j (α := ℝ)]
  obtain ⟨N,hN⟩ := exists_nat_ge (B+1)
  let Cg := max (∑' n, gaussParameterMajorant B 1 N (n+1)*r^n) 0
  have hCg : 0 ≤ Cg := le_max_right _ _
  refine ⟨1+Cg*r,by positivity,?_⟩
  intro u hu z hz
  have hh := hypergeometric_sub_one_bound hB (by norm_num : (0:ℝ)<1) hr hr1 (ha u hu) (hb u hu) hc hsep N hN hz
  have hsub : ‖gaussFactor u chi true z-1‖ ≤ Cg*r := by
    have he : ‖gaussFactor u chi true z-1‖ ≤ (∑' n, gaussParameterMajorant B 1 N (n+1)*r^n)*‖z‖ := by
      simpa only [gaussFactor,radialSeries,↓reduceIte,outerSeries,ordinaryHypergeometric] using hh
    exact he.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg z)).trans
      (mul_le_mul_of_nonneg_left hz hCg))
  have ht := norm_add_le (gaussFactor u chi true z-1) (1:ℂ)
  rw [sub_add_cancel,norm_one] at ht
  linarith

/-- Uniform control extends to the true outer endpoint for the original source-weighted solution. -/
theorem outerSource_uniform_bound (s chi a J K w : ℂ) {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ ball w 1, ∀ t ∈ Icc b (1:ℝ),
      ‖normalizable u chi t*sourceProfile s u a J K 1 t‖ ≤ C := by
  let P (p : ℂ × ℝ) : ℂ := power (p.1/2) p.2*power (1/2) (1-p.2)*power (p.1/2) p.2*
    sourceRemainder s p.1 a J K 1 p.2
  have hp : ContinuousOn (fun p : ℂ × ℝ => power (p.1/2) p.2) (closedBall w 1 ×ˢ Icc b (1:ℝ)) := by
    intro p hp
    have ht : 0 < p.2 := hb.trans_le hp.2.1
    have hh := (Complex.continuousAt_ofReal_cpow p.2 (p.1/2) (Or.inr (ne_of_gt ht))).comp_of_eq
      (show ContinuousAt (fun q : ℂ × ℝ => (q.2,q.1/2)) p by fun_prop) rfl
    exact hh.continuousWithinAt
  have houter : Continuous (fun p : ℂ × ℝ => power (1/2) (1-p.2)) := by
    exact (Complex.continuous_ofReal_cpow_const (y := (1/2:ℂ)) (by norm_num)).comp
      (show Continuous (fun p : ℂ × ℝ => 1-p.2) by fun_prop)
  have hP : ContinuousOn P (closedBall w 1 ×ˢ Icc b (1:ℝ)) :=
    ((hp.mul houter.continuousOn).mul hp).mul (sourceRemainder_joint_continuous s a J K 1).continuousOn
  obtain ⟨A,hA⟩ := ((isCompact_closedBall w 1).prod isCompact_Icc).exists_bound_of_continuousOn hP
  obtain ⟨Cg,hCg,hg⟩ := outerGauss_uniform_bound w chi (by linarith : 0 < 1-b) (by linarith : 1-b < 1)
  refine ⟨max A 0*Cg,mul_nonneg (le_max_right _ _) hCg,?_⟩
  intro u hu t ht
  have he : normalizable u chi t*sourceProfile s u a J K 1 t = P (u,t)*gaussFactor u chi true (1-t) := by
    unfold normalizable dress outerFactor sourceProfile P
    ring
  rw [he,norm_mul]
  have hn : ‖(1-(t:ℂ))‖ ≤ 1-b := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by linarith [ht.2])]
    linarith [ht.1]
  exact mul_le_mul ((hA (u,t) ⟨ball_subset_closedBall hu,ht⟩).trans (le_max_left _ _))
    (hg u hu _ hn) (norm_nonneg _) (le_max_right _ _)

end
end RHTower.D4BMLaplaceRadial
