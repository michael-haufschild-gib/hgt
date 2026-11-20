import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline

/-! # Time occupation below half a robust maximum gate count -/
open Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- A measurable set of times with a forbidden positive difference fits twice,
together with its translate, in an interval lengthened by that difference. -/
private theorem twice_occupation_le_of_forbidden_difference (A : Set ℝ) (hA : MeasurableSet A)
    (u : ℝ) (hu : 0 ≤ u) (hsep : ∀ x ∈ A, x+u ∉ A) (a T : ℝ) (hT : 0 ≤ T) :
    2*volume.real (A ∩ Icc a (a+T)) ≤ T+u := by
  let F := A ∩ Icc a (a+T)
  let G := (fun t : ℝ => t+(-u)) ⁻¹' F
  have hm : MeasurableSet F := hA.inter measurableSet_Icc
  have hG : volume G = volume F :=
    (measurePreserving_add_right volume (-u)).measure_preimage hm.nullMeasurableSet
  have hGF : volume.real G = volume.real F := congrArg ENNReal.toReal hG
  have hfin : volume F ≠ ⊤ := measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hd : Disjoint F G := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have h := hsep (x+-u) hy.1
    apply h
    rw [show x+-u+u=x by ring]
    exact hx.1
  have hsub : F ∪ G ⊆ Icc a (a+T+u) := by
    rintro x (hx|hx)
    · exact ⟨hx.2.1,by linarith only [hx.2.2,hu]⟩
    · have hb : x+-u ∈ Icc a (a+T) := hx.2
      exact ⟨by linarith only [hb.1,hu],by linarith only [hb.2]⟩
  have hbound := measureReal_mono hsub measure_Icc_lt_top.ne
  rw [measureReal_union' hd hm hfin (hG.trans_ne hfin),hGF,
    Real.volume_real_Icc_of_le (by linarith only [hT,hu])] at hbound
  change 2*volume.real F ≤ T+u
  linarith only [hbound]

/-- A time u beyond the entire 2s-gate tube at error 1/10 forbids a pair of
s-gate approximations at error 1/20 separated by u. This bounds occupation
uniformly on every observation window, without a distributional assumption. -/
theorem affordable_time_le_half_of_hard_lag {n s : ℕ} (H : selfAdjoint (Reg n))
    (u : ℝ) (hu : 0 ≤ u) (hh : ProjectiveCircuitSeparated n (1/10:ℝ) (2*s)
      (unitaryEvolution H.val u)) (a T : ℝ) (hT : 0 ≤ T) :
    2*volume.real ({t | HasProjectiveCircuitApproximation n (1/20:ℝ) s
      (unitaryEvolution H.val t)} ∩ Icc a (a+T)) ≤ T+u := by
  let A := {t | HasProjectiveCircuitApproximation n (1/20:ℝ) s (unitaryEvolution H.val t)}
  have hm : MeasurableSet A := by
    have hL : LipschitzWith ⟨‖H.val‖,norm_nonneg _⟩ (unitaryEvolution H.val) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm,Real.dist_eq]
      exact norm_unitaryEvolution_time_sub_le H.2 x y
    dsimp only [A]
    simp only [hasProjectiveCircuitApproximation_iff_infDist]
    exact (isClosed_compactTargetCaptureTimeSet _ hL.continuous _ _).measurableSet
  refine twice_occupation_le_of_forbidden_difference A hm u hu ?_ a T hT
  intro x hx hy
  have hx' : HasProjectiveCircuitApproximation n (1/20:ℝ) s (unitaryEvolution H.val x) := hx
  have h := projectiveCircuitSeparated_unitaryEvolution_backward_cone H
    (by omega : s ≤ 2*s) hh (hx'.neg_time H) (by norm_num : (1/20:ℝ)+1/20 ≤ 1/10)
  rw [show u-(-x)=x+u by ring,show 2*s-s=s by omega] at h
  obtain ⟨z,hz,C,hC,he⟩ := hy
  exact (not_lt_of_ge he) (h z hz C hC)

#print axioms affordable_time_le_half_of_hard_lag
end
end GaloisForLFunctions.HTGeometry
