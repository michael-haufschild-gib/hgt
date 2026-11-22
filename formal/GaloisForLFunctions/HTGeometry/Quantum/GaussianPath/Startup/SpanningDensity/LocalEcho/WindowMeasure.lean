import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.VisitClusters
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualDynamics

/-! # Uniform physical occupation bounds from the first time window onward -/
open Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
noncomputable section

/-- Each interval of length b meets at most one cluster. Its occupied
part lies within d of its leftmost limiting point. -/
private theorem measure_one (E : Set ℝ) (d b a : ℝ) (hd : 0≤d)
    (gap : ∀ v∈E, ∀ w∈E, |w-v|<d ∨ b < |w-v|) :
    volume.real (E∩Icc a (a+b))≤d := by
  let F := E∩Icc a (a+b)
  rcases F.eq_empty_or_nonempty with he|hn
  · change volume.real F≤_; rw [he,measureReal_empty]; exact hd
  have hb : BddBelow F := ⟨a,fun _ hx => hx.2.1⟩
  have hs : F ⊆ Icc (sInf F) (sInf F+d) := by
    intro x hx
    refine ⟨csInf_le hb hx,?_⟩
    apply sub_le_iff_le_add.mp
    apply le_csInf hn
    intro y hy
    rcases gap y hy.1 x hx.1 with h|h
    · linarith only [(abs_lt.mp h).2]
    · have hdist : |x-y|≤b := abs_le.mpr ⟨by linarith only [hx.2.1,hy.2.2],by linarith only [hx.2.2,hy.2.1]⟩
      exact (h.not_ge hdist).elim
  apply (measureReal_mono (μ:=volume) hs measure_Icc_lt_top.ne).trans
  rw [Real.volume_real_Icc_of_le (le_add_of_nonneg_right hd)]
  linarith

private theorem measure_windows (E : Set ℝ) (d b : ℝ) (hd : 0≤d) (hb : 0≤b)
    (gap : ∀ v∈E, ∀ w∈E, |w-v|<d ∨ b < |w-v|) (a : ℝ) (m : ℕ) :
    volume.real (E∩Icc a (a+m*b))≤m*d := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero,zero_mul,add_zero,Icc_self]
    exact (measureReal_mono (μ:=volume) inter_subset_right (by simp)).trans_eq (by simp)
  | succ m ih =>
    let p := a+m*b
    have he : E∩Icc a (a+(m+1:ℕ)*b)=(E∩Icc a p)∪(E∩Icc p (p+b)) := by
      rw [←inter_union_distrib_left]
      congr 1
      have hp : a≤p := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hb)
      have hr : a+(m+1:ℕ)*b=p+b := by dsimp only [p]; push_cast; ring
      rw [hr,Icc_union_Icc_eq_Icc hp (le_add_of_nonneg_right hb)]
    rw [he]
    apply (measureReal_union_le ..).trans
    exact (add_le_add ih (measure_one E d b p hd gap)).trans_eq (by push_cast; ring)

/-- Every observation window, including those starting at zero or a first
crossing, has at most O((1+T)/N) physical time below any fixed density κ<1/2. -/
theorem gaussian_uniform_window_occupation (κ : ℝ) (hκ : κ<1/2) : ∃ A b : ℝ, 0<A ∧ 0<b ∧
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, (s:ℝ)≤κ*(n+1:ℕ) →
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      let E := {t : ℝ | HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H t)}
      ∀ a T : ℝ, 0≤T → volume.real (E∩Icc a (a+T))≤(1+T/b)*(A/(n+1:ℕ)) := by
  obtain ⟨A,b,hA,hb,hw⟩ := gaussian_visit_clusters κ hκ
  refine ⟨A,b,hA,hb,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  intro s hs H E a T hT
  let m := ⌈T/b⌉₊
  have ht : T≤m*b := (div_le_iff₀ hb).mp (Nat.le_ceil _)
  have hd : 0≤A/(n+1:ℕ) := by positivity
  have he := measure_windows E _ b hd hb.le (hn s hs).1 a m
  have hsub : E∩Icc a (a+T) ⊆ E∩Icc a (a+m*b) := inter_subset_inter_right _ (Icc_subset_Icc_right (add_le_add_left ht _))
  have hfin : volume (E∩Icc a (a+m*b))≠⊤ := ((measure_mono inter_subset_right).trans_lt measure_Icc_lt_top).ne
  apply ((measureReal_mono (μ:=volume) hsub hfin).trans he).trans
  apply mul_le_mul_of_nonneg_right _ hd
  simpa only [add_comm (T/b)] using (Nat.ceil_lt_add_one (div_nonneg hT hb.le)).le

/-- After each half-tolerance visit, including the first after any chosen
crossing, total affordable time in the next fixed window is exactly of
inverse-volume order for all budgets below half density. -/
theorem gaussian_deep_visit_window (κ : ℝ) (hκ : κ<1/2) : ∃ c A b : ℝ, 0<c ∧ 0<A ∧ 0<b ∧
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, (s:ℝ)≤κ*(n+1:ℕ) →
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      let E := {t : ℝ | HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H t)}
      ∀ v : ℝ, HasProjectiveCircuitApproximation (n+2) (1/20) s (unitaryEvolution H v) →
        volume.real (E∩Icc v (v+b)) ∈ Icc (c/(n+2:ℕ)) (A/(n+1:ℕ)) := by
  obtain ⟨A,b,hA,hb,hw⟩ := gaussian_visit_clusters κ hκ
  obtain ⟨C,hC,hH⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  let c := min b (1/(20*C))
  have hc : 0<c := lt_min hb (by positivity)
  refine ⟨c,A,b,hc,hA,hb,?_⟩
  filter_upwards [hw,hH] with ω hω hnorm
  filter_upwards [hω,hnorm] with n hn hnorm
  intro s hs H E v hv
  have hp : 0<((n+2:ℕ):ℝ) := by positivity
  have hr : 0≤c/(n+2:ℕ) := div_nonneg hc.le hp.le
  have hshort : c/(n+2:ℕ)≤b := (div_le_self hc.le (by exact_mod_cast (show 1≤n+2 by omega))).trans (min_le_left ..)
  refine ⟨?_,measure_one E _ b v (by positivity) (hn s hs).1⟩
  obtain ⟨z,hz,D,hD,herr⟩ := hv
  have hsub : Icc v (v+c/(n+2:ℕ)) ⊆ E∩Icc v (v+b) := by
    intro w hw
    refine ⟨⟨z,hz,D,hD,?_⟩,hw.1,hw.2.trans (add_le_add_left hshort _)⟩
    have hdist := norm_unitaryEvolution_time_sub_le (H:=H) (isSelfAdjoint_pathHamiltonian _) w v
    rw [abs_of_nonneg (sub_nonneg.mpr hw.1)] at hdist
    have hl : w-v≤c/(n+2:ℕ) := by linarith only [hw.2]
    have hc' : c*(20*C)≤1 := (le_div_iff₀ (mul_pos (by norm_num) hC)).mp (min_le_right ..)
    have hmul := mul_le_mul hnorm hl (sub_nonneg.mpr hw.1) (mul_nonneg hC.le hp.le)
    rw [show C*(n+2:ℕ)*(c/(n+2:ℕ))=C*c by field_simp] at hmul
    have he := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution H w) (unitaryEvolution H v) (z • D.eval.val)
    linarith only [hdist,hmul,hc',he,herr]
  have hfin : volume (E∩Icc v (v+b))≠⊤ := ((measure_mono inter_subset_right).trans_lt measure_Icc_lt_top).ne
  have hm := measureReal_mono (μ:=volume) hsub hfin
  rwa [Real.volume_real_Icc_of_le (le_add_of_nonneg_right hr),add_sub_cancel_left] at hm

#print axioms gaussian_deep_visit_window
#print axioms gaussian_uniform_window_occupation
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
