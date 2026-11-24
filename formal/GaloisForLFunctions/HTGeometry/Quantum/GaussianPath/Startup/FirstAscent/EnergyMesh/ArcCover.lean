import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralEnclosingArc

/-! # The enclosing arc of an energy interval sampled with bounded gaps -/

open Finset Set Real
namespace GaloisForLFunctions.HTGeometry.FirstAscent.EnergyMesh
noncomputable section

private theorem close_lift (a c : ℝ) :
    ∃ v : ℝ, |a-v|=circDist a c ∧ circDist v c=0 := by
  obtain ⟨k,hk⟩ := exists_int_phaseGap a c
  let v := c-2*π*(k:ℝ)
  refine ⟨v,?_,le_antisymm ?_ (circDist_nonneg _ _)⟩
  · change |a-v|=|phaseGap a c|
    rw [hk]
    dsimp only [v]
    congr 1
    ring
  · have h := circDist_le v c k
    rwa [show v-c+2*π*(k:ℝ)=0 by dsimp only [v]; ring,abs_zero] at h

/-- An arc shorter than the ordinary span must leave its antipode in
an internal gap. Thus a mesh of radius q forces an arc of length at
least 2π−2q whenever taking the ordinary span is not optimal. -/
theorem arc_of_interval_cover {I : Type*} [Fintype I] [Nonempty I] (θ : I→ℝ) (i j : I)
    {q : ℝ} (hl : ∀ k, θ i ≤ θ k) (hu : ∀ k, θ k ≤ θ j)
    (hmesh : ∀ y ∈ Icc (θ i) (θ j), ∃ k, |θ k-y| ≤ q) :
    min (θ j-θ i) (2*π-2*q) ≤ spectralEnclosingArcLength θ ∧
      spectralEnclosingArcLength θ ≤ min (θ j-θ i) (2*π) := by
  let A := spectralEnclosingArcLength θ
  let R := A/2
  have hR : 0 ≤ R := div_nonneg (spectralEnclosingArcLength_nonneg θ) zero_le_two
  have hπ : R ≤ π := by
    have h := spectralEnclosingArcLength_lt_two_pi θ
    dsimp only [R,A]
    linarith only [h]
  have htop := spectralEnclosingArcLength_le_twice_radius θ ((θ i+θ j)/2) ((θ j-θ i)/2) (fun k => by
    apply (circDist_le _ _ 0).trans
    simp only [Int.cast_zero,mul_zero,add_zero]
    exact abs_le.mpr ⟨by linarith only [hl k],by linarith only [hu k]⟩)
  refine ⟨?_,le_min (by linarith only [htop]) (spectralEnclosingArcLength_lt_two_pi θ).le⟩
  by_cases hs : θ j-θ i ≤ A
  · exact (min_le_left ..).trans hs
  obtain ⟨c,hc⟩ := exists_spectralEnclosingArc_center θ
  obtain ⟨v,hv,hvc⟩ := close_lift (θ i) c
  have hi : |θ i-v| ≤ R := hv.le.trans (hc i)
  have hsame (x : ℝ) : circDist x v=circDist x c := by
    apply le_antisymm
    · have h := circDist_triangle x c v
      rwa [circDist_comm c v,hvc,add_zero] at h
    · have h := circDist_triangle x v c
      rwa [hvc,add_zero] at h
  have hj : R<θ j-v := by
    have h := (abs_le.mp hi).1
    change ¬θ j-θ i ≤ A at hs
    dsimp only [R] at h ⊢
    linarith only [lt_of_not_ge hs,h]
  have hright : v+π ≤ θ j := by
    by_contra! h
    have hd : |θ j-v| ≤ π := abs_le.mpr ⟨by linarith only [hj,hR,pi_pos],by linarith only [h]⟩
    have hh := hc j
    rw [←hsame, circDist_eq_abs_of_le_pi hd,abs_of_nonneg (hR.trans hj.le)] at hh
    exact hj.not_ge hh
  have hleft : θ i ≤ v+π := by linarith only [(abs_le.mp hi).2,hπ]
  obtain ⟨k,hk⟩ := hmesh (v+π) ⟨hleft,hright⟩
  have hdist : circDist (v+π) v=π := by
    have h : |v+π-v|=π := by rw [add_sub_cancel_left,abs_of_pos pi_pos]
    exact (circDist_eq_abs_of_le_pi h.le).trans h
  have hnear : circDist (v+π) (θ k) ≤ q := by
    apply (circDist_le _ _ 0).trans
    simpa only [Int.cast_zero,mul_zero,add_zero] using (abs_sub_comm (v+π) (θ k)).le.trans hk
  have ht := circDist_triangle (v+π) (θ k) v
  rw [hdist,hsame] at ht
  exact (min_le_right ..).trans (by linarith only [ht,hnear,hc k])

#print axioms arc_of_interval_cover
end
end GaloisForLFunctions.HTGeometry.FirstAscent.EnergyMesh
