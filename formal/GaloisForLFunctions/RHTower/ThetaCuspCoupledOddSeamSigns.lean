import GaloisForLFunctions.RHTower.ThetaCuspCoupledOddSeamModel
/-! # Fixed-direction failure and optimal-direction reserve on the full seam source box -/
namespace HTGeometry.ThetaSeamCoupled
noncomputable section
theorem canonical_Lo_neg (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hpos : 0 < u+v) :
    canonicalHom ((191*u+192*v)/10) (u+v) (157/50) < 0 := by
  have huv : 0 < u ∨ 0 < v := by
    by_cases h : 0 < u
    · exact Or.inl h
    · exact Or.inr (by linarith)
  apply neg_pos.mp
  rw [(canonicalLoNorm _ _).property]
  dsimp only [canonicalLoNorm]
  rcases huv with hp | hp
  all_goals ring_nf; positivity

theorem canonical_Hi_neg (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hpos : 0 < u+v) :
    canonicalHom ((191*u+192*v)/10) (u+v) (63/20) < 0 := by
  have huv : 0 < u ∨ 0 < v := by
    by_cases h : 0 < u
    · exact Or.inl h
    · exact Or.inr (by linarith)
  apply neg_pos.mp
  rw [(canonicalHiNorm _ _).property]
  dsimp only [canonicalHiNorm]
  rcases huv with hp | hp
  all_goals ring_nf; positivity

theorem canonical_mid_neg (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hpos : 0 < u+v) :
    canonicalMidControlHom ((191*u+192*v)/10) (u+v) < 0 := by
  have huv : 0 < u ∨ 0 < v := by
    by_cases h : 0 < u
    · exact Or.inl h
    · exact Or.inr (by linarith)
  apply neg_pos.mp
  rw [(canonicalMidControlHomNorm _ _).property]
  dsimp only [canonicalMidControlHomNorm]
  rcases huv with hp | hp
  all_goals ring_nf; positivity


theorem canonical_neg_of_box {a q : ℝ}
    (ha0 : 191/10 ≤ a) (ha1 : a ≤ 96/5) (hq0 : 157/50 ≤ q) (hq1 : q ≤ 63/20) :
    canonicalCleared a q < 0 := by
  let u := 192-10*a
  let v := 10*a-191
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have huv : u+v=1 := by dsimp [u,v]; ring
  have hav : (191*u+192*v)/10=a := by dsimp [u,v]; ring
  have hL := canonical_Lo_neg u v hu hv (by rw [huv]; norm_num)
  have hU := canonical_Hi_neg u v hu hv (by rw [huv]; norm_num)
  have hM := canonical_mid_neg u v hu hv (by rw [huv]; norm_num)
  rw [hav,huv] at hL hU hM
  rw [← canonicalHom_one,canonicalHom_bernstein]
  have ht0 : 0 ≤ 100*q-314 := by linarith
  have ht1 : 100*q-314 ≤ 1 := by linarith
  by_cases ht : 100*q-314=1
  · simpa [ht] using hU
  · have hlt : 0 < 1-(100*q-314) := by
      have := lt_of_le_of_ne ht1 ht
      linarith
    have hA := mul_neg_of_pos_of_neg (sq_pos_of_pos hlt) hL
    have hB := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ 2*(100*q-314)*(1-(100*q-314)) by positivity) hM.le
    have hC := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (100*q-314)) hU.le
    linarith only [hA,hB,hC]

theorem optimal_pos (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hpos : 0 < u+v) :
    0 < optimalHom ((191*u+192*v)/10) (u+v) := by
  have huv : 0 < u ∨ 0 < v := by
    by_cases h : 0 < u
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [(optimalHomNorm _ _).property]
  dsimp only [optimalHomNorm]
  rcases huv with hp | hp
  all_goals ring_nf; positivity


theorem optimal_pos_of_box {a : ℝ} (ha0 : 191/10 ≤ a) (ha1 : a ≤ 96/5) :
    0 < optimalHom a 1 := by
  let u := 192-10*a
  let v := 10*a-191
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have huv : u+v=1 := by dsimp [u,v]; ring
  have hav : (191*u+192*v)/10=a := by dsimp [u,v]; ring
  have h := optimal_pos u v hu hv (by rw [huv]; norm_num)
  simpa only [hav,huv] using h

end
end HTGeometry.ThetaSeamCoupled
