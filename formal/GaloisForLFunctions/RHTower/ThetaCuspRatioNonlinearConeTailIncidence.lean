import GaloisForLFunctions.RHTower.ThetaCuspRatioNonlinearConeTail
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare Filter Topology

theorem strictCoarseCone_compact_bounds {h r t : ℝ} (hh : 0<h)
    (hc : StrictCoarseCone (9-r*h^2) h⁻¹ ((1-t*h)/3)) :
    0≤r ∧ r≤361/25 ∧ 0<t ∧ 0<compactSpeed h r t := by
  obtain ⟨hv0,hv9,hk,hz0,hz3,hkr,hf⟩ := hc
  have hn : h≠0 := hh.ne'
  have hr : 0<r := by
    have hs : 0<r*h^2 := by linarith only [hv9]
    exact (mul_pos_iff_of_pos_right (sq_pos_of_pos hh)).mp hs
  have he : h⁻¹^2*(9-(9-r*h^2))=r := by field_simp [hn]; ring
  rw [he] at hkr
  have ht : 0<t := by
    have hs : 0<t*h := by linarith only [hz3]
    exact (mul_pos_iff_of_pos_right hh).mp hs
  refine ⟨hr.le,hkr.le,ht,?_⟩
  have heF : h⁻¹^2*(9-(9-r*h^2))-6*h⁻¹-4+
      2*(9-r*h^2)*(h⁻¹+2/3)*((1-t*h)/3)=compactSpeed h r t := by
    unfold compactSpeed
    field_simp [hn]
    ring
  rwa [heF] at hf

theorem strictNonlinearCone_slope_tail_pos :
    ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ r t : ℝ,
      StrictCoarseCone (9-r*h^2) h⁻¹ ((1-t*h)/3) →
      r*(1/12-7*h/72)<t-h^2*t^2 →
      0<(eval (sourcePoint (h:ℂ) (r:ℂ) (t:ℂ)) ThetaRatioSquare.slope).re := by
  filter_upwards [nonlinear_cone_tail_pos,self_mem_nhdsWithin] with h hh hp
  intro r t hc he
  have hb := strictCoarseCone_compact_bounds hp hc
  have hs := hh r t hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 he
  have hreg := regularSlopeValue_eq h r t hp.ne'
  rw [←hreg] at hs
  exact (mul_pos_iff_of_pos_left (pow_pos hp 19)).mp hs

end
end HTGeometry.ThetaRatioInfinity
