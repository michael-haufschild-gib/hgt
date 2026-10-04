import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinitySign

/-! # Exact source-flow compactification and the third-slope expanding mode. -/

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare Filter Topology


/-- The currently available pointwise inequalities, in squared source coordinates. -/
def StrictCoarseCone (v k z : ℝ) : Prop :=
  0<v ∧ v<9 ∧ 5/4<k ∧ 0<z ∧ z<1/3 ∧
  k^2*(9-v)<361/25 ∧ 0<k^2*(9-v)-6*k-4+2*v*(k+2/3)*z

theorem counterfamily_in_cone (h : ℝ) (hh : 0<h) (hb : h<1/2) :
    StrictCoarseCone (9-h^2) h⁻¹ ((1-h/24)/3) := by
  have hn : h≠0 := ne_of_gt hh
  have hs : 0<h^2 := sq_pos_of_pos hh
  have hsq : h^2<1/4 := by nlinarith
  have hk : (5/4:ℝ)<h⁻¹ := by
    rw [inv_eq_one_div,lt_div_iff₀ hh]
    linarith
  have hr : h⁻¹^2*(9-(9-h^2))=1 := by field_simp [hn]; ring
  have hf : h⁻¹^2*(9-(9-h^2))-6*h⁻¹-4+
      2*(9-h^2)*(h⁻¹+2/3)*((1-h/24)/3)=
      3/4-(5/6)*h-(5/12)*h^2+(1/54)*h^3 := by
    field_simp [hn]
    ring
  unfold StrictCoarseCone
  refine ⟨by linarith,by linarith,hk,by linarith,by linarith,?_,?_⟩
  · rw [hr]
    norm_num
  · rw [hf]
    have hp : 0≤h^3 := pow_nonneg hh.le 3
    nlinarith

theorem slopeValue_counterfamily (h : ℝ) :
    slopeValue h 1 (1/24)=
      (eval (basePoint ((9-h^2:ℝ):ℂ) ((h⁻¹:ℝ):ℂ)
        (((1-h/24)/3:ℝ):ℂ)) ThetaRatioSquare.slope).re := by
  have he : sourcePoint (h:ℂ) 1 (1/24)=
      basePoint ((9-h^2:ℝ):ℂ) ((h⁻¹:ℝ):ℂ) (((1-h/24)/3:ℝ):ℂ) := by
    funext i
    cases i <;> simp [sourcePoint,basePoint] <;> ring
  simpa only [slopeValue,Complex.ofReal_one,Complex.ofReal_div,Complex.ofReal_ofNat,he]

/-- An unconditional obstruction to proving the slope from the coarse inequalities alone.
This is a state-space counterexample, not a point of the actual modular orbit. -/
theorem exists_coarseCone_negative_slope :
    ∃ v k z : ℝ, StrictCoarseCone v k z ∧
      (eval (basePoint (v:ℂ) (k:ℂ) (z:ℂ)) ThetaRatioSquare.slope).re<0 := by
  have hn := slopeValue_eventually_neg 1 (1/24) (by norm_num)
  have hb : ∀ᶠ h in 𝓝[>] (0:ℝ), h<1/2 :=
    (eventually_lt_nhds (show (0:ℝ)<1/2 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hp : ∀ᶠ h in 𝓝[>] (0:ℝ), 0<h := self_mem_nhdsWithin
  obtain ⟨h,hh,hs,hb⟩ := (hp.and (hn.and hb)).exists
  refine ⟨9-h^2,h⁻¹,(1-h/24)/3,counterfamily_in_cone h hh hb,?_⟩
  rwa [← slopeValue_counterfamily]

end
end HTGeometry.ThetaRatioInfinity
