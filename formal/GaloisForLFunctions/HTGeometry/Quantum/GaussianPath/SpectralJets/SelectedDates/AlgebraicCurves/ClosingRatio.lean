import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.PhysicalPhases

/-! # Arithmetic of the eigenphase ratio at the endpoints of a closing arc -/

open Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
noncomputable section

/-- Oriented endpoint ratio of the shortest enclosing arc at physical error ε. -/
def closingRatio (ε : ℝ) : ℂ := Complex.exp (-((4*arcsin (ε/2):ℝ):ℂ)*Complex.I)

theorem anchor_div_at_closing_gap {I : Type*} (E : I → ℝ) {i j : I} {t ε : ℝ} {q : ℤ}
    (hg : t*(E i-E j)=2*π*((q:ℝ)+SharpOccupation.physicalArc ε)) :
    anchorPhase E i t/anchorPhase E j t=closingRatio ε := by
  have ht : t*(E i-E j)=(q:ℝ)*(2*π)+4*arcsin (ε/2) := by
    rw [hg,SharpOccupation.physicalArc]
    field_simp [pi_ne_zero]
    ring
  have h := congrArg Complex.ofReal ht
  push_cast at h
  rw [anchorPhase,anchorPhase,←Complex.exp_sub]
  have hex : -(Complex.I*((t:ℂ)*(E i:ℂ)))- -(Complex.I*((t:ℂ)*(E j:ℂ))) =
      ((-q:ℤ):ℂ)*(2*π*Complex.I)+ -((4*arcsin (ε/2):ℝ):ℂ)*Complex.I := by
    push_cast
    linear_combination -Complex.I * h
  rw [hex,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,one_mul,closingRatio]

/-- The physical error determines the symmetric Laurent polynomial in
the closing eigenphase by the double-angle identity applied twice. -/
theorem closingRatio_add_inv {ε : ℝ} (hε : 0<ε) (hs : ε<sqrt 2) :
    closingRatio ε+(closingRatio ε)⁻¹ = ((ε:ℂ)^2-2)^2-2 := by
  let θ := arcsin (ε/2)
  have hsin : sin θ=ε/2 := sin_arcsin (by linarith only [hε]) (by
    nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),hs,sqrt_nonneg 2])
  have hcos : 2*cos (4*θ)=(ε^2-2)^2-2 := by
    rw [show 4*θ=2*(2*θ) by ring,cos_two_mul,cos_two_mul_eq_one_sub,hsin]
    ring
  have h := congrArg Complex.ofReal hcos
  push_cast at h
  rw [Complex.two_cos] at h
  have hi : (closingRatio ε)⁻¹=Complex.exp (((4*θ:ℝ):ℂ)*Complex.I) := by
    rw [closingRatio,←Complex.exp_neg,neg_mul,neg_neg]
  rw [hi,closingRatio,add_comm]
  simpa only [θ,Complex.ofReal_mul,Complex.ofReal_ofNat] using h

/-- The closing ratio is algebraic exactly at algebraic physical errors. -/
theorem closingRatio_algebraic_iff {ε : ℝ} (hε : 0<ε) (hs : ε<sqrt 2) :
    IsAlgebraic ℚ (closingRatio ε) ↔ IsAlgebraic ℚ (ε:ℂ) := by
  let z := closingRatio ε
  let S := algebraicClosure ℚ ℂ
  have h₂ : (2:ℂ)∈S := ofNat_mem S 2
  have root {x : ℂ} (hx : x^2∈S) : x∈S := mem_algebraicClosure_iff.mpr
    (IsAlgebraic.of_pow (by decide : 0<2) (mem_algebraicClosure_iff.mp hx))
  have hz : z≠0 := Complex.exp_ne_zero _
  have he : z+z⁻¹=((ε:ℂ)^2-2)^2-2 := closingRatio_add_inv hε hs
  constructor
  · intro ha
    have hzS : z∈S := mem_algebraicClosure_iff.mpr ha
    have hsum := S.add_mem hzS (S.inv_mem hzS)
    rw [he] at hsum
    have hsq : ((ε:ℂ)^2-2)^2∈S := by simpa only [sub_add_cancel] using S.add_mem hsum h₂
    have hv : (ε:ℂ)^2-2∈S := root hsq
    have hw : (ε:ℂ)^2∈S := by simpa only [sub_add_cancel] using S.add_mem hv h₂
    exact mem_algebraicClosure_iff.mp (root hw)
  · intro ha
    let w := z+z⁻¹
    have hae : (ε:ℂ)∈S := mem_algebraicClosure_iff.mpr ha
    have hw : w∈S := by
      change z+z⁻¹∈S
      rw [he]
      exact S.sub_mem (S.pow_mem (S.sub_mem (S.pow_mem hae 2) h₂) 2) h₂
    have hdiff : (z-z⁻¹)^2=w^2-2^2 := by
      dsimp only [w]
      field_simp [hz]
      ring
    have hd : z-z⁻¹∈S := root
      (show (z-z⁻¹)^2∈S by rw [hdiff]; exact S.sub_mem (S.pow_mem hw 2) (S.pow_mem h₂ 2))
    have hrepr : (w+(z-z⁻¹))/2=z := by dsimp only [w]; ring
    have hzS := S.div_mem (S.add_mem hw hd) h₂
    rw [hrepr] at hzS
    exact mem_algebraicClosure_iff.mp hzS

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
