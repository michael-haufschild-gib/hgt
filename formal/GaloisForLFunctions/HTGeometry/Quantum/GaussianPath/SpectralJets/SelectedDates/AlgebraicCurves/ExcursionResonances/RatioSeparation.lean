import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.ExcursionResonances.ClosingTurn

/-! # Separation of the two energy ratios in a resonant excursion date -/

namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.ExcursionResonances
noncomputable section

/-- At algebraic spectra, equality of two actions at a candidate
resonant wait forces both energy ratios to agree separately. -/
theorem two_ratio_eq_iff {x A B A' B' : ℝ} (hx : Transcendental ℚ x)
    (hA : IsAlgebraic ℚ A) (hB : IsAlgebraic ℚ B) (hA' : IsAlgebraic ℚ A')
    (hB' : IsAlgebraic ℚ B') (q l : ℤ) (hl : l≠0) :
    ((q:ℝ)+x)*A-(l:ℝ)*B=((q:ℝ)+x)*A'-(l:ℝ)*B' ↔ A=A' ∧ B=B' := by
  constructor
  · intro h
    let K := algebraicClosure ℚ ℝ
    have ha : A=A' := by
      by_contra hn
      have hd : A-A'∈K := K.sub_mem (mem_algebraicClosure_iff.mpr hA) (mem_algebraicClosure_iff.mpr hA')
      have he : B-B'∈K := K.sub_mem (mem_algebraicClosure_iff.mpr hB) (mem_algebraicClosure_iff.mpr hB')
      have hrepr : x=(l:ℝ)*(B-B')/(A-A')-q := by
        apply (eq_sub_iff_add_eq.mpr ((eq_div_iff (sub_ne_zero.mpr hn)).mpr ?_))
        linear_combination h
      apply hx
      rw [hrepr]
      exact mem_algebraicClosure_iff.mp (K.sub_mem (K.div_mem (K.mul_mem (K.intCast_mem l) he) hd) (K.intCast_mem q))
    refine ⟨ha,?_⟩
    rw [ha] at h
    exact mul_left_cancel₀ (Int.cast_ne_zero.mpr hl : (l:ℝ)≠0) (sub_right_inj.mp h)
  · rintro ⟨rfl,rfl⟩
    rfl

/-- For error one tenth this separation holds for every integer
winding of the closing pair and every nonzero putative resonance winding. -/
theorem tenth_action_eq_iff (A B A' B' : algebraicClosure ℚ ℝ) (q l : ℤ) (hl : l≠0) :
    ((q:ℝ)+SharpOccupation.physicalArc (1/10))*(A:ℝ)-(l:ℝ)*B =
      ((q:ℝ)+SharpOccupation.physicalArc (1/10))*(A':ℝ)-(l:ℝ)*B' ↔ A=A' ∧ B=B' := by
  simpa only [Subtype.coe_inj] using two_ratio_eq_iff tenth_closing_turn_transcendental
    (mem_algebraicClosure_iff.mp A.property) (mem_algebraicClosure_iff.mp B.property)
    (mem_algebraicClosure_iff.mp A'.property) (mem_algebraicClosure_iff.mp B'.property) q l hl

#print axioms tenth_action_eq_iff
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.ExcursionResonances
