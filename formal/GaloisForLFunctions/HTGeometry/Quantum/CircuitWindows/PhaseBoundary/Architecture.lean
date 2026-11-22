import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.CircuitWord

/-! # The polynomial equations describe exactly the affordable architecture -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section

/-- The real witness vector encodes precisely the unit scalar, special
unitary gates, and the closed operator ball at this architecture. -/
theorem architecture_iff {N g : ℕ} (D : TwoQubitArchitecture N g) (U : Square (Bits N))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∃ z : ℂ, ‖z‖=1 ∧ ∃ G : Fin g → Matrix.specialUnitaryGroup PairBits ℂ,
        ‖U-z • (D.contraction G).val‖ ≤ ε) ↔
      ∃ w : Coord N g → ℝ, ∀ e, residual D U ε w e = 0 := by
  constructor
  · rintro ⟨z,hz,G,he⟩
    obtain ⟨B,hB⟩ := (norm_le_iff_slack _ hε).mp he
    obtain ⟨w,hp,hg,hb⟩ := exists_witness_tuple z (fun k => (G k).val) B
    refine ⟨w,?_⟩
    rintro (v|⟨k,v|⟨i,j⟩⟩|⟨i,j⟩)
    · change star (phaseVar w)*phaseVar w-1=0
      rw [hp,Complex.star_def,Complex.conj_mul',hz]; norm_num
    · change (gateVar w k).det-1=0
      rw [hg,(Matrix.mem_specialUnitaryGroup_iff.mp (G k).property).2,sub_self]
    · change (star (gateVar w k)*gateVar w k-1) i j=0
      rw [hg,Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp (G k).property).1,sub_self]
      rfl
    · simp only [residual,hp,hg,hb,rawWord_eval,hB,sub_self,Matrix.zero_apply]
  · rintro ⟨w,hw⟩
    let z := phaseVar w
    let G := gateVar w
    have hunit : star z*z=1 := sub_eq_zero.mp (hw (.inl ()))
    have hz : ‖z‖=1 := by
      have h := congrArg norm hunit
      rw [norm_mul,norm_star,norm_one] at h
      nlinarith only [h,norm_nonneg z,sq_nonneg (‖z‖-1)]
    have hg (k : Fin g) : G k ∈ Matrix.specialUnitaryGroup PairBits ℂ := by
      refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff'.mpr ?_,?_⟩
      · apply sub_eq_zero.mp
        exact Matrix.ext fun i j => hw (.inr (.inl (k,.inr (i,j))))
      · exact sub_eq_zero.mp (hw (.inr (.inl (k,.inl ()))))
    let V (k : Fin g) : Matrix.specialUnitaryGroup PairBits ℂ := ⟨G k,hg k⟩
    refine ⟨z,hz,V,(norm_le_iff_slack _ hε).2 ⟨slackVar w,?_⟩⟩
    rw [←rawWord_eval]
    apply sub_eq_zero.mp
    exact Matrix.ext fun i j => hw (.inr (.inr (i,j)))

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
