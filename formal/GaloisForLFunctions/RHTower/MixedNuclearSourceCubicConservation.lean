import GaloisForLFunctions.RHTower.FormationAnchoredCubicHomotopyDefect

/-!
# Cubic conservation from a nuclear adjacent product

Put A=R-Q and B=Q-P. For orthogonal projections it suffices that AB is
nuclear; neither A nor B need be compact and P,Q need not commute.
Adjoint factorization makes BA nuclear. All six mixed cubic words are then
nuclear. Cyclicity groups their traces into three copies of
Tr(A^(2 : ℕ) B + A B^(2 : ℕ))=Tr([AB,Q])=0.

The hypothesis concerns the adjacent product, not merely the combined
cubic defect. The projections may be noncommuting.
-/

noncomputable section
namespace RHTower
open ContinuousLinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem mixedNuclear_add {X Y : H →L[ℂ] H}
    (hX : MemSchattenClass 1 X) (hY : MemSchattenClass 1 Y) :
    MemSchattenClass 1 (X+Y) :=
  memSchattenClass_one_add (hX.isCompactOperator one_pos)
    (hY.isCompactOperator one_pos) hX hY

/-- Nuclearity of one mixed product supplies the reversed product for self-adjoint factors. -/
theorem nuclear_reverse_product_of_selfAdjoint
    (A B : H →L[ℂ] H) (hA : adjoint A=A) (hB : adjoint B=B)
    (hAB : MemSchattenClass 1 (A*B)) : MemSchattenClass 1 (B*A) := by
  obtain ⟨X,Y,hX,hY,hfac⟩ := hAB.one_isTraceClass
  have hfac' : B*A = adjoint Y ∘L adjoint X := by
    have h := congrArg (fun T : H →L[ℂ] H => adjoint T) hfac
    change adjoint (A ∘L B) = adjoint (X ∘L Y) at h
    rw [adjoint_comp,adjoint_comp,hA,hB] at h
    exact h
  rw [hfac']
  exact (memRectSchattenClass_iff_memSchattenClass 1 _).mp
    (memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hX.adjoint hY.adjoint)

/-- Mixed-product admission suffices for cubic conservation, without compact displacements
or commuting projections. The three two-word channels have separately zero trace. -/
theorem mixedNuclearSourceCubicAssociator_conservation
    (R Q P : H →L[ℂ] H)
    (hR : R*R=R) (hQ : Q*Q=Q) (hP : P*P=P)
    (hRadj : adjoint R=R) (hQadj : adjoint Q=Q) (hPadj : adjoint P=P)
    (hAB : MemSchattenClass 1 ((R-Q)*(Q-P))) :
    let A := R-Q
    let B := Q-P
    let T₀ := (A*A)*B+A*(B*B)
    let T₁ := (A*B)*A+(B*A)*B
    let T₂ := (B*A)*A+(B*B)*A
    MemSchattenClass 1 T₀ ∧ MemSchattenClass 1 T₁ ∧ MemSchattenClass 1 T₂ ∧
      opTrace T₀=0 ∧ opTrace T₁=0 ∧ opTrace T₂=0 ∧
      MemSchattenClass 1 (formationAnchoredCubicAssociator R Q P) ∧
      opTrace (formationAnchoredCubicAssociator R Q P)=0 := by
  let A := R-Q
  let B := Q-P
  let T₀ := (A*A)*B+A*(B*B)
  let T₁ := (A*B)*A+(B*A)*B
  let T₂ := (B*A)*A+(B*B)*A
  change MemSchattenClass 1 (A*B) at hAB
  have hA : adjoint A=A := by dsimp [A]; rw [adjoint.map_sub,hRadj,hQadj]
  have hB : adjoint B=B := by dsimp [B]; rw [adjoint.map_sub,hQadj,hPadj]
  have hBA : MemSchattenClass 1 (B*A) :=
    nuclear_reverse_product_of_selfAdjoint A B hA hB hAB
  have hAAB : MemSchattenClass 1 ((A*A)*B) := by
    simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_assoc] using
      memSchattenClass_one_comp_left hAB A
  have hABA : MemSchattenClass 1 ((A*B)*A) := memSchattenClass_one_comp_right hAB A
  have hBAA : MemSchattenClass 1 ((B*A)*A) := memSchattenClass_one_comp_right hBA A
  have hABB : MemSchattenClass 1 (A*(B*B)) := by
    simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_assoc] using
      memSchattenClass_one_comp_right hAB B
  have hBAB : MemSchattenClass 1 ((B*A)*B) := memSchattenClass_one_comp_right hBA B
  have hBBA : MemSchattenClass 1 ((B*B)*A) := by
    simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_assoc] using
      memSchattenClass_one_comp_left hBA B
  have hT₀ : MemSchattenClass 1 T₀ := mixedNuclear_add hAAB hABB
  have hT₁ : MemSchattenClass 1 T₁ := mixedNuclear_add hABA hBAB
  have hT₂ : MemSchattenClass 1 T₂ := mixedNuclear_add hBAA hBBA
  have hcross : T₀=(A*B)*Q-Q*(A*B) := by
    have hQQP : Q*(Q*P)=Q*P := by rw [← mul_assoc,hQ]
    dsimp only [T₀,A,B]
    noncomm_ring [hR,hQ,hP,hQQP]
  have htraceT₀ : opTrace T₀=0 := by
    have hABQ : MemSchattenClass 1 ((A*B)*Q) := memSchattenClass_one_comp_right hAB Q
    have hQAB : MemSchattenClass 1 (Q*(A*B)) := memSchattenClass_one_comp_left hAB Q
    rw [hcross,opTrace_sub_of_memSchattenClass_one hABQ hQAB]
    exact sub_eq_zero.mpr (hAB.one_opTrace_comp_comm Q).symm
  have hcycAA : opTrace ((A*A)*B)=opTrace ((A*B)*A) := by
    simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_assoc] using
      hAB.one_opTrace_comp_comm A
  have hcycBA : opTrace ((B*A)*A)=opTrace ((A*B)*A) := by
    simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_assoc] using
      (hBA.one_opTrace_comp_comm A).symm
  have hcycBB : opTrace (A*(B*B))=opTrace ((B*A)*B) := by
    simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_assoc] using
      (hAB.one_opTrace_comp_comm B).symm
  have hcycAB : opTrace ((B*B)*A)=opTrace ((B*A)*B) := by
    simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_assoc] using
      hBA.one_opTrace_comp_comm B
  have htraceT₁ : opTrace T₁=0 := by
    rw [show opTrace T₁=opTrace ((A*B)*A)+opTrace ((B*A)*B) from
      opTrace_add_of_memSchattenClass_one hABA hBAB,← hcycAA,← hcycBB,
      ← opTrace_add_of_memSchattenClass_one hAAB hABB]
    exact htraceT₀
  have htraceT₂ : opTrace T₂=0 := by
    rw [show opTrace T₂=opTrace ((B*A)*A)+opTrace ((B*B)*A) from
      opTrace_add_of_memSchattenClass_one hBAA hBBA,hcycBA,hcycAB,
      ← opTrace_add_of_memSchattenClass_one hABA hBAB]
    exact htraceT₁
  have hdecomp : formationAnchoredCubicAssociator R Q P=T₀+T₁+T₂ := by
    dsimp only [formationAnchoredCubicAssociator,formationAnchoredCubicDefect,
      restrictedProjectionCubicDefect,restrictedProjectionDisplacement,T₀,T₁,T₂,A,B]
    noncomm_ring
  have hC : MemSchattenClass 1 (formationAnchoredCubicAssociator R Q P) := by
    rw [hdecomp]
    exact mixedNuclear_add (mixedNuclear_add hT₀ hT₁) hT₂
  refine ⟨hT₀,hT₁,hT₂,htraceT₀,htraceT₁,htraceT₂,hC,?_⟩
  rw [hdecomp,opTrace_add_of_memSchattenClass_one (mixedNuclear_add hT₀ hT₁) hT₂,
    opTrace_add_of_memSchattenClass_one hT₀ hT₁,htraceT₀,htraceT₁,htraceT₂]
  simp

end RHTower
