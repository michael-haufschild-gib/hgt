import GaloisForLFunctions.RHTower.FormationAnchoredCubicHomotopyDefect
import GaloisForLFunctions.RHTower.TraceClassCompressionCurvature

/-!
Nested-source cubic conservation beyond compact displacement.

Paper proof: let P <= Q be orthogonal projections, R another orthogonal projection,
D=Q-P, E=1-D, A=E R D, and C=(R-P)^3-(R-Q)^3-(Q-P)^3.
Projection algebra gives D C D=-A* A and E C E=A A*.
If only C is nuclear, its D-compression is nuclear, hence A is Hilbert--Schmidt.
Trace-class pinching and Hilbert--Schmidt cyclicity give Tr C=0.
No compactness of R-P, R-Q, or Q-P is assumed.

This is an operator-theoretic bridge and an obstruction to manufacturing an integer
charge from this particular nested-source associator. It is not an RH estimate;
it does not classify nonnested polarizations or modular/nontracial pairings.
-/

noncomputable section
namespace RHTower
open ContinuousLinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem opTrace_idempotent_pinching
    (D C : H →L[ℂ] H) (hD : D * D = D) (hC : MemSchattenClass 1 C) :
    opTrace C = opTrace (D * C * D) + opTrace ((1-D) * C * (1-D)) := by
  let E : H →L[ℂ] H := 1-D
  have hE : E * E = E := by dsimp [E]; noncomm_ring [hD]
  have hDC : MemSchattenClass 1 (D*C) := by
    simpa only [ContinuousLinearMap.mul_def] using memSchattenClass_one_comp_left hC D
  have hEC : MemSchattenClass 1 (E*C) := by
    simpa only [ContinuousLinearMap.mul_def] using memSchattenClass_one_comp_left hC E
  have hd : opTrace (D*C) = opTrace (D*C*D) := by
    have h := hDC.one_opTrace_comp_comm D
    change opTrace (D*(D*C)) = opTrace ((D*C)*D) at h
    simpa only [← mul_assoc, hD] using h
  have he : opTrace (E*C) = opTrace (E*C*E) := by
    have h := hEC.one_opTrace_comp_comm E
    change opTrace (E*(E*C)) = opTrace ((E*C)*E) at h
    simpa only [← mul_assoc, hE] using h
  calc
    opTrace C = opTrace (D*C+E*C) := by congr 1; dsimp [E]; noncomm_ring
    _ = opTrace (D*C) + opTrace (E*C) := opTrace_add_of_memSchattenClass_one hDC hEC
    _ = _ := by rw [hd, he]

/-- Nuclearity of the combined nested-source cubic associator forces a finite transition
energy and zero ordinary charge, even when all three displacements are noncompact. -/
theorem nestedSourceCubicAssociator_nuclear_conservation
    (R Q P : H →L[ℂ] H)
    (hR : R*R=R) (hQ : Q*Q=Q) (hP : P*P=P)
    (hRadj : adjoint R=R) (hQadj : adjoint Q=Q) (hPadj : adjoint P=P)
    (hPQ : P*Q=P) (hQP : Q*P=P)
    (hC : MemSchattenClass 1 (formationAnchoredCubicAssociator R Q P)) :
    ((1-(Q-P))*R*(Q-P)).IsHilbertSchmidt ∧
      opTrace (formationAnchoredCubicAssociator R Q P) = 0 ∧
      (opTrace ((Q-P)*formationAnchoredCubicAssociator R Q P*(Q-P))).re =
        -hsNormSq ((1-(Q-P))*R*(Q-P)) ∧
      (opTrace ((1-(Q-P))*formationAnchoredCubicAssociator R Q P*(1-(Q-P)))).re =
        hsNormSq ((1-(Q-P))*R*(Q-P)) := by
  let D := Q-P
  let E : H →L[ℂ] H := 1-D
  let A := E*R*D
  let C := formationAnchoredCubicAssociator R Q P
  have hD : D*D=D := by dsimp [D]; noncomm_ring [hQ,hP,hPQ,hQP]
  have hE : E*E=E := by dsimp [E]; noncomm_ring [hD]
  have hDP : D*P=0 := by dsimp [D]; noncomm_ring [hQP,hP]
  have hPD : P*D=0 := by dsimp [D]; noncomm_ring [hPQ,hP]
  have hDQ : D*Q=D := by dsimp [D]; noncomm_ring [hQ,hPQ]
  have hQD : Q*D=D := by dsimp [D]; noncomm_ring [hQ,hQP]
  have hDadj : adjoint D=D := by
    dsimp only [D]; rw [map_sub,hQadj,hPadj]
  have hEadj : adjoint E=E := by
    dsimp only [E]; rw [map_sub,adjoint_one,hDadj]
  have hAadj : adjoint A = D*R*E := by
    change adjoint ((E ∘L R) ∘L D) = D*R*E
    rw [adjoint_comp,adjoint_comp,hDadj,hRadj,hEadj]
    rfl
  have hform : C=R*D*R+P*R*P-Q*R*Q := by
    dsimp only [C,D,formationAnchoredCubicAssociator,formationAnchoredCubicDefect,
      restrictedProjectionCubicDefect,restrictedProjectionDisplacement]
    noncomm_ring [hR,hQ,hP,hPQ,hQP]
  have hnegative : D*C*D = -(adjoint A*A) := by
    rw [hform,hAadj]
    change D*(R*D*R+P*R*P-Q*R*Q)*D = -((D*R*E)*(E*R*D))
    have hRRD : R*(R*D)=R*D := by rw [← mul_assoc,hR]
    have hEE : (D*R*E)*(E*R*D)=D*R*E*R*D := by
      calc
        _ = D*R*(E*E)*R*D := by noncomm_ring
        _ = _ := by rw [hE]
    rw [hEE]
    calc
      _ = D*R*D*R*D+(D*P)*R*(P*D)-(D*Q)*R*(Q*D) := by noncomm_ring
      _ = D*R*D*R*D-D*R*D := by rw [hDP,hDQ,hQD]; simp
      _ = _ := by dsimp only [E]; noncomm_ring [hRRD]
  have hpositive : E*C*E = A*adjoint A := by
    rw [hform,hAadj]
    change E*(R*D*R+P*R*P-Q*R*Q)*E = (E*R*D)*(D*R*E)
    have hEP : E*P=P := by dsimp only [E]; rw [sub_mul,one_mul,hDP,sub_zero]
    have hPE : P*E=P := by dsimp only [E]; rw [mul_sub,mul_one,hPD,sub_zero]
    have hEQ : E*Q=P := by
      dsimp only [E]; rw [sub_mul,one_mul,hDQ]; dsimp only [D]; abel
    have hQE : Q*E=P := by
      dsimp only [E]; rw [mul_sub,mul_one,hQD]; dsimp only [D]; abel
    calc
      _ = E*R*D*R*E+(E*P)*R*(P*E)-(E*Q)*R*(Q*E) := by noncomm_ring
      _ = E*R*D*R*E := by rw [hEP,hPE,hEQ,hQE]; abel
      _ = E*R*(D*D)*R*E := by rw [hD]
      _ = _ := by noncomm_ring
  have hDCD : MemSchattenClass 1 (D*C*D) := by
    have hDC := memSchattenClass_one_comp_left hC D
    simpa only [ContinuousLinearMap.mul_def,C] using
      memSchattenClass_one_comp_right hDC D
  have hGram : MemSchattenClass 1 (adjoint A*A) := by
    rw [hnegative] at hDCD
    simpa using memSchattenClass_one_smul hDCD (-1 : ℂ)
  have hA : A.IsHilbertSchmidt :=
    isHilbertSchmidt_of_adjoint_mul_self_memSchattenClass_one A hGram
  have hcycle := ContinuousLinearMap.opTrace_comp_comm hA.adjoint hA
  change opTrace (adjoint A*A)=opTrace (A*adjoint A) at hcycle
  have htrace : opTrace C=0 := by
    rw [opTrace_idempotent_pinching D C hD hC]
    change opTrace (D*C*D)+opTrace (E*C*E)=0
    rw [hnegative,hpositive,opTrace_neg,hcycle]
    abel
  refine ⟨hA,htrace,?_,?_⟩
  · change (opTrace (D*C*D)).re = -hsNormSq A
    rw [hnegative,opTrace_neg,Complex.neg_re]
    exact congrArg Neg.neg (ContinuousLinearMap.re_opTrace_adjoint_comp_self hA)
  · change (opTrace (E*C*E)).re = hsNormSq A
    rw [hpositive,← hcycle]
    exact ContinuousLinearMap.re_opTrace_adjoint_comp_self hA

end RHTower
