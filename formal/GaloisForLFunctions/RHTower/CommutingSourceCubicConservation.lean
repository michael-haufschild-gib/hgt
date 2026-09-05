import GaloisForLFunctions.RHTower.FormationAnchoredCubicHomotopyDefect
import GaloisForLFunctions.RHTower.TraceClassCompressionCurvature

/-!
Commuting-source cubic conservation without compact displacement.

Paper proof. For commuting orthogonal P,Q and orthogonal R, set
U=Q-PQ, V=P-PQ, W=I-U-V, A=WRU, B=WRV, J=VRU,
C=(R-P)^3-(R-Q)^3-(Q-P)^3. The joint source projections U,V,W are
orthogonal and sum to I. Projection algebra gives
  UCU=-(A* A+2 J* J), VCV=B* B+2 J J*, WCW=A A*-B B*.
If C is nuclear, the negative U-compression has a summable nonnegative
basis diagonal, which forces A and J Hilbert--Schmidt. Subtracting the
now-nuclear J terms from VCV makes B* B nuclear, hence B Hilbert--Schmidt.
Nuclear pinching and Hilbert--Schmidt cyclicity cancel every transition
in Tr C; the three real block traces are -a-2j, b+2j, a-b, respectively.

This strengthens the nested-source obstruction F660/CANNOT-296. No
compactness or Schatten admission of the individual displacements is used.
It closes the nonnested-but-commuting variant of this ordinary cubic charge,
not an RH implication. No literal arithmetic projection model is supplied.
This is an operator-theoretic bridge; no priority or new-field claim is made.
-/

noncomputable section
namespace RHTower
open ContinuousLinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem hsGram_nuclear (A : H →L[ℂ] H) (hA : A.IsHilbertSchmidt) :
    MemSchattenClass 1 (adjoint A*A) := by
  have hrect := memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hA hA.adjoint
  exact (memRectSchattenClass_iff_memSchattenClass 1 (adjoint A ∘L A)).mp hrect

private theorem trace_idempotent_left
    (D C : H →L[ℂ] H) (hD : D*D=D) (hC : MemSchattenClass 1 C) :
    opTrace (D*C) = opTrace (D*C*D) := by
  have hd : MemSchattenClass 1 (D*C) := memSchattenClass_one_comp_left hC D
  have h := hd.one_opTrace_comp_comm D
  change opTrace (D*(D*C)) = opTrace ((D*C)*D) at h
  simpa only [← mul_assoc,hD] using h

private theorem trace_three_idempotent_pinching
    (U V W C : H →L[ℂ] H) (hU : U*U=U) (hV : V*V=V) (hW : W*W=W)
    (hsum : U+V+W=1) (hC : MemSchattenClass 1 C) :
    opTrace C = opTrace (U*C*U)+opTrace (V*C*V)+opTrace (W*C*W) := by
  have hu : MemSchattenClass 1 (U*C) := memSchattenClass_one_comp_left hC U
  have hv : MemSchattenClass 1 (V*C) := memSchattenClass_one_comp_left hC V
  have hw : MemSchattenClass 1 (W*C) := memSchattenClass_one_comp_left hC W
  have huv := memSchattenClass_one_add (hu.isCompactOperator one_pos)
    (hv.isCompactOperator one_pos) hu hv
  calc
    opTrace C = opTrace (U*C+V*C+W*C) := by
      congr 1
      rw [← add_mul,← add_mul,hsum,one_mul]
    _ = opTrace (U*C)+opTrace (V*C)+opTrace (W*C) := by
      rw [opTrace_add_of_memSchattenClass_one huv hw,opTrace_add_of_memSchattenClass_one hu hv]
    _ = _ := by rw [trace_idempotent_left U C hU hC,
      trace_idempotent_left V C hV hC,trace_idempotent_left W C hW hC]

/-- Only nuclearity of the combined cubic defect is assumed. Commuting source projections
force three finite transition energies and zero ordinary charge, without nesting or compact
individual displacements. -/
theorem commutingSourceCubicAssociator_nuclear_conservation
    (R Q P : H →L[ℂ] H)
    (hR : R*R=R) (hQ : Q*Q=Q) (hP : P*P=P)
    (hRadj : adjoint R=R) (hQadj : adjoint Q=Q) (hPadj : adjoint P=P)
    (hcomm : P*Q=Q*P)
    (hC : MemSchattenClass 1 (formationAnchoredCubicAssociator R Q P)) :
    let U := Q-P*Q
    let V := P-P*Q
    let W := 1-U-V
    let A := W*R*U
    let B := W*R*V
    let J := V*R*U
    let C := formationAnchoredCubicAssociator R Q P
    A.IsHilbertSchmidt ∧ B.IsHilbertSchmidt ∧ J.IsHilbertSchmidt ∧
      opTrace C=0 ∧
      (opTrace (U*C*U)).re = -hsNormSq A-2*hsNormSq J ∧
      (opTrace (V*C*V)).re = hsNormSq B+2*hsNormSq J ∧
      (opTrace (W*C*W)).re = hsNormSq A-hsNormSq B := by
  let S := P*Q
  let U := Q-S
  let V := P-S
  let W : H →L[ℂ] H := 1-U-V
  let A := W*R*U
  let B := W*R*V
  let J := V*R*U
  let C := formationAnchoredCubicAssociator R Q P
  have hPS : P*S=S := by dsimp [S]; rw [← mul_assoc,hP]
  have hSQ : S*Q=S := by dsimp [S]; rw [mul_assoc,hQ]
  have hSP : S*P=S := by
    change (P*Q)*P=S
    rw [mul_assoc,← hcomm]
    exact hPS
  have hQS : Q*S=S := by
    change Q*(P*Q)=S
    rw [← mul_assoc,← hcomm]
    exact hSQ
  have hS : S*S=S := by
    change S*(P*Q)=S
    rw [← mul_assoc,hSP,hSQ]
  have hU : U*U=U := by dsimp only [U]; noncomm_ring [hQ,hS,hQS,hSQ]
  have hV : V*V=V := by dsimp only [V]; noncomm_ring [hP,hS,hPS,hSP]
  have hUV : U*V=0 := by
    calc
      _ = Q*P-S := by dsimp only [U,V]; noncomm_ring [hQS,hSP,hS]
      _ = 0 := by rw [← hcomm]; exact sub_self _
  have hVU : V*U=0 := by
    calc
      _ = P*Q-S := by dsimp only [U,V]; noncomm_ring [hPS,hSQ,hS]
      _ = 0 := sub_self _
  have hW : W*W=W := by dsimp only [W]; noncomm_ring [hU,hV,hUV,hVU]
  have hUP : U*P=0 := by
    dsimp only [U]; rw [sub_mul,hSP,← hcomm]; exact sub_self _
  have hPU : P*U=0 := by dsimp only [U]; rw [mul_sub,hPS]; exact sub_self _
  have hUQ : U*Q=U := by dsimp only [U]; rw [sub_mul,hQ,hSQ]
  have hQU : Q*U=U := by dsimp only [U]; rw [mul_sub,hQ,hQS]
  have hVP : V*P=V := by dsimp only [V]; rw [sub_mul,hP,hSP]
  have hPV : P*V=V := by dsimp only [V]; rw [mul_sub,hP,hPS]
  have hVQ : V*Q=0 := by dsimp only [V]; rw [sub_mul,hSQ]; exact sub_self _
  have hQV : Q*V=0 := by
    dsimp only [V]; rw [mul_sub,hQS,← hcomm]; exact sub_self _
  have hWP : W*P=S := by
    dsimp only [W]; rw [sub_mul,sub_mul,one_mul,hUP,hVP,sub_zero]
    dsimp only [V]; abel
  have hPW : P*W=S := by
    dsimp only [W]; rw [mul_sub,mul_sub,mul_one,hPU,hPV,sub_zero]
    dsimp only [V]; abel
  have hWQ : W*Q=S := by
    dsimp only [W]; rw [sub_mul,sub_mul,one_mul,hUQ,hVQ,sub_zero]
    dsimp only [U]; abel
  have hQW : Q*W=S := by
    dsimp only [W]; rw [mul_sub,mul_sub,mul_one,hQU,hQV,sub_zero]
    dsimp only [U]; abel
  have hSadj : adjoint S=S := by
    change adjoint (P ∘L Q)=S
    rw [adjoint_comp,hPadj,hQadj]
    exact hcomm.symm
  have hUadj : adjoint U=U := by dsimp only [U]; rw [map_sub,hQadj,hSadj]
  have hVadj : adjoint V=V := by dsimp only [V]; rw [map_sub,hPadj,hSadj]
  have hWadj : adjoint W=W := by
    dsimp only [W]; rw [map_sub,map_sub,adjoint_one,hUadj,hVadj]
  have hadj (X Y : H →L[ℂ] H) (hx : adjoint X=X) (hy : adjoint Y=Y) :
      adjoint (X*R*Y)=Y*R*X := by
    change adjoint ((X ∘L R) ∘L Y)=Y*R*X
    rw [adjoint_comp,adjoint_comp,hx,hy,hRadj]; rfl
  have hAadj : adjoint A=U*R*W := hadj W U hWadj hUadj
  have hBadj : adjoint B=V*R*W := hadj W V hWadj hVadj
  have hJadj : adjoint J=U*R*V := hadj V U hVadj hUadj
  have hgram (X Y : H →L[ℂ] H) (hy : Y*Y=Y) :
      (X*R*Y)*(Y*R*X)=X*R*Y*R*X := by
    calc
      _ = X*R*(Y*Y)*R*X := by noncomm_ring
      _ = _ := by rw [hy]
  have hAA : adjoint A*A=U*R*W*R*U := by rw [hAadj]; exact hgram U W hW
  have hBB : adjoint B*B=V*R*W*R*V := by rw [hBadj]; exact hgram V W hW
  have hJJ : adjoint J*J=U*R*V*R*U := by rw [hJadj]; exact hgram U V hV
  have hAA' : A*adjoint A=W*R*U*R*W := by rw [hAadj]; exact hgram W U hU
  have hBB' : B*adjoint B=W*R*V*R*W := by rw [hBadj]; exact hgram W V hV
  have hJJ' : J*adjoint J=V*R*U*R*V := by rw [hJadj]; exact hgram V U hU
  have hPQP : P*Q*P=S := hSP
  have hQPQ : Q*P*Q=S := by rw [← hcomm]; exact hSQ
  have hform : C=R*(U-V)*R+P*R*P-Q*R*Q := by
    dsimp only [C,U,V,formationAnchoredCubicAssociator,formationAnchoredCubicDefect,
      restrictedProjectionCubicDefect,restrictedProjectionDisplacement]
    noncomm_ring [hR,hQ,hP,hPQP,hQPQ]
  have hRRU : R*(R*U)=R*U := by rw [← mul_assoc,hR]
  have hRRV : R*(R*V)=R*V := by rw [← mul_assoc,hR]
  have hnegative : U*C*U=-(adjoint A*A+adjoint J*J+adjoint J*J) := by
    rw [hform,hAA,hJJ]
    calc
      _ = U*R*(U-V)*R*U+(U*P)*R*(P*U)-(U*Q)*R*(Q*U) := by noncomm_ring
      _ = U*R*(U-V)*R*U-U*R*U := by rw [hUP,hUQ,hQU]; simp
      _ = _ := by dsimp only [W]; noncomm_ring [hRRU]
  have hpositive : V*C*V=adjoint B*B+J*adjoint J+J*adjoint J := by
    rw [hform,hBB,hJJ']
    calc
      _ = V*R*(U-V)*R*V+(V*P)*R*(P*V)-(V*Q)*R*(Q*V) := by noncomm_ring
      _ = V*R*(U-V)*R*V+V*R*V := by rw [hVQ,hVP,hPV]; simp
      _ = _ := by dsimp only [W]; noncomm_ring [hRRV]
  have hmiddle : W*C*W=A*adjoint A-B*adjoint B := by
    rw [hform,hAA',hBB']
    calc
      _ = W*R*(U-V)*R*W+(W*P)*R*(P*W)-(W*Q)*R*(Q*W) := by noncomm_ring
      _ = _ := by rw [hWP,hPW,hWQ,hQW]; noncomm_ring

  have hc (X : H →L[ℂ] H) : MemSchattenClass 1 (X*C*X) :=
    memSchattenClass_one_comp_right (memSchattenClass_one_comp_left hC X) X
  have hsumGram : MemSchattenClass 1 (adjoint A*A+adjoint J*J+adjoint J*J) := by
    have hn := hc U
    rw [hnegative] at hn
    simpa only [neg_one_smul,neg_neg] using memSchattenClass_one_smul hn (-1 : ℂ)
  have hdiag := hsumGram.one_summable_inner_diag
  have hsum : Summable (fun i => ‖A (hsBasis ℂ H i)‖^2 +
      ‖J (hsBasis ℂ H i)‖^2+‖J (hsBasis ℂ H i)‖^2) := by
    rw [← RCLike.summable_ofReal (𝕜 := ℂ)]
    refine hdiag.congr fun i => ?_
    simp only [add_apply,inner_add_right,mul_apply_eq_comp,
      adjoint_inner_right,inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hA : A.IsHilbertSchmidt := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ?_ hsum
    intro i
    nlinarith only [sq_nonneg ‖J (hsBasis ℂ H i)‖]
  have hJ : J.IsHilbertSchmidt := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ?_ hsum
    intro i
    nlinarith only [sq_nonneg ‖A (hsBasis ℂ H i)‖,sq_nonneg ‖J (hsBasis ℂ H i)‖]
  have hAAt := hsGram_nuclear A hA
  have hJJt := hsGram_nuclear J hJ
  have hJ'Jt : MemSchattenClass 1 (J*adjoint J) := by
    simpa only [adjoint_adjoint] using hsGram_nuclear (adjoint J) hJ.adjoint
  have hBBt : MemSchattenClass 1 (adjoint B*B) := by
    have hv := hc V
    rw [hpositive] at hv
    convert (hv.one_sub hJ'Jt).one_sub hJ'Jt using 1
    abel
  have hB := isHilbertSchmidt_of_adjoint_mul_self_memSchattenClass_one B hBBt
  have hA'At : MemSchattenClass 1 (A*adjoint A) := by
    simpa only [adjoint_adjoint] using hsGram_nuclear (adjoint A) hA.adjoint
  have hB'Bt : MemSchattenClass 1 (B*adjoint B) := by
    simpa only [adjoint_adjoint] using hsGram_nuclear (adjoint B) hB.adjoint
  have hAJt := memSchattenClass_one_add (hAAt.isCompactOperator one_pos)
    (hJJt.isCompactOperator one_pos) hAAt hJJt
  have hBJt := memSchattenClass_one_add (hBBt.isCompactOperator one_pos)
    (hJ'Jt.isCompactOperator one_pos) hBBt hJ'Jt
  have htraceU : opTrace (U*C*U) = -(opTrace (adjoint A*A)+
      opTrace (adjoint J*J)+opTrace (adjoint J*J)) := by
    rw [hnegative,opTrace_neg,opTrace_add_of_memSchattenClass_one hAJt hJJt,
      opTrace_add_of_memSchattenClass_one hAAt hJJt]
  have hcycleA : opTrace (adjoint A*A)=opTrace (A*adjoint A) :=
    ContinuousLinearMap.opTrace_comp_comm hA.adjoint hA
  have hcycleB : opTrace (adjoint B*B)=opTrace (B*adjoint B) :=
    ContinuousLinearMap.opTrace_comp_comm hB.adjoint hB
  have hcycleJ : opTrace (adjoint J*J)=opTrace (J*adjoint J) :=
    ContinuousLinearMap.opTrace_comp_comm hJ.adjoint hJ
  have htraceV : opTrace (V*C*V) = opTrace (adjoint B*B)+
      opTrace (adjoint J*J)+opTrace (adjoint J*J) := by
    rw [hpositive,opTrace_add_of_memSchattenClass_one hBJt hJ'Jt,
      opTrace_add_of_memSchattenClass_one hBBt hJ'Jt,← hcycleJ]
  have htraceW : opTrace (W*C*W) = opTrace (adjoint A*A)-opTrace (adjoint B*B) := by
    rw [hmiddle,opTrace_sub_of_memSchattenClass_one hA'At hB'Bt,← hcycleA,← hcycleB]
  have htrace : opTrace C=0 := by
    rw [trace_three_idempotent_pinching U V W C hU hV hW
      (by dsimp only [W]; abel) hC,htraceU,htraceV,htraceW]
    abel
  have henergyA : (opTrace (adjoint A*A)).re=hsNormSq A :=
    re_opTrace_adjoint_comp_self hA
  have henergyB : (opTrace (adjoint B*B)).re=hsNormSq B :=
    re_opTrace_adjoint_comp_self hB
  have henergyJ : (opTrace (adjoint J*J)).re=hsNormSq J :=
    re_opTrace_adjoint_comp_self hJ
  refine ⟨hA,hB,hJ,htrace,?_,?_,?_⟩
  · change (opTrace (U*C*U)).re = -hsNormSq A-2*hsNormSq J
    rw [htraceU,Complex.neg_re,Complex.add_re,Complex.add_re,
      henergyA,henergyJ]
    ring
  · change (opTrace (V*C*V)).re = hsNormSq B+2*hsNormSq J
    rw [htraceV,Complex.add_re,Complex.add_re,
      henergyB,henergyJ]
    ring
  · change (opTrace (W*C*W)).re = hsNormSq A-hsNormSq B
    rw [htraceW,Complex.sub_re,henergyA,henergyB]

end RHTower

