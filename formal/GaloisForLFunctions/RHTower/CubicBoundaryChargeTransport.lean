import GaloisForLFunctions.RHTower.TraceClassProjectionRounding
import GaloisForLFunctions.RHTower.CubicAggregateSpectralCurrent

/-!
# Cubic boundary charge from source projections

Under nuclear cutoff commutators, compressing three source projections and rounding them modulo
trace class produces genuine orthogonal projections. If the source aggregate commutes with its
cyclic current, the combined cubic is nuclear and its trace is exactly half the source boundary
pairing. Source flatness is not replaced by separate trace admission of the cubic channels.

This is a general source-to-boundary comparison theorem. It neither constructs the explicit
nonzero Schwartz loop nor identifies such a loop with the Xi divisor or a prime-labelled source.
-/

noncomputable section
namespace RHTower
open ContinuousLinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem trace_nuclear_projection_compression
    (Q T : H →L[ℂ] H) (hQ : IsIdempotentElem Q) (hT : MemSchattenClass 1 T) :
    opTrace (Q*T*Q) = opTrace (T*Q) := by
  have hTQ := memSchattenClass_one_comp_right hT Q
  have h := hTQ.one_opTrace_comp_comm Q
  change opTrace (Q*(T*Q)) = opTrace ((T*Q)*Q) at h
  have hQQ : Q*Q = Q := hQ
  simpa only [← mul_assoc, show T*Q*Q = T*Q by rw [mul_assoc, hQQ]] using h

/-- The trace of a compressed commuting source pair is its literal boundary pairing.
Only the cutoff commutator of the second source is required to be nuclear. -/
theorem nuclear_compressed_commutator_trace
    (Q A B : H →L[ℂ] H) (hQ : IsIdempotentElem Q) (hAB : A*B = B*A)
    (hD : MemSchattenClass 1 (Q*B-B*Q)) :
    MemSchattenClass 1 ((Q*A*Q)*(Q*B*Q)-(Q*B*Q)*(Q*A*Q)) ∧
      opTrace ((Q*A*Q)*(Q*B*Q)-(Q*B*Q)*(Q*A*Q)) = opTrace (A*(Q*B-B*Q)) := by
  let D := Q*B-B*Q
  change MemSchattenClass 1 D at hD
  have hQQ : Q*Q = Q := hQ
  have hQAQ : Q*(Q*A) = Q*A := by rw [← mul_assoc, hQQ]
  have hQBQ : Q*(Q*B) = Q*B := by rw [← mul_assoc, hQQ]
  have hDQ : D*Q+Q*D = D := by
    dsimp [D]
    noncomm_ring [hQQ, hQBQ]
  have heq : (Q*A*Q)*(Q*B*Q)-(Q*B*Q)*(Q*A*Q) = Q*(A*D)*Q+Q*(D*A)*Q := by
    have hleft : (Q*A*Q)*(Q*B*Q) = Q*A*Q*B*Q := by
      calc _ = Q*A*(Q*Q)*B*Q := by noncomm_ring
           _ = _ := by rw [hQQ]
    have hright : (Q*B*Q)*(Q*A*Q) = Q*B*Q*A*Q := by
      calc _ = Q*B*(Q*Q)*A*Q := by noncomm_ring
           _ = _ := by rw [hQQ]
    rw [hleft, hright]
    dsimp [D]
    have hQBA : Q*(B*A) = Q*(A*B) := by rw [hAB]
    have hQQBA : Q*(Q*(B*A)) = Q*(B*A) := by rw [← mul_assoc, hQQ]
    have hQQABQ : Q*(Q*(A*(B*Q))) = Q*(A*(B*Q)) := by rw [← mul_assoc, hQQ]
    noncomm_ring [hQQ, hQQBA, hQBA, hQQABQ]
  have hAD : MemSchattenClass 1 (A*D) := memSchattenClass_one_comp_left hD A
  have hDA : MemSchattenClass 1 (D*A) := memSchattenClass_one_comp_right hD A
  have hcAD : MemSchattenClass 1 (Q*(A*D)*Q) :=
    memSchattenClass_one_comp_right (memSchattenClass_one_comp_left hAD Q) Q
  have hcDA : MemSchattenClass 1 (Q*(D*A)*Q) :=
    memSchattenClass_one_comp_right (memSchattenClass_one_comp_left hDA Q) Q
  rw [heq]
  refine ⟨hcAD.one_add hcDA, ?_⟩
  rw [opTrace_add_of_memSchattenClass_one hcAD hcDA,
    trace_nuclear_projection_compression Q (A*D) hQ hAD,
    trace_nuclear_projection_compression Q (D*A) hQ hDA]
  have hcyc := hD.one_opTrace_comp_comm (A*Q)
  change opTrace ((A*Q)*D) = opTrace (D*(A*Q)) at hcyc
  rw [mul_assoc D A Q, ← hcyc]
  have hADQ : MemSchattenClass 1 ((A*D)*Q) := memSchattenClass_one_comp_right hAD Q
  have hAQD : MemSchattenClass 1 ((A*Q)*D) := memSchattenClass_one_comp_left hD (A*Q)
  rw [← opTrace_add_of_memSchattenClass_one hADQ hAQD]
  have hs : (A*D)*Q+(A*Q)*D = A*D := by
    rw [mul_assoc, mul_assoc, ← mul_add, hDQ]
  rw [hs]

/-- A source projection with nuclear cutoff commutator compresses to an almost-projection
that admits an orthogonal projection lift modulo trace class. -/
theorem projection_compression_has_nuclear_rounding
    (Q P : H →L[ℂ] H) (hQ : IsIdempotentElem Q) (hP : IsIdempotentElem P)
    (hQs : IsSelfAdjoint Q) (hPs : IsSelfAdjoint P)
    (hD : MemSchattenClass 1 (Q*P-P*Q)) :
    ∃ R : H →L[ℂ] H, IsSelfAdjoint R ∧ IsIdempotentElem R ∧
      MemSchattenClass 1 (R-Q*P*Q) := by
  apply exists_projection_traceClass_perturbation
  · show star (Q*P*Q) = Q*P*Q
    simp only [star_mul, hQs.star_eq, hPs.star_eq, mul_assoc]
  · have hQQ : Q*Q = Q := hQ
    have hPP : P*P = P := hP
    have hsq : (Q*P*Q)*(Q*P*Q) = Q*P*Q*P*Q := by
      calc _ = Q*P*(Q*Q)*P*Q := by noncomm_ring
           _ = _ := by rw [hQQ]
    have heq : Q*P*Q-(Q*P*Q)*(Q*P*Q) = -(Q*P*(Q*P-P*Q)*Q) := by
      rw [hsq]
      have hPPQ : P*(P*Q) = P*Q := by rw [← mul_assoc, hPP]
      noncomm_ring [hPPQ, hQQ]
    rw [heq]
    exact (memSchattenClass_one_comp_right
      (memSchattenClass_one_comp_left hD (Q*P)) Q).one_neg

omit [CompleteSpace H] in
private theorem nuclear_mul_congr (A B X Y : H →L[ℂ] H)
    (hA : MemSchattenClass 1 (A-X)) (hB : MemSchattenClass 1 (B-Y)) :
    MemSchattenClass 1 (A*B-X*Y) := by
  have h1 : MemSchattenClass 1 ((A-X)*B) := memSchattenClass_one_comp_right hA B
  have h2 : MemSchattenClass 1 (X*(B-Y)) := memSchattenClass_one_comp_left hB X
  convert h1.one_add h2 using 1
  noncomm_ring

omit [CompleteSpace H] in
private theorem cut_nuclear_mul (E A B : H →L[ℂ] H)
    (hA : MemSchattenClass 1 (E*A-A*E)) (hB : MemSchattenClass 1 (E*B-B*E)) :
    MemSchattenClass 1 (E*(A*B)-(A*B)*E) := by
  have h1 : MemSchattenClass 1 ((E*A-A*E)*B) := memSchattenClass_one_comp_right hA B
  have h2 : MemSchattenClass 1 (A*(E*B-B*E)) := memSchattenClass_one_comp_left hB A
  convert h1.one_add h2 using 1
  noncomm_ring

omit [CompleteSpace H] in
private theorem compression_pair_defect (E A B : H →L[ℂ] H)
    (hE : IsIdempotentElem E) (hB : MemSchattenClass 1 (E*B-B*E)) :
    MemSchattenClass 1 ((E*A*E)*(E*B*E)-E*(A*B)*E) := by
  have hEE : E*E = E := hE
  have hprod : (E*A*E)*(E*B*E) = E*A*E*B*E := by
    calc _ = E*A*(E*E)*B*E := by noncomm_ring
         _ = _ := by rw [hEE]
  have heq : (E*A*E)*(E*B*E)-E*(A*B)*E = E*A*(E*B-B*E)*E := by
    rw [hprod]
    noncomm_ring [hEE]
  rw [heq]
  exact memSchattenClass_one_comp_right (memSchattenClass_one_comp_left hB (E*A)) E

private theorem rounded_pair_landing (E A B P Q : H →L[ℂ] H)
    (hE : IsIdempotentElem E)
    (hA : MemSchattenClass 1 (E*A-A*E)) (hB : MemSchattenClass 1 (E*B-B*E))
    (hP : MemSchattenClass 1 (P-E*A*E)) (hQ : MemSchattenClass 1 (Q-E*B*E)) :
    MemSchattenClass 1 ((P*Q-Q*P)-E*(A*B-B*A)*E) := by
  have h1 := (nuclear_mul_congr P Q (E*A*E) (E*B*E) hP hQ).one_add
    (compression_pair_defect E A B hE hB)
  have h2 := (nuclear_mul_congr Q P (E*B*E) (E*A*E) hQ hP).one_add
    (compression_pair_defect E B A hE hA)
  convert h1.one_sub h2 using 1
  noncomm_ring

/-- Construct genuine projections from a source triple and retain the exact boundary charge.
Flatness of the source aggregate/current pair supplies admission of the combined cubic, while
its charge is the source cutoff pairing. No RH or separate cubic admission is assumed. -/
theorem exists_rounded_cubic_with_boundary_trace
    (E A B C : H →L[ℂ] H)
    (hE : IsIdempotentElem E) (hEs : IsSelfAdjoint E)
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B) (hC : IsIdempotentElem C)
    (hAs : IsSelfAdjoint A) (hBs : IsSelfAdjoint B) (hCs : IsSelfAdjoint C)
    (hEA : MemSchattenClass 1 (E*A-A*E))
    (hEB : MemSchattenClass 1 (E*B-B*E))
    (hEC : MemSchattenClass 1 (E*C-C*E))
    (hflat : cubicAggregate A B C * cubicCyclicCurrent A B C =
      cubicCyclicCurrent A B C * cubicAggregate A B C) :
    ∃ P Q R : H →L[ℂ] H,
      IsSelfAdjoint P ∧ IsSelfAdjoint Q ∧ IsSelfAdjoint R ∧
      IsIdempotentElem P ∧ IsIdempotentElem Q ∧ IsIdempotentElem R ∧
      MemSchattenClass 1 (P-E*A*E) ∧ MemSchattenClass 1 (Q-E*B*E) ∧
      MemSchattenClass 1 (R-E*C*E) ∧
      MemSchattenClass 1 (formationAnchoredCubicAssociator R Q P) ∧
      (2 : ℂ) * opTrace (formationAnchoredCubicAssociator R Q P) =
        opTrace (cubicAggregate A B C *
          (E*cubicCyclicCurrent A B C-cubicCyclicCurrent A B C*E)) := by
  obtain ⟨P,hPs,hPi,hP⟩ := projection_compression_has_nuclear_rounding E A hE hA hEs hAs hEA
  obtain ⟨Q,hQs,hQi,hQ⟩ := projection_compression_has_nuclear_rounding E B hE hB hEs hBs hEB
  obtain ⟨R,hRs,hRi,hR⟩ := projection_compression_has_nuclear_rounding E C hE hC hEs hCs hEC
  have hS : MemSchattenClass 1 (cubicAggregate P Q R-E*cubicAggregate A B C*E) := by
    convert (hP.one_add hQ).one_add hR using 1
    dsimp [cubicAggregate]
    noncomm_ring
  have hPQ := rounded_pair_landing E A B P Q hE hEA hEB hP hQ
  have hQR := rounded_pair_landing E B C Q R hE hEB hEC hQ hR
  have hRP := rounded_pair_landing E C A R P hE hEC hEA hR hP
  have hK : MemSchattenClass 1 (cubicCyclicCurrent P Q R-E*cubicCyclicCurrent A B C*E) := by
    convert (hPQ.one_add hQR).one_add hRP using 1
    dsimp [cubicCyclicCurrent]
    noncomm_ring
  have hAB := (cut_nuclear_mul E A B hEA hEB).one_sub (cut_nuclear_mul E B A hEB hEA)
  have hBC := (cut_nuclear_mul E B C hEB hEC).one_sub (cut_nuclear_mul E C B hEC hEB)
  have hCA := (cut_nuclear_mul E C A hEC hEA).one_sub (cut_nuclear_mul E A C hEA hEC)
  have hEK : MemSchattenClass 1 (E*cubicCyclicCurrent A B C-cubicCyclicCurrent A B C*E) := by
    convert (hAB.one_add hBC).one_add hCA using 1
    dsimp [cubicCyclicCurrent]
    noncomm_ring
  have hbase := nuclear_compressed_commutator_trace E
    (cubicAggregate A B C) (cubicCyclicCurrent A B C) hE hflat hEK
  have hcorr := traceClass_commutator_perturbation_invariance
    (E*cubicAggregate A B C*E) (E*cubicCyclicCurrent A B C*E)
    (cubicAggregate P Q R-E*cubicAggregate A B C*E)
    (cubicCyclicCurrent P Q R-E*cubicCyclicCurrent A B C*E) hbase.1 hS hK
  have hsimp : E*cubicAggregate A B C*E+
      (cubicAggregate P Q R-E*cubicAggregate A B C*E) = cubicAggregate P Q R := by abel
  have ksimp : E*cubicCyclicCurrent A B C*E+
      (cubicCyclicCurrent P Q R-E*cubicCyclicCurrent A B C*E) = cubicCyclicCurrent P Q R := by abel
  rw [hsimp, ksimp, cubicAggregate_commutator P Q R hPi hQi hRi] at hcorr
  have hhalf : (1/2 : ℂ) •
      (formationAnchoredCubicAssociator R Q P+formationAnchoredCubicAssociator R Q P) =
        formationAnchoredCubicAssociator R Q P := by
    rw [smul_add, ← add_smul]
    norm_num
  have hcharged := memSchattenClass_one_smul hcorr.1 (1/2 : ℂ)
  rw [hhalf] at hcharged
  refine ⟨P,Q,R,hPs,hQs,hRs,hPi,hQi,hRi,hP,hQ,hR,hcharged,?_⟩
  have ht := hcorr.2.trans hbase.2
  rw [opTrace_add_of_memSchattenClass_one hcharged hcharged] at ht
  linear_combination ht

end RHTower
