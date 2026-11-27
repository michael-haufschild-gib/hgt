import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EigenstatePreparation.BellBlocks.Stationarity

/-! # One-spin signals of a guarded Bell dimer -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

private theorem commute_test (R J T C : Mat I) (hRT : Commute R T) (hRC : Commute R C)
    (hJT : Commute J T) :
    (R+J)*(T*C)-(T*C)*(R+J)=T*(J*C-C*J) := by
  rw [add_mul,mul_add,(hRT.mul_right hRC).eq,add_sub_add_left_eq_sub,←mul_assoc,hJT.eq,
    mul_assoc,mul_assoc,mul_sub]

private theorem signal_of_multiple (H : selfAdjoint (Mat I)) (J L C : Mat I)
    (i : I) (q : ℕ) (hq : 0<q) (h : J*L-L*J=q • C) (hL : 2*‖L‖≤q) :
    ‖energyDiagonal H C i‖≤‖J-H.val‖ := by
  have hx := commutator_signal H J L i
  rw [h] at hx
  have he : energyDiagonal H (q • C) i=q • energyDiagonal H C i := by
    simp only [energyDiagonal,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_apply]
  rw [he,nsmul_eq_mul,norm_mul,Complex.norm_natCast] at hx
  have hd := mul_le_mul_of_nonneg_left hL (norm_nonneg (J-H.val))
  have hq' : 0<(q:ℝ) := by exact_mod_cast hq
  apply (mul_le_mul_iff_right₀ hq').mp
  calc _ ≤ _ := hx
       _ = ‖J-H.val‖*(2*‖L‖) := by ring
       _ ≤ _ := hd.trans_eq (mul_comm ..)

/-- For J = A + 2B, a Pauli commuting with A and anticommuting with B
is the commutator with BC/4. The spectator can have arbitrary spectrum. -/
theorem commuting_first_signal (H : selfAdjoint (Mat I)) (R A B C : Mat I) (i : I)
    (hab : Commute A B) (hrb : Commute R B) (hrc : Commute R C)
    (hca : Commute C A) (hcb : C*B=-(B*C)) (hB : B*B=1)
    (hnB : ‖B‖≤1) (hnC : ‖C‖≤1) :
    ‖energyDiagonal H C i‖≤‖(R+(A+(B+B)))-H.val‖ := by
  let J := A+(B+B)
  have hj : Commute J B := hab.add_left ((Commute.refl B).add_left (Commute.refl B))
  have h := commute_test R J B C hrb hrc hj
  have hsq : B*(B*C)=C := by rw [←mul_assoc,hB,one_mul]
  apply signal_of_multiple H (R+J) (B*C) C i 4 (by decide)
  · rw [h]
    dsimp only [J]
    rw [add_mul,add_mul,mul_add,mul_add,hca.eq,hcb]
    have hd : A*C+(B*C+B*C)-(A*C+(-(B*C)+ -(B*C)))=B*C+B*C+(B*C+B*C) := by abel
    rw [hd,mul_add,mul_add,hsq]
    abel
  · have hn := (norm_mul_le B C).trans ((mul_le_mul hnB hnC (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
    linarith only [hn]

/-- A Pauli anticommuting with A and commuting with B uses AC/2. -/
theorem commuting_second_signal (H : selfAdjoint (Mat I)) (R A B C : Mat I) (i : I)
    (hab : Commute A B) (hra : Commute R A) (hrc : Commute R C)
    (hca : C*A=-(A*C)) (hcb : Commute C B) (hA : A*A=1)
    (hnA : ‖A‖≤1) (hnC : ‖C‖≤1) :
    ‖energyDiagonal H C i‖≤‖(R+(A+(B+B)))-H.val‖ := by
  let J := A+(B+B)
  have hj : Commute J A := (Commute.refl A).add_left (hab.symm.add_left hab.symm)
  have h := commute_test R J A C hra hrc hj
  have hsq : A*(A*C)=C := by rw [←mul_assoc,hA,one_mul]
  apply signal_of_multiple H (R+J) (A*C) C i 2 (by decide)
  · rw [h]
    dsimp only [J]
    rw [add_mul,add_mul,mul_add,mul_add,hca,hcb.eq]
    have hd : A*C+(B*C+B*C)-(-(A*C)+(B*C+B*C))=A*C+A*C := by abel
    rw [hd,mul_add,hsq,two_nsmul]
  · have hn := (norm_mul_le A C).trans ((mul_le_mul hnA hnC (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
    linarith only [hn]

/-- When both stabilizers anticommute with the probe, the inverse of
twice J on that commutator is (2B − A)/6. -/
theorem anticommuting_signal (H : selfAdjoint (Mat I)) (R A B C : Mat I) (i : I)
    (hab : Commute A B) (hra : Commute R A) (hrb : Commute R B) (hrc : Commute R C)
    (hca : C*A=-(A*C)) (hcb : C*B=-(B*C)) (hA : A*A=1) (hB : B*B=1)
    (hnA : ‖A‖≤1) (hnB : ‖B‖≤1) (hnC : ‖C‖≤1) :
    ‖energyDiagonal H C i‖≤‖(R+(A+(B+B)))-H.val‖ := by
  let J := A+(B+B)
  let T := (B+B)-A
  have hjA : Commute J A := (Commute.refl A).add_left (hab.symm.add_left hab.symm)
  have hjB : Commute J B := hab.add_left ((Commute.refl B).add_left (Commute.refl B))
  have h := commute_test R J T C ((hrb.add_right hrb).sub_right hra) hrc
    ((hjB.add_right hjB).sub_right hjA)
  have hTJ : T*J=(1:Mat I)+1+1 := by
    dsimp only [T,J]
    simp only [sub_mul,add_mul,mul_add,hab.eq,hA,hB]
    abel
  have hCJ : C*J= -(J*C) := by
    simp only [J,mul_add,add_mul,hca,hcb,neg_add_rev]
    abel
  apply signal_of_multiple H (R+J) (T*C) C i 6 (by decide)
  · rw [h,hCJ,sub_neg_eq_add,mul_add,←mul_assoc,hTJ,add_mul,add_mul,one_mul]
    abel
  · have hT : ‖T‖≤3 := (norm_sub_le _ _).trans (by linarith only [norm_add_le B B,hnA,hnB])
    have hn := (norm_mul_le T C).trans ((mul_le_mul hT hnC (norm_nonneg _) (by norm_num)).trans_eq (mul_one _))
    linarith only [hn]

#print axioms anticommuting_signal
end
end GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
