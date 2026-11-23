import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleRotation

/-! # Directed signals of a quarter turn about two anticommuting bonds -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
noncomputable section
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]

/-- A local probe anticommutes with exactly one of the two bonds. -/
def oddProbe (A B P : R) : Prop :=
  (A*P=-(P*A) ∧ Commute B P) ∨ (Commute A P ∧ B*P=-(P*B))

omit [NormedAlgebra ℂ R] in
private theorem odd_product {A B Q : R} (h : oddProbe A B Q) : A*B*Q=-(Q*(A*B)) := by
  rcases h with ⟨hA,hB⟩|⟨hA,hB⟩
  · rw [mul_assoc,hB.eq,←mul_assoc,hA,neg_mul,mul_assoc]
  · rw [mul_assoc,hB,mul_neg,←mul_assoc,hA.eq,mul_assoc]

/-- Under the quarter turn every such probe acquires the bond product
up to a sign. It anticommutes with every commuting odd probe. -/
theorem mix_exchange (A B P Q : R) (ha : A*A=1) (hb : B*B=1) (hab : A*B=-(B*A))
    (hp : oddProbe A B P) (hq : oddProbe A B Q) (hc : Commute P Q) :
    (mix A B*P*mix A B)*Q=-(Q*(mix A B*P*mix A B)) := by
  have hsig : P*(A*B)*Q=-(Q*(P*(A*B))) := by
    rw [mul_assoc P,odd_product hq,mul_neg,←mul_assoc P,hc.eq,mul_assoc]
  rcases hp with ⟨hA,hB⟩|⟨hA,hB⟩
  · rw [mix_conjugate A B P ha hb hab hA hB,mul_assoc P,neg_mul,mul_neg,neg_neg,hsig,neg_neg]
  · have hba : B*A=-(A*B) := by rw [hab,neg_neg]
    have hm : mix A B=mix B A := by rw [mix,mix,add_comm A B]
    rw [hm,mix_conjugate B A P hb ha hba hB hA,mul_assoc P,hba,mul_neg,neg_neg,hsig]

private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- The commutator has the largest possible norm, two. Arbitrary
phases multiplying the propagator cancel under conjugation. -/
theorem quarter_exchange_norm {N : ℕ} (A B P Q : Reg N)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (ha : A*A=1) (hb : B*B=1) (hab : A*B=-(B*A))
    (hp : oddProbe A B P) (hq : oddProbe A B Q) (hc : Commute P Q)
    (hP : P∈unitary _) (hQ : Q∈unitary _) :
    let U := unitaryEvolution (mix A B) (π/2)
    ‖(star U*P*U)*Q-Q*(star U*P*U)‖=2 := by
  intro U
  have hs : IsSelfAdjoint (mix A B) := by
    change star (((1/sqrt 2:ℝ):ℂ) • (A+B))=_
    rw [star_smul,star_add,hA.star_eq,hB.star_eq,Complex.star_def,Complex.conj_ofReal]
    rfl
  have he : star U*P*U=mix A B*P*mix A B := by
    dsimp only [U]
    rw [mix_quarter A B ha hb hab,star_smul,hs.star_eq,Complex.star_def,map_neg,Complex.conj_I,
      neg_neg,smul_mul_assoc,mul_smul_comm,smul_mul_assoc,smul_smul]
    simp only [neg_mul,Complex.I_mul_I,neg_neg,one_smul]
  let M := Q*(star U*P*U)
  have hu := unitaryEvolution_mem_unitary hs (π/2)
  have hm : M∈unitary _ := mul_mem hQ (mul_mem (mul_mem (Unitary.star_mem hu) hP) hu)
  have hanti : (star U*P*U)*Q = -M := by
    dsimp only [M]
    rw [he]
    exact mix_exchange A B P Q ha hb hab hp hq hc
  change ‖(star U*P*U)*Q-M‖=2
  rw [hanti,show -M-M= -((2:ℂ) • M) by rw [two_smul]; abel,
    norm_neg,norm_smul,CStarRing.norm_of_mem_unitary hm,mul_one]
  norm_num

#print axioms quarter_exchange_norm
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
