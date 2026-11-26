import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.SparsePacket
import GaloisForLFunctions.HTGeometry.Quantum.LocalPacketComparison

/-! # A local rotation cannot preserve two sparse fits across the same packet -/

open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ
private abbrev UReg (N : ℕ) := unitaryGroup (Fin N → Bool) ℂ

/-- A matrix admits a unitary approximation touching at most r wires of
the packet. The complement has unrestricted support. -/
def packetFit {N : ℕ} (R : Finset (Fin N)) (r : ℕ) (ε : ℝ) (W : Reg N) : Prop :=
  ∃ (S : Finset (Fin N)) (A : UReg N),
    (R∩S).card≤r ∧ IsSiteSupported S A.val ∧ ‖W-A.val‖≤ε

/-- A rotation on the exterior can be absorbed in a sparse fit. -/
theorem packetFit_exterior {N : ℕ} {R : Finset (Fin N)} {r : ℕ} {ε : ℝ} {W : Reg N}
    (V : UReg N) (hV : IsSiteSupported Rᶜ V.val) :
    packetFit R r ε (V.val*W) ↔ packetFit R r ε W := by
  have step (U : UReg N) (hU : IsSiteSupported Rᶜ U.val) (X : Reg N) :
      packetFit R r ε X → packetFit R r ε (U.val*X) := by
    rintro ⟨S,A,hr,hA,he⟩
    have hsites : R∩(Rᶜ∪S)=R∩S := by ext; simp only [Finset.mem_inter,Finset.mem_union,Finset.mem_compl]; tauto
    refine ⟨Rᶜ∪S,U*A,by rwa [hsites],
      IsSiteSupported.matrix_mul (S:=Rᶜ∪S) (hU.mono Finset.subset_union_left)
        (hA.mono Finset.subset_union_right),?_⟩
    change ‖U.val*X-U.val*A.val‖≤ε
    rw [←mul_sub]
    exact (norm_mul_le _ _).trans (by rwa [CStarRing.norm_of_mem_unitary U.2,one_mul])
  refine ⟨fun h => ?_,step V hV W⟩
  have h' := step V⁻¹ hV.conjTranspose _ h
  have hi : (V⁻¹ : UReg N).val*V.val=1 := (Unitary.mem_iff.mp V.2).1
  rwa [←mul_assoc,hi,one_mul] at h'

/-- The quotient of sparse fits before and after a packet rotation is
supported on their union. Its error is at most the sum of the two errors. -/
private theorem quotient_fit {N : ℕ} (V A : UReg N) (W B : Reg N) :
    ‖V.val-B*star A.val‖ ≤ ‖W-A.val‖+‖V.val*W-B‖ := by
  have hA : A.val*star A.val=1 := (Unitary.mem_iff.mp A.2).2
  have he : V.val-B*star A.val=(V.val*A.val-B)*star A.val := by
    rw [sub_mul,mul_assoc,hA,mul_one]
  have hnorm : ‖star A.val‖=1 := (norm_star _).trans (CStarRing.norm_of_mem_unitary A.2)
  have ht := norm_sub_le_norm_sub_add_norm_sub (V.val*A.val) (V.val*W) B
  rw [←mul_sub] at ht
  have h := norm_mul_le V.val (A.val-W)
  rw [CStarRing.norm_of_mem_unitary V.2,one_mul,norm_sub_rev A.val W] at h
  rw [he]
  exact (norm_mul_le _ _).trans ((by rw [hnorm,mul_one] : ‖V.val*A.val-B‖*‖star A.val‖=‖V.val*A.val-B‖).le.trans
    (ht.trans (add_le_add h le_rfl)))

/-- The relative rotation of two sparse fits has a fit on twice as
many packet wires at twice the error. -/
theorem packetFit_relative {N : ℕ} {R : Finset (Fin N)} {r : ℕ} {ε : ℝ}
    (V : UReg N) (W : Reg N) (h₁ : packetFit R r ε W)
    (h₂ : packetFit R r ε (V.val*W)) : packetFit R (2*r) (2*ε) V.val := by
  obtain ⟨S,A,hS,hA,he⟩ := h₁
  obtain ⟨T,B,hT,hB,hf⟩ := h₂
  refine ⟨T∪S,B*A⁻¹,?_,?_,?_⟩
  · rw [Finset.inter_union_distrib_left]
    exact (Finset.card_union_le _ _).trans ((Nat.add_le_add hT hS).trans_eq (two_mul r).symm)
  · exact IsSiteSupported.matrix_mul (S:=T∪S) (hB.mono Finset.subset_union_left)
      (hA.conjTranspose.mono Finset.subset_union_right)
  · exact (quotient_fit V A W B.val).trans ((add_le_add he hf).trans_eq (two_mul ε).symm)

/-- With a single baseline, fits before and after a packet rotation
force a bound on every spectral chord of that rotation. Exterior
actions and the choice of the two approximants are unrestricted. -/
theorem two_sparse_fits_chord {n : ℕ} (R : Finset (Fin (n+2))) (u : PathShell n)
    (W : Reg (n+2)) (r : ℕ) (t ε : ℝ) (i j : Fin (n+2) → Bool) :
    let H := pathHamiltonianOnSites R u
    let E := (isSelfAdjoint_pathHamiltonianOnSites R u).isHermitian.eigenvalues
    packetFit R r ε W → packetFit R r ε (unitaryEvolution H t*W) →
    ‖anchorPhase E i t-anchorPhase E j t‖ ≤
      2*(2*ε+2*|t| *(sqrt (21*(2*(r:ℝ)))*‖pathShellOnSites R u‖)) := by
  intro H E h₁ h₂
  let V : UReg (n+2) := ⟨_,unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonianOnSites R u) t⟩
  obtain ⟨S,A,hcard,hsupp,herr⟩ := packetFit_relative V W h₁ h₂
  have hroot : sqrt (21*((R∩S).card:ℝ)) ≤ sqrt (21*(2*(r:ℝ))) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by norm_num))
  have hc := packet_chord_floor R S u A.val hsupp i j t
  exact hc.trans (mul_le_mul_of_nonneg_left
    (add_le_add herr
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hroot (norm_nonneg _)) (by positivity))) zero_le_two)

#print axioms packetFit_exterior
#print axioms packetFit_relative
#print axioms two_sparse_fits_chord
end
end GaloisForLFunctions.HTGeometry.BlockDilations
