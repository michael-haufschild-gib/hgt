import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.PathCuts
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitDeletionBound
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.OneGate
import GaloisForLFunctions.HTGeometry.Quantum.LocalPacketComparison
import GaloisForLFunctions.HTGeometry.SiteSupportedEvolutionFactorization

/-! # A cut crossed by many physical bonds has a small commutator for every affordable unitary -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

private theorem gate_supported {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    (U : Matrix.specialUnitaryGroup (Bool×Bool) ℂ) (S : Finset (Fin N)) (ha : a∈S) (hb : b∈S) :
    IsSiteSupported (A:=fun _ : Fin N => Bool) S (twoQubitLift a b hab U).val := by
  let C := TwoQubitCircuit.singleOn a b hab U
  have h : C.touchedSites ⊆ S := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
      exact ha
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
      exact hb
  simpa only [C,TwoQubitCircuit.singleOn_eval] using C.isSiteSupported_touchedSites.mono h

/-- Conjugating by the entire circuit preserves the algebra on each side
of a gate-respecting cut, even if both sides carry nontrivial gates. -/
theorem circuit_conjugate_supported {N : ℕ} (C : TwoQubitCircuit N) (S : Finset (Fin N))
    (hc : ∀ i : Fin C.gateCount, (C.architecture.sites i).1∈S ↔ (C.architecture.sites i).2∈S)
    (A : Reg N) (hA : IsSiteSupported S A) : IsSiteSupported S (star C.eval.val*A*C.eval.val) := by
  classical
  let P (U : Matrix.unitaryGroup (Fin N→Bool) ℂ) :=
    ∀ M : Reg N, IsSiteSupported S M → IsSiteSupported S (star U.val*M*U.val)
  have hp (l : List (Matrix.unitaryGroup (Fin N→Bool) ℂ)) (hl : ∀ U∈l, P U) : P l.prod := by
    induction l with
    | nil => intro M hM; simpa using hM
    | cons u l ih =>
      intro M hM
      have hh := ih (fun v hv => hl v (List.mem_cons_of_mem _ hv)) _
        (hl u List.mem_cons_self M hM)
      simpa only [List.prod_cons,Submonoid.coe_mul,star_mul,mul_assoc] using hh
  apply hp ((List.ofFn fun i => C.architecture.gateLift i (C.gates i)).reverse) _ A hA
  intro U hU
  rw [List.mem_reverse,List.mem_ofFn] at hU
  obtain ⟨i,rfl⟩ := hU
  let a := (C.architecture.sites i).1
  let b := (C.architecture.sites i).2
  let u := twoQubitLift a b (C.architecture.distinct i) (C.gates i)
  intro M hM
  change IsSiteSupported S (star u.val*M*u.val)
  by_cases ha : a∈S
  · have hu := gate_supported a b (C.architecture.distinct i) (C.gates i) S ha ((hc i).mp ha)
    exact IsSiteSupported.matrix_mul (IsSiteSupported.matrix_mul (IsSiteSupported.conjTranspose hu) hM) hu
  · have hu := gate_supported a b (C.architecture.distinct i) (C.gates i) Sᶜ
      (Finset.mem_compl.mpr ha) (Finset.mem_compl.mpr (fun h => ha ((hc i).mpr h)))
    have hm : Commute M u.val := commute_of_isSiteSupported_disjoint disjoint_compl_right hM hu
    rw [mul_assoc,hm.eq,← mul_assoc,Unitary.star_mul_self_of_mem u.property,one_mul]
    exact hM

private theorem conjugate_dist {N : ℕ} (U V A : Reg N) (hu : ‖U‖≤1) (hv : ‖V‖≤1)
    (ha : ‖A‖≤1) : ‖star U*A*U-star V*A*V‖ ≤ 2*‖U-V‖ := by
  have h : star U*A*U-star V*A*V = star (U-V)*A*U+star V*A*(U-V) := by
    rw [star_sub]; noncomm_ring
  have h₁ : ‖star (U-V)*A*U‖ ≤ ‖U-V‖ := by
    calc _ ≤ ‖star (U-V)*A‖*‖U‖ := norm_mul_le _ _
         _ ≤ (‖U-V‖*1)*1 := mul_le_mul ((norm_mul_le _ _).trans (by
               rw [norm_star]; gcongr)) hu (norm_nonneg _) (by positivity)
         _ = _ := by ring
  have h₂ : ‖star V*A*(U-V)‖ ≤ ‖U-V‖ := by
    calc _ ≤ ‖star V*A‖*‖U-V‖ := norm_mul_le _ _
         _ ≤ (1*1)*‖U-V‖ := by
               gcongr
               exact (norm_mul_le _ _).trans (mul_le_mul (by simpa only [norm_star] using hv) ha
                 (norm_nonneg _) zero_le_one)
         _ = _ := by ring
  rw [h]
  linarith only [norm_add_le (star (U-V)*A*U) (star V*A*(U-V)),h₁,h₂]

/-- Two unitaries differing on a directed signal have a projective norm gap. -/
theorem projective_missing_signal_bound {N : ℕ} (W U : Matrix.unitaryGroup (Fin N→Bool) ℂ) (z : ℂ) (hz : ‖z‖=1)
    (A B : Reg N) (ha : ‖A‖≤1) (hb : ‖B‖≤1)
    (hcomm : Commute (star W.val*A*W.val) B) :
    ‖(star U.val*A*U.val)*B-B*(star U.val*A*U.val)‖ ≤ 4*‖U.val-z • W.val‖ := by
  let V := z • W.val
  have hv : ‖V‖≤1 := by simp only [V,norm_smul,hz,one_mul,CStarRing.norm_of_mem_unitary W.property,le_refl]
  have hphase : star V*A*V=star W.val*A*W.val := by
    simp only [V,star_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    rw [show z*star z=1 by simp [Complex.mul_conj',hz],one_smul]
  let X := star U.val*A*U.val
  let Y := star V*A*V
  have hY : Commute Y B := by
    dsimp only [Y]; rw [hphase]
    exact hcomm
  have he : X*B-B*X=(X-Y)*B-B*(X-Y) := by rw [sub_mul,mul_sub]; rw [hY.eq]; abel
  change ‖X*B-B*X‖ ≤ _
  rw [he]
  have hd := conjugate_dist U.val V A (CStarRing.norm_of_mem_unitary U.property).le hv ha
  calc _ ≤ ‖X-Y‖*‖B‖+‖B‖*‖X-Y‖ :=
         (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
       _ ≤ ‖X-Y‖*1+1*‖X-Y‖ := by gcongr
       _ ≤ _ := by change _ ≤ 4*‖U.val-V‖; linarith only [hd]

/-- A signal absent from the circuit bounds its projective approximation error. -/
theorem missing_signal_bound {N : ℕ} (C : TwoQubitCircuit N)
    (U : Matrix.unitaryGroup (Fin N→Bool) ℂ) (z : ℂ) (hz : ‖z‖=1)
    (A B : Reg N) (ha : ‖A‖≤1) (hb : ‖B‖≤1)
    (hcomm : Commute (star C.eval.val*A*C.eval.val) B) :
    ‖(star U.val*A*U.val)*B-B*(star U.val*A*U.val)‖ ≤ 4*‖U.val-z • C.eval.val‖ :=
  projective_missing_signal_bound C.eval U z hz A B ha hb hcomm

/-- Approximation in projective operator norm controls every commutator
between a transported observable and an observable on the opposite side. -/
theorem many_bonds_small_commutator {n : ℕ} (C : TwoQubitCircuit (n+1))
    (U : Matrix.unitaryGroup (Fin (n+1)→Bool) ℂ) (z : ℂ) (hz : ‖z‖=1) :
    ∃ x : Cut C, n ≤ C.gateCount+2*(crossed x).card ∧
      ∀ A B : Reg (n+1), ‖A‖≤1 → ‖B‖≤1 →
        IsSiteSupported (Finset.univ.filter fun i => x.val i=true) A →
        IsSiteSupported (Finset.univ.filter fun i => x.val i=true)ᶜ B →
        ‖(star U.val*A*U.val)*B-B*(star U.val*A*U.val)‖ ≤ 4*‖U.val-z • C.eval.val‖ := by
  obtain ⟨x,hx⟩ := many_crossed C
  refine ⟨x,hx,?_⟩
  intro A B ha hb hA hB
  let S := Finset.univ.filter fun i => x.val i=true
  have hf := circuit_conjugate_supported C S (fun i => by simp only [S,Finset.mem_filter,
    Finset.mem_univ,true_and,x.gate_agrees i]) A hA
  exact missing_signal_bound C U z hz A B ha hb
    (commute_of_isSiteSupported_disjoint disjoint_compl_right hf hB)

#print axioms many_bonds_small_commutator
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
