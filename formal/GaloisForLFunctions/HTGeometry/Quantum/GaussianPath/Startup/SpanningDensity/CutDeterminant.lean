import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutEnergies
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.DiagonalPhases
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.DisconnectedSpectra.Factorization

/-! # A physical circuit must reproduce all four diagonal phases on every cut rectangle -/
open Matrix
open scoped Kronecker Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

def phase (t E : ℝ) : ℂ := Complex.exp ((-(t*E):ℝ)*Complex.I)

theorem phase_norm (t E : ℝ) : ‖phase t E‖=1 := Complex.norm_exp_ofReal_mul_I _

theorem phase_add (t a b : ℝ) : phase t (a+b)=phase t a*phase t b := by
  unfold phase; rw [← Complex.exp_add]; congr 1; push_cast; ring

private def det₂ (f : Bool→Bool→ℂ) := f false false*f true true-f true false*f false true

private theorem det_phase (t : ℝ) (E : Bool→Bool→ℝ) :
    ‖det₂ (fun a b => phase t (E a b))‖=‖phase t (contrast E)-1‖ := by
  unfold det₂
  rw [← phase_add,←phase_add]
  let s := E true false+E false true
  have he : E false false+E true true=contrast E+s := by unfold contrast s; ring
  rw [he,phase_add]
  change ‖phase t (contrast E)*phase t s-phase t s‖=_
  rw [←sub_one_mul,norm_mul,phase_norm,mul_one]

private theorem circuit_det_zero {n : ℕ} (C : TwoQubitCircuit (n+1)) (c : Cut C)
    (x : Fin (n+1)→Bool) (z : ℂ) :
    det₂ (fun a b => z*C.eval.val (corner c.val x a b) (corner c.val x a b))=0 := by
  classical
  let S := Finset.univ.filter fun i => c.val i=true
  let e := configurationSplitEquiv (fun _ : Fin (n+1) => Bool) S
  obtain ⟨A,B,hAB⟩ := DisconnectedSpectra.factor_on_cut C S (fun i => by
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,c.gate_agrees i])
  let l (a : Bool) : LocalConfiguration (fun _ : Fin (n+1) => Bool) S := fun i => xor (x i.val) a
  let r (b : Bool) : OutsideConfiguration (fun _ : Fin (n+1) => Bool) S := fun i => xor (x i.val) b
  have hs (a b : Bool) : e (corner c.val x a b)=(l a,r b) := by
    apply Prod.ext
    · funext i
      change xor (x i.val) (if c.val i.val then a else b)=_
      rw [(Finset.mem_filter.mp i.2).2]; rfl
    · funext i
      have h : c.val i.val=false := Bool.eq_false_iff.mpr (fun hi =>
        i.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩))
      change xor (x i.val) (if c.val i.val then a else b)=_
      rw [h]; rfl
  have h (a b : Bool) : C.eval.val (corner c.val x a b) (corner c.val x a b) =
      A (l a) (l a)*B (r b) (r b) := by
    let y := corner c.val x a b
    have hh := congrArg (fun M => M (e y) (e y)) hAB
    change C.eval.val (e.symm (e y)) (e.symm (e y))=A (e y).1 (e y).1*B (e y).2 (e y).2 at hh
    rw [Equiv.symm_apply_apply] at hh
    simpa only [y,hs] using hh
  unfold det₂
  simp_rw [h]
  ring

private theorem det_difference (f g : Bool→Bool→ℂ) (d : ℝ)
    (hf : ∀ a b, ‖f a b‖≤1) (hg : ∀ a b, ‖g a b‖≤1)
    (h : ∀ a b, ‖f a b-g a b‖≤d) : ‖det₂ f-det₂ g‖≤4*d := by
  have hp (a b p q : Bool) : ‖f a b*f p q-g a b*g p q‖ ≤ 2*d := by
    rw [show f a b*f p q-g a b*g p q=(f a b-g a b)*f p q+g a b*(f p q-g p q) by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,two_mul]
    simpa only [mul_one,one_mul] using add_le_add
      (mul_le_mul (h a b) (hf p q) (norm_nonneg _) ((norm_nonneg _).trans (h a b)))
      (mul_le_mul (hg a b) (h p q) (norm_nonneg _) zero_le_one)
  unfold det₂
  rw [sub_sub_sub_comm]
  linarith only [norm_sub_le (f false false*f true true-g false false*g true true)
    (f true false*f false true-g true false*g false true),hp false false true true,hp true false false true]

/-- A gate-respecting cut forces every signed crossed energy to have
small phase contrast if the circuit approximates the propagator. -/
theorem cut_phase_bound {n : ℕ} (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (x : Fin (n+2)→Bool) (z : ℂ) (hz : ‖z‖=1) (t : ℝ) :
    ‖phase t (4*∑ e ∈ crossed c, u (.inr (e,2,2))*(spin (x e.castSucc)*spin (x e.succ)))-1‖ ≤
      4*(‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖ + |t| *(Real.sqrt 21*‖u‖)) := by
  let U := unitaryEvolution (pathHamiltonian u) t
  let V := z • C.eval.val
  let k := corner c.val x
  let E := fun a b => pathDiagEnergy u (k a b)
  have hcut : crossed c=Finset.univ.filter (fun e : Fin (n+1) => c.val e.castSucc≠c.val e.succ) := by
    ext i; simp [mem_crossed_iff]
  rw [hcut,←energy_contrast,←det_phase]
  let f := fun a b => phase t (E a b)
  let g := fun a b => V (k a b) (k a b)
  have hg : det₂ g=0 := circuit_det_zero C c x z
  change ‖det₂ f‖≤4*(‖U-V‖+_)
  rw [← sub_zero (det₂ f),←hg]
  apply det_difference
  · intro a b; exact (phase_norm ..).le
  · intro a b
    exact (norm_entry_le_l2_opNorm V _ _).trans (by simp only [V,norm_smul,hz,one_mul,
      CStarRing.norm_of_mem_unitary C.eval.2,le_refl])
  · intro a b
    have h₁ := path_diagonal_phase u (k a b) t
    have h₂ := norm_entry_le_l2_opNorm (U-V) (k a b) (k a b)
    change ‖U (k a b) (k a b)-g a b‖≤_ at h₂
    rw [norm_sub_rev] at h₁
    exact (norm_sub_le_norm_sub_add_norm_sub (f a b) (U (k a b) (k a b)) (g a b)).trans
      ((add_le_add h₁ h₂).trans_eq (add_comm ..))

#print axioms cut_phase_bound
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
