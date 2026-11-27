import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.MatchedAxes
import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw

/-! # Repeating a circuit amplifies time without changing its cut -/

open Finset Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance powerCutAlgebra (N : ℕ) : CStarAlgebra (Reg N) where
variable {n : ℕ}

private theorem power_cut {C : TwoQubitCircuit (n+2)} (c : Cut C) (r : ℕ) :
    ∃ d : Cut (C.pow r), d.val=c.val := by
  have hg : ∀ i : Fin (C.pow r).gateCount,
      c.val ((C.pow r).architecture.sites i).1=c.val ((C.pow r).architecture.sites i).2 := by
    induction r with
    | zero => exact fun i => Fin.elim0 i
    | succ r ih =>
      intro i
      change c.val (Fin.append C.architecture.sites (C.pow r).architecture.sites i).1=
        c.val (Fin.append C.architecture.sites (C.pow r).architecture.sites i).2
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using c.gate_agrees j
      · simpa using ih j
  refine ⟨⟨c.val,?_⟩,rfl⟩
  funext i
  change xor (c.val ((C.pow r).architecture.sites i).1) (c.val ((C.pow r).architecture.sites i).2)=false
  rw [hg i]
  cases c.val ((C.pow r).architecture.sites i).2 <;> rfl

private theorem phase_power_error (u : PathShell n) (C : TwoQubitCircuit (n+2))
    (z : ℂ) (hz : ‖z‖=1) (t : ℝ) (r : ℕ) :
    ‖unitaryEvolution (pathHamiltonian u) (r*t)-z^r • (C.pow r).eval.val‖≤
      r*‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖ := by
  have hc : star z*z=1 := by rw [Complex.star_def,Complex.conj_mul',hz]; norm_num
  have hc' : z*star z=1 := (mul_comm ..).trans hc
  have hV : z • C.eval.val∈unitary (Reg (n+2)) := by
    obtain ⟨hl,hr⟩ := Unitary.mem_iff.mp C.eval.2
    apply Unitary.mem_iff.mpr
    simp only [star_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hc,hc',hl,hr,one_smul,and_self]
  have h := unitary_pow_norm_sub_pow_le _ _ (unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t) hV r
  rw [TwoQubitCircuit.pow_eval_coe]
  simpa only [unitaryEvolution,exp_real_smul_pow,smul_pow] using h

/-- A fixed circuit cut remains available at every integer multiple of
the observation time. Its admissible coefficient mass shrinks by the
same integer factor whenever the accumulated error remains small. -/
theorem power_cut_mass (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (b : Fin (n+1)→Fin 3×Fin 3) (t : ℝ) (z : ℂ) (hz : ‖z‖=1) (r : ℕ)
    (hfit : (r:ℝ)*‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤1/4)
    (ht : (r:ℝ)*|t| * ‖u‖≤1/100) :
    (r:ℝ)*4*|t| * (∑ e∈crossed c, |u (.inr (e,b e))|)<2*π := by
  obtain ⟨d,hd⟩ := power_cut c r
  have he : crossed d=crossed c := by ext e; simp only [mem_crossed_iff,hd]
  have hab : |(r:ℝ)*t|=(r:ℝ)*|t| := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  have h := matched_axes_cut u (C.pow r) d (r*t) (z^r) (by rw [norm_pow,hz,one_pow])
    ((phase_power_error u C z hz t r).trans hfit) (by rwa [hab]) b
  rw [he,hab] at h
  linarith only [h]

#print axioms power_cut_mass
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
