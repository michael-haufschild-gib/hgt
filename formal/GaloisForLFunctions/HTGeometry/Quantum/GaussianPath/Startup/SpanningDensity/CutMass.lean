import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutDeterminant
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.SignedWeights
import GaloisForLFunctions.HTGeometry.DiagonalPatchConstruction

/-! # At small physical error every gate-respecting cut has limited longitudinal mass -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
noncomputable section

private theorem phase_distance (t a b : ℝ) : ‖phase t a-phase t b‖ ≤ |t| * |a-b| := by
  have h : phase t a-phase t b=(phase t (a-b)-1)*phase t b := by
    rw [sub_mul,one_mul,←phase_add,sub_add_cancel]
  rw [h,norm_mul,phase_norm,mul_one]
  simpa only [phase,mul_comm Complex.I,Real.norm_eq_abs,abs_neg,abs_mul] using
    Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(t*(a-b)))

/-- Once the crossed ZZ couplings can span a half turn, the circuit has
projective error at least 1/2 up to an explicit column-variance correction. -/
theorem half_turn_error {n : ℕ} (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (t : ℝ) (z : ℂ) (hz : ‖z‖=1)
    (hm : π ≤ 4*|t| *(∑ e∈crossed c, |u (.inr (e,2,2))|)) :
    2 ≤ 4*‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖+
      (8+4*Real.sqrt 21)*(|t| * ‖u‖) := by
  have ht : t≠0 := by intro h; rw [h,abs_zero,mul_zero,zero_mul] at hm; exact pi_pos.not_ge hm
  let y := -π/(4*t)
  have hy : |y|≤∑ e∈crossed c, |u (.inr (e,2,2))| := by
    dsimp only [y]; rw [abs_div,abs_neg,abs_of_pos pi_pos,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
    exact (div_le_iff₀ (mul_pos (by norm_num) (abs_pos.mpr ht))).mpr (by linarith only [hm])
  let J (e : Fin (n+1)) := u (.inr (e,2,2))
  obtain ⟨x,hx⟩ := realize_signed_energy (crossed c) J ‖u‖ y (norm_nonneg _)
    (fun e _ => abs_coord_le_norm u _) hy
  let a := ∑ e∈crossed c, J e*(spin (x e.castSucc)*spin (x e.succ))
  have hπ : phase t (4*y) = -1 := by
    unfold phase
    rw [show -(t*(4*y))=π by dsimp only [y]; field_simp]
    exact Complex.exp_pi_mul_I
  have hp := phase_distance t (4*a) (4*y)
  rw [←mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)] at hp
  have hδ : ‖phase t (4*a)-phase t (4*y)‖ ≤ 8*(|t| * ‖u‖) :=
    hp.trans (by change |t| * (4*|a-y|) ≤ _; nlinarith only [mul_le_mul_of_nonneg_left hx (abs_nonneg t)])
  have hh := cut_phase_bound u C c x z hz t
  have hdist := norm_sub_le_norm_sub_add_norm_sub (phase t (4*y)) (phase t (4*a)) 1
  rw [hπ,show ‖(-1:ℂ)-1‖=(2:ℝ) by norm_num,norm_sub_rev (-1:ℂ)] at hdist
  rw [hπ] at hδ
  change ‖phase t (4*a)-1‖≤_ at hh
  linarith only [hdist,hδ,hh]

/-- At tolerances up to 1/4 and |t|‖u‖≤1/100, some cut crosses at least
half the excess of the path length over the gate count, yet the total
absolute longitudinal phase on those bonds is smaller than π/4. -/
theorem affordable_sparse_cut {n : ℕ} (u : PathShell n) (C : TwoQubitCircuit (n+2))
    (t : ℝ) (z : ℂ) (hz : ‖z‖=1)
    (hc : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖ ≤ 1/4)
    (ht : |t| * ‖u‖ ≤ 1/100) :
    ∃ c : Cut C, n+1 ≤ C.gateCount+2*(crossed c).card ∧
      4*|t| *(∑ e∈crossed c, |u (.inr (e,2,2))|)<π := by
  obtain ⟨c,hh⟩ := many_crossed C
  refine ⟨c,hh,?_⟩
  by_contra! h
  have h₂ := half_turn_error u C c t z hz h
  have h₃ : Real.sqrt 21 ≤ 5 := (Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
  have hb := mul_le_mul (show 8+4*Real.sqrt 21≤28 by linarith only [h₃]) ht
    (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (by norm_num)
  linarith only [h₂,hb,hc]

#print axioms affordable_sparse_cut
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
