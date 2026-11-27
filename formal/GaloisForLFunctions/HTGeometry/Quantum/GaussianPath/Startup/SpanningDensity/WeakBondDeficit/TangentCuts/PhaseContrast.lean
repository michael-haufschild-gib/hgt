import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.TangentCuts.ColumnPhase
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.CircuitFit

/-! # First-order mass of the bonds across an arbitrary circuit cut -/

open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit.TangentCuts
noncomputable section
open private det₂ det_phase circuit_det_zero det_difference from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutDeterminant
variable {n : ℕ}

private theorem phase_displacement (t E : ℝ) :
    |t| * |E|≤‖phase t E-1‖+t^2*E^2 := by
  let a : ℂ := (-E:ℝ)*Complex.I
  have ha : a∈skewAdjoint ℂ := by
    rw [skewAdjoint.mem_iff]
    simp [a,Complex.star_def]
  have he : t • a=(-(t*E):ℝ)*Complex.I := by
    simp only [a,Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_mul]
    ring
  have hn : ‖a‖=|E| := by simp [a,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have h := compressed_remainder a (1:ℂ) 1 ha t
  simp only [one_mul,mul_one,←Complex.exp_eq_exp_ℂ,he,hn,←sq,sq_abs] at h
  have hdiff := norm_sub_le_norm_sub_add_norm_sub (t • a) (phase t E-1) 0
  rw [sub_zero,sub_zero,norm_sub_rev (t • a),norm_smul,Real.norm_eq_abs,hn,he] at hdiff
  change ‖phase t E-1- _‖≤_ at h
  linarith only [hdiff,h]

/-- If the circuit does not cross the chosen cut, the determinant of
its four diagonal entries vanishes. Choosing the signs of the spins
realizes the full absolute longitudinal interaction across that cut. -/
theorem longitudinal_cut_speed (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (z : ℂ) (hz : ‖z‖=1) (t : ℝ) :
    let S := ∑ e∈crossed c, |u (.inr (e,2,2))|
    |t| * S≤‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖+t^2*(21*‖u‖^2+4*S^2) := by
  intro S
  let J (e : Fin (n+1)) := u (.inr (e,2,2))
  obtain ⟨x,hx⟩ := realize_edge_signs (fun e => decide (J e<0))
  have hspin (e : Fin (n+1)) : J e*(spin (x e.castSucc)*spin (x e.succ))=|J e| := by
    rw [hx]
    by_cases h : J e<0
    · simp [h,spin,abs_of_neg h]
    · simp [h,spin,abs_of_nonneg (le_of_not_gt h)]
  let k := corner c.val x
  let E (a b : Bool) := pathDiagEnergy u (k a b)
  have hcut : crossed c=univ.filter (fun e : Fin (n+1) => c.val e.castSucc≠c.val e.succ) := by
    ext e; simp [mem_crossed_iff]
  have hc : contrast E=4*S := by
    rw [energy_contrast u c.val x,←hcut]
    apply congrArg (4*·)
    exact sum_congr rfl fun e _ => hspin e
  let U := unitaryEvolution (pathHamiltonian u) t
  let V := z • C.eval.val
  let f := fun a b => phase t (E a b)
  let g := fun a b => V (k a b) (k a b)
  have hg : det₂ g=0 := circuit_det_zero C c x z
  have hdet : ‖phase t (4*S)-1‖≤4*(‖U-V‖+t^2*(21*‖u‖^2)) := by
    rw [←hc,←det_phase,←sub_zero (det₂ f),←hg]
    apply det_difference
    · exact fun _ _ => (phase_norm ..).le
    · intro a b
      exact (norm_entry_le_l2_opNorm V _ _).trans (by rw [norm_smul,hz,one_mul,CStarRing.norm_of_mem_unitary C.eval.2])
    · intro a b
      have hp := path_column_phase_quadratic u (k a b) t
      rw [norm_sub_rev] at hp
      exact (norm_sub_le_norm_sub_add_norm_sub (f a b) (U (k a b) (k a b)) (g a b)).trans
        ((add_le_add hp (norm_entry_le_l2_opNorm (U-V) (k a b) (k a b))).trans_eq (add_comm ..))
  have hS : 0≤S := sum_nonneg fun _ _ => abs_nonneg _
  have hp := phase_displacement t (4*S)
  rw [abs_of_nonneg (mul_nonneg (by norm_num) hS)] at hp
  change |t| * S≤‖U-V‖+_
  linarith only [hp,hdet]

/-- The same bound applies in every product Pauli frame with the original
physical gate locations and error. -/
theorem frame_cut_speed (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (z : ℂ) (hz : ‖z‖=1) (t : ℝ) (a : Fin (n+2)→Fin 3) :
    let S := ∑ e∈crossed c, |u (.inr (e,a e.castSucc,a e.succ))|
    |t| * S≤‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖+t^2*(21*‖u‖^2+4*S^2) := by
  obtain ⟨T,hT⟩ := frame_preserves_fit a u C t z
  let D : TwoQubitCircuit (n+2) := ⟨C.gateCount,C.architecture,T⟩
  let c' : Cut D := ⟨c.val,c.property⟩
  have hs : crossed c'=crossed c := by ext e; simp only [mem_crossed_iff,c']
  simpa only [hs,rotatedShell_longitudinal,rotatedShell_norm,hT] using
    longitudinal_cut_speed (rotatedShell a u) D c' z hz t

#print axioms frame_cut_speed
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit.TangentCuts
