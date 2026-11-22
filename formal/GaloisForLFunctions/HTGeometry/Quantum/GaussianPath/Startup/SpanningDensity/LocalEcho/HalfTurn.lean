import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.MaskBracket
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutEcho
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutMass

/-! # Detecting a half turn with a bounded number of local flips -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
noncomputable section
variable {n : ℕ}

private theorem phase_half_bound (v : PathShell n) (t : ℝ) (ht : 0<t) (M : ℝ) (hM : 0 ≤ M)
    (hdiag : ∀ x, pathDiagEnergy v x=∑ e, v (zz e)*(spin (x e.castSucc)*spin (x e.succ)))
    (hm : ∀ l, |v l|≤4*M) (hmass : π ≤ t*∑ e, |v (zz e)|) :
    2 ≤ ‖unitaryEvolution (pathHamiltonian v) (-t)-1‖+t*(sqrt 21*‖v‖)+8*(t*M) := by
  let y := π/t
  have hy : |y| ≤ ∑ e, |v (zz e)| := by
    change |π/t| ≤ _
    rw [abs_of_nonneg (div_nonneg pi_pos.le ht.le)]
    exact (div_le_iff₀ ht).mpr (by linarith only [hmass])
  obtain ⟨x,hx⟩ := realize_signed_energy Finset.univ (fun e => v (zz e)) (4*M) y (by positivity)
    (fun e _ => hm _) hy
  let E := pathDiagEnergy v x
  change |(∑ e, v (zz e)*(spin (x e.castSucc)*spin (x e.succ)))-y| ≤ 2*(4*M) at hx
  rw [←hdiag] at hx
  change |E-y| ≤ 2*(4*M) at hx
  have hπ : phase (-t) y= -1 := by
    unfold phase
    rw [show -(-t*y)=π by dsimp only [y]; field_simp]
    exact Complex.exp_pi_mul_I
  have he : phase (-t) E-phase (-t) y=(phase (-t) (E-y)-1)*phase (-t) y := by
    rw [sub_mul,one_mul,←phase_add,sub_add_cancel]
  have hδ : ‖phase (-t) E-phase (-t) y‖≤8*(t*M) := by
    rw [he,norm_mul,phase_norm,mul_one]
    have hp := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(-t*(E-y)))
    have hb := mul_le_mul_of_nonneg_left hx ht.le
    apply (show ‖phase (-t) (E-y)-1‖ ≤ t*|E-y| by
      simpa only [phase,mul_comm Complex.I,Real.norm_eq_abs,abs_neg,abs_mul,abs_of_pos ht] using hp).trans
    linarith only [hb]
  let U := unitaryEvolution (pathHamiltonian v) (-t)
  have hc := path_diagonal_phase v x (-t)
  change ‖U x x-phase (-t) E‖ ≤ |-t| *(sqrt 21*‖v‖) at hc
  rw [abs_neg,abs_of_pos ht] at hc
  have hu : ‖U x x-1‖ ≤ ‖U-1‖ := by
    calc ‖U x x-1‖ = ‖(U-1) x x‖ := by
           change _ = ‖U x x-(1 : Register (n+2)) x x‖
           rw [Matrix.one_apply_eq]
         _ ≤ _ := norm_entry_le_l2_opNorm (U-1) x x
  have h₁ := norm_sub_le_norm_sub_add_norm_sub (phase (-t) y) (phase (-t) E) 1
  have h₂ := norm_sub_le_norm_sub_add_norm_sub (phase (-t) E) (U x x) 1
  rw [hπ,show ‖(-1:ℂ)-1‖=(2:ℝ) by norm_num,norm_sub_rev (-1:ℂ)] at h₁
  rw [hπ] at hδ
  rw [norm_sub_rev (phase (-t) E) (U x x)] at h₂
  linarith only [h₁,h₂,hδ,hc,hu]

private def cutSide {C : TwoQubitCircuit (n+2)} (c : Cut C) := Finset.univ.filter fun i => c.val i=true

private theorem opposite_bits (a b : Bool) (h : a≠b) : a=true ↔ b≠true := by
  cases a <;> cases b <;> simp_all

/-- Each selected bond contributes its full mixed longitudinal coefficient. -/
private theorem crossed_mass (u : PathShell n) {C : TwoQubitCircuit (n+2)} (c : Cut C) (Q : Finset (Fin (n+1)))
    (hQ : Q ⊆ crossed c) (t : ℝ) (ht : 0≤t) (hmass : π ≤ 4*t*∑ e∈Q, |u (zz e)|) :
    let v := mixedShell (ends Q∩cutSide c) (ends Q\cutSide c) u
    π ≤ t*∑ e, |v (zz e)| := by
  intro v
  have hv (e) (he : e∈Q) : v (zz e)=4*u (zz e) := by
    have hi (i) (h : i ∈ ({e.castSucc,e.succ} : Finset (Fin (n+2)))) : i∈ends Q := Finset.mem_biUnion.mpr ⟨e,he,h⟩
    apply mixed_crossed u (ends Q) (cutSide c) e (hi _ (by simp)) (hi _ (by simp))
    simpa only [cutSide,Finset.mem_filter,Finset.mem_univ,true_and] using
      opposite_bits _ _ ((mem_crossed_iff c e).mp (hQ he))
  have he : (∑ e∈Q, |v (zz e)|)=4*∑ e∈Q, |u (zz e)| := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e h => by rw [hv e h,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Q)
    (fun e _ _ => abs_nonneg (v (zz e)))) ht
  rw [he] at hh
  exact (hmass.trans_eq (by ring : 4*t*(∑ e∈Q, |u (zz e)|)=t*(4*∑ e∈Q, |u (zz e)|))).trans hh

/-- The two circuit-side flips have zero transmitted signal before approximation. -/
private theorem fitted_echo {C : TwoQubitCircuit (n+2)} (c : Cut C) (L R : Finset (Fin (n+2)))
    (hl : L ⊆ cutSide c) (hr : R ⊆ (cutSide c)ᶜ) (U : Matrix.unitaryGroup (Fin (n+2)→Bool) ℂ) (z : ℂ) (hz : ‖z‖=1) :
    ‖echo U.val (flip L) (flip R)-1‖ ≤ 4*‖U.val-z • C.eval.val‖ := by
  have hcomm := SpanningDensity.circuit_conjugate_supported C (cutSide c) (fun i => by
    simp only [cutSide,Finset.mem_filter,Finset.mem_univ,true_and,c.gate_agrees i]) (flip L) ((flip_supported L).mono hl)
  have hflip (A : Finset (Fin (n+2))) : ‖flip A‖≤1 := (CStarRing.norm_of_mem_unitary (finitePauliMatrix_mem_unitary (mask A))).le
  rw [echo_norm U.val (flip L) (flip R) U.property (finitePauliMatrix_mem_unitary (mask L)) (finitePauliMatrix_mem_unitary (mask R))
    (finitePauliMatrix_mul_self (mask L)) (finitePauliMatrix_mul_self (mask R))]
  exact SpanningDensity.missing_signal_bound C U z hz (flip L) (flip R) (hflip L) (hflip R)
    (commute_of_isSiteSupported_disjoint disjoint_compl_right hcomm ((flip_supported R).mono hr))

private theorem quarter_floor (d e t M q w : ℝ) (hphase : 2 ≤ e+t*(sqrt 21*w)+8*(t*M))
    (hflow : e ≤ 16*(4*43^2*q*M^2)*t^2+4*d) (hw : w^2 ≤ 43*q*(4*M)^2)
    (hsmall : t*M≤1/100) (hvar : q*M^2*t^2≤1/1000000) : 1/4<d := by
  have hsq : (t*(sqrt 21*w))^2 ≤ 21*43*16*(q*M^2*t^2) := by
    rw [mul_pow,mul_pow,sq_sqrt (by norm_num : (0:ℝ)≤21)]
    nlinarith only [mul_le_mul_of_nonneg_left hw (sq_nonneg t)]
  have hsd : t*(sqrt 21*w) ≤ 1/4 := by
    apply le_of_sq_le_sq _ (by norm_num)
    nlinarith only [hsq,hvar]
  linarith only [hphase,hflow,hsmall,hvar,hsd]

/-- A cut-respecting circuit cannot approximate the evolution at error
1/4 when the selected crossed bonds provide a half turn at small local error. -/
theorem no_cut_fit (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C) (Q : Finset (Fin (n+1)))
    (hQ : Q ⊆ crossed c) (M t : ℝ) (hM : 0≤M) (ht : 0<t)
    (hm : ∀ e∈Q, localMass u e≤M^2) (hmass : π ≤ 4*t*∑ e∈Q, |u (zz e)|)
    (hsmall : t*M ≤ 1/100) (hvar : (Q.card:ℝ)*M^2*t^2 ≤ 1/1000000) (z : ℂ) (hz : ‖z‖=1) :
    1/4 < ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖ := by
  classical
  let S := cutSide c
  let L := ends Q∩S
  let R := ends Q\S
  let v := mixedShell L R u
  let U : Matrix.unitaryGroup (Fin (n+2)→Bool) ℂ := ⟨_,unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t⟩
  have hl : L ⊆ S := Finset.inter_subset_right
  have hr : R ⊆ Sᶜ := fun _ h => Finset.mem_compl.mpr (Finset.mem_sdiff.mp h).2
  have hd : Disjoint L R := disjoint_compl_right.mono hl hr
  obtain ⟨ha,hb⟩ := mixed_bounds u Q L R Finset.inter_subset_left M hM hm
  have hp := phase_half_bound v t ht M hM (mixed_energy u hd) ha (crossed_mass u c Q hQ t ht.le hmass)
  have he := echo_error u Q M t hM ht.le hm L R hd Finset.inter_subset_left Finset.sdiff_subset
  let F := echo U.val (flip L) (flip R)
  let E := unitaryEvolution (pathHamiltonian v) (-t)
  have hh : ‖E-1‖ ≤ ‖F-E‖+‖F-1‖ := by
    rw [norm_sub_rev F E]; exact norm_sub_le_norm_sub_add_norm_sub E F 1
  exact quarter_floor _ _ t M Q.card ‖v‖ hp (hh.trans (add_le_add he (fitted_echo c L R hl hr U z hz))) hb hsmall hvar

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
