import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EigenlineSignals.GateFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.TimedReflection

/-! # A hard spectrum in every basis followed by a scalar echo -/
open Matrix MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EigenlineSignals
noncomputable section
open SpectralJets SpanningDensity.ProductInputs
private abbrev Reg (n : ℕ) := Matrix (Fin n→Bool) (Fin n→Bool) ℂ

theorem single_reflection {N d : ℕ} (e : (Fin N→Bool) ≃ Fin (d+1))
    (V : Matrix.unitaryGroup (Fin N→Bool) ℂ) (j : Fin d) :
    anchoredSpectralBooleanReflection e V (fun k => decide (k=j))=
      twist (-1) (marked V (e.symm j.succ)) := by
  let r := e.symm j.succ
  have hp (k : Fin (d+1)) : anchoredBooleanPacket (fun i => decide (i=j)) k=
      if k=j.succ then -1 else 1 := by
    refine Fin.cases (by simp [anchoredBooleanPacket]) (fun i => ?_) k
    by_cases h : i=j <;> simp [anchoredBooleanPacket,h]
  have hd : Matrix.diagonal (anchoredBooleanPacket (fun i => decide (i=j)) ∘ e)=
      (1 : Reg N)+((-1:ℂ)-1) • basisProjector r := by
    ext i k
    by_cases hi : i=k
    · subst k
      have he : e i=j.succ ↔ i=r := by
        constructor
        · intro h; exact e.injective (h.trans (e.apply_symm_apply _).symm)
        · intro h; rw [h]; exact e.apply_symm_apply _
      by_cases h : i=r <;> simp [Function.comp_apply,hp,he,h,basisProjector]
    · simp [Matrix.diagonal_apply,Matrix.one_apply,hi,basisProjector]
  rw [anchoredSpectralBooleanReflection,hd,show (V⁻¹).val=star V.val by simp]
  simp only [mul_add,add_mul,mul_one,Matrix.mul_smul,Matrix.smul_mul,
    (Unitary.mem_iff.mp V.property).2,marked,twist]

/-- Moving a unit scalar from the reflection to the target preserves distance. -/
theorem move_phase {N : ℕ} (R U : Reg N) (z : ℂ) (hz : ‖z‖=1) :
    ‖R-z⁻¹ • U‖=‖U-z • R‖ := by
  have hn : z ≠ 0 := norm_ne_zero_iff.mp (hz.trans_ne one_ne_zero)
  rw [norm_sub_rev,show z⁻¹ • U-R=z⁻¹ • (U-z • R) by
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hn,one_smul],norm_smul,norm_inv,hz,inv_one,one_mul]

private theorem basis_change {N : ℕ} (W V : Matrix.unitaryGroup (Fin N→Bool) ℂ)
    (z : ℂ) (r : Fin N→Bool) :
    W.val*twist z (marked V r)*star W.val=twist z (marked (W*V) r) := by
  simp only [twist,marked,mul_add,add_mul,mul_one,Matrix.mul_smul,Matrix.smul_mul,
    (Unitary.mem_iff.mp W.property).2,Submonoid.coe_mul,star_mul,mul_assoc]

/-- Each sufficiently large prefix has, in every phase-filling interval, a
date requiring at least N−1+floor((N−1)/2) gates even after an arbitrary
basis change. At twice that date the empty circuit achieves error 1/40. -/
theorem gaussian_conjugacy_hard_echo :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Reg N) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a : ℝ, ∃ t ∈ Icc a (a+derivativePhaseHorizon k),
        (∀ (W : Matrix.unitaryGroup (Fin N→Bool) ℂ) (s : ℕ),
          HasProjectiveCircuitApproximation N (1/10) s (W.val*unitaryEvolution H.val t*star W.val) →
          N-1+(N-1)/2 ≤ s) ∧
        HasProjectiveCircuitApproximation N (1/40) 0 (unitaryEvolution H.val (2*t)) := by
  filter_upwards [gaussian_path_derivative_phase_filling] with ω hω
  filter_upwards [hω] with k hk
  intro N H a
  obtain ⟨e,hfill⟩ := hk
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  have hdim : 1 < 2^N := one_lt_pow₀ (by norm_num) (by dsimp only [N]; omega)
  let j : Fin (2^N-1) := ⟨0,by omega⟩
  let x (i : Fin (2^N-1)) := decide (i=j)
  let r := e.symm j.succ
  let J := anchoredSpectralBooleanReflection e V x
  obtain ⟨t,ht,z,hz,hclose⟩ := phase_interval_approaches_reflection e H a _ (hfill a) x
  change ‖unitaryEvolution H.val t-z • J‖ ≤ 1/80 at hclose
  refine ⟨t,ht,?_,?_⟩
  · intro W s hs
    let U := unitaryEvolution H.val t
    let M := W.val*U*star W.val
    let R := twist (-1) (marked (W*V) r)
    have hw : W.val*J*star W.val=R := by rw [show J=twist (-1) (marked V r) from single_reflection e V j,basis_change]
    have hh : ‖M-z • R‖ ≤ 1/80 := by
      rw [←hw,show M-z • (W.val*J*star W.val)=W.val*(U-z • J)*star W.val by
        simp only [M,mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul]]
      rwa [l2_opNorm_unitary_conj_eq W.property]
    have hr : ‖R-z⁻¹ • M‖ ≤ 1/80 := (move_phase R M z hz).le.trans hh
    obtain ⟨w,hphase,C,hcost,he⟩ := hs
    apply marked_robust_gate_count (by dsimp [N]; omega) (W*V) r (by norm_num : ‖(-1:ℂ)‖=1)
      (z⁻¹ • M) (1/10) (1/80) hr (by norm_num) s
    refine ⟨z⁻¹*w,by rw [norm_mul,norm_inv,hz,hphase]; norm_num,C,hcost,?_⟩
    rwa [←smul_smul,←smul_sub,norm_smul,norm_inv,hz,inv_one,one_mul]
  · let w : Circle := ⟨z,by change z ∈ Metric.sphere (0:ℂ) 1; simpa using hz⟩
    obtain ⟨c,hc,C,hC,he⟩ := spectral_sign_doubled_time_zero_gate e V x H t w
    refine ⟨c,hc,C,hC,he.trans ?_⟩
    change 2*‖unitaryEvolution H.val t-z • J‖ ≤ 1/40
    linarith only [hclose]

#print axioms gaussian_conjugacy_hard_echo
end
end GaloisForLFunctions.HTGeometry.EigenlineSignals
