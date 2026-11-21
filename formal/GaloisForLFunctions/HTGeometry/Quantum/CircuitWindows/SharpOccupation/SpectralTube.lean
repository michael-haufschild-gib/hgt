import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhaseBoxes
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryDiagonal

/-! # Sharp spectral-torus domination of one arbitrary physical unitary -/
open Matrix Complex Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

private theorem arc_tolerance_sq_lt_two {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1/2) :
    0 ≤ zeroGateArcTolerance r ∧ (zeroGateArcTolerance r)^2 < 2 := by
  have h0 : 0 ≤ Real.pi*r/2 := by positivity
  have hπ : Real.pi*r/2 < Real.pi/4 := by
    linarith only [mul_lt_mul_of_pos_left hr' Real.pi_pos]
  have hh := Real.strictMonoOn_sin (show Real.pi*r/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by
    constructor <;> linarith only [h0,hπ,Real.pi_pos])
    (show Real.pi/4 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith only [Real.pi_pos]) hπ
  rw [Real.sin_pi_div_four] at hh
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith only [hπ,Real.pi_pos])
  have ha : 0 ≤ zeroGateArcTolerance r := mul_nonneg zero_le_two hs
  have hb : zeroGateArcTolerance r < Real.sqrt 2 := by unfold zeroGateArcTolerance; linarith only [hh]
  exact ⟨ha,(pow_lt_pow_left₀ hb ha (by decide : 2 ≠ 0)).trans_eq (Real.sq_sqrt (by norm_num))⟩

/-- Each physical unitary has a fixed spectral phase packet whose projective
tube at the same tolerance contains every visit to the original unitary. -/
theorem unitary_visits_subset_shifted {n : ℕ} (H : selfAdjoint (Register n))
    (W : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
    ∃ ψ : (Fin n → Bool) → ℝ, ∀ (r : ℝ), 0 ≤ r → r < 1/2 → ∀ (t : ℝ) (c : ℂ), ‖c‖=1 →
      ‖unitaryEvolution H.val t-c • (W:Register n)‖ ≤ zeroGateArcTolerance r →
        t ∈ shiftedTimes H ψ r := by
  let V := H.2.isHermitian.eigenvectorUnitary
  let B := V⁻¹*W*V
  let ψ (i : Fin n → Bool) := ((B : Register n) i i).arg
  refine ⟨ψ,?_⟩
  intro r hr hr' t c hc h
  let θ (j : Fin n → Bool) := -(t*H.2.isHermitian.eigenvalues j)
  let f (j : Fin n → Bool) := Complex.exp ((θ j:ℂ)*I)
  have hf (j) : ‖f j‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hU : unitaryEvolution H.val t = (V:Register n)*diagonal f*star (V:Register n) := by
    rw [unitaryEvolution_spectral H.2.isHermitian]
    congr 2
    funext j
    dsimp [f,θ]
    push_cast
    congr 1
    ring
  have hBW : (V:Register n)*(B:Register n)*star (V:Register n) = (W:Register n) := by
    have he : V*B*V⁻¹=W := by dsimp [B]; group
    exact congrArg Subtype.val he
  have hdiff : ‖diagonal f-c • (B:Register n)‖ ≤ zeroGateArcTolerance r := by
    rw [← l2_opNorm_unitary_conj_eq V.2,Matrix.mul_sub,Matrix.sub_mul,←hU,
      Matrix.mul_smul,Matrix.smul_mul,hBW]
    exact h
  obtain ⟨hε,hsmall⟩ := arc_tolerance_sq_lt_two hr hr'
  have hphase : Complex.exp ((c.arg:ℂ)*I)=c := by
    simpa only [hc,Complex.ofReal_one,one_mul] using Complex.norm_mul_exp_arg_mul_I c
  have hangle (j) : circDist (θ j-ψ j) c.arg ≤ Real.pi*r := by
    let q := Complex.exp ((ψ j:ℂ)*I)
    have hq : ‖q‖=1 := Complex.norm_exp_ofReal_mul_I _
    have hraw := rounded_diagonal_chord f hf (B:Register n) B.2 c hc _ hε hsmall hdiff j
    change ‖f j-c*q‖ ≤ _ at hraw
    have he : Complex.exp (((θ j-ψ j:ℝ):ℂ)*I) = f j/q := by
      rw [Complex.ofReal_sub,sub_mul,Complex.exp_sub]
    have hchord : ‖Complex.exp (((θ j-ψ j:ℝ):ℂ)*I)-Complex.exp ((c.arg:ℂ)*I)‖ ≤
        zeroGateArcTolerance r := by
      rw [he,hphase,div_sub' (norm_ne_zero_iff.mp (hq.trans_ne one_ne_zero)),norm_div,hq,div_one,mul_comm q c]
      exact hraw
    rw [norm_expI_sub_eq_sin_circDist,zeroGateArcTolerance,mul_le_mul_iff_of_pos_left zero_lt_two] at hchord
    have hd0 := circDist_nonneg (θ j-ψ j) c.arg
    have hdπ := circDist_le_pi (θ j-ψ j) c.arg
    have hx := mul_le_mul_of_nonneg_left hr'.le Real.pi_pos.le
    have hhalf := Real.strictMonoOn_sin.le_iff_le
      (show circDist (θ j-ψ j) c.arg/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith only [hd0,hdπ,Real.pi_pos])
      (show Real.pi*r/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith only [mul_nonneg Real.pi_pos.le hr,hx,Real.pi_pos])
    linarith only [hhalf.mp hchord]
  change spectralEnclosingArcLength (fun j => θ j-ψ j) ≤ _
  exact (spectralEnclosingArcLength_le_twice_radius _ _ _ hangle).trans_eq (by ring)

#print axioms unitary_visits_subset_shifted
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
