import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.GeneratorTail
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.GeneratorApproximation

/-! # Gate cost forced by the spectral tails of a local generator -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
noncomputable section

/-- The displacement exceeding twice the fitting error leaves a margin
for truncating the energy layers. Its square enters the gate floor. -/
theorem spectral_gate_floor_margin {n : ℕ} (u : PathShell n) {t B ρ ε : ℝ}
    (ht : t ≠ 0) (hρ : 0 < ρ)
    (hB : 0 < B) (hmass : ‖u‖^2 ≤ B) (W : unitaryGroup (Fin (n+2) → Bool) ℂ)
    {s : ℕ} (hfar : 2*ε+ρ < ‖1-unitaryEvolution (pathHamiltonian u) t‖)
    (hfit : HasProjectiveCircuitApproximation (n+2) ε s
      (W.val*unitaryEvolution (pathHamiltonian u) t*star W.val)) :
    ρ^2/(882*B*t^2) ≤ Real.log 42+(s:ℝ)*Real.log 4 := by
  let r := ρ/(21*|t|)
  have hpos := abs_pos.mpr ht
  have hr : 0 < r := div_pos hρ (mul_pos (by norm_num) hpos)
  obtain ⟨G,hG,hrank⟩ := path_generator_tail u hB hmass hr.le
  have he : |t| *(21*r)=ρ := by dsimp only [r]; field_simp [hpos.ne']
  have hdist := mul_le_mul_of_nonneg_left hG hpos.le
  rw [he] at hdist
  have hc := generator_rank_gate_floor (isSelfAdjoint_pathHamiltonian u).isHermitian t G W
    (by linarith only [hdist,hfar]) hfit
  have hsize : 2^(n+2) ≤ 4^s*G.rank := by
    calc 2^(n+2) ≤ 2^(2*s+(n+2-2*s)) := Nat.pow_le_pow_right (by decide) (by omega)
         _ = 4^s*2^(n+2-2*s) := by rw [pow_add,pow_mul]; rfl
         _ ≤ _ := Nat.mul_le_mul_left _ hc
  let D := (2:ℝ)^(n+2)
  let x := r^2/(2*B)
  have hD : 0 < D := pow_pos (by norm_num) _
  have hsize' : D ≤ (4:ℝ)^s*(G.rank:ℝ) := by dsimp only [D]; exact_mod_cast hsize
  have hscaled := hsize'.trans (mul_le_mul_of_nonneg_left hrank (by positivity))
  have hone : 1 ≤ 42*(4:ℝ)^s*Real.exp (-x) := by
    apply (mul_le_mul_iff_left₀ hD).mp
    change D ≤ (4:ℝ)^s*(42*D*Real.exp (-(r^2)/(2*B))) at hscaled
    rw [neg_div] at hscaled
    change D ≤ (4:ℝ)^s*(42*D*Real.exp (-x)) at hscaled
    linarith only [hscaled]
  rw [Real.exp_neg,←div_eq_mul_inv,le_div_iff₀ (Real.exp_pos x),one_mul] at hone
  have hlog := Real.log_le_log (Real.exp_pos x) hone
  rw [Real.log_exp,Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hlog
  apply le_trans (le_of_eq ?_) hlog
  dsimp only [x,r]
  rw [div_pow,mul_pow,sq_abs]
  field_simp [hB.ne',ht]
  ring

/-- Outside the quarter-ball, fitting at error one tenth costs order
1/(Bt²) gates even after an arbitrary basis change. -/
theorem spectral_gate_floor {n : ℕ} (u : PathShell n) {t B : ℝ} (ht : t ≠ 0)
    (hB : 0 < B) (hmass : ‖u‖^2 ≤ B) (W : unitaryGroup (Fin (n+2) → Bool) ℂ)
    {s : ℕ} (hfar : (1/4:ℝ) < ‖1-unitaryEvolution (pathHamiltonian u) t‖)
    (hfit : HasProjectiveCircuitApproximation (n+2) (1/10) s
      (W.val*unitaryEvolution (pathHamiltonian u) t*star W.val)) :
    1/(352800*B*t^2) ≤ Real.log 42+(s:ℝ)*Real.log 4 := by
  have h := spectral_gate_floor_margin u ht (by norm_num : (0:ℝ)<1/20) hB hmass W
    (by rwa [show 2*(1/10:ℝ)+1/20=1/4 by norm_num]) hfit
  apply le_trans (le_of_eq ?_) h
  field_simp [hB.ne',ht]
  ring

#print axioms spectral_gate_floor
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
