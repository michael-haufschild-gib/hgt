import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalWeightedEntryModels
import GaloisForLFunctions.U0.PolyAsymptotics
import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalFlatTransfer
import Mathlib.Tactic.ComputeDegree

namespace HTGeometry.ThetaRatioWeightedSquare
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity Filter Topology
open RHTower.ThetaCuspModularRatio

-- Natural endpoint of the proposed whole-cone certificate, with every
-- source moment retained. This is not an actual finite-center point.
theorem terminalUpperDeterminant_boundary_pos :
    0 < ((terminalUpperDeterminant (10000000000000:ℂ)).eval (5/4)).re := by
  rw [terminalUpperDeterminantNorm.property]
  norm_num [terminalUpperDeterminantNorm, Nat.rawCast, Int.rawCast]

theorem terminalUpperDeterminant_degree_le :
    (terminalUpperDeterminant (10000000000000:ℂ)).natDegree ≤ 34 := by
  rw [terminalUpperDeterminantNorm.property]
  dsimp only [terminalUpperDeterminantNorm]
  norm_num only [Nat.rawCast,Int.rawCast]
  compute_degree!

theorem terminalUpperDeterminant_top_re_pos :
    0 < ((terminalUpperDeterminant (10000000000000:ℂ)).coeff 34).re := by
  rw [terminalUpperDeterminantNorm.property]
  dsimp only [terminalUpperDeterminantNorm]
  norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_add,
    Polynomial.coeff_mul_C,Polynomial.coeff_X_pow,Polynomial.coeff_X,←mul_assoc]

theorem terminalUpperDeterminant_degree :
    (terminalUpperDeterminant (10000000000000:ℂ)).natDegree = 34 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero terminalUpperDeterminant_degree_le
  intro h
  have hp := terminalUpperDeterminant_top_re_pos
  rw [h] at hp
  norm_num at hp

theorem terminalUpperDeterminant_leading_re_pos :
    0 < (terminalUpperDeterminant (10000000000000:ℂ)).leadingCoeff.re := by
  rw [←Polynomial.coeff_natDegree,terminalUpperDeterminant_degree]
  exact terminalUpperDeterminant_top_re_pos

theorem actualUpperDeterminant_normalized_tendsto :
    Tendsto (fun x =>
      eval (actualSquarePoint x) (upperCenterDeterminant (10000000000000:ℂ)) /
        (k x:ℂ)^(terminalUpperDeterminant (10000000000000:ℂ)).natDegree)
      atTop (𝓝 (terminalUpperDeterminant (10000000000000:ℂ)).leadingCoeff) := by
  let P := upperCenterDeterminant (10000000000000:ℂ)
  let Q := terminalUpperDeterminant (10000000000000:ℂ)
  have ht := (PolyAsymptotics.tendsto_eval_div_pow_natDegree Q).comp k_tendsto_atTop
  have hd : Tendsto (fun x => eval (actualSquarePoint x) P-eval (terminalBase x) P)
      atTop (𝓝 0) := by
    simpa only [pow_zero,one_mul] using actual_terminal_polynomial_flat P 0
  have hi : Tendsto (fun x => (k x:ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto (0:ℝ)).comp inverse_k_tendsto_zero
  have hs := (hd.mul (hi.pow Q.natDegree)).add ht
  convert hs using 1
  · funext x
    dsimp only [P,Q,Function.comp_def]
    rw [terminalUpperDeterminant_eval]
    simp only [terminalBase,div_eq_mul_inv,inv_pow]
    ring
  · simp [Q]

theorem actualUpperDeterminant_eventually_pos :
    ∀ᶠ x in atTop,
      0 < (eval (actualSquarePoint x)
        (upperCenterDeterminant (10000000000000:ℂ))).re := by
  have hr := (Complex.continuous_re.tendsto
      (terminalUpperDeterminant (10000000000000:ℂ)).leadingCoeff).comp
    actualUpperDeterminant_normalized_tendsto
  have hp := hr.eventually_const_lt terminalUpperDeterminant_leading_re_pos
  filter_upwards [hp,eventually_ge_atTop (0:ℝ)] with x hp hx
  dsimp only [Function.comp_apply] at hp
  rw [←Complex.ofReal_pow,Complex.div_ofReal_re] at hp
  have hk : 0 < k x := lt_trans (by norm_num) (k_gt hx)
  have hs := mul_pos hp
    (pow_pos hk (terminalUpperDeterminant (10000000000000:ℂ)).natDegree)
  rw [div_mul_cancel₀ _ (pow_ne_zero _ hk.ne')] at hs
  exact hs

theorem terminalUpperDeterminant_shift_pos (y : ℝ) (hy : 0 ≤ y) :
    0 < ((terminalUpperDeterminant (10000000000000:ℂ)).eval
      ((5/4+y:ℝ):ℂ)).re := by
  rw [terminalUpperDeterminantNorm.property]
  conv_rhs =>
    norm_num [terminalUpperDeterminantNorm,Nat.rawCast,Int.rawCast,
      ←Complex.ofReal_pow,-Complex.ofReal_add]
    ring_nf
  positivity

end
end HTGeometry.ThetaRatioWeightedSquare
