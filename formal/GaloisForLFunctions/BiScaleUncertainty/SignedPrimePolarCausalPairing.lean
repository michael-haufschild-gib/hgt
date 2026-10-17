import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalMoments

open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower
noncomputable section
set_option autoImplicit false

theorem primeTerm_sourceFactorialCausal {N : ℕ} (hN : 1 ≤ N) :
    primeTerm (sourceFactorialCausal N) = primeTerm (factorialBiNull N) := by
  funext n
  unfold primeTerm
  split_ifs with hn
  · rw [sourceFactorialCausal_at_log hN (by omega)]
  · rfl

theorem sourceFactorialCausal_admissible {N : ℕ} (hN : 1 ≤ N) :
    (Function.support (primeTerm (sourceFactorialCausal N))).Finite ∧
      Summable (fun n => |primeTerm (sourceFactorialCausal N) n|) ∧
      IntegrableOn (fun x => polarDensity x*sourceFactorialCausal N x) (Ici 0) := by
  rw [primeTerm_sourceFactorialCausal hN]
  refine ⟨(factorialBiNull_admissible N).1, (factorialBiNull_admissible N).2.1, ?_⟩
  exact ((continuous_polarDensity.mul (continuous_sourceFactorialCausal N)).integrable_of_hasCompactSupport
    ((hasCompactSupport_sourceFactorialCausal hN).mul_left (f := polarDensity))).integrableOn

theorem fullPairing_sourceFactorialCausal_eq {N : ℕ} (hN : 1 ≤ N) :
    fullPairing (sourceFactorialCausal N) =
      (2*chebyshevBiNullProducer N-sourceFactorialCoefficient N*harmonicCorrection N)/Real.sqrt N := by
  have hip : Integrable (fun x => Real.exp (x/2)*sourceFactorialCausal N x) :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul
      (continuous_sourceFactorialCausal N)).integrable_of_hasCompactSupport
        ((hasCompactSupport_sourceFactorialCausal hN).mul_left)
  have him : Integrable (fun x => Real.exp (-(x/2))*sourceFactorialCausal N x) :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2).neg).mul
      (continuous_sourceFactorialCausal N)).integrable_of_hasCompactSupport
        ((hasCompactSupport_sourceFactorialCausal hN).mul_left)
  have hp : (fun x => polarDensity x*sourceFactorialCausal N x) =
      fun x => Real.exp (x/2)*sourceFactorialCausal N x+Real.exp (-(x/2))*sourceFactorialCausal N x := by
    funext x
    unfold polarDensity
    rw [Real.cosh_eq]
    ring
  unfold fullPairing
  rw [primeTerm_sourceFactorialCausal hN, tsum_primeTerm_factorialBiNull,
    ← integral_weight_sourceFactorialCausal_eq_halfLine hN polarDensity, hp,
    integral_add hip him, integral_exp_half_sourceFactorialCausal hN,
    integral_exp_neg_half_sourceFactorialCausal hN]
  ring

theorem abs_fullPairing_sourceFactorialCausal_le {N : ℕ} (hN : 1 ≤ N) :
    |fullPairing (sourceFactorialCausal N)| ≤
      (10*Real.log (4*(N : ℝ)+1)+3+1/(4*(N : ℝ)))/Real.sqrt N := by
  rw [fullPairing_sourceFactorialCausal_eq hN, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hb := abs_chebyshevBiNullProducer_le hN
  obtain ⟨hc0,hc1⟩ := harmonicCorrection_bounds hN
  obtain ⟨ha0,ha1⟩ := sourceFactorialCoefficient_bounds hN
  calc
    _ ≤ |2*chebyshevBiNullProducer N|+|sourceFactorialCoefficient N*harmonicCorrection N| := abs_sub _ _
    _ = 2*|chebyshevBiNullProducer N|+sourceFactorialCoefficient N*harmonicCorrection N := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (mul_nonneg (by linarith) hc0)]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hc1 (by linarith : 0 ≤ sourceFactorialCoefficient N)]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
