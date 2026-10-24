import GaloisForLFunctions.ArithmeticDefectRigidity.TheCofactorTailCarriesTheForcing
import GaloisForLFunctions.RHTower.StieltjesGammaAffineMultiPrime

/-!
# A source-defined growing cofactor window misses the forcing

The cutoff `floor(log(F_T/E_T))` tends to infinity for the actual source. Its cofactor tail
still converges to the complete forcing in forcing normalization. The error is paid by
`(1 + log(F_T/E_T))² / (F_T/E_T)`, which tends to zero.

This gives a growing window with a proved error, rather than an exchange of fixed-cutoff and
horizon limits. The cutoff is computed from finite source energies; no admission input is used.
-/

open Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- A growing cofactor window determined by the separation of the two source energies. -/
def forcingCofactorWindow (ε : ℝ) (T : ℕ) : ℕ :=
  ⌊Real.log (forcingEnergy ε T / dampedMobiusEnergy ε T)⌋₊

theorem tendsto_forcingCofactorWindow_atTop (ε : SubcriticalDamping) :
    Tendsto (forcingCofactorWindow ε) atTop atTop := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_forcingEnergy_div_receiver_atTop ε)
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hlog.eventually_ge_atTop (b : ℝ)] with T hT
  exact Nat.le_floor hT

/-- The signed tail beyond the growing source-defined window retains all forcing energy. -/
theorem tendsto_movingCofactorTailError_div_forcingEnergy_zero (ε : SubcriticalDamping) :
    Tendsto (fun T => cofactorTailErrorEnergy ε (forcingCofactorWindow ε T) T /
      forcingEnergy ε T) atTop (𝓝 0) := by
  have hratio := tendsto_forcingEnergy_div_receiver_atTop ε
  have hlog := Real.tendsto_log_atTop.comp hratio
  have hlim := (RHTower.StieltjesGammaAffine.tendsto_one_add_log_pow_div_atTop 2).comp hratio
  refine squeeze_zero' (Filter.Eventually.of_forall fun T =>
    div_nonneg (cofactorTailErrorEnergy_nonneg ε _ T) (forcingEnergy_nonneg ε T)) ?_ hlim
  filter_upwards [hlog.eventually_ge_atTop 0] with T hT
  have hfloor : (forcingCofactorWindow ε T : ℝ) ≤
      Real.log (forcingEnergy ε T / dampedMobiusEnergy ε T) := Nat.floor_le hT
  have hhead := cofactorHeadCoefficient_le ε (forcingCofactorWindow ε T)
  have hcost : (1 + cofactorHeadCoefficient ε (forcingCofactorWindow ε T)) ^ 2 ≤
      (1 + Real.log (forcingEnergy ε T / dampedMobiusEnergy ε T)) ^ 2 :=
    pow_le_pow_left₀ (by linarith [cofactorHeadCoefficient_nonneg (ε : ℝ)
      (forcingCofactorWindow ε T)]) (add_le_add (le_refl 1) (hhead.trans hfloor)) 2
  calc
    _ ≤ (1 + cofactorHeadCoefficient ε (forcingCofactorWindow ε T)) ^ 2 *
        (dampedMobiusEnergy ε T / forcingEnergy ε T) := by
      simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
        (cofactorTailErrorEnergy_le (ε : ℝ) (forcingCofactorWindow ε T) T)
        (forcingEnergy_nonneg ε T)
    _ ≤ (1 + Real.log (forcingEnergy ε T / dampedMobiusEnergy ε T)) ^ 2 *
        (dampedMobiusEnergy ε T / forcingEnergy ε T) :=
      mul_le_mul_of_nonneg_right hcost
        (div_nonneg (dampedMobiusEnergy_nonneg ε T) (forcingEnergy_nonneg ε T))
    _ = (1 + Real.log (forcingEnergy ε T / dampedMobiusEnergy ε T)) ^ 2 *
        (forcingEnergy ε T / dampedMobiusEnergy ε T)⁻¹ := by rw [inv_div]
    _ = _ := (div_eq_mul_inv _ _).symm

end GaloisForLFunctions.ArithmeticDefectRigidity
