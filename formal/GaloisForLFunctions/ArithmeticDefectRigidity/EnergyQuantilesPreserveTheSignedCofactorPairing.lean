import GaloisForLFunctions.ArithmeticDefectRigidity.EnergyQuantilesRetainDiffuseEscape
import GaloisForLFunctions.ArithmeticDefectRigidity.TheRenormalizedCofactorIsAntipodalOnEscape

/-!
# Signed cofactor pairing survives energy-quantile transport

The paid forcing remainder controls signed cofactor work on every energy-quantile interval.
The error is uniform over both endpoints: at total energy `E`, it is at most `2 B √E + 1`.
Thus diffuse energy transport retains the actual antipodal pairing, rather than only the
positive energy distribution. Mixed covariances with other arithmetic operations remain
separate quantities.
-/

open Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- Signed actual cofactor work between two prescribed energy crossings. -/
def quantileCofactorWork (ε : SubcriticalDamping) (T : ℕ) (r s : EnergyFraction) : ℝ :=
  renormalizedCofactorWork ε (receiverEnergyQuantile ε T s) -
    renormalizedCofactorWork ε (receiverEnergyQuantile ε T r)

private theorem abs_quantile_antipodal_error_le (ε : SubcriticalDamping) (T : ℕ)
    (r : EnergyFraction) :
    |dampedMobiusEnergy ε (receiverEnergyQuantile ε T r) +
      renormalizedCofactorWork ε (receiverEnergyQuantile ε T r)| ≤
        Real.sqrt (dampedMobiusEnergy ε T) * forcingRemainderBudget ε := by
  refine (abs_receiverEnergy_add_renormalizedCofactorWork_le ε _).trans ?_
  exact mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt ((dampedMobiusEnergy_mono ε) (receiverEnergyQuantile_le_horizon ε T r)))
    (forcingRemainderBudget_nonneg ε)

/-- Quantile transport preserves signed work with a uniform absolute source budget. -/
theorem abs_quantileCofactorWork_error_le (ε : SubcriticalDamping) (T : ℕ)
    (r s : EnergyFraction) :
    |quantileCofactorWork ε T r s + ((s : ℝ) - (r : ℝ)) * dampedMobiusEnergy ε T| ≤
      2 * forcingRemainderBudget ε * Real.sqrt (dampedMobiusEnergy ε T) + 1 := by
  let er := dampedMobiusEnergy ε (receiverEnergyQuantile ε T r)
  let es := dampedMobiusEnergy ε (receiverEnergyQuantile ε T s)
  let wr := renormalizedCofactorWork ε (receiverEnergyQuantile ε T r)
  let ws := renormalizedCofactorWork ε (receiverEnergyQuantile ε T s)
  have hr : |er + wr| ≤ Real.sqrt (dampedMobiusEnergy ε T) * forcingRemainderBudget ε :=
    abs_quantile_antipodal_error_le ε T r
  have hs : |es + ws| ≤ Real.sqrt (dampedMobiusEnergy ε T) * forcingRemainderBudget ε :=
    abs_quantile_antipodal_error_le ε T s
  have hq : |(es - er) - ((s : ℝ) - (r : ℝ)) * dampedMobiusEnergy ε T| ≤ 1 :=
    abs_receiverEnergyQuantile_interval_error_le ε T r s
  have heq : quantileCofactorWork ε T r s +
      ((s : ℝ) - (r : ℝ)) * dampedMobiusEnergy ε T =
      ((es + ws) - (er + wr)) -
        ((es - er) - ((s : ℝ) - (r : ℝ)) * dampedMobiusEnergy ε T) := by
    unfold quantileCofactorWork er es wr ws
    ring
  have htri : |(es + ws) - (er + wr)| ≤ |es + ws| + |er + wr| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (es + ws) (-(er + wr))
  rw [heq]
  calc
    _ ≤ |(es + ws) - (er + wr)| +
        |(es - er) - ((s : ℝ) - (r : ℝ)) * dampedMobiusEnergy ε T| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le ((es + ws) - (er + wr))
        (-((es - er) - ((s : ℝ) - (r : ℝ)) * dampedMobiusEnergy ε T))
    _ ≤ (|es + ws| + |er + wr|) +
        |(es - er) - ((s : ℝ) - (r : ℝ)) * dampedMobiusEnergy ε T| :=
      add_le_add htri (le_refl _)
    _ ≤ _ := by linarith

/-- A squared relative budget, uniform over both energy-quantile endpoints. -/
theorem normalized_quantileCofactorWork_error_sq_le (ε : SubcriticalDamping) (T : ℕ)
    (r s : EnergyFraction) :
    (quantileCofactorWork ε (T + 1) r s / dampedMobiusEnergy ε (T + 1) +
      ((s : ℝ) - (r : ℝ))) ^ 2 ≤
      8 * forcingRemainderBudget ε ^ 2 / dampedMobiusEnergy ε (T + 1) +
        2 * (1 / dampedMobiusEnergy ε (T + 1)) ^ 2 := by
  have hE := receiverEnergy_succ_pos ε T
  have hsq := pow_le_pow_left₀ (abs_nonneg _)
    (abs_quantileCofactorWork_error_le ε (T + 1) r s) 2
  rw [sq_abs] at hsq
  have hupper : (quantileCofactorWork ε (T + 1) r s +
      ((s : ℝ) - (r : ℝ)) * dampedMobiusEnergy ε (T + 1)) ^ 2 ≤
      8 * forcingRemainderBudget ε ^ 2 * dampedMobiusEnergy ε (T + 1) + 2 := by
    refine hsq.trans ?_
    calc
      _ ≤ 2 * (2 * forcingRemainderBudget ε *
          Real.sqrt (dampedMobiusEnergy ε (T + 1))) ^ 2 + 2 := by
        nlinarith [sq_nonneg (2 * forcingRemainderBudget ε *
          Real.sqrt (dampedMobiusEnergy ε (T + 1)) - 1)]
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hE.le]; ring
  calc
    _ = (quantileCofactorWork ε (T + 1) r s +
        ((s : ℝ) - (r : ℝ)) * dampedMobiusEnergy ε (T + 1)) ^ 2 /
        dampedMobiusEnergy ε (T + 1) ^ 2 := by field_simp [hE.ne']
    _ ≤ (8 * forcingRemainderBudget ε ^ 2 * dampedMobiusEnergy ε (T + 1) + 2) /
        dampedMobiusEnergy ε (T + 1) ^ 2 :=
      div_le_div_of_nonneg_right hupper (sq_nonneg _)
    _ = _ := by field_simp [hE.ne']

/-- Escaping receivers retain the signed antipodal pairing on every energy-quantile interval. -/
theorem admits_or_quantiles_preserve_antipodal_work (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ r s : EnergyFraction,
      Tendsto (fun T => (quantileCofactorWork ε (T + 1) r s /
        dampedMobiusEnergy ε (T + 1) + ((s : ℝ) - (r : ℝ))) ^ 2) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · have hE' := hE.comp (tendsto_add_atTop_nat 1)
    have hi : Tendsto (fun T => 1 / dampedMobiusEnergy ε (T + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hE'
    have hfirst : Tendsto (fun T => 8 * forcingRemainderBudget ε ^ 2 /
        dampedMobiusEnergy ε (T + 1)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hE'
    have hlast : Tendsto (fun T => 2 * (1 / dampedMobiusEnergy ε (T + 1)) ^ 2)
        atTop (𝓝 0) := by simpa using (hi.pow 2).const_mul 2
    refine Or.inr fun r s => squeeze_zero (fun T => sq_nonneg _)
      (fun T => normalized_quantileCofactorWork_error_sq_le ε T r s) ?_
    simpa only [add_zero] using hfirst.add hlast

end GaloisForLFunctions.ArithmeticDefectRigidity
