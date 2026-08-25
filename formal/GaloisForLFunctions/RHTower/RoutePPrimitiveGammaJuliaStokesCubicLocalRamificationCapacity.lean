import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCubicMicrolocalWittSignatureRigidity

/-!
# Cubic wall--Xi local ramification capacity

Every coefficient-generated irregular-Stokes landing of the negative cubic wall--Xi residual pays
a pointwise ramification-capacity cost at every marked point.  Finite Cauchy--Schwarz compares the
common physical rank with local terminal orbit energy, while nonnegative Rees blocks place that
terminal energy below the global positive channel.  The unique negative rank square must dominate
that channel, forcing the product of global Lorentz debt and squared local ramification capacity
strictly above one.

On a one-puncture sphere this gives a positive inverse-capacity gap above normalized Puiseux slope
one.  No landing existence or RH conclusion is asserted.
-/

open GaloisForLFunctions
open GaloisForLFunctions.IrregularStokes
open GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

namespace RHTower

noncomputable section

private theorem localTerminalEnergy_le_globalReesPositiveForm
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    (d : LocalData p n m K N) (parameter : ReesParameter d)
    (hparameter : ∀ a edge, 0 ≤ parameter a edge)
    (x : compatibleCharges d) (a : Fin (p + 1)) :
    (d a).toOrbitCoareaDatum.terminalEnergy (x.1 a) ≤
      globalReesPositiveForm d parameter x := by
  classical
  have hlocal :
      (d a).toOrbitCoareaDatum.terminalEnergy (x.1 a) ≤
        localReesPositiveForm (d a) (parameter a) (x.1 a) := by
    rw [localReesPositiveForm_apply]
    exact le_add_of_nonneg_right
      ((d a).toOrbitCoareaDatum.reesBlockEnergy_nonneg (hparameter a) (x.1 a))
  rw [globalReesPositiveForm, QuadraticMap.sum_apply]
  exact hlocal.trans <| Finset.single_le_sum
    (fun b _ => localReesPositiveForm_nonneg (d b) (hparameter b) (x.1 b))
    (Finset.mem_univ a)

private theorem localRank_sq_le_terminalEnergy_mul_ramificationCapacity
    {r s A B : ℕ} (d : PuiseuxOrbitCoareaDatum r s A B) (x : Fin r → ℝ) :
    localRankLinear d x ^ 2 ≤
      d.toOrbitCoareaDatum.terminalEnergy x *
        ∑ i, (d.toOrbitCoareaDatum.ramification i : ℝ) ^ 2 := by
  rw [localRankLinear_apply, d.toOrbitCoareaDatum.physicalRank_eq_ramification_sum]
  simpa only [OrbitCoareaDatum.terminalEnergy] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x
      (fun i => (d.toOrbitCoareaDatum.ramification i : ℝ)))

/-- Every marked point of a cubic Xi Malgrange landing has enough squared ramification capacity
to carry the unique global Lorentz rank debt. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_localRamificationCapacity_gt_one
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (hparameter : ∀ a edge, 0 ≤ parameter a edge)
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber genus d parameter)
    (a : Fin (p + 1)) :
    1 < -globalRankCoefficient genus d *
      ∑ i, ((d a).toOrbitCoareaDatum.ramification i : ℝ) ^ 2 := by
  have hpositive : 0 < globalReesPositiveForm d parameter x.1 :=
    globalReesPositiveForm_pos d parameter hparameter
      (routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_charge_ne_zero x)
  have hcoefficient : 0 < -globalRankCoefficient genus d :=
    neg_pos.mpr
      (routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_rankCoefficient_neg
        hparameter x)
  have hdebt :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_rankDebt_gt_positive x
  have hcauchy :=
    localRank_sq_le_terminalEnergy_mul_ramificationCapacity (d a) (x.1.1 a)
  rw [compatible_localRank d x.1 a] at hcauchy
  have hterminal :=
    localTerminalEnergy_le_globalReesPositiveForm d parameter hparameter x.1 a
  have hcapacity :
      0 ≤ ∑ i, ((d a).toOrbitCoareaDatum.ramification i : ℝ) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrankBound := mul_le_mul_of_nonneg_left hcauchy hcoefficient.le
  have hterminalBound := mul_le_mul_of_nonneg_left hterminal
    (mul_nonneg hcoefficient.le hcapacity)
  nlinarith

/-- On a one-puncture sphere the cubic Xi landing slope lies above one by the reciprocal squared
ramification capacity, strengthening the bare irregularity bound. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sphereOnePuncture_slope_gt_one_add_inv_ramificationCapacity
    {n m K N : Fin 1 → ℕ}
    {d : LocalData 0 n m K N} {parameter : ReesParameter d}
    (hparameter : ∀ a edge, 0 ≤ parameter a edge)
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber 0 d parameter) :
    1 + 1 / (∑ i, ((d 0).toOrbitCoareaDatum.ramification i : ℝ) ^ 2) <
      (((K 0 + 1 : ℕ) : ℝ) / N 0) := by
  let capacity : ℝ :=
    ∑ i, ((d 0).toOrbitCoareaDatum.ramification i : ℝ) ^ 2
  have hcapacity : 1 < -globalRankCoefficient 0 d * capacity := by
    simpa only [capacity] using
      routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_localRamificationCapacity_gt_one
        hparameter x (0 : Fin 1)
  have hcapacity_nonneg : 0 ≤ capacity := by
    dsimp [capacity]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcapacity_pos : 0 < capacity := by
    by_contra h
    push Not at h
    have hzero : capacity = 0 := le_antisymm h hcapacity_nonneg
    rw [hzero] at hcapacity
    norm_num at hcapacity
  have hproduct :
      1 < ((((K 0 + 1 : ℕ) : ℝ) / N 0) - 1) * capacity := by
    simpa [capacity, globalRankCoefficient, fusionCoefficient,
      PuiseuxOrbitCoareaDatum.toOrbit_root] using hcapacity
  have hinverse :
      1 / capacity < (((K 0 + 1 : ℕ) : ℝ) / N 0) - 1 :=
    (div_lt_iff₀ hcapacity_pos).2 (by simpa [mul_comm] using hproduct)
  change 1 + 1 / capacity < (((K 0 + 1 : ℕ) : ℝ) / N 0)
  linarith

end

end RHTower
