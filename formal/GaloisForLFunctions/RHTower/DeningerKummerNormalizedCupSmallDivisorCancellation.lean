import GaloisForLFunctions.RHTower.DeningerCylinderModes
import Mathlib.Analysis.MeanInequalities

/-!
# Kummer normalized-cup small-divisor cancellation

Raw harmonic Kummer modes have norm-square `1 / |μ|` and opposite-mode cup `i / μ`.  Multiplying
both modes by the energy normalization `sqrt |μ|` cancels the complete small divisor, leaving the
unimodular value `i * sign μ`.  Consequently the finite normalized cup packets obey a uniform
Cauchy--Schwarz bound independent of frequencies and rank.

These are the unconditional statements behind
`DAC_KUMMER_NORMALIZED_CUP_SMALL_DIVISOR_CANCELLATION`.
-/

namespace RHTower

open UnitAddTorus MeasureTheory Set
open scoped BigOperators

noncomputable section

variable {d : Type*} [Fintype d]

/-- The cylinder cup is complex-bilinear under constant rescaling. -/
theorem deningerCylinderCup_smul (c e : ℂ)
    (α β : ℝ → UnitAddTorus d → ℂ × ℂ) :
    deningerCylinderCup (fun r η => c • α r η) (fun r η => e • β r η) =
      c * e * deningerCylinderCup α β := by
  rw [deningerCylinderCup, deningerCylinderCup, ← integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  change deningerCxWedge (c • α r η) (e • β r η) =
    c * e * deningerCxWedge (α r η) (β r η)
  rw [deningerCxWedge_smul_left, deningerCxWedge_smul_right]
  ring

/-- Energy normalization cancels the complete Kummer small divisor in the opposite-mode cup. -/
theorem deningerNormalizedCylinderMode_cup_neg
    (lam : d → ℝ) (n : d → ℤ) (hn : deningerFrequency n lam ≠ 0) :
    deningerCylinderCup (deningerNormalizedCylinderMode lam n)
        (deningerNormalizedCylinderMode lam (-n)) =
      Complex.I * (deningerFreqSign (deningerFrequency n lam) : ℂ) := by
  let μ := deningerFrequency n lam
  have hneg : deningerFrequency (-n) lam = -μ := deningerFrequency_neg n lam
  change deningerCylinderCup
      (fun r η => ((Real.sqrt |μ| : ℝ) : ℂ) • deningerCylinderMode lam n r η)
      (fun r η => ((Real.sqrt |deningerFrequency (-n) lam| : ℝ) : ℂ) •
        deningerCylinderMode lam (-n) r η) =
      Complex.I * (deningerFreqSign μ : ℂ)
  rw [deningerCylinderCup_smul, deningerCylinderCup_mode_neg lam hn, hneg, abs_neg]
  have habs : 0 ≤ |μ| := abs_nonneg μ
  have hsqrt : ((Real.sqrt |μ| : ℝ) : ℂ) * ((Real.sqrt |μ| : ℝ) : ℂ) =
      ((|μ| : ℝ) : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (Real.mul_self_sqrt habs)
  rw [hsqrt]
  have hμc : (μ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hsign : ((|μ| : ℝ) : ℂ) = (deningerFreqSign μ : ℂ) * (μ : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (deningerFreqSign_abs hn)
  rw [hsign]
  rw [show deningerFrequency n lam = μ by rfl]
  field_simp

section Packet

variable {ι : Type*} [Fintype ι]

/-- Finite normalized Kummer cup packet with a chosen opposite-character equivalence. -/
def deningerNormalizedKummerCupPacket
    (opp : ι ≃ ι) (sign : ι → ℝ) (a b : ι → ℂ) : ℂ :=
  ∑ i, a i * b (opp i) * (Complex.I * (sign i : ℂ))

/-- Squared coefficient mass of a normalized Kummer packet. -/
def deningerNormalizedKummerPacketMass (a : ι → ℂ) : ℝ :=
  ∑ i, ‖a i‖ ^ (2 : ℕ)

/-- The normalized Kummer cup is uniformly bounded; no frequency divisor remains. -/
theorem deningerNormalizedKummerCupPacket_norm_le
    (opp : ι ≃ ι) (sign : ι → ℝ)
    (hsign : ∀ i, ‖(sign i : ℂ)‖ = 1) (a b : ι → ℂ) :
    ‖deningerNormalizedKummerCupPacket opp sign a b‖ ≤
      Real.sqrt (deningerNormalizedKummerPacketMass a) *
        Real.sqrt (deningerNormalizedKummerPacketMass b) := by
  calc
    ‖deningerNormalizedKummerCupPacket opp sign a b‖
        ≤ ∑ i, ‖a i * b (opp i) * (Complex.I * (sign i : ℂ))‖ :=
          norm_sum_le _ _
    _ = ∑ i, ‖a i‖ * ‖b (opp i)‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, hsign, one_mul, mul_one]
    _ ≤ Real.sqrt (∑ i, ‖a i‖ ^ (2 : ℕ)) * Real.sqrt (∑ i, ‖b (opp i)‖ ^ (2 : ℕ)) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖a i‖) (fun i => ‖b (opp i)‖)
    _ = Real.sqrt (deningerNormalizedKummerPacketMass a) *
        Real.sqrt (deningerNormalizedKummerPacketMass b) := by
      rw [deningerNormalizedKummerPacketMass, deningerNormalizedKummerPacketMass]
      congr 2
      exact Fintype.sum_equiv opp (fun i => ‖b (opp i)‖ ^ (2 : ℕ))
        (fun j => ‖b j‖ ^ (2 : ℕ)) (fun i => rfl)

end Packet

end


end RHTower
