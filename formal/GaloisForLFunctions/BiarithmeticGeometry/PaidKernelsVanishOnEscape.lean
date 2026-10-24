import GaloisForLFunctions.ArithmeticDefectRigidity.TheForcingSplitsIntoAPowerAndAnAdmittedRemainder

/-!+# Repairing kernels vanish in actual escape normalization

The exact convolution law differs from the cofactor action by a uniformly paid kernel prefix.
Consequently every critical Wiener kernel repairing the actual damped Möbius source has bounded
cofactor-action energy. On the escaping branch this energy vanishes after receiver normalization.
The action uses the full kernel at each finite horizon; paid finite truncations are not assumed.
-/

noncomputable section

open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.ArithmeticDefectRigidity
open GaloisForLFunctions.TransHorizonIncidenceMechanics
  (CriticalWiener ReceiverBounded weightCenteredPrefix weightPronicEnergy dampedDensity
   hasSum_pmPowerDampedRealWeight_div hasSum_dirichletConv_div
   weightCenteredPrefix_dirichletConv pronicNorm_weightCenteredPrefix_le_critical)

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The full kernel acts on the actual receiver by floor dilations at its current horizon. -/
def actualKernelAction (ε : ℝ) (k : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 n, k j * pmPowerDampedCenteredDivisorPrefix ε (n / j)

private theorem actualPrefix_eq (ε : ℝ) (n : ℕ) :
    weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n =
      pmPowerDampedCenteredDivisorPrefix ε n := by
  rw [weightCenteredPrefix, RHTower.pmPowerDampedCenteredDivisorPrefix_eq]
  rfl

/-- The only difference between convolution and the cofactor action is the kernel's own prefix. -/
theorem actualKernelAction_eq_convolution_sub_boundary (ε : ℝ) (k : ℕ → ℝ) (n : ℕ) :
    actualKernelAction ε k n =
      weightCenteredPrefix (dirichletConv k (pmPowerDampedRealWeight ε))
        ((∑' j : ℕ, k j / j) * dampedDensity ε) n -
          dampedDensity ε * weightCenteredPrefix k (∑' j : ℕ, k j / j) n := by
  have h := weightCenteredPrefix_dirichletConv k (pmPowerDampedRealWeight ε)
    (∑' j : ℕ, k j / j) (dampedDensity ε) n
  simp only [actualPrefix_eq] at h
  change (∑ j ∈ Icc 1 n, k j * pmPowerDampedCenteredDivisorPrefix ε (n / j)) = _
  linarith only [h]

/-- A repairing Wiener kernel has a uniformly bounded actual cofactor action. -/
theorem paidKernelAction_bounded (ε : SubcriticalDamping) (k : ℕ → ℝ)
    (hk : CriticalWiener k) :
    ReceiverBounded (dirichletConv k (pmPowerDampedRealWeight ε)) →
      ∃ C : ℝ, ∀ T : ℕ,
        TransHorizonIncidenceMechanics.pronicNorm (actualKernelAction ε k) T ≤ C := by
  intro hpaid
  have hc : HasSum (fun n : ℕ => pmPowerDampedRealWeight ε n / n) (dampedDensity ε) :=
    hasSum_pmPowerDampedRealWeight_div ε.property.1
  have hmean : (∑' n : ℕ, dirichletConv k (pmPowerDampedRealWeight ε) n / n) =
      (∑' j : ℕ, k j / j) * dampedDensity ε :=
    (hasSum_dirichletConv_div hk.summable_abs_div.of_abs.hasSum hc
      hk.summable_abs_div hc.summable.abs).tsum_eq
  obtain ⟨B, hB⟩ := hpaid
  refine ⟨Real.sqrt B + |dampedDensity ε| * ((Real.sqrt 2 + 1) *
    ∑' j : ℕ, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))), ?_⟩
  intro T
  have hconv : TransHorizonIncidenceMechanics.pronicNorm
      (weightCenteredPrefix (dirichletConv k (pmPowerDampedRealWeight ε))
        ((∑' j : ℕ, k j / j) * dampedDensity ε)) T ≤ Real.sqrt B := by
    have hb := hB T
    rw [hmean] at hb
    exact Real.sqrt_le_sqrt hb
  have heq : actualKernelAction ε k = fun n =>
      weightCenteredPrefix (dirichletConv k (pmPowerDampedRealWeight ε))
        ((∑' j : ℕ, k j / j) * dampedDensity ε) n +
          (-dampedDensity ε) * weightCenteredPrefix k (∑' j : ℕ, k j / j) n := by
    funext n
    rw [actualKernelAction_eq_convolution_sub_boundary]
    ring
  rw [heq]
  refine (TransHorizonIncidenceMechanics.pronicNorm_add_le _ _ T).trans ?_
  rw [TransHorizonIncidenceMechanics.pronicNorm_smul, abs_neg]
  exact add_le_add hconv (mul_le_mul_of_nonneg_left
    (pronicNorm_weightCenteredPrefix_le_critical hk T) (abs_nonneg _))

/-- Either the actual receiver is bounded, or every repairing Wiener action vanishes in its
energy normalization. This assertion includes infinite kernels without truncating the paid ideal. -/
theorem admitted_or_paidKernelAction_vanishes (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      ∀ k : ℕ → ℝ, CriticalWiener k →
        ReceiverBounded (dirichletConv k (pmPowerDampedRealWeight ε)) →
          Tendsto (fun T : ℕ =>
            TransHorizonIncidenceMechanics.pronicNorm (actualKernelAction ε k) (T + 1) ^ 2 /
              dampedMobiusEnergy ε (T + 1)) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop ε with hpaid | hescape
  · exact Or.inl hpaid
  · refine Or.inr ?_
    intro k hk hpaid
    obtain ⟨C, hC⟩ := paidKernelAction_bounded ε k hk hpaid
    have hlim : Tendsto (fun T : ℕ => C ^ 2 / dampedMobiusEnergy ε (T + 1))
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hescape.comp (tendsto_add_atTop_nat 1))
    refine squeeze_zero (fun T => div_nonneg (sq_nonneg _)
      (dampedMobiusEnergy_nonneg _ _)) (fun T => ?_) hlim
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (TransHorizonIncidenceMechanics.pronicNorm_nonneg _ _) (hC _) 2)
      (dampedMobiusEnergy_nonneg _ _)

end GaloisForLFunctions.BiarithmeticGeometry
