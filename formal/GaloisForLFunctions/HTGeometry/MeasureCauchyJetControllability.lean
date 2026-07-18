import GaloisForLFunctions.HTGeometry.MeasureCauchyJetDetection
import GaloisForLFunctions.HTGeometry.RegularizedHerglotzTransform
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Measure-level controllability of Cauchy jets

The detector of the previous module reads coefficients off almost-everywhere vanishing.  Its dual
is the statement actually needed for transversality: no nonzero finite Cauchy-jet functional
annihilates every bounded reweighting of a measure with infinite support.

The pairing of a jet functional with a reweighting is an integral against the *form*

```text
Q t = ∑ i ∑ j c i j * (t - x i)⁻¹ ^ (j + 1),
```

which is bounded on the real axis because every node lies off it.  So `Q` is integrable against a
finite measure, and vanishing of all of its set integrals forces `Q = 0` almost everywhere.  The
detector then kills every coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- The finite confluent Cauchy-jet form of a coefficient packet, read on the real axis. -/
def cauchyJetForm {ι : Type*} [Fintype ι] (x : ι → ℂ) (n : ι → ℕ)
    (c : (i : ι) → Fin (n i) → ℂ) (t : ℝ) : ℂ :=
  ∑ i, ∑ j : Fin (n i), c i j * (((t : ℝ) : ℂ) - x i)⁻¹ ^ (j.1 + 1)

/-- The uniform bound carried by a jet form whose nodes avoid the real axis. -/
def cauchyJetFormBound {ι : Type*} [Fintype ι] (x : ι → ℂ) (n : ι → ℕ)
    (c : (i : ι) → Fin (n i) → ℂ) : ℝ :=
  ∑ i, ∑ j : Fin (n i), ‖c i j‖ * (|(x i).im|⁻¹) ^ (j.1 + 1)

/-- Off the real axis the jet form is uniformly bounded. -/
theorem norm_cauchyJetForm_le {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, (x i).im ≠ 0) (n : ι → ℕ)
    (c : (i : ι) → Fin (n i) → ℂ) (t : ℝ) :
    ‖cauchyJetForm x n c t‖ ≤ cauchyJetFormBound x n c := by
  rw [cauchyJetForm, cauchyJetFormBound]
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro i _
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, norm_pow]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_inv_real_sub_le (hupper i) t) (j.1 + 1)

/-- Against a finite measure the jet form is integrable. -/
theorem integrable_cauchyJetForm {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ι → ℂ) (hupper : ∀ i, (x i).im ≠ 0) (n : ι → ℕ)
    (c : (i : ι) → Fin (n i) → ℂ) :
    Integrable (cauchyJetForm x n c) μ := by
  have hmeas : AEStronglyMeasurable (cauchyJetForm x n c) μ := by
    apply Measurable.aestronglyMeasurable
    unfold cauchyJetForm
    fun_prop
  refine Integrable.mono' (integrable_const (cauchyJetFormBound x n c)) hmeas ?_
  filter_upwards with t
  exact norm_cauchyJetForm_le x hupper n c t

/-- **Measure-level Cauchy-jet controllability, dual form.**  No nonzero finite Cauchy-jet
functional at distinct nodes off the real axis annihilates every bounded reweighting of a finite
measure with infinite support: if all set integrals of the jet form vanish, so does every
coefficient. -/
theorem cauchyJet_coeff_eq_zero_of_forall_setIntegral_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hsupp : μ.support.Infinite)
    (x : ι → ℂ) (hx : Function.Injective x) (hne : ∀ i, (x i).im ≠ 0)
    (n : ι → ℕ) (c : (i : ι) → Fin (n i) → ℂ)
    (hpair : ∀ S : Set ℝ, MeasurableSet S →
      ∫ t in S, cauchyJetForm x n c t ∂μ = 0) :
    ∀ i j, c i j = 0 := by
  have hint := integrable_cauchyJetForm μ x hne n c
  have hae : cauchyJetForm x n c =ᵐ[μ] 0 :=
    Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero hint
      (fun S hS _ => hpair S hS)
  apply cauchyJet_coeff_eq_zero_of_ae hsupp x hx hne n c
  filter_upwards [hae] with t ht
  exact ht

end

end GaloisForLFunctions.HTGeometry
