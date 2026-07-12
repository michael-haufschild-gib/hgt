import GaloisForLFunctions.HTGeometry.LinftyFiniteConstraintAperture
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Positivity of the finite-constraint `L∞` aperture

An `L∞` perturbation of norm strictly below one cannot destroy the almost-everywhere positivity
of the constant density one.  Combining this sharp order estimate with the geometrically weighted
Hilbert-cube construction gives a closed Hilbert cube of strictly positive densities inside every
exact finite constraint fiber, whenever the parameter measure supplies countably many disjoint
positive blocks.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The `L∞` norm controls a representative pointwise almost everywhere. -/
theorem linfty_ae_abs_le_norm (f : Lp ℝ ∞ μ) : ∀ᵐ x ∂μ, |f x| ≤ ‖f‖ := by
  simpa only [Real.norm_eq_abs, Lp.norm_def, lpNorm,
    if_pos (Lp.memLp f).1] using
    ae_le_lpNorm_exponent_top (Lp.memLp f)

/-- Strict positivity for an `L∞` class means positivity of a representative almost everywhere. -/
def LinftyStrictlyPositive (w : Lp ℝ ∞ μ) : Prop :=
  ∀ᵐ x ∂μ, 0 < w x

variable [IsFiniteMeasure μ]

/-- The constant-one class in `L∞`. -/
noncomputable def linftyOne : Lp ℝ ∞ μ :=
  Lp.const ∞ μ 1

/-- The open unit ball about the constant-one density lies in the strictly positive cone. -/
theorem linftyOne_add_strictlyPositive_of_norm_lt_one
    (f : Lp ℝ ∞ μ) (hf : ‖f‖ < 1) :
    LinftyStrictlyPositive μ (linftyOne μ + f) := by
  have hone : ⇑(linftyOne μ) =ᵐ[μ] fun _ => (1 : ℝ) := Lp.coeFn_const ∞ μ 1
  have hadd : ⇑(linftyOne μ + f) =ᵐ[μ] ⇑(linftyOne μ) + ⇑f := Lp.coeFn_add _ _
  filter_upwards [linfty_ae_abs_le_norm μ f, hone, hadd] with x hx h1 hplus
  rw [hplus, Pi.add_apply, h1]
  have hneg : -1 < ⇑f x := by
    calc
      -1 < -‖f‖ := neg_lt_neg hf
      _ ≤ -|⇑f x| := neg_le_neg hx
      _ ≤ ⇑f x := neg_abs_le (⇑f x)
  linarith

/-- Every point of a geometrically weighted aperture of radius below one is strictly positive. -/
theorem affinePositiveHilbertCubeMap_linftyOne_strictlyPositive
    {delta : ℝ} (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1)
    {v : ℕ → Lp ℝ ∞ μ} (hv : ∀ n, ‖v n‖ ≤ 1)
    (t : SignedHilbertCube) :
    LinftyStrictlyPositive μ
      (affinePositiveHilbertCubeMap (linftyOne μ) delta v t) := by
  apply linftyOne_add_strictlyPositive_of_norm_lt_one μ
  exact (norm_positiveHilbertCubeMap_le hdelta0 hv t).trans_lt hdelta1

/-- **Positive finite-constraint aperture.** Under an explicit countable positive block
partition, every finite continuous-linear constraint fiber through the constant density one
contains a closed embedded Hilbert cube of strictly positive densities. -/
theorem exists_positive_closedEmbeddedHilbertCube_in_linfty_finiteConstraintFiber
    {k : ℕ} (T : (Lp ℝ ∞ μ) →L[ℝ] (Fin k → ℝ))
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (A : ℕ → Fin (k + 1) → Set α)
    (hAmeas : ∀ j l, MeasurableSet (A j l))
    (hApos : ∀ j l, μ (A j l) ≠ 0)
    (hAdisj : ∀ j l m r, (j, l) ≠ (m, r) → Disjoint (A j l) (A m r)) :
    ∃ v : ℕ → Lp ℝ ∞ μ, ∃ ell : ℕ → (Lp ℝ ∞ μ) →L[ℝ] ℝ,
      (∀ n, ‖v n‖ = 1) ∧ (∀ n, T (v n) = 0) ∧
      (∀ n m, ell n (v m) = if n = m then 1 else 0) ∧
      Topology.IsClosedEmbedding
        (affinePositiveHilbertCubeMap (linftyOne μ) delta v) ∧
      ∀ t : SignedHilbertCube,
        T (affinePositiveHilbertCubeMap (linftyOne μ) delta v t) = T (linftyOne μ) ∧
        LinftyStrictlyPositive μ
          (affinePositiveHilbertCubeMap (linftyOne μ) delta v t) := by
  obtain ⟨v, ell, hvnorm, hvker, hbio, hembed, hconstraint⟩ :=
    exists_closedEmbeddedHilbertCube_in_linfty_finiteConstraintFiber
      μ T (linftyOne μ) hdelta0 A hAmeas hApos hAdisj
  refine ⟨v, ell, hvnorm, hvker, hbio, hembed, ?_⟩
  intro t
  exact ⟨hconstraint t,
    affinePositiveHilbertCubeMap_linftyOne_strictlyPositive μ hdelta0.le hdelta1
      (fun n => (hvnorm n).le) t⟩

end

end GaloisForLFunctions.HTGeometry
