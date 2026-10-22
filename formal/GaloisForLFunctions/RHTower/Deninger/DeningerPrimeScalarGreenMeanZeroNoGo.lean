import GaloisForLFunctions.RHTower.Deninger.DeningerGreenFormPullbackTransport
import GaloisForLFunctions.RHTower.Deninger.DeningerPacketNonlocal

/-!
# Scalar prime-residue Green forms miss mean-zero packet modes

The canonical packet average is bounded for the compact-open supremum norm, so it defines a
continuous scalar residue comparison.  Pulling back the positive scalar inner product gives a
continuous nonnegative Green form.  Its radical is exactly the mean-zero packet subspace, which is
nontrivial whenever the packet has a clopen set of intermediate probability.

Consequently the one-coordinate-per-prime Green model cannot by itself represent the full packet
coefficient retained by Route L.  A faithful arithmetic comparison must add the mean-zero packet
modes (and their transverse Fourier coordinates), or prove they are genuine boundaries by a
separate source theorem.
-/

namespace RHTower

open MeasureTheory Set

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- Packet averaging as a continuous linear functional for the supremum norm. -/
def deningerPacketAvContinuous : C(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous (deningerPacketAv μ) 1 (by
    intro f
    rw [one_mul, Real.norm_eq_abs]
    exact (deningerPacketAv_abs_le μ f).trans (by
      have hmono : ∀ x, |f x| ≤ ‖f‖ := fun x => by
        simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
      calc
        (∫ x, |f x| ∂μ) ≤ ∫ _x, ‖f‖ ∂μ := integral_mono
          (Continuous.integrable_of_hasCompactSupport
            (continuous_abs.comp f.continuous) (HasCompactSupport.of_compactSpace _))
          (integrable_const _) hmono
        _ = ‖f‖ := by rw [integral_const, probReal_univ, one_smul]))

@[simp] theorem deningerPacketAvContinuous_apply (f : C(X, ℝ)) :
    deningerPacketAvContinuous μ f = deningerPacketAv μ f := rfl

/-- Positive scalar Green form obtained solely from the packet-average residue coordinate. -/
def deningerPacketScalarResidueGreenForm :
    C(X, ℝ) →L[ℝ] C(X, ℝ) →L[ℝ] ℝ :=
  deningerPullbackGreenForm (deningerPacketAvContinuous μ) (innerSL ℝ)

/-- Scalar residue energy is the square of the packet average. -/
theorem deningerPacketScalarResidueGreenForm_self
    (f : C(X, ℝ)) :
    deningerPacketScalarResidueGreenForm μ f f = (deningerPacketAv μ f) ^ (2 : ℕ) := by
  rw [deningerPacketScalarResidueGreenForm, deningerPullbackGreenForm_apply_apply,
    deningerPacketAvContinuous_apply, innerSL_apply_apply,
    real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The scalar-residue Green radical is exactly the mean-zero packet subspace. -/
theorem deningerPacketScalarResidueGreenForm_self_eq_zero_iff
    (f : C(X, ℝ)) :
    deningerPacketScalarResidueGreenForm μ f f = 0 ↔
      deningerPacketAv μ f = 0 := by
  rw [deningerPacketScalarResidueGreenForm_self]
  exact sq_eq_zero_iff

/-- **Mean-zero packet no-go.**  A clopen packet piece of intermediate mass produces a nonzero
mode invisible to every Green form using only the scalar packet average. -/
theorem exists_ne_zero_deningerPacketScalarResidueGreenForm_self_eq_zero
    {D : Set X} (hD : IsClopen D) (hpos : 0 < μ.real D) (hlt : μ.real D < 1) :
    ∃ f : C(X, ℝ),
      deningerPacketScalarResidueGreenForm μ f f = 0 ∧ f ≠ 0 := by
  obtain ⟨f, havg, hf⟩ := deningerPacketAv_ker_ne_bot μ hD hpos hlt
  exact ⟨f, (deningerPacketScalarResidueGreenForm_self_eq_zero_iff μ f).2 havg, hf⟩

end

end RHTower
