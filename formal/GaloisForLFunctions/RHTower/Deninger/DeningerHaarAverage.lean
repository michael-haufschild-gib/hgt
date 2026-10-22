import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Haar averaging over a compact group

Integrating the orbit of a vector against a left-invariant probability measure produces an
invariant vector, and does nothing to a vector that is already invariant.  This is why taking
invariants of a compact group action is exact: a lift of an invariant vector can be averaged.

* `deningerHaarAverage` : the orbit average.
* `deningerHaarAverage_invariant` : it is invariant.
* `deningerHaarAverage_of_invariant` : it fixes invariant vectors.
* `deningerInvariants_surjective` : an invariant vector lifts to an invariant vector.
-/

namespace RHTower

open MeasureTheory

section HaarAverage

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E))

/-- The average of the orbit of a vector. -/
noncomputable def deningerHaarAverage (m : E) : E := ∫ g, ρ g m ∂μ

variable (hρ : ∀ m : E, Continuous fun g : G => ρ g m)

omit [IsTopologicalGroup G] [CompleteSpace E] [μ.IsMulLeftInvariant] in
include hρ in
theorem deningerOrbit_integrable (m : E) : Integrable (fun g : G => ρ g m) μ :=
  (hρ m).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

include hρ in
/-- **The orbit average is invariant.** -/
theorem deningerHaarAverage_invariant (m : E) (g₀ : G) :
    ρ g₀ (deningerHaarAverage μ ρ m) = deningerHaarAverage μ ρ m := by
  have hmul : (fun g : G => ρ g₀ (ρ g m)) = fun g : G => ρ (g₀ * g) m := by
    funext g
    rw [map_mul]
    rfl
  calc ρ g₀ (deningerHaarAverage μ ρ m)
      = ∫ g, ρ g₀ (ρ g m) ∂μ := by
        rw [deningerHaarAverage]
        exact ((ρ g₀).toLinearIsometry.toContinuousLinearMap.integral_comp_comm
          (deningerOrbit_integrable μ ρ hρ m)).symm
    _ = ∫ g, ρ (g₀ * g) m ∂μ := by rw [hmul]
    _ = deningerHaarAverage μ ρ m := integral_mul_left_eq_self (fun g : G => ρ g m) g₀

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [μ.IsMulLeftInvariant] in
/-- **The average fixes invariant vectors.** -/
theorem deningerHaarAverage_of_invariant {m : E} (hm : ∀ g : G, ρ g m = m) :
    deningerHaarAverage μ ρ m = m := by
  have hfun : (fun g : G => ρ g m) = fun _ : G => m := funext hm
  rw [deningerHaarAverage, hfun, integral_const, probReal_univ, one_smul]

include hρ in
/-- **Invariants of an equivariant surjection are surjective.**  An invariant vector downstairs is
the image of an invariant vector upstairs: lift it arbitrarily and average the lift. -/
theorem deningerInvariants_surjective
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (σ : G →* (F ≃ₗᵢ[ℝ] F)) (π : E →L[ℝ] F)
    (hπ : ∀ (g : G) (m : E), π (ρ g m) = σ g (π m))
    {n : F} (hn : ∀ g : G, σ g n = n) (m : E) (hm : π m = n) :
    (∀ g : G, ρ g (deningerHaarAverage μ ρ m) = deningerHaarAverage μ ρ m)
      ∧ π (deningerHaarAverage μ ρ m) = n := by
  refine ⟨fun g => deningerHaarAverage_invariant μ ρ hρ m g, ?_⟩
  have h1 : π (∫ g, ρ g m ∂μ) = ∫ g, π (ρ g m) ∂μ :=
    (π.integral_comp_comm (deningerOrbit_integrable μ ρ hρ m)).symm
  have h2 : (fun g : G => π (ρ g m)) = fun _ : G => n := by
    funext g
    rw [hπ, hm, hn]
  rw [deningerHaarAverage, h1, h2, integral_const, probReal_univ, one_smul]

end HaarAverage

end RHTower
