import GaloisForLFunctions.RHTower.Deninger.DeningerTestL2Dense

/-!
# The Banach step of a test/Hilbert scale

A linear map into a Banach space bounded by a seminorm kills the kernel of that seminorm, so it
descends to the seminorm quotient and extends to its completion, a Banach space.  The test space
maps densely into that completion, and if the original map had dense range so does its extension.

This factors a two step scale `test space → Hilbert space` into a three step scale
`test space → Banach space → Hilbert space`, with all maps continuous and of dense range, and
therefore with injective transposes in the reverse direction.

* `deningerSeminormFactor`, `_mk` : a bounded map descends to the seminorm quotient.
* `deningerSeminormFactorC`, `_coe`, `_denseRange` : and extends to the completion.
* `deningerSeminormMkC_denseRange` : the space is dense in the completion of its quotient.
* `deningerScale_three_step` : **the factored scale.**
-/

namespace RHTower

open UniformSpace ContinuousLinearMap

section Factorization

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

omit [CompleteSpace 𝕜] in
/-- **A map bounded by a seminorm descends to the seminorm quotient.** -/
noncomputable def deningerSeminormFactor {p : Seminorm 𝕜 E} {T : E →ₗ[𝕜] H} {C : ℝ}
    (h : ∀ x, ‖T x‖ ≤ C * p x) : DeningerSeminormSpace p →L[𝕜] H :=
  LinearMap.mkContinuous
    (Submodule.liftQ (deningerSeminormKer p) T (by
      intro x hx
      have hp : p x = 0 := hx
      have hnorm : ‖T x‖ = 0 :=
        le_antisymm (by simpa [hp] using h x) (norm_nonneg _)
      exact norm_eq_zero.mp hnorm))
    C (by
      rintro ⟨a⟩
      exact h a)

omit [CompleteSpace 𝕜] in
theorem deningerSeminormFactor_mk {p : Seminorm 𝕜 E} {T : E →ₗ[𝕜] H} {C : ℝ}
    (h : ∀ x, ‖T x‖ ≤ C * p x) (x : E) :
    deningerSeminormFactor h (deningerSeminormMk p x) = T x := rfl

omit [CompleteSpace 𝕜] in
/-- **The space maps densely into the completion of its seminorm quotient.** -/
theorem deningerSeminormMkC_denseRange (p : Seminorm 𝕜 E) :
    DenseRange (deningerSeminormMkC p) := by
  have hrange : Set.range (deningerSeminormMkC p)
      = Set.range (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p)) := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨deningerSeminormMk p x, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := deningerSeminormMk_surjective p z
      exact ⟨x, rfl⟩
  rw [DenseRange, hrange]
  exact deningerDenseRange_toComplL p

variable [CompleteSpace H]

/-- **The extension of the descended map to the completion**: the Banach step of a scale. -/
noncomputable def deningerSeminormFactorC {p : Seminorm 𝕜 E} {T : E →ₗ[𝕜] H} {C : ℝ}
    (h : ∀ x, ‖T x‖ ≤ C * p x) : DeningerSeminormCompletion p →L[𝕜] H :=
  (deningerSeminormFactor h).extend
    (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p))

omit [CompleteSpace 𝕜] in
theorem deningerSeminormFactorC_class {p : Seminorm 𝕜 E} {T : E →ₗ[𝕜] H} {C : ℝ}
    (h : ∀ x, ‖T x‖ ≤ C * p x) (z : DeningerSeminormSpace p) :
    deningerSeminormFactorC h
        (Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p) z)
      = deningerSeminormFactor h z :=
  ContinuousLinearMap.extend_eq (f := deningerSeminormFactor h)
    (e := Completion.toComplL (𝕜 := 𝕜) (E := DeningerSeminormSpace p))
    (deningerDenseRange_toComplL p) (deningerIsUniformInducing_toComplL p) z

omit [CompleteSpace 𝕜] in
theorem deningerSeminormFactorC_coe {p : Seminorm 𝕜 E} {T : E →ₗ[𝕜] H} {C : ℝ}
    (h : ∀ x, ‖T x‖ ≤ C * p x) (x : E) :
    deningerSeminormFactorC h (deningerSeminormMkC p x) = T x :=
  deningerSeminormFactorC_class h (deningerSeminormMk p x)

omit [CompleteSpace 𝕜] in
/-- **The extension has dense range** as soon as the original map has. -/
theorem deningerSeminormFactorC_denseRange {p : Seminorm 𝕜 E} {T : E →ₗ[𝕜] H} {C : ℝ}
    (h : ∀ x, ‖T x‖ ≤ C * p x) (hT : DenseRange T) :
    DenseRange (deningerSeminormFactorC h) := by
  refine hT.mono ?_
  rintro y ⟨x, rfl⟩
  exact ⟨deningerSeminormMkC p x, deningerSeminormFactorC_coe h x⟩

omit [CompleteSpace 𝕜] in
/-- **The three step scale**: the space maps densely into the Banach completion of a seminorm
quotient, which maps densely into the Hilbert space, and the composite is the original map. -/
theorem deningerScale_three_step {p : Seminorm 𝕜 E} {T : E →ₗ[𝕜] H} {C : ℝ}
    (h : ∀ x, ‖T x‖ ≤ C * p x) (hT : DenseRange T) :
    DenseRange (deningerSeminormMkC p) ∧ DenseRange (deningerSeminormFactorC h) ∧
      ∀ x, deningerSeminormFactorC h (deningerSeminormMkC p x) = T x :=
  ⟨deningerSeminormMkC_denseRange p, deningerSeminormFactorC_denseRange h hT,
    deningerSeminormFactorC_coe h⟩

omit [CompleteSpace 𝕜] in
/-- **The first dual step**: a continuous functional on the Banach completion is determined by its
restriction to the space. -/
theorem deningerScale_dual_injective_mkC (p : Seminorm 𝕜 E)
    {φ ψ : DeningerSeminormCompletion p →ₗ[𝕜] 𝕜} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ.comp (deningerSeminormMkC p) = ψ.comp (deningerSeminormMkC p)) : φ = ψ :=
  deningerDual_injective_of_denseRange (deningerSeminormMkC_denseRange p) hφ hψ h

omit [CompleteSpace 𝕜] in
/-- **The second dual step**: a continuous functional on the Hilbert space is determined by its
restriction to the Banach completion. -/
theorem deningerScale_dual_injective_factorC {p : Seminorm 𝕜 E} {T : E →ₗ[𝕜] H} {C : ℝ}
    (h : ∀ x, ‖T x‖ ≤ C * p x) (hT : DenseRange T) {φ ψ : H →ₗ[𝕜] 𝕜} (hφ : Continuous φ)
    (hψ : Continuous ψ)
    (heq : φ.comp (deningerSeminormFactorC h).toLinearMap
      = ψ.comp (deningerSeminormFactorC h).toLinearMap) : φ = ψ :=
  deningerDual_injective_of_denseRange (deningerSeminormFactorC_denseRange h hT) hφ hψ heq

end Factorization

section TestScale

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
variable [TotallyDisconnectedSpace Y] [SecondCountableTopology Y]
variable [MeasurableSpace Y] [BorelSpace Y] (μ : MeasureTheory.Measure Y) [μ.Regular]

/-- **The test/Banach/Hilbert scale of the locally constant test space.**  Any seminorm dominating
the `L²` norm inserts a Banach space between the test space and `L²`, with dense continuous maps
throughout. -/
theorem deningerTestScale_three_step {p : Seminorm ℝ (DeningerTestSpace Y)} {C : ℝ}
    (h : ∀ g, ‖deningerTestToL2 μ g‖ ≤ C * p g) :
    DenseRange (deningerSeminormMkC p) ∧
      DenseRange (deningerSeminormFactorC h) ∧
      ∀ g, deningerSeminormFactorC h (deningerSeminormMkC p g) = deningerTestToL2 μ g :=
  deningerScale_three_step h (deningerTestToL2_denseRange μ)

end TestScale

end RHTower
