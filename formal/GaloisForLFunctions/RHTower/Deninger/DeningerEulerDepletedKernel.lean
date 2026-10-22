import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPeriodization
import GaloisForLFunctions.RHTower.Deninger.DeningerCommutatorExactKernel

/-!
# The Euler-depleted commutator and its exact kernel

Deleting the `p`-Euler orbit replaces the source by the image of the periodization defect
`Δ_L = 1 - τ_L`, `L = log p`.  That defect is injective on the exponentially decreasing source — a
translation-periodic member must vanish at infinity — so it is a linear isomorphism onto its range
and admits a Green inverse `G_p` there.

Composing the commutator with that inverse transports the exact kernel verbatim:

`ker 𝔖_{μ,p} = Δ_p Z(H_∩)`.

No Euler-product continuation and no analytic estimate is used: the only input beyond `(5)` is the
injectivity of the defect.

* `deningerPeriodizationDefect_injective` : **`Δ_L` is injective on the source.**
* `deningerGreenInverse` : the Green inverse on the range of the defect.
* `deningerEulerDepletedCommutator` : `𝔖_{μ,p} = 𝔖_μ ∘ G_p`.
* `deningerEulerDepleted_exact_kernel` : **`ker 𝔖_{μ,p} = Δ_p Z(H_∩)`.**
-/

namespace RHTower

open SchwartzMap FourierTransform

noncomputable section

/-- **The periodization defect is injective on the exponentially decreasing source.** -/
theorem deningerPeriodizationDefect_injective {L : ℝ} (hL : 0 < L) :
    Function.Injective (deningerPeriodizationDefect L) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
  have hper : ∀ t : ℝ, ((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = ((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (t + L) := by
    intro t
    have h0 : ((deningerPeriodizationDefect L f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t = 0 := by
      rw [hf]
      rfl
    rw [deningerPeriodizationDefect_apply] at h0
    linear_combination (norm := ring_nf) h0
  exact Subtype.ext (deningerExpSchwartz_eq_zero_of_periodic f.2 hL hper)

/-- The periodization defect, as a linear isomorphism onto its range. -/
def deningerDefectEquiv {L : ℝ} (hL : 0 < L) :
    DeningerExpSchwartz ≃ₗ[ℂ] LinearMap.range (deningerPeriodizationDefect L) :=
  LinearEquiv.ofInjective _ (deningerPeriodizationDefect_injective hL)

/-- **The Green inverse of the periodization defect** on the zero-periodization sector. -/
def deningerGreenInverse {L : ℝ} (hL : 0 < L) :
    LinearMap.range (deningerPeriodizationDefect L) →ₗ[ℂ] DeningerExpSchwartz :=
  (deningerDefectEquiv hL).symm.toLinearMap

@[simp]
theorem deningerGreenInverse_defect {L : ℝ} (hL : 0 < L) (h : DeningerExpSchwartz) :
    deningerGreenInverse hL (deningerDefectEquiv hL h) = h :=
  (deningerDefectEquiv hL).symm_apply_apply h

/-- **The Euler-depleted commutator** `𝔖_{μ,p} = 𝔖_μ ∘ G_p`. -/
def deningerEulerDepletedCommutator {L : ℝ} (hL : 0 < L)
    (y : LinearMap.range (deningerPeriodizationDefect L)) : 𝓢'(ℝ, ℂ) :=
  deningerMobiusCommutator (deningerGreenInverse hL y)

@[simp]
theorem deningerEulerDepletedCommutator_defect {L : ℝ} (hL : 0 < L) (h : DeningerExpSchwartz) :
    deningerEulerDepletedCommutator hL (deningerDefectEquiv hL h)
      = deningerMobiusCommutator h := by
  rw [deningerEulerDepletedCommutator, deningerGreenInverse_defect]

/-- **The exact kernel of the Euler-depleted commutator.**  The Green inverse transports `(5)`
verbatim: deleting one Euler orbit admits exactly the depleted Poisson boundaries. -/
theorem deningerEulerDepleted_exact_kernel {L : ℝ} (hL : 0 < L) :
    {y : LinearMap.range (deningerPeriodizationDefect L) |
        deningerEulerDepletedCommutator hL y = 0}
      = deningerDefectEquiv hL '' Set.range deningerPoissonSource := by
  ext y
  constructor
  · intro hy
    refine ⟨deningerGreenInverse hL y, ?_, ?_⟩
    · have hker : deningerMobiusCommutator (deningerGreenInverse hL y) = 0 := hy
      have hmem : deningerGreenInverse hL y ∈
          {h : DeningerExpSchwartz | deningerMobiusCommutator h = 0} := hker
      rwa [deningerCommutator_exact_kernel] at hmem
    · exact (deningerDefectEquiv hL).apply_symm_apply y
  · rintro ⟨h, hh, rfl⟩
    have hker : deningerMobiusCommutator h = 0 := by
      have hmem : h ∈ Set.range deningerPoissonSource := hh
      rw [← deningerCommutator_exact_kernel] at hmem
      exact hmem
    show deningerEulerDepletedCommutator hL (deningerDefectEquiv hL h) = 0
    rw [deningerEulerDepletedCommutator_defect]
    exact hker

end

end RHTower
