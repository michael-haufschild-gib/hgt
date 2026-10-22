import GaloisForLFunctions.RHTower.Deninger.DeningerCommutatorExactKernel
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittTwoPrimeOrientationBoundaryWall

/-!
# The source–Poisson chain-lift obstruction

Asking for a degree-one lift `R₁` with `R₂ D = Z R₁` leaves a fake degree of freedom: once the
degree-two realization is fixed, canonical Möbius inversion already builds the only
source-compatible candidate on the positive ray.  What is actually missing is the vanishing of one
explicit opposite-collar Fourier obstruction — the commutator evaluated at the realized value.

The exact kernel `ker 𝔖_μ = Z(H_∩)` therefore collapses the four formulations of the lifting
problem into a single equivalence, and the lift, when it exists, is the canonical prelift `E f_h`
rather than a chosen one.

* `deningerChainLiftObstruction` : the obstruction `Ω_{μ,Γ} = 𝔖_μ ∘ 𝒢_Γ ∘ D`.
* `deningerChainLift_tfae` : **the four formulations are equivalent.**
* `deningerChainLift_onSubspace` : **`(5)`: the lift exists on a subspace iff `Ω` vanishes there.**
-/

namespace RHTower

open MeasureTheory SchwartzMap FourierTransform

noncomputable section

/-- **The source–Poisson lifting obstruction** at a value of the degree-two realization. -/
def deningerChainLiftObstruction (h : DeningerExpSchwartz) : 𝓢'(ℝ, ℂ) :=
  deningerMobiusCommutator h

/-- **The four formulations of the chain-lift problem are equivalent.**

`(1)` the obstruction vanishes; `(2)` the value is a Poisson boundary; `(3)` the *canonical*
prelift `E f_h` extends through the radial origin to a member of Meyer's space whose opposite
collar is its Fourier transform and whose Poisson sum is the value; `(4)` the value admits some
Meyer–Poisson chain lift. -/
theorem deningerChainLift_tfae (h : DeningerExpSchwartz) :
    List.TFAE
      [ deningerChainLiftObstruction h = 0,
        h ∈ Set.range deningerPoissonSource,
        ∃ f : 𝓢(ℝ, ℂ), ∃ hf : f ∈ DeningerMeyerCap,
          deningerEvenPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) =ᵐ[volume] (f : ℝ → ℂ) ∧
            deningerPoissonSource ⟨f, hf⟩ = h,
        ∃ f : DeningerMeyerCap, deningerPoissonSource f = h ] := by
  tfae_have 1 → 3 := by
    intro hker
    obtain ⟨f, hae, hfour⟩ := deningerCommutatorKernel_schwartz hker
    exact ⟨f, deningerKernelSchwartz_mem hae hfour, hae,
      deningerKernel_eq_poissonSource (deningerKernelSchwartz_mem hae hfour) hae⟩
  tfae_have 3 → 4 := by
    rintro ⟨f, hf, -, hZ⟩
    exact ⟨⟨f, hf⟩, hZ⟩
  tfae_have 4 → 2 := by
    rintro ⟨f, hZ⟩
    exact ⟨f, hZ⟩
  tfae_have 2 → 1 := by
    intro hmem
    have := deningerPoissonRange_subset_commutatorKernel hmem
    exact this
  tfae_finish

/-- **The opposite collar of the canonical prelift is its Fourier transform** whenever the
obstruction vanishes. -/
theorem deningerChainLift_collar_fourier {h : DeningerExpSchwartz}
    (hker : deningerChainLiftObstruction h = 0) :
    deningerEvenPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))
      =ᵐ[volume]
        𝓕 (deningerEvenPreimage
          ((deningerCollarExchange h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) :=
  deningerEvenPreimage_ae_fourier hker

/-- The obstruction of a degree-two realization composed with the differential. -/
def deningerRealizationObstruction {C₁ C₂ : Type*} [AddCommGroup C₁] [Module ℂ C₁]
    [AddCommGroup C₂] [Module ℂ C₂] (D : C₁ →ₗ[ℂ] C₂)
    (G : C₂ →ₗ[ℂ] DeningerExpSchwartz) (w : C₁) : 𝓢'(ℝ, ℂ) :=
  deningerChainLiftObstruction (G (D w))

/-- **The lifting criterion at a single cochain.** -/
theorem deningerRealization_lift_iff {C₁ C₂ : Type*} [AddCommGroup C₁] [Module ℂ C₁]
    [AddCommGroup C₂] [Module ℂ C₂] (D : C₁ →ₗ[ℂ] C₂)
    (G : C₂ →ₗ[ℂ] DeningerExpSchwartz) (w : C₁) :
    deningerRealizationObstruction D G w = 0
      ↔ ∃ f : DeningerMeyerCap, deningerPoissonSource f = G (D w) :=
  ((deningerChainLift_tfae (G (D w))).out 0 3)

/-- **`(5)`: on a source subspace the chain lift exists exactly where the obstruction vanishes.**
The lift is then the canonical prelift, not a choice. -/
theorem deningerChainLift_onSubspace {C₁ C₂ : Type*} [AddCommGroup C₁] [Module ℂ C₁]
    [AddCommGroup C₂] [Module ℂ C₂] (D : C₁ →ₗ[ℂ] C₂)
    (G : C₂ →ₗ[ℂ] DeningerExpSchwartz) (V : Submodule ℂ C₁) :
    (∀ w ∈ V, deningerRealizationObstruction D G w = 0)
      ↔ ∀ w ∈ V, ∃ f : DeningerMeyerCap, deningerPoissonSource f = G (D w) := by
  constructor
  · intro hobs w hw
    exact (deningerRealization_lift_iff D G w).mp (hobs w hw)
  · intro hlift w hw
    exact (deningerRealization_lift_iff D G w).mpr (hlift w hw)

end

end RHTower

/-! ## The sharp two-prime endpoint audit -/

namespace RHTower

open SchwartzMap

noncomputable section

/-- The two-prime Green boundary of the oriented Calderón–Witt complex, at the primes `2` and
`3`. -/
def deningerChainLiftTwoPrimeBoundary :=
  deningerCalderonWittGlobalOrientedBoundary
    (deningerCalderonWittTwoPrimeOrientationGreenBoundaryWitness
      deningerCalderonWittPrimeTwo deningerCalderonWittPrimeThree)

/-- **`(7)`: the sharp endpoint implication of the two-prime audit.**  If an evaluation of the
obstruction at the two-prime cochain reproduces the two-prime Xi jet with a nonzero calibration —
the audit `(6)` — then vanishing of the obstruction forces the critical line.

The audit is a hypothesis of the statement, exactly as on the card: this theorem asserts neither
the realization nor the vanishing. -/
theorem deningerChainLift_twoPrime_endpoint {ρ c : ℂ} (hc : c ≠ 0)
    (Ev : 𝓢'(ℝ, ℂ) → ℂ) (hEv : Ev 0 = 0) {Ω : 𝓢'(ℝ, ℂ)}
    (haudit : Ev Ω
      = c * deningerCalderonWittPrimeIndexedPhysicalOrientationReporter ρ
          deningerChainLiftTwoPrimeBoundary)
    (hvanish : Ω = 0) : ρ.re = 1 / 2 := by
  have h0 : c * deningerCalderonWittPrimeIndexedPhysicalOrientationReporter ρ
      deningerChainLiftTwoPrimeBoundary = 0 := by
    rw [← haudit, hvanish, hEv]
  exact
    (deningerCalderonWittPrimeIndexedPhysicalReporter_twoPrimeBoundary_mul_eq_zero_iff ρ c hc).mp h0

end

end RHTower
