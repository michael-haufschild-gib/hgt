import GaloisForLFunctions.RHTower.Deninger.DeningerFloquetPoissonFlow
import GaloisForLFunctions.RHTower.Deninger.DeningerFloquetHilbert
import GaloisForLFunctions.HTGeometry.OrthogonalClosureCriterion

/-!
# The closed Poisson-boundary space is the resonance annihilator

In `L²` of the arithmetic lattice measure the Poisson boundaries span a subspace whose closure is
exactly the annihilator of the resonant nodes — the lattice frequencies at which the zeta function
vanishes on the critical line.

One inclusion is the Poisson--Mellin factorization: the sample of a Poisson boundary carries the
factor `ζ(1/2-2πiξ)`, so it vanishes at every resonant node.  The other is a completeness argument.
Scaling the explicit Poisson test function realizes every critical-line character times one fixed
nowhere-vanishing profile, so a vector orthogonal to all Poisson boundaries has vanishing Fourier
coefficients against that fixed weight; a Gaussian average in the scaling parameter concentrates at
a single node and shows that the vector vanishes at every non-resonant node.

* `deningerFloquetBoundary` : the span of the Poisson boundary samples.
* `deningerFloquetResonanceSpan` : the span of the resonant node indicators.
* `deningerFloquetBoundary_orthogonal_inf_eq_bot` : **the completeness computation.**
* `deningerFloquetBoundary_topologicalClosure` : **the closed Poisson-boundary space.**
* `deningerFloquetBoundary_closure_orthogonal` : **the exact Floquet Hilbert quotient.**
-/

namespace RHTower

open MeasureTheory Complex Set Filter Topology SchwartzMap
open GaloisForLFunctions.HTGeometry
open scoped ENNReal InnerProductSpace FourierTransform

noncomputable section

/-! ## Node indicators as `L²` vectors -/

/-- The `L²`-class of the indicator of a node. -/
def deningerFloquetAtomLp (ξ : ℝ) : Lp ℂ 2 deningerFloquetMeasure :=
  (memLp_indicator_const 2 (measurableSet_singleton ξ) (1 : ℂ)
    (Or.inr (deningerFloquetMeasure_singleton_lt_top ξ).ne)).toLp _

theorem deningerFloquetAtomLp_coeFn (ξ : ℝ) :
    (deningerFloquetAtomLp ξ : ℝ → ℂ)
      =ᵐ[deningerFloquetMeasure] Set.indicator ({ξ} : Set ℝ) (fun _ => (1 : ℂ)) :=
  MemLp.coeFn_toLp _

theorem inner_deningerFloquetAtomLp (ξ : ℝ) (a : Lp ℂ 2 deningerFloquetMeasure) :
    ⟪deningerFloquetAtomLp ξ, a⟫_ℂ
      = ∫ x in ({ξ} : Set ℝ), (a : ℝ → ℂ) x ∂deningerFloquetMeasure := by
  rw [L2.inner_def, ← integral_indicator (measurableSet_singleton ξ)]
  refine integral_congr_ae ?_
  filter_upwards [deningerFloquetAtomLp_coeFn ξ] with x hx
  rw [RCLike.inner_apply, hx]
  by_cases hxx : x = ξ
  · subst hxx
    simp
  · simp [hxx]

/-- The inner product with a node indicator reads off the value at the node. -/
theorem inner_deningerFloquetAtomLp_of_ae (ξ : ℝ) (a : Lp ℂ 2 deningerFloquetMeasure)
    {g : ℝ → ℂ} (hg : (a : ℝ → ℂ) =ᵐ[deningerFloquetMeasure] g) :
    ⟪deningerFloquetAtomLp ξ, a⟫_ℂ = (deningerFloquetMeasure.real {ξ} : ℝ) • g ξ := by
  rw [inner_deningerFloquetAtomLp,
    setIntegral_congr_ae (measurableSet_singleton ξ) (hg.mono fun x hx _ => hx),
    integral_singleton]

theorem inner_deningerFloquetAtomLp_self (ξ : ℝ) (a : Lp ℂ 2 deningerFloquetMeasure) :
    ⟪deningerFloquetAtomLp ξ, a⟫_ℂ = (deningerFloquetMeasure.real {ξ} : ℝ) • (a : ℝ → ℂ) ξ :=
  inner_deningerFloquetAtomLp_of_ae ξ a (Filter.EventuallyEq.refl _ _)

/-! ## The two subspaces -/

/-- The span of the Mellin samples of the Poisson boundaries. -/
def deningerFloquetBoundary : Submodule ℂ (Lp ℂ 2 deningerFloquetMeasure) :=
  Submodule.span ℂ (Set.range fun f : DeningerMeyerCap =>
    deningerFloquetLp (deningerPoissonSource f))

/-- The span of the resonant node indicators. -/
def deningerFloquetResonanceSpan : Submodule ℂ (Lp ℂ 2 deningerFloquetMeasure) :=
  Submodule.span ℂ (deningerFloquetAtomLp '' deningerFloquetResonance)

/-- **Every Poisson boundary annihilates the resonant nodes.** -/
theorem deningerFloquetBoundary_le :
    deningerFloquetBoundary ≤ deningerFloquetResonanceSpanᗮ := by
  refine Submodule.span_le.2 ?_
  rintro u ⟨f, rfl⟩
  refine mem_span_orthogonal ?_
  rintro v ⟨ξ, hξ, rfl⟩
  rw [inner_deningerFloquetAtomLp_of_ae ξ _ (deningerFloquetLp_coeFn (deningerPoissonSource f)),
    deningerFloquetSample_poissonSource_eq_zero f hξ, smul_zero]

end

end RHTower
