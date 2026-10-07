import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic

/-!
# Discrete rescaled displacements determine an affine germ

A derivative supplies a limit for rescaled displacements. Closedness and discreteness turn
that limit into eventual exact equality. The analytic identity theorem then determines the germ.
The proof uses no growth or counting estimate.
-/

namespace GaloisForLFunctions.HTGeometry.DiscreteDilationGerm

open Filter Topology Set

theorem eventually_eq_of_closed_discrete {X : Type*} [TopologicalSpace X]
    {S : Set X} (hclosed : IsClosed S) (hdiscrete : IsDiscrete S)
    {u : ℕ → X} {a : X} (hlim : Tendsto u atTop (𝓝 a))
    (hmem : ∀ᶠ n in atTop, u n ∈ S) : ∀ᶠ n in atTop, u n = a := by
  have ha : a ∈ S := hclosed.mem_of_tendsto hlim hmem
  obtain ⟨U, hU, hUS⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hdiscrete a ha
  have haU : a ∈ U := by
    have : a ∈ U ∩ S := by rw [hUS]; exact mem_singleton a
    exact this.1
  filter_upwards [hlim.eventually (hU.mem_nhds haU), hmem] with n hnU hnS
  have : u n ∈ U ∩ S := ⟨hnU, hnS⟩
  simpa [hUS] using this

theorem shrinking_samples {lam a : ℂ} (hlam : lam ≠ 0) (ha : a ≠ 0)
    (hlim : Tendsto (fun n : ℕ => (lam ^ n)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => a / lam ^ n) atTop (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa [div_eq_mul_inv] using hlim.const_mul a
  · exact Eventually.of_forall fun n => div_ne_zero ha (pow_ne_zero n hlam)

/-- Differentiability and a discrete rescaled displacement give exact affine samples. -/
theorem eventually_affine_samples {g : ℂ → ℂ} {b lam a : ℂ}
    (hg : HasDerivAt g b 0) (hlam : lam ≠ 0) (ha : a ≠ 0)
    (hlim : Tendsto (fun n : ℕ => (lam ^ n)⁻¹) atTop (𝓝 0))
    {S : Set ℂ} (hclosed : IsClosed S) (hdiscrete : IsDiscrete S)
    (hmem : ∀ᶠ n in atTop, lam ^ n * (g (a / lam ^ n) - g 0) ∈ S) :
    ∀ᶠ n in atTop, g (a / lam ^ n) = g 0 + b * (a / lam ^ n) := by
  have hsamples := shrinking_samples hlam ha hlim
  have hd := (hg.tendsto_slope_zero.comp hsamples).const_mul a
  have hrescale : Tendsto (fun n : ℕ => lam ^ n * (g (a / lam ^ n) - g 0))
      atTop (𝓝 (a * b)) := by
    convert hd using 1
    funext n
    simp only [Function.comp_def, zero_add, smul_eq_mul, inv_div]
    field_simp
  have heq := eventually_eq_of_closed_discrete hclosed hdiscrete hrescale hmem
  filter_upwards [heq] with n hn
  have hpow := pow_ne_zero n hlam
  apply (mul_left_cancel₀ hpow)
  field_simp
  linear_combination hn

/-- The affine conclusion is a germ equality, not just a limit or a first-order approximation. -/
theorem affine_germ_of_discrete_displacements {g : ℂ → ℂ} {b lam a : ℂ}
    (hgan : AnalyticAt ℂ g 0) (hg : HasDerivAt g b 0)
    (hlam : lam ≠ 0) (ha : a ≠ 0)
    (hlim : Tendsto (fun n : ℕ => (lam ^ n)⁻¹) atTop (𝓝 0))
    {S : Set ℂ} (hclosed : IsClosed S) (hdiscrete : IsDiscrete S)
    (hmem : ∀ᶠ n in atTop, lam ^ n * (g (a / lam ^ n) - g 0) ∈ S) :
    ∀ᶠ z in 𝓝 (0 : ℂ), g z = g 0 + b * z := by
  have heq := eventually_affine_samples hg hlam ha hlim hclosed hdiscrete hmem
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), g z = g 0 + b * z :=
    (shrinking_samples hlam ha hlim).frequently heq.frequently
  exact (hgan.frequently_eq_iff_eventually_eq
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id))).mp hfreq

end GaloisForLFunctions.HTGeometry.DiscreteDilationGerm
