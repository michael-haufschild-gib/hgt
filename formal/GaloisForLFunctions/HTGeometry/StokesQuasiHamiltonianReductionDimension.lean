import Mathlib

/-!
# Source-level tangent dimension for wild Hamiltonian reduction

The tangent space of a smooth stable wild reduction is constructed as the cohomology quotient
`ker(moment derivative) / range(gauge derivative)`.  Surjectivity of the moment derivative,
injectivity of the effective gauge action, and the infinitesimal moment-map identity give its
dimension by rank-nullity.  Counting handle, fission, formal-centralizer, Stokes-root, and conjugacy
factors then derives the wild character-variety dimension polynomial; no published dimension
formula is an input.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes
namespace WildReduction

noncomputable section

/-- Linearized Hamiltonian reduction at a smooth stable point. -/
structure LinearHamiltonianReduction (ambient constraint gauge : ℕ) where
  moment : (Fin ambient → ℂ) →ₗ[ℂ] (Fin constraint → ℂ)
  gaugeAction : (Fin gauge → ℂ) →ₗ[ℂ] (Fin ambient → ℂ)
  moment_surjective : Function.Surjective moment
  gauge_injective : Function.Injective gaugeAction
  complex : moment.comp gaugeAction = 0

namespace LinearHamiltonianReduction

variable {ambient constraint gauge : ℕ}

/-- Infinitesimal gauge action with codomain restricted to the moment-map kernel. -/
def gaugeToKernel (d : LinearHamiltonianReduction ambient constraint gauge) :
    (Fin gauge → ℂ) →ₗ[ℂ] d.moment.ker where
  toFun x := ⟨d.gaugeAction x, by
    have h := LinearMap.congr_fun d.complex x
    simpa using h⟩
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

theorem gaugeToKernel_injective (d : LinearHamiltonianReduction ambient constraint gauge) :
    Function.Injective d.gaugeToKernel := by
  intro x y h
  apply d.gauge_injective
  exact Subtype.ext_iff.mp h

/-- Reduced tangent as the actual cohomology quotient. -/
abbrev reducedTangent (d : LinearHamiltonianReduction ambient constraint gauge) :=
  d.moment.ker ⧸ d.gaugeToKernel.range

theorem finrank_moment_range (d : LinearHamiltonianReduction ambient constraint gauge) :
    Module.finrank ℂ d.moment.range = constraint := by
  rw [(LinearMap.range_eq_top.mpr d.moment_surjective)]
  simp

theorem finrank_moment_ker_add_constraint
    (d : LinearHamiltonianReduction ambient constraint gauge) :
    Module.finrank ℂ d.moment.ker + constraint = ambient := by
  have h := d.moment.finrank_range_add_finrank_ker
  rw [d.finrank_moment_range] at h
  simpa [Nat.add_comm] using h

theorem finrank_gaugeRange (d : LinearHamiltonianReduction ambient constraint gauge) :
    Module.finrank ℂ d.gaugeToKernel.range = gauge := by
  rw [LinearMap.finrank_range_of_inj d.gaugeToKernel_injective]
  simp

theorem finrank_reducedTangent_add_gauge
    (d : LinearHamiltonianReduction ambient constraint gauge) :
    Module.finrank ℂ d.reducedTangent + gauge = Module.finrank ℂ d.moment.ker := by
  have h := Submodule.finrank_quotient_add_finrank d.gaugeToKernel.range
  rw [d.finrank_gaugeRange] at h
  exact h

/-- Rank-nullity dimension of the reduced tangent. -/
theorem finrank_reducedTangent
    (d : LinearHamiltonianReduction ambient constraint gauge) :
    Module.finrank ℂ d.reducedTangent = ambient - constraint - gauge := by
  have hm := d.finrank_moment_ker_add_constraint
  have hr := d.finrank_reducedTangent_add_gauge
  omega

end LinearHamiltonianReduction

/-- Dimensions of all geometric factors in a wild surface presentation. -/
structure WildFactorCounts (p : ℕ) where
  genus : ℕ
  groupDim : ℕ
  centerDim : ℕ
  center_le_group : centerDim ≤ groupDim
  formalCentralizerDim : Fin p → ℕ
  stokesRootDim : Fin p → ℕ
  conjugacyDim : Fin p → ℕ

namespace WildFactorCounts

variable {p : ℕ}

/-- Product tangent before moment constraints and gauge reduction:
`2g dim G + sum_a (dim G + dim H_a + s_a + k_a)`. -/
def ambientDim (c : WildFactorCounts p) : ℕ :=
  2 * c.genus * c.groupDim +
    ∑ a, (c.groupDim + c.formalCentralizerDim a +
      c.stokesRootDim a + c.conjugacyDim a)

/-- Effective moment and gauge dimension:
`dim G - dim Z(G) + sum_a dim H_a`. -/
def reductionDim (c : WildFactorCounts p) : ℕ :=
  (c.groupDim - c.centerDim) + ∑ a, c.formalCentralizerDim a

/-- Derived wild dimension polynomial. -/
def expectedDim (c : WildFactorCounts p) : ℤ :=
  2 * (c.centerDim : ℤ) +
    ((2 * c.genus : ℤ) - 2 + p) * c.groupDim +
    ∑ a, ((c.stokesRootDim a : ℤ) +
      c.conjugacyDim a - c.formalCentralizerDim a)

/-- Factor count minus two reductions is the wild dimension polynomial. -/
theorem ambient_sub_two_reductions (c : WildFactorCounts p) :
    (c.ambientDim : ℤ) - 2 * c.reductionDim = c.expectedDim := by
  simp only [ambientDim, reductionDim, expectedDim]
  push_cast [Nat.cast_sub c.center_le_group]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [Finset.sum_add_distrib]
  simp
  ring

end WildFactorCounts

/-- Smooth stable wild reduction whose tangent maps come from the explicit factor product. -/
structure WildSmoothReduction {p : ℕ} (counts : WildFactorCounts p) where
  linear : LinearHamiltonianReduction counts.ambientDim counts.reductionDim counts.reductionDim

namespace WildSmoothReduction

variable {p : ℕ} {counts : WildFactorCounts p}

abbrev tangent (d : WildSmoothReduction counts) := d.linear.reducedTangent

/-- **Wild tangent dimension formula derived from source.** -/
theorem tangent_finrank_eq_expectedDim (d : WildSmoothReduction counts) :
    (Module.finrank ℂ d.tangent : ℤ) = counts.expectedDim := by
  have hm := d.linear.finrank_moment_ker_add_constraint
  have hr := d.linear.finrank_reducedTangent_add_gauge
  change Module.finrank ℂ d.tangent + counts.reductionDim =
    Module.finrank ℂ d.linear.moment.ker at hr
  have hnat : Module.finrank ℂ d.tangent + 2 * counts.reductionDim = counts.ambientDim := by
    omega
  have hint : (Module.finrank ℂ d.tangent : ℤ) =
      (counts.ambientDim : ℤ) - 2 * counts.reductionDim := by
    have hcast := congrArg (fun q : ℕ => (q : ℤ)) hnat
    push_cast at hcast
    linarith
  rw [hint, counts.ambient_sub_two_reductions]

end WildSmoothReduction

end
end WildReduction
end IrregularStokes
end GaloisForLFunctions
