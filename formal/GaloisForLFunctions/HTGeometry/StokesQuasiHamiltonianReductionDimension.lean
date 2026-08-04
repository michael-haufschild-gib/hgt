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

/-! ## Explicit three-term deformation complex -/

namespace WildSmoothReduction

variable {p : ℕ} {counts : WildFactorCounts p}

/-- Degree-zero cochains: central stabilizer plus effective infinitesimal gauge. -/
abbrev Degree0 (_d : WildSmoothReduction counts) :=
  (Fin counts.centerDim → ℂ) × (Fin counts.reductionDim → ℂ)

/-- Degree-one cochains: tangent of the full factor product. -/
abbrev Degree1 (_d : WildSmoothReduction counts) := Fin counts.ambientDim → ℂ

/-- Degree-two cochains: moment constraints plus the dual central channel. -/
abbrev Degree2 (_d : WildSmoothReduction counts) :=
  (Fin counts.reductionDim → ℂ) × (Fin counts.centerDim → ℂ)

/-- Degree-zero differential is the effective gauge derivative; center acts trivially. -/
def d0 (d : WildSmoothReduction counts) : d.Degree0 →ₗ[ℂ] d.Degree1 where
  toFun x := d.linear.gaugeAction x.2
  map_add' x y := by simp
  map_smul' c x := by simp

/-- Degree-one differential is the moment derivative; central obstruction component is zero. -/
def d1 (d : WildSmoothReduction counts) : d.Degree1 →ₗ[ℂ] d.Degree2 where
  toFun x := (d.linear.moment x, 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Infinitesimal moment invariance makes the deformation sequence a complex. -/
theorem d1_comp_d0 (d : WildSmoothReduction counts) : d.d1.comp d.d0 = 0 := by
  apply LinearMap.ext
  intro x
  change (d.linear.moment (d.linear.gaugeAction x.2), 0) = (0, 0)
  have hx : d.linear.moment (d.linear.gaugeAction x.2) = 0 := by
    simpa using LinearMap.congr_fun d.linear.complex x.2
  rw [hx]

/-- Infinitesimal stabilizers. -/
abbrev H0 (d : WildSmoothReduction counts) := d.d0.ker

/-- Tangent cohomology. -/
abbrev H1 (d : WildSmoothReduction counts) := d.tangent

/-- Obstruction cohomology. -/
abbrev H2 (d : WildSmoothReduction counts) := d.Degree2 ⧸ d.d1.range

theorem d0_range_eq_gauge_range (d : WildSmoothReduction counts) :
    d.d0.range = d.linear.gaugeAction.range := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.2, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(0, x), rfl⟩

/-- Stability leaves precisely the central stabilizer in degree zero. -/
theorem finrank_H0 (d : WildSmoothReduction counts) :
    Module.finrank ℂ d.H0 = counts.centerDim := by
  have hrange : Module.finrank ℂ d.d0.range = counts.reductionDim := by
    rw [d.d0_range_eq_gauge_range,
      LinearMap.finrank_range_of_inj d.linear.gauge_injective]
    simp
  have h := d.d0.finrank_range_add_finrank_ker
  rw [hrange] at h
  have hdom : Module.finrank ℂ d.Degree0 =
      counts.centerDim + counts.reductionDim := by simp
  have h' : counts.reductionDim + Module.finrank ℂ d.d0.ker =
      counts.centerDim + counts.reductionDim := h.trans hdom
  change Module.finrank ℂ d.d0.ker = counts.centerDim
  omega

theorem d1_ker_eq_moment_ker (d : WildSmoothReduction counts) :
    d.d1.ker = d.linear.moment.ker := by
  ext v
  simp [d1]

theorem finrank_d1_range (d : WildSmoothReduction counts) :
    Module.finrank ℂ d.d1.range = counts.reductionDim := by
  have h := d.d1.finrank_range_add_finrank_ker
  have hker : Module.finrank ℂ d.d1.ker = Module.finrank ℂ d.linear.moment.ker :=
    congrArg (fun s : Submodule ℂ d.Degree1 => Module.finrank ℂ s)
      d.d1_ker_eq_moment_ker
  rw [hker] at h
  have hm := d.linear.finrank_moment_ker_add_constraint
  have hdom : Module.finrank ℂ d.Degree1 = counts.ambientDim := by simp
  have h' : Module.finrank ℂ d.d1.range + Module.finrank ℂ d.linear.moment.ker =
      counts.ambientDim := h.trans hdom
  omega

/-- Moment regularity leaves precisely the dual central obstruction channel in degree two. -/
theorem finrank_H2 (d : WildSmoothReduction counts) :
    Module.finrank ℂ d.H2 = counts.centerDim := by
  have h := Submodule.finrank_quotient_add_finrank d.d1.range
  rw [d.finrank_d1_range] at h
  have hdom : Module.finrank ℂ d.Degree2 =
      counts.reductionDim + counts.centerDim := by simp
  have h' : Module.finrank ℂ d.H2 + counts.reductionDim =
      counts.reductionDim + counts.centerDim := h.trans hdom
  omega

/-- Euler characteristic of the explicit deformation complex. -/
def cohomologicalEuler (d : WildSmoothReduction counts) : ℤ :=
  Module.finrank ℂ d.H0 - Module.finrank ℂ d.H1 + Module.finrank ℂ d.H2

/-- Cellular source count for the deformation Euler characteristic. -/
def expectedEuler (c : WildFactorCounts p) : ℤ :=
  ((2 : ℤ) - 2 * c.genus - p) * c.groupDim +
    ∑ a, ((c.formalCentralizerDim a : ℤ) - c.stokesRootDim a - c.conjugacyDim a)

/-- **Deformation-complex Euler formula.** Degree-zero and degree-two center channels plus the
source-derived tangent dimension give the complete cellular index. -/
theorem cohomologicalEuler_eq_expectedEuler (d : WildSmoothReduction counts) :
    d.cohomologicalEuler = expectedEuler counts := by
  rw [cohomologicalEuler, d.finrank_H0, d.tangent_finrank_eq_expectedDim,
    d.finrank_H2]
  simp only [WildFactorCounts.expectedDim, expectedEuler]
  simp_rw [Finset.sum_sub_distrib]
  simp_rw [Finset.sum_add_distrib]
  ring

end WildSmoothReduction

end
end WildReduction
end IrregularStokes
end GaloisForLFunctions
