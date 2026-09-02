import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixAlgebraicUntwistingNoGo

/-!
# Central-scalar relation rigidity for Gamma-six descent

Route L's remaining descent problem permits a singular or multivalued source-to-physical
comparison.  Multivaluedness and noncommutative coefficient spaces do not by themselves evade the
Gamma-six holonomy obstruction when that holonomy still acts through a central real scalar and the
physical target fibre is fixed.

The algebraic theorem below is exact.  A linear relation with one output surviving quotient by its
vertical fibre is covariant for source scalar `u` and target scalar `v` exactly when `u = v`.  No
topology, closedness, boundedness, finite-dimensionality, or single-valuedness is assumed.  Applied
to the literal Xi-selected Gamma-six holonomy and the fixed target scalar `1`, covariance is
equivalent to critical-line placement.

Thus the entire central-scalar linear-correspondence escape is terminal.  A surviving Route L
comparison must change the action itself: matched non-scalar/operator-valued holonomy,
non-real-linear transport, or a source-forced domain/fibre change.
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact quotient-support classification for scalar-covariant linear relations.  Once one target
class survives quotient by the vertical fibre, covariance for two scalar characters is possible
exactly when the characters agree. -/
theorem linearRelation_scalarCovariance_iff_eq_of_nonvertical
    {𝕜 X Y : Type*} [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    (R : Submodule 𝕜 (X × Y))
    (x₀ : X) (y₀ : Y) (hxy : (x₀, y₀) ∈ R)
    (hnonvertical : ((0 : X), y₀) ∉ R)
    (u v : 𝕜) :
    (∀ x y, (x, y) ∈ R → (u • x, v • y) ∈ R) ↔ u = v := by
  constructor
  · intro hcov
    by_contra huv
    have hscaled := hcov x₀ y₀ hxy
    have hcommon := R.smul_mem u hxy
    have hdiff := R.sub_mem hscaled hcommon
    have hvu : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
    have hvertical : ((0 : X), (v - u) • y₀) ∈ R := by
      simpa [sub_smul] using hdiff
    have hunscale := R.smul_mem (v - u)⁻¹ hvertical
    apply hnonvertical
    simpa [hvu] using hunscale
  · rintro rfl x y hxy'
    simpa using R.smul_mem u hxy'

/-- The literal Xi-selected Gamma-six holonomy is trivial exactly on the critical line. -/
theorem sourceHorizontalGammaSixPhysicalHolonomy_eq_one_iff
    (q : XiZeroCopy) :
    sourceHorizontalGammaSixPhysicalHolonomy q = 1 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [← sourceHorizontalGammaSixHolonomyBoundary_eq_deningerZBoundary_iff]
  exact sourceHorizontalGammaSixPhysicalCovariantBoundary_eq_fixed_iff q

/-- **[L CENTRAL-SCALAR CORRESPONDENCE ROUTE-CLASS KILL].**  For arbitrary real modules and an
arbitrary multivalued linear relation with a nonzero target quotient class, covariance from the
literal Gamma-six physical holonomy to the fixed physical scalar action is exactly critical-line
placement. -/
theorem
    sourceHorizontalGammaSixPhysical_fixedTarget_relationCovariance_iff_criticalLine
    {X Y : Type*}
    [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    (q : XiZeroCopy)
    (R : Submodule ℝ (X × Y))
    (x₀ : X) (y₀ : Y) (hxy : (x₀, y₀) ∈ R)
    (hnonvertical : ((0 : X), y₀) ∉ R) :
    (∀ x y, (x, y) ∈ R →
      (sourceHorizontalGammaSixPhysicalHolonomy q • x, y) ∈ R) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [show (∀ x y, (x, y) ∈ R →
      (sourceHorizontalGammaSixPhysicalHolonomy q • x, y) ∈ R) ↔
      sourceHorizontalGammaSixPhysicalHolonomy q = 1 by
    simpa using linearRelation_scalarCovariance_iff_eq_of_nonvertical
      R x₀ y₀ hxy hnonvertical
        (sourceHorizontalGammaSixPhysicalHolonomy q) 1]
  exact sourceHorizontalGammaSixPhysicalHolonomy_eq_one_iff q

end

end RHTower
