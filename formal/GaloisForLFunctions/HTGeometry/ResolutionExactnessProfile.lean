import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Resolution exactness profiles

A completion defect can disappear at coarse resolution and reappear when the resolving aperture
closes.  A `ResolutionExactnessProfile` records the sharp transition by a nonnegative core radius:
the resolved object is exact at aperture `epsilon` precisely when the core is zero or the aperture
is strictly larger than the core.

The main theorem is a cofinal rigidity law.  Exactness along one positive sequence of apertures
converging to zero is possible exactly when the core radius is zero.  Thus a nonzero core is a
literal obstruction to resolution-independent completion, not a scalar analogy.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A sharp exactness wall indexed by a real resolution aperture. -/
structure ResolutionExactnessProfile where
  /-- Smallest resolving scale retained by the defect. -/
  coreRadius : ℝ
  /-- Core radii are physical scales. -/
  coreRadius_nonneg : 0 ≤ coreRadius
  /-- Exactness predicate at a supplied aperture. -/
  exactAt : ℝ → Prop
  /-- Sharp wall: a nonzero core is exact only above its radius. -/
  exactAt_iff : ∀ epsilon : ℝ,
    exactAt epsilon ↔ coreRadius = 0 ∨ coreRadius < epsilon

namespace ResolutionExactnessProfile

/-- Exactness on a positive cofinal family of apertures closing to zero. -/
def CofinallyExact (P : ResolutionExactnessProfile) : Prop :=
  ∃ aperture : ℕ → ℝ,
    (∀ n, 0 < aperture n) ∧
    Tendsto aperture atTop (nhds 0) ∧
    ∀ n, P.exactAt (aperture n)

/-- Every aperture above the core resolves the defect. -/
theorem exactAt_of_coreRadius_lt (P : ResolutionExactnessProfile)
    {epsilon : ℝ} (h : P.coreRadius < epsilon) :
    P.exactAt epsilon :=
  (P.exactAt_iff epsilon).2 (Or.inr h)

/-- A nonzero defect is not exact at its own core scale. -/
theorem not_exactAt_coreRadius (P : ResolutionExactnessProfile)
    (hcore : P.coreRadius ≠ 0) :
    ¬P.exactAt P.coreRadius := by
  rw [P.exactAt_iff]
  exact fun h => h.elim hcore (lt_irrefl P.coreRadius)

/-- **Cofinal resolution rigidity.**  Exactness can persist through apertures closing to zero
exactly when the resolution core vanishes. -/
theorem cofinallyExact_iff_coreRadius_eq_zero (P : ResolutionExactnessProfile) :
    P.CofinallyExact ↔ P.coreRadius = 0 := by
  constructor
  · rintro ⟨aperture, _hpositive, haperture, hexact⟩
    by_contra hcore
    have hcorePos : 0 < P.coreRadius :=
      lt_of_le_of_ne P.coreRadius_nonneg (Ne.symm hcore)
    have hbelow : ∀ᶠ n : ℕ in atTop, aperture n < P.coreRadius :=
      (tendsto_order.1 haperture).2 P.coreRadius hcorePos
    obtain ⟨n, hn⟩ := hbelow.exists
    rcases (P.exactAt_iff (aperture n)).1 (hexact n) with hzero | habove
    · exact hcore hzero
    · exact (not_lt_of_ge habove.le) hn
  · intro hcore
    refine ⟨fun n : ℕ => (((n : ℝ) + 1)⁻¹), ?_, ?_, ?_⟩
    · intro n
      positivity
    · simpa only [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0))
    · intro n
      exact (P.exactAt_iff _).2 (Or.inl hcore)

/-- Positive core is exactly failure of cofinal resolution exactness. -/
theorem not_cofinallyExact_iff_coreRadius_pos (P : ResolutionExactnessProfile) :
    ¬P.CofinallyExact ↔ 0 < P.coreRadius := by
  rw [P.cofinallyExact_iff_coreRadius_eq_zero]
  exact ⟨fun h => lt_of_le_of_ne P.coreRadius_nonneg (Ne.symm h),
    fun h => ne_of_gt h⟩

end ResolutionExactnessProfile
end GaloisForLFunctions.HTGeometry
