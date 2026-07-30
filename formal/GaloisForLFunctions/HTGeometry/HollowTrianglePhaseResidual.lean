import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

namespace GaloisForLFunctions.HTGeometry

/-!
# Hollow-triangle phase residual

This file isolates the exact scalar obstruction exposed by the smallest
irreducible pairwise-compatibility scenario.  Three pair-context normalization
equations fix all three squared amplitudes, but leave two relative phases after
quotienting one common phase.

Every declaration is unconditional.  The final theorem gives an algebraic orbit
classification rather than assuming the topological quotient `𝕋³ / 𝕋 ≃ 𝕋²`.
No physical interpretation of the phases, contextuality scenario, gauge field,
or spacetime is asserted.
-/

/-- The three pair-context normalization equations of the hollow triangle. -/
def HollowTrianglePairNormalized (u₀ u₁ u₂ : ℂ) : Prop :=
  Complex.normSq u₀ + Complex.normSq u₁ = 1 ∧
  Complex.normSq u₁ + Complex.normSq u₂ = 1 ∧
  Complex.normSq u₂ + Complex.normSq u₀ = 1

/-- Three pairwise unit-sum constraints force all three intensities to be one half. -/
theorem hollowTriangle_intensity_rigidity
    {a b c : ℝ}
    (hab : a + b = 1)
    (hbc : b + c = 1)
    (hca : c + a = 1) :
    a = 1 / 2 ∧ b = 1 / 2 ∧ c = 1 / 2 := by
  have hac : a = c := by
    apply add_right_cancel
    calc
      a + b = 1 := hab
      _ = b + c := hbc.symm
      _ = c + b := add_comm b c
  have hba : b = a := by
    apply add_right_cancel
    calc
      b + c = 1 := hbc
      _ = c + a := hca.symm
      _ = a + c := add_comm c a
  have haa : a + a = 1 := by
    simpa only [hba] using hab
  have ha : a = 1 / 2 := by
    apply (eq_div_iff two_ne_zero).2
    simpa only [mul_two] using haa
  exact ⟨ha, hba.trans ha, hac.symm.trans ha⟩

/-- The hollow-triangle equations fix all squared complex amplitudes to one half. -/
theorem hollowTriangle_normSq_rigidity
    {u₀ u₁ u₂ : ℂ}
    (h : HollowTrianglePairNormalized u₀ u₁ u₂) :
    Complex.normSq u₀ = 1 / 2 ∧
      Complex.normSq u₁ = 1 / 2 ∧
      Complex.normSq u₂ = 1 / 2 :=
  hollowTriangle_intensity_rigidity h.1 h.2.1 h.2.2

/-- Once a half-intensity radius is fixed, independent unit phases remain free. -/
theorem hollowTriangle_independent_unit_phases
    {r u₀ u₁ u₂ : ℂ}
    (hr : Complex.normSq r + Complex.normSq r = 1)
    (hu₀ : Complex.normSq u₀ = 1)
    (hu₁ : Complex.normSq u₁ = 1)
    (hu₂ : Complex.normSq u₂ = 1) :
    HollowTrianglePairNormalized (r * u₀) (r * u₁) (r * u₂) := by
  simp only [HollowTrianglePairNormalized, map_mul, hu₀, hu₁, hu₂, mul_one]
  exact ⟨hr, hr, hr⟩

/-- The two relative phases obtained after using the zeroth phase as reference. -/
def hollowTriangleRelativePhases (u₀ u₁ u₂ : ℂ) : ℂ × ℂ :=
  ((starRingEnd ℂ) u₀ * u₁, (starRingEnd ℂ) u₀ * u₂)

/-- Multiplication by one common unit phase leaves both relative phases unchanged. -/
theorem hollowTriangleRelativePhases_common_invariant
    {lam u₀ u₁ u₂ : ℂ}
    (hlam : Complex.normSq lam = 1) :
    hollowTriangleRelativePhases (lam * u₀) (lam * u₁) (lam * u₂) =
      hollowTriangleRelativePhases u₀ u₁ u₂ := by
  have hlamc : (starRingEnd ℂ) lam * lam = 1 := by
    simpa only [hlam, Complex.ofReal_one] using
      (Complex.normSq_eq_conj_mul_self (z := lam)).symm
  apply Prod.ext
  · change
      (starRingEnd ℂ) (lam * u₀) * (lam * u₁) =
        (starRingEnd ℂ) u₀ * u₁
    rw [map_mul]
    calc
      (starRingEnd ℂ) lam * (starRingEnd ℂ) u₀ * (lam * u₁) =
          ((starRingEnd ℂ) lam * lam) * ((starRingEnd ℂ) u₀ * u₁) := by
            ring
      _ = (starRingEnd ℂ) u₀ * u₁ := by rw [hlamc, one_mul]
  · change
      (starRingEnd ℂ) (lam * u₀) * (lam * u₂) =
        (starRingEnd ℂ) u₀ * u₂
    rw [map_mul]
    calc
      (starRingEnd ℂ) lam * (starRingEnd ℂ) u₀ * (lam * u₂) =
          ((starRingEnd ℂ) lam * lam) * ((starRingEnd ℂ) u₀ * u₂) := by
            ring
      _ = (starRingEnd ℂ) u₀ * u₂ := by rw [hlamc, one_mul]

/-- Orbit relation for triples under multiplication by one common unit phase. -/
def HollowTriangleCommonPhaseEquivalent
    (u₀ u₁ u₂ v₀ v₁ v₂ : ℂ) : Prop :=
  ∃ lam : ℂ,
    Complex.normSq lam = 1 ∧
    v₀ = lam * u₀ ∧
    v₁ = lam * u₁ ∧
    v₂ = lam * u₂

/--
Two triples of unit phases have the same two relative phases exactly when they
differ by one common unit phase.  This is the algebraic orbit classification
underlying the residual two-torus.
-/
theorem hollowTriangle_relativePhases_complete
    {u₀ u₁ u₂ v₀ v₁ v₂ : ℂ}
    (hu₀ : Complex.normSq u₀ = 1)
    (hv₀ : Complex.normSq v₀ = 1) :
    hollowTriangleRelativePhases u₀ u₁ u₂ =
        hollowTriangleRelativePhases v₀ v₁ v₂ ↔
      HollowTriangleCommonPhaseEquivalent u₀ u₁ u₂ v₀ v₁ v₂ := by
  constructor
  · intro hrel
    have hu₀c : (starRingEnd ℂ) u₀ * u₀ = 1 := by
      simpa only [hu₀, Complex.ofReal_one] using
        (Complex.normSq_eq_conj_mul_self (z := u₀)).symm
    have hv₀c : v₀ * (starRingEnd ℂ) v₀ = 1 := by
      simpa only [hv₀, Complex.ofReal_one] using Complex.mul_conj v₀
    have hrel₁ :
        (starRingEnd ℂ) u₀ * u₁ = (starRingEnd ℂ) v₀ * v₁ :=
      congrArg Prod.fst hrel
    have hrel₂ :
        (starRingEnd ℂ) u₀ * u₂ = (starRingEnd ℂ) v₀ * v₂ :=
      congrArg Prod.snd hrel
    let lam := v₀ * (starRingEnd ℂ) u₀
    have hlam₀ : v₀ = lam * u₀ := by
      dsimp only [lam]
      calc
        v₀ = v₀ * 1 := by rw [mul_one]
        _ = v₀ * ((starRingEnd ℂ) u₀ * u₀) := by rw [hu₀c]
        _ = (v₀ * (starRingEnd ℂ) u₀) * u₀ := by ring
    have hlam₁ : v₁ = lam * u₁ := by
      dsimp only [lam]
      calc
        v₁ = 1 * v₁ := by rw [one_mul]
        _ = (v₀ * (starRingEnd ℂ) v₀) * v₁ := by rw [hv₀c]
        _ = v₀ * ((starRingEnd ℂ) v₀ * v₁) := by ring
        _ = v₀ * ((starRingEnd ℂ) u₀ * u₁) := by rw [hrel₁]
        _ = (v₀ * (starRingEnd ℂ) u₀) * u₁ := by ring
    have hlam₂ : v₂ = lam * u₂ := by
      dsimp only [lam]
      calc
        v₂ = 1 * v₂ := by rw [one_mul]
        _ = (v₀ * (starRingEnd ℂ) v₀) * v₂ := by rw [hv₀c]
        _ = v₀ * ((starRingEnd ℂ) v₀ * v₂) := by ring
        _ = v₀ * ((starRingEnd ℂ) u₀ * u₂) := by rw [hrel₂]
        _ = (v₀ * (starRingEnd ℂ) u₀) * u₂ := by ring
    have hlam : Complex.normSq lam = 1 := by
      calc
        Complex.normSq lam = Complex.normSq lam * 1 := by rw [mul_one]
        _ = Complex.normSq lam * Complex.normSq u₀ := by rw [hu₀]
        _ = Complex.normSq (lam * u₀) := (map_mul Complex.normSq lam u₀).symm
        _ = Complex.normSq v₀ := by rw [← hlam₀]
        _ = 1 := hv₀
    exact ⟨lam, hlam, hlam₀, hlam₁, hlam₂⟩
  · rintro ⟨lam, hlam, rfl, rfl, rfl⟩
    exact (hollowTriangleRelativePhases_common_invariant hlam).symm

end GaloisForLFunctions.HTGeometry
