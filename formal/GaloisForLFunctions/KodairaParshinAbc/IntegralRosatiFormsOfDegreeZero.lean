import GaloisForLFunctions.KodairaParshinAbc.DegreeZeroClassesHaveVanishingTateHeight

/-!
# Integral Rosati forms of degree zero

On a scaling datum `D` the integral Rosati form `ξ ↦ τ_x(ξ ξ′)` on `ℤ[G]`
(`ArithmeticEffectivityTheory.intRosatiForm`) is homogeneous of degree two.  The two height
principles for classes on a curve apply to it, on every scaling datum — in particular to the
multiplicative-scale and two-prime forms built from the zeta scaling data:

* **negative degree** — a Rosati form bounded above on `ℤ[G]` is `≤ 0`
  (`intRosatiForm_nonpos_of_bounded_above`); if moreover the orbit Hodge index holds at `x`, it
  vanishes (`intRosatiForm_eq_zero_of_hodgeIndex_of_bounded_above`);
* **degree zero** — if `|τ_x - c τ_y| ≤ ε τ_y + B_ε` on `ℤ[G]` for every `ε > 0`, then
  `τ_x = c τ_y` (`intRosatiForm_eq_smul_of_degree_zero`).
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc

open ArithmeticEffectivityTheory

variable {G : Type*} [AddCommGroup G] {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (D : ArithmeticOrientationGeometry.ScalingDatum G E)

theorem intRosatiForm_two_nsmul (x : E) (ξ : G →₀ ℤ) :
    intRosatiForm D x (2 • ξ) = 4 * intRosatiForm D x ξ := by
  rw [intRosatiForm_nsmul]
  norm_num

/-- **Negative degree**: a Rosati form bounded above on `ℤ[G]` is nonpositive. -/
theorem intRosatiForm_nonpos_of_bounded_above (x : E) {B : ℝ}
    (hB : ∀ ξ : G →₀ ℤ, intRosatiForm D x ξ ≤ B) (ξ : G →₀ ℤ) : intRosatiForm D x ξ ≤ 0 :=
  nonpos_of_two_nsmul_of_bounded_above (q := intRosatiForm D x) (intRosatiForm_two_nsmul D x) hB ξ

/-- A Rosati form that satisfies the orbit Hodge index and is bounded above vanishes. -/
theorem intRosatiForm_eq_zero_of_hodgeIndex_of_bounded_above (x : E) (hH : D.OrbitHodgeIndex x)
    {B : ℝ} (hB : ∀ ξ : G →₀ ℤ, intRosatiForm D x ξ ≤ B) (ξ : G →₀ ℤ) :
    intRosatiForm D x ξ = 0 :=
  le_antisymm (intRosatiForm_nonpos_of_bounded_above D x hB ξ)
    ((orbitHodgeIndex_iff_int D x).mp hH ξ)

/-- **Degree zero**: Rosati forms whose difference has degree zero are proportional. -/
theorem intRosatiForm_eq_smul_of_degree_zero (x y : E) (c : ℝ)
    (hcor : ∀ ε > 0, ∃ B, ∀ ξ : G →₀ ℤ,
      |intRosatiForm D x ξ - c * intRosatiForm D y ξ| ≤ ε * intRosatiForm D y ξ + B)
    (ξ : G →₀ ℤ) : intRosatiForm D x ξ = c * intRosatiForm D y ξ := by
  have h := eq_zero_of_two_nsmul_of_degree_zero
    (q := fun η => intRosatiForm D x η - c * intRosatiForm D y η) (qM := intRosatiForm D y)
    (fun η => by simp only [intRosatiForm_two_nsmul]; ring) (intRosatiForm_two_nsmul D y)
    hcor ξ
  linarith

end GaloisForLFunctions.KodairaParshinAbc
