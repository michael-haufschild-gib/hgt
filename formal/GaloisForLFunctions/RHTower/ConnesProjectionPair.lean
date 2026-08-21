import Mathlib

/-!
# Connes' pair of projections and the angle operator

Formalization of §VIII (30) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

To perform the cutoff `R_Λ = P̂_Λ P_Λ` at an archimedean place, Connes recalls the geometry of a
pair of orthogonal projections: `P₁, P₂` is the same datum as a unitary representation of the
dihedral group `ℤ/2 ∗ ℤ/2` (via the symmetries `U_i = 2P_i - 1`), whose irreducible unitary
representations are at most two dimensional and are parametrized by an angle `θ ∈ [0, π/2]`; a
general pair is characterized by the *angle operator* `Θ`, uniquely defined by

  `sin Θ = |P₁ - P₂|`,

which commutes with both `P_i`.

The algebra behind these statements is proved here without hypotheses:

* `connes_symmetry_sq` - `(2P - 1)² = 1`: the dihedral presentation.
* `connes_projDiff_sq` - `(P - Q)² = P + Q - PQ - QP`.
* `connes_one_sub_projDiff_sq` - the identity `1 - (P-Q)² = (1-P)(1-Q)(1-P) + PQP`, which exhibits
  `1 - (P-Q)²` as a sum of two conjugates of projections and therefore as a positive element.
* `connes_projDiff_sq_commute_left` / `_right` - `(P-Q)²` commutes with `P` and with `Q`.
* `connes_projDiff_sq_le_one`, `connes_norm_projDiff_le_one` - `(P-Q)² ≤ 1` and `‖P - Q‖ ≤ 1`, so
  `arcsin` may be applied and `Θ ∈ [0, π/2]`.
* `connes_commute_cfc_projDiff_sq_left` / `_right` - every continuous function of `(P-Q)²`,
  in particular `|P - Q| = ((P-Q)²)^{1/2}` and `Θ = arcsin((P-Q)²)^{1/2}`, commutes with `P` and
  with `Q`.
-/

namespace GaloisForLFunctions.RHTower

section Algebraic
variable {R : Type*} [Ring R] {P Q : R}

/-- **§VIII (30), the symmetry attached to a projection.**  If `P` is idempotent then `2P - 1` is
an involution; this is how a pair of projections becomes a unitary representation of the dihedral
group `ℤ/2 ∗ ℤ/2`. -/
theorem connes_symmetry_sq (hP : P * P = P) : (2 * P - 1) * (2 * P - 1) = 1 := by
  have h : (2 * P - 1) * (2 * P - 1) = 4 * (P * P) - 4 * P + 1 := by noncomm_ring
  rw [h, hP]; noncomm_ring

/-- The square of the difference of two idempotents. -/
theorem connes_projDiff_sq (hP : P * P = P) (hQ : Q * Q = Q) :
    (P - Q) ^ 2 = P + Q - P * Q - Q * P := by
  have h : (P - Q) ^ 2 = P * P - P * Q - Q * P + Q * Q := by noncomm_ring
  rw [h, hP, hQ]; noncomm_ring

/-- **The key positivity identity.**  For two idempotents,
`1 - (P - Q)² = (1-P)(1-Q)(1-P) + P Q P`.
Both summands are of the form `a* b a` with `b` a projection, so in a C*-algebra the right-hand
side is positive; this is what bounds the angle operator `Θ` of §VIII (30) by `π/2`. -/
theorem connes_one_sub_projDiff_sq (hP : P * P = P) (hQ : Q * Q = Q) :
    1 - (P - Q) ^ 2 = (1 - P) * (1 - Q) * (1 - P) + P * Q * P := by
  have hR : (1 - P) * (1 - Q) * (1 - P)
      = 1 - 2 * P + P * P - Q + Q * P + P * Q - P * Q * P := by noncomm_ring
  rw [connes_projDiff_sq hP hQ, hR, hP]; noncomm_ring

/-- **§VIII (30), commutation.**  `(P₁ - P₂)²` commutes with `P₁`. -/
theorem connes_projDiff_sq_commute_left (hP : P * P = P) (hQ : Q * Q = Q) :
    P * (P - Q) ^ 2 = (P - Q) ^ 2 * P := by
  rw [connes_projDiff_sq hP hQ]
  have h1 : P * (P + Q - P * Q - Q * P)
      = (P * P) + P * Q - (P * P) * Q - P * (Q * P) := by noncomm_ring
  have h2 : (P + Q - P * Q - Q * P) * P
      = (P * P) + Q * P - (P * Q) * P - Q * (P * P) := by noncomm_ring
  rw [h1, h2, hP]
  noncomm_ring

/-- **§VIII (30), commutation.**  `(P₁ - P₂)²` commutes with `P₂`. -/
theorem connes_projDiff_sq_commute_right (hP : P * P = P) (hQ : Q * Q = Q) :
    Q * (P - Q) ^ 2 = (P - Q) ^ 2 * Q := by
  have h : (Q - P) ^ 2 = (P - Q) ^ 2 := by noncomm_ring
  rw [← h]
  exact connes_projDiff_sq_commute_left hQ hP

end Algebraic

section CStar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {P Q : A}

set_option linter.unusedSectionVars false

/-- A self-adjoint idempotent is a positive element. -/
theorem connes_proj_nonneg (hP : P * P = P) (hPs : IsSelfAdjoint P) : 0 ≤ P := by
  have h : P = star P * P := by rw [hPs.star_eq, hP]
  rw [h]; exact star_mul_self_nonneg P

/-- **§VIII (30), the angle bound.**  `(P₁ - P₂)² ≤ 1` for two orthogonal projections. -/
theorem connes_projDiff_sq_le_one (hP : P * P = P) (hPs : IsSelfAdjoint P)
    (hQ : Q * Q = Q) (hQs : IsSelfAdjoint Q) : (P - Q) ^ 2 ≤ 1 := by
  have hQ1 : (1 - Q) * (1 - Q) = 1 - Q := by
    have : (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
    rw [this, hQ]; noncomm_ring
  have hQ1s : IsSelfAdjoint (1 - Q) := IsSelfAdjoint.sub (.one A) hQs
  have hP1s : IsSelfAdjoint (1 - P) := IsSelfAdjoint.sub (.one A) hPs
  have hQ1nn : (0:A) ≤ 1 - Q := connes_proj_nonneg hQ1 hQ1s
  have hQnn : (0:A) ≤ Q := connes_proj_nonneg hQ hQs
  have h1 : (0:A) ≤ (1 - P) * (1 - Q) * (1 - P) := hP1s.conjugate_nonneg hQ1nn
  have h2 : (0:A) ≤ P * Q * P := hPs.conjugate_nonneg hQnn
  have hkey : (0:A) ≤ 1 - (P - Q) ^ 2 := by
    rw [connes_one_sub_projDiff_sq hP hQ]
    exact add_nonneg h1 h2
  exact sub_nonneg.mp hkey

/-- **§VIII (30), the norm bound.**  `‖P₁ - P₂‖ ≤ 1`, so the angle operator `Θ` defined by
`sin Θ = |P₁ - P₂|` takes values in `[0, π/2]`. -/
theorem connes_norm_projDiff_le_one [Nontrivial A] (hP : P * P = P) (hPs : IsSelfAdjoint P)
    (hQ : Q * Q = Q) (hQs : IsSelfAdjoint Q) : ‖P - Q‖ ≤ 1 := by
  have hPQs : IsSelfAdjoint (P - Q) := hPs.sub hQs
  have hsq : (P - Q) ^ 2 = star (P - Q) * (P - Q) := by
    rw [hPQs.star_eq, sq]
  have hnn : (0:A) ≤ (P - Q) ^ 2 := by rw [hsq]; exact star_mul_self_nonneg _
  have hle := connes_projDiff_sq_le_one hP hPs hQ hQs
  have hnorm : ‖(P - Q) ^ 2‖ ≤ ‖(1 : A)‖ :=
    CStarAlgebra.norm_le_norm_of_nonneg_of_le hnn hle
  rw [norm_one] at hnorm
  have hid : ‖(P - Q) ^ 2‖ = ‖P - Q‖ * ‖P - Q‖ := by
    rw [sq]
    nth_rewrite 2 [← hPQs.star_eq]
    exact CStarRing.norm_self_mul_star
  rw [hid] at hnorm
  nlinarith [norm_nonneg (P - Q)]

/-- **§VIII (30), commutation.**  The angle operator `Θ`, being a continuous function of
`(P₁ - P₂)²`, commutes with both projections.  Stated for an arbitrary real functional calculus
function, which covers `|P₁ - P₂| = ((P₁-P₂)²)^{1/2}` and `Θ = arcsin ∘ (·)^{1/2}`. -/
theorem connes_commute_cfc_projDiff_sq_left (hP : P * P = P) (hPs : IsSelfAdjoint P)
    (hQ : Q * Q = Q) (hQs : IsSelfAdjoint Q) (f : ℝ → ℝ) :
    Commute (cfc f ((P - Q) ^ 2)) P := by
  have hsa : IsSelfAdjoint ((P - Q) ^ 2) := (hPs.sub hQs).pow 2
  exact hsa.commute_cfc (Commute.symm (connes_projDiff_sq_commute_left hP hQ)) f

theorem connes_commute_cfc_projDiff_sq_right (hP : P * P = P) (hPs : IsSelfAdjoint P)
    (hQ : Q * Q = Q) (hQs : IsSelfAdjoint Q) (f : ℝ → ℝ) :
    Commute (cfc f ((P - Q) ^ 2)) Q := by
  have hsa : IsSelfAdjoint ((P - Q) ^ 2) := (hPs.sub hQs).pow 2
  exact hsa.commute_cfc (Commute.symm (connes_projDiff_sq_commute_right hP hQ)) f

end CStar

end GaloisForLFunctions.RHTower
