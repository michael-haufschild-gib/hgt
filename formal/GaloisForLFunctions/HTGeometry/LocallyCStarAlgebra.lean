import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Projective limits of C*-algebras

A *locally C*-algebra* is a complete topological `*`-algebra whose topology is given by a family of
C*-seminorms; the standard source of examples is the projective limit of a tower of C*-algebras.

This module builds that object from a tower `bond n : A (n+1) → A n` of continuous
`*`-ring homomorphisms:

* `projLimit` — the coherent sequences, a subring closed under `star`;
* `isClosed_projLimit` and the induced completeness, so the limit is a complete topological
  `*`-algebra;
* `norm_star_mul_self_apply` — each defining seminorm `a ↦ ‖a n‖` satisfies the C*-identity, which
  is what makes the limit *locally* C*;
* `boundedPart` and `boundedNorm` — the bounded elements with their sup-norm, and
  `boundedNorm_star_mul_self`: the sup-norm satisfies the C*-identity too, so the bounded part is a
  C*-normed algebra.

The last statement is the one with content: a supremum of squares is the square of the supremum
only because the norms are nonnegative, and that is exactly what the C*-identity needs.
-/

namespace GaloisForLFunctions.HTGeometry

namespace LocallyCStar

variable {A : ℕ → Type*} [∀ n, NormedRing (A n)] [∀ n, StarRing (A n)]

/-- A sequence is coherent for a tower of bonds when each entry maps to the previous one. -/
def IsCoherentTower (bond : ∀ n, A (n + 1) →+* A n) (a : ∀ n, A n) : Prop :=
  ∀ n, bond n (a (n + 1)) = a n

/-- The projective limit of a tower of rings. -/
def projLimit (bond : ∀ n, A (n + 1) →+* A n) : Set (∀ n, A n) :=
  {a | IsCoherentTower bond a}

omit [(n : ℕ) → StarRing (A n)] in
theorem mem_projLimit {bond : ∀ n, A (n + 1) →+* A n} {a : ∀ n, A n} :
    a ∈ projLimit bond ↔ ∀ n, bond n (a (n + 1)) = a n := Iff.rfl

/-- The projective limit is a subring of the product. -/
def projSubring (bond : ∀ n, A (n + 1) →+* A n) : Subring (∀ n, A n) where
  carrier := projLimit bond
  zero_mem' := fun n => by simp
  one_mem' := fun n => by simp
  add_mem' {a b} ha hb := fun n => by
    simp only [Pi.add_apply, map_add, ha n, hb n]
  neg_mem' {a} ha := fun n => by
    simp only [Pi.neg_apply, map_neg, ha n]
  mul_mem' {a b} ha hb := fun n => by
    simp only [Pi.mul_apply, map_mul, ha n, hb n]

/-- The projective limit is closed under the involution when the bonds are `*`-maps. -/
theorem star_mem_projLimit {bond : ∀ n, A (n + 1) →+* A n}
    (hstar : ∀ n (x : A (n + 1)), bond n (star x) = star (bond n x)) {a : ∀ n, A n}
    (ha : a ∈ projLimit bond) : star a ∈ projLimit bond := by
  intro n
  simp only [Pi.star_apply]
  rw [hstar n, ha n]

omit [(n : ℕ) → StarRing (A n)] in
/-- The projective limit is closed in the product topology. -/
theorem isClosed_projLimit {bond : ∀ n, A (n + 1) →+* A n}
    (hcont : ∀ n, Continuous (bond n)) : IsClosed (projLimit bond) := by
  have : projLimit bond = ⋂ n : ℕ, {a : ∀ m, A m | bond n (a (n + 1)) = a n} := by
    ext a; simp [projLimit, IsCoherentTower, Set.mem_iInter]
  rw [this]
  exact isClosed_iInter fun n =>
    isClosed_eq ((hcont n).comp (continuous_apply (n + 1))) (continuous_apply n)

omit [(n : ℕ) → StarRing (A n)] in
/-- The projective limit of complete C*-algebras is complete. -/
theorem completeSpace_projLimit [∀ n, CompleteSpace (A n)] {bond : ∀ n, A (n + 1) →+* A n}
    (hcont : ∀ n, Continuous (bond n)) : CompleteSpace ↥(projLimit bond) :=
  (isClosed_projLimit hcont).completeSpace_coe

/-! ## The defining C*-seminorms -/

variable [∀ n, CStarRing (A n)]

/-- **Each defining seminorm satisfies the C*-identity.** -/
theorem norm_star_mul_self_apply (a : ∀ n, A n) (n : ℕ) :
    ‖(star a * a) n‖ = ‖a n‖ * ‖a n‖ := by
  show ‖star (a n) * a n‖ = ‖a n‖ * ‖a n‖
  exact CStarRing.norm_star_mul_self

/-! ## The bounded part -/

/-- The bounded elements of the projective limit. -/
def boundedPart (bond : ∀ n, A (n + 1) →+* A n) : Set (∀ n, A n) :=
  {a ∈ projLimit bond | BddAbove (Set.range fun n => ‖a n‖)}

/-- The supremum norm of a sequence. -/
noncomputable def boundedNorm (a : ∀ n, A n) : ℝ := ⨆ n, ‖a n‖

omit [(n : ℕ) → StarRing (A n)] [∀ (n : ℕ), CStarRing (A n)] in
theorem boundedNorm_nonneg (a : ∀ n, A n) : 0 ≤ boundedNorm a :=
  Real.iSup_nonneg fun _ => norm_nonneg _

omit [(n : ℕ) → StarRing (A n)] [∀ (n : ℕ), CStarRing (A n)] in
theorem le_boundedNorm {a : ∀ n, A n} (hb : BddAbove (Set.range fun n => ‖a n‖)) (n : ℕ) :
    ‖a n‖ ≤ boundedNorm a :=
  le_ciSup hb n

omit [(n : ℕ) → StarRing (A n)] [∀ (n : ℕ), CStarRing (A n)] in
theorem boundedNorm_le {a : ∀ n, A n} {r : ℝ} (hr : ∀ n, ‖a n‖ ≤ r) : boundedNorm a ≤ r :=
  ciSup_le hr

/-- **The supremum norm satisfies the C*-identity.**  A supremum of squares is the square of the
supremum because the norms are nonnegative. -/
theorem boundedNorm_star_mul_self {a : ∀ n, A n} (hb : BddAbove (Set.range fun n => ‖a n‖)) :
    boundedNorm (star a * a) = boundedNorm a * boundedNorm a := by
  have hbsq : BddAbove (Set.range fun n => ‖(star a * a) n‖) := by
    obtain ⟨r, hr⟩ := hb
    refine ⟨r * r, ?_⟩
    rintro _ ⟨n, rfl⟩
    show ‖(star a * a) n‖ ≤ r * r
    rw [norm_star_mul_self_apply]
    have hn : ‖a n‖ ≤ r := hr ⟨n, rfl⟩
    exact mul_le_mul hn hn (norm_nonneg _) (le_trans (norm_nonneg _) hn)
  refine le_antisymm ?_ ?_
  · refine boundedNorm_le fun n => ?_
    rw [norm_star_mul_self_apply]
    have hn := le_boundedNorm hb n
    exact mul_le_mul hn hn (norm_nonneg _) (boundedNorm_nonneg a)
  · -- `‖a n‖ ≤ √(boundedNorm (star a * a))` for every `n`
    have hsqrt : boundedNorm a ≤ Real.sqrt (boundedNorm (star a * a)) := by
      refine boundedNorm_le fun n => ?_
      have h1 : ‖a n‖ * ‖a n‖ ≤ boundedNorm (star a * a) := by
        rw [← norm_star_mul_self_apply]
        exact le_boundedNorm hbsq n
      have h2 : Real.sqrt (‖a n‖ * ‖a n‖) ≤ Real.sqrt (boundedNorm (star a * a)) :=
        Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_mul_self (norm_nonneg _)] at h2
    have hnn : 0 ≤ boundedNorm (star a * a) := boundedNorm_nonneg _
    calc boundedNorm a * boundedNorm a
        ≤ Real.sqrt (boundedNorm (star a * a)) * Real.sqrt (boundedNorm (star a * a)) :=
          mul_le_mul hsqrt hsqrt (boundedNorm_nonneg a) (Real.sqrt_nonneg _)
      _ = boundedNorm (star a * a) := Real.mul_self_sqrt hnn

omit [(n : ℕ) → StarRing (A n)] [∀ (n : ℕ), CStarRing (A n)] in
/-- The bounded part is a subring closed under the involution. -/
theorem boundedPart_subset_projLimit (bond : ∀ n, A (n + 1) →+* A n) :
    boundedPart bond ⊆ projLimit bond := fun _ h => h.1

omit [(n : ℕ) → StarRing (A n)] [∀ (n : ℕ), CStarRing (A n)] in
theorem mul_mem_boundedPart {bond : ∀ n, A (n + 1) →+* A n} {a b : ∀ n, A n}
    (ha : a ∈ boundedPart bond) (hb : b ∈ boundedPart bond) : a * b ∈ boundedPart bond := by
  refine ⟨(projSubring bond).mul_mem ha.1 hb.1, ?_⟩
  obtain ⟨r, hr⟩ := ha.2
  obtain ⟨s, hs⟩ := hb.2
  refine ⟨r * s, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hrn : ‖a n‖ ≤ r := hr ⟨n, rfl⟩
  have hsn : ‖b n‖ ≤ s := hs ⟨n, rfl⟩
  calc ‖(a * b) n‖ = ‖a n * b n‖ := rfl
    _ ≤ ‖a n‖ * ‖b n‖ := norm_mul_le _ _
    _ ≤ r * s := mul_le_mul hrn hsn (norm_nonneg _) (le_trans (norm_nonneg _) hrn)

omit [(n : ℕ) → StarRing (A n)] [∀ (n : ℕ), CStarRing (A n)] in
theorem add_mem_boundedPart {bond : ∀ n, A (n + 1) →+* A n} {a b : ∀ n, A n}
    (ha : a ∈ boundedPart bond) (hb : b ∈ boundedPart bond) : a + b ∈ boundedPart bond := by
  refine ⟨(projSubring bond).add_mem ha.1 hb.1, ?_⟩
  obtain ⟨r, hr⟩ := ha.2
  obtain ⟨s, hs⟩ := hb.2
  refine ⟨r + s, ?_⟩
  rintro _ ⟨n, rfl⟩
  calc ‖(a + b) n‖ = ‖a n + b n‖ := rfl
    _ ≤ ‖a n‖ + ‖b n‖ := norm_add_le _ _
    _ ≤ r + s := add_le_add (hr ⟨n, rfl⟩) (hs ⟨n, rfl⟩)

theorem star_mem_boundedPart {bond : ∀ n, A (n + 1) →+* A n}
    (hstar : ∀ n (x : A (n + 1)), bond n (star x) = star (bond n x)) {a : ∀ n, A n}
    (ha : a ∈ boundedPart bond) : star a ∈ boundedPart bond := by
  refine ⟨star_mem_projLimit hstar ha.1, ?_⟩
  obtain ⟨r, hr⟩ := ha.2
  refine ⟨r, ?_⟩
  rintro _ ⟨n, rfl⟩
  calc ‖(star a) n‖ = ‖star (a n)‖ := rfl
    _ = ‖a n‖ := norm_star _
    _ ≤ r := hr ⟨n, rfl⟩

end LocallyCStar

end GaloisForLFunctions.HTGeometry
