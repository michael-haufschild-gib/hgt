import GaloisForLFunctions.HTGeometry.HurwitzTriangleCoverTower
import GaloisForLFunctions.HTGeometry.VonDyckTriangleGroup

/-!
# Unramified subgroups of `Δ(2,3,7)` of unbounded index

The tower of connected unramified `(2,3,7)` covers produces, through the monodromy
representation of the triangle group, subgroups of

```text
Δ(2,3,7) = ⟨ x, y | x² = y³ = (x y)⁷ = 1 ⟩
```

of finite index exceeding any bound, each containing no conjugate of a nontrivial power of `x`,
`y` or `x y`.  For a cocompact triangle group this last property is exactly torsion-freeness,
every element of finite order being conjugate to a power of an elliptic generator; it is also
exactly what makes the associated cover unramified, and the index of the subgroup is the degree
`D = 42(2g − 2)` of that cover.

In particular `Δ(2,3,7)` is infinite.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv

/-- A subgroup of a triangle group is *elliptic-free* when it contains no conjugate of a
nontrivial power of the three elliptic generators. -/
def EllipticFree {a b c : ℕ} (H : Subgroup (VonDyck a b c)) : Prop :=
  (∀ g : VonDyck a b c, ∀ k, 0 < k → k < a → g * (vonDyckX a b c) ^ k * g⁻¹ ∉ H) ∧
  (∀ g : VonDyck a b c, ∀ k, 0 < k → k < b → g * (vonDyckY a b c) ^ k * g⁻¹ ∉ H) ∧
  (∀ g : VonDyck a b c, ∀ k, 0 < k → k < c →
    g * (vonDyckX a b c * vonDyckY a b c) ^ k * g⁻¹ ∉ H)

/-- The sheet stabiliser of a monodromy cover is elliptic-free. -/
theorem MonodromyCover.ellipticFree_sheetStabilizer {a b c : ℕ} {S : Type*} [Fintype S]
    [DecidableEq S] (F : MonodromyCover a b c S) (s₀ : S) :
    EllipticFree (F.sheetStabilizer s₀) :=
  ⟨fun g _ hk0 hka => F.sheetStabilizer_ellipticFree_X s₀ g hk0 hka,
   fun g _ hk0 hkb => F.sheetStabilizer_ellipticFree_Y s₀ g hk0 hkb,
   fun g _ hk0 hkc => F.sheetStabilizer_ellipticFree_XY s₀ g hk0 hkc⟩

/-- **Unramified subgroups of unbounded index.**  For every bound the triangle group `Δ(2,3,7)`
has an elliptic-free subgroup whose finite index exceeds the bound and equals `42(2g − 2)` for an
integer `g`. -/
theorem exists_ellipticFree_subgroup_index_gt (B : ℕ) :
    ∃ (H : Subgroup (VonDyck 2 3 7)) (g : ℤ),
      B < H.index ∧ EllipticFree H ∧ (H.index : ℤ) = 42 * (2 * g - 2) := by
  obtain ⟨n, hn⟩ := hurwitzTower_degree_unbounded B
  set C := hurwitzTower n with hC
  have hne : Nonempty C.Sheets := by
    rw [← Fintype.card_pos_iff]
    simpa [MonodromyCover.degree] using C.pos
  obtain ⟨s₀⟩ := hne
  obtain ⟨g, _, hg⟩ := C.cover.hurwitz_capacity_exact
  refine ⟨C.cover.sheetStabilizer s₀, g, ?_, C.cover.ellipticFree_sheetStabilizer s₀, ?_⟩
  · rw [C.cover.sheetStabilizer_index s₀]
    exact hn
  · rw [C.cover.sheetStabilizer_index s₀]
    exact hg

/-- **The `(2,3,7)` triangle group is infinite.**  It has subgroups of arbitrarily large finite
index. -/
theorem infinite_vonDyck_237 : Infinite (VonDyck 2 3 7) := by
  rw [← not_finite_iff_infinite]
  intro hfin
  obtain ⟨H, _, hindex, _, _⟩ := exists_ellipticFree_subgroup_index_gt (Nat.card (VonDyck 2 3 7))
  have hdvd : H.index ∣ Nat.card (VonDyck 2 3 7) := Subgroup.index_dvd_card H
  have hpos : 0 < Nat.card (VonDyck 2 3 7) := Nat.card_pos
  have : H.index ≤ Nat.card (VonDyck 2 3 7) := Nat.le_of_dvd hpos hdvd
  omega

end GaloisForLFunctions.HTGeometry
