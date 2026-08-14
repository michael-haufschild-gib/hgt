import GaloisForLFunctions.HTGeometry.OrbifoldMonodromyCover

/-!
# The von Dyck triangle group and its unramified subgroups

`VonDyck a b c` is the orientation-preserving triangle group

```text
Δ(a,b,c) = ⟨ x, y | x^a = y^b = (x y)^c = 1 ⟩,
```

realised as a presented group on two generators.

A monodromy cover of the `(a,b,c)` orbifold is exactly a transitive `Δ(a,b,c)`-action whose
elliptic generators act freely, and the point stabiliser is then a subgroup of index the degree of
the cover which contains **no conjugate of a nontrivial power of `x`, `y` or `x y`** — the
unramifiedness of the cover, and the property that makes the covering surface smooth.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv

/-- Relators of the orientation-preserving triangle group. -/
def vonDyckRelators (a b c : ℕ) : Set (FreeGroup (Fin 2)) :=
  {FreeGroup.of 0 ^ a, FreeGroup.of 1 ^ b, (FreeGroup.of 0 * FreeGroup.of 1) ^ c}

/-- The von Dyck (orientation-preserving triangle) group `Δ(a,b,c)`. -/
abbrev VonDyck (a b c : ℕ) : Type := PresentedGroup (vonDyckRelators a b c)

/-- The first elliptic generator. -/
def vonDyckX (a b c : ℕ) : VonDyck a b c := PresentedGroup.of 0

/-- The second elliptic generator. -/
def vonDyckY (a b c : ℕ) : VonDyck a b c := PresentedGroup.of 1

section Relations

variable {a b c : ℕ}

theorem vonDyckX_pow : (vonDyckX a b c) ^ a = 1 := by
  have h : ((FreeGroup.of 0 : FreeGroup (Fin 2)) ^ a) ∈ vonDyckRelators a b c := by
    simp [vonDyckRelators]
  have hmk := PresentedGroup.one_of_mem h
  rw [map_pow] at hmk
  exact hmk

theorem vonDyckY_pow : (vonDyckY a b c) ^ b = 1 := by
  have h : ((FreeGroup.of 1 : FreeGroup (Fin 2)) ^ b) ∈ vonDyckRelators a b c := by
    simp [vonDyckRelators]
  have hmk := PresentedGroup.one_of_mem h
  rw [map_pow] at hmk
  exact hmk

theorem vonDyckXY_pow : (vonDyckX a b c * vonDyckY a b c) ^ c = 1 := by
  have h : (((FreeGroup.of 0 : FreeGroup (Fin 2)) * FreeGroup.of 1) ^ c)
      ∈ vonDyckRelators a b c := by
    simp [vonDyckRelators]
  have hmk := PresentedGroup.one_of_mem h
  rw [map_pow, map_mul] at hmk
  exact hmk

end Relations

section Monodromy

variable {a b c : ℕ} {S : Type*} [Fintype S] [DecidableEq S]

/-- The monodromy representation of the triangle group attached to a cover. -/
def MonodromyCover.toVonDyckHom (F : MonodromyCover a b c S) : VonDyck a b c →* Perm S :=
  PresentedGroup.toGroup (f := ![F.X, F.Y]) (by
    intro r hr
    rcases hr with h | h | h
    · rw [h]
      simp only [map_pow, FreeGroup.lift_apply_of]
      simpa using F.freeX.pow_eq_one
    · rw [h]
      simp only [map_pow, FreeGroup.lift_apply_of]
      simpa using F.freeY.pow_eq_one
    · rw [h]
      simp only [map_pow, map_mul, FreeGroup.lift_apply_of]
      simpa using F.freeZ.pow_eq_one)

@[simp] theorem MonodromyCover.toVonDyckHom_X (F : MonodromyCover a b c S) :
    F.toVonDyckHom (vonDyckX a b c) = F.X :=
  (PresentedGroup.toGroup.of (f := ![F.X, F.Y]) (rels := vonDyckRelators a b c) (x := 0)
    _).trans (by simp)

@[simp] theorem MonodromyCover.toVonDyckHom_Y (F : MonodromyCover a b c S) :
    F.toVonDyckHom (vonDyckY a b c) = F.Y :=
  (PresentedGroup.toGroup.of (f := ![F.X, F.Y]) (rels := vonDyckRelators a b c) (x := 1)
    _).trans (by simp)

/-- The monodromy representation hits the whole monodromy group. -/
theorem MonodromyCover.closure_le_range (F : MonodromyCover a b c S) :
    Subgroup.closure ({F.X, F.Y} : Set (Perm S)) ≤ F.toVonDyckHom.range := by
  rw [Subgroup.closure_le]
  rintro σ (rfl | hσ)
  · exact ⟨vonDyckX a b c, F.toVonDyckHom_X⟩
  · simp only [Set.mem_singleton_iff] at hσ
    exact ⟨vonDyckY a b c, by rw [hσ]; exact F.toVonDyckHom_Y⟩

/-- **The unramified subgroup of a cover**: the stabiliser of a sheet inside the triangle
group. -/
def MonodromyCover.sheetStabilizer (F : MonodromyCover a b c S) (s₀ : S) :
    Subgroup (VonDyck a b c) :=
  Subgroup.comap F.toVonDyckHom (MulAction.stabilizer (Perm S) s₀)

theorem MonodromyCover.mem_sheetStabilizer {F : MonodromyCover a b c S} {s₀ : S}
    {g : VonDyck a b c} : g ∈ F.sheetStabilizer s₀ ↔ F.toVonDyckHom g s₀ = s₀ := Iff.rfl

/-- **The index is the degree.**  Transitivity of the cover makes the sheet stabiliser a subgroup
of index exactly the number of sheets. -/
theorem MonodromyCover.sheetStabilizer_index (F : MonodromyCover a b c S) (s₀ : S) :
    (F.sheetStabilizer s₀).index = F.degree := by
  letI : MulAction (VonDyck a b c) S := MulAction.compHom S F.toVonDyckHom
  have hstab : F.sheetStabilizer s₀ = MulAction.stabilizer (VonDyck a b c) s₀ := rfl
  have horb : MulAction.orbit (VonDyck a b c) s₀ = Set.univ := by
    ext s
    simp only [Set.mem_univ, iff_true]
    obtain ⟨σ, hσ, hσs⟩ := F.transitive s₀ s
    obtain ⟨g, hg⟩ := F.closure_le_range hσ
    refine ⟨g, ?_⟩
    show F.toVonDyckHom g s₀ = s
    rw [hg]
    exact hσs
  rw [hstab, MulAction.index_stabilizer, horb, Set.ncard_univ, Nat.card_eq_fintype_card]
  rfl

/-- **Unramifiedness.**  No conjugate of a nontrivial power of the first elliptic generator lies
in the sheet stabiliser. -/
theorem MonodromyCover.sheetStabilizer_ellipticFree_X (F : MonodromyCover a b c S) (s₀ : S)
    (g : VonDyck a b c) {k : ℕ} (hk0 : 0 < k) (hka : k < a) :
    g * (vonDyckX a b c) ^ k * g⁻¹ ∉ F.sheetStabilizer s₀ := by
  intro hmem
  rw [MonodromyCover.mem_sheetStabilizer] at hmem
  simp only [map_mul, map_pow, map_inv, MonodromyCover.toVonDyckHom_X] at hmem
  have hfix : (F.X ^ k) ((F.toVonDyckHom g)⁻¹ s₀) = (F.toVonDyckHom g)⁻¹ s₀ := by
    have := congrArg (fun t => (F.toVonDyckHom g)⁻¹ t) hmem
    simpa [Equiv.Perm.mul_apply] using this
  exact F.freeX.free k hk0 hka _ hfix

/-- No conjugate of a nontrivial power of the second elliptic generator lies in the sheet
stabiliser. -/
theorem MonodromyCover.sheetStabilizer_ellipticFree_Y (F : MonodromyCover a b c S) (s₀ : S)
    (g : VonDyck a b c) {k : ℕ} (hk0 : 0 < k) (hkb : k < b) :
    g * (vonDyckY a b c) ^ k * g⁻¹ ∉ F.sheetStabilizer s₀ := by
  intro hmem
  rw [MonodromyCover.mem_sheetStabilizer] at hmem
  simp only [map_mul, map_pow, map_inv, MonodromyCover.toVonDyckHom_Y] at hmem
  have hfix : (F.Y ^ k) ((F.toVonDyckHom g)⁻¹ s₀) = (F.toVonDyckHom g)⁻¹ s₀ := by
    have := congrArg (fun t => (F.toVonDyckHom g)⁻¹ t) hmem
    simpa [Equiv.Perm.mul_apply] using this
  exact F.freeY.free k hk0 hkb _ hfix

/-- No conjugate of a nontrivial power of the third elliptic generator lies in the sheet
stabiliser. -/
theorem MonodromyCover.sheetStabilizer_ellipticFree_XY (F : MonodromyCover a b c S) (s₀ : S)
    (g : VonDyck a b c) {k : ℕ} (hk0 : 0 < k) (hkc : k < c) :
    g * (vonDyckX a b c * vonDyckY a b c) ^ k * g⁻¹ ∉ F.sheetStabilizer s₀ := by
  intro hmem
  rw [MonodromyCover.mem_sheetStabilizer] at hmem
  simp only [map_mul, map_pow, map_inv, MonodromyCover.toVonDyckHom_X,
    MonodromyCover.toVonDyckHom_Y] at hmem
  have hfix : ((F.X * F.Y) ^ k) ((F.toVonDyckHom g)⁻¹ s₀) = (F.toVonDyckHom g)⁻¹ s₀ := by
    have := congrArg (fun t => (F.toVonDyckHom g)⁻¹ t) hmem
    simpa [Equiv.Perm.mul_apply] using this
  exact F.freeZ.free k hk0 hkc _ hfix

end Monodromy

end GaloisForLFunctions.HTGeometry
