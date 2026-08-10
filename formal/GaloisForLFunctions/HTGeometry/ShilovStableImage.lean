import GaloisForLFunctions.HTGeometry.ShilovBoundaryMigrationDefect

/-!
# The stable image filtration of a tower

Derived vanishing for a countable tower is decided by how far the late stages reach into an early
one.  This module builds that filtration.

The composite transition `downTo bond h : A m →ₗ A n` for `n ≤ m` is defined by `Nat.leRec`, which
keeps every stage index literal: no index arithmetic and no transport appears, and both structural
identities — peeling a bond at the top (`downTo_succ`) and at the bottom (`downTo_shift`) — are
available.  `reach bond n m h` is its range, the part of stage `n` seen from stage `m`.  These
decrease as `m` grows, so every stage carries a canonical antitone filtration, and
`HasStableImages` is the Mittag-Leffler condition that each chain is eventually constant.

The two extreme results of `ShilovBoundaryMigrationDefect.lean` sit at the two ends of this one
filtration: onto bonds keep every reach at the top, zero bonds collapse every reach beyond the
first, and both are Mittag-Leffler — which is why both have vanishing `lim¹` although the towers
look unrelated.
-/

namespace GaloisForLFunctions.HTGeometry

namespace BoundaryMigration

universe u v

variable {𝕜 : Type u} [Field 𝕜]
variable {A : ℕ → Type v} [∀ n, AddCommGroup (A n)] [∀ n, Module 𝕜 (A n)]

/-! ## Composite transitions -/

/-- The composite transition from stage `m` down to stage `n`. -/
def downTo (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) {n : ℕ} :
    ∀ {m : ℕ}, n ≤ m → (A m →ₗ[𝕜] A n) :=
  Nat.leRec LinearMap.id fun {k} _ ih => ih.comp (bond k)

@[simp]
theorem downTo_self (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (n : ℕ) :
    downTo bond (le_refl n) = LinearMap.id :=
  Nat.leRec_self _ _

/-- Peeling a bond at the top. -/
theorem downTo_succ (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) {n m : ℕ} (h : n ≤ m)
    (h' : n ≤ m + 1) : downTo bond h' = (downTo bond h).comp (bond m) :=
  Nat.leRec_succ _ _ h

/-- Peeling a bond at the bottom. -/
theorem downTo_shift (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) {n m : ℕ} (h : n + 1 ≤ m) :
    downTo bond (le_trans (Nat.le_succ n) h) = (bond n).comp (downTo bond h) := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [downTo_succ bond (le_refl n), downTo_self, downTo_self]
    ext x
    simp
  | succ m hm ih =>
    rw [downTo_succ bond (le_trans (Nat.le_succ n) hm), ih, downTo_succ bond hm]
    rfl

/-! ## The reach filtration -/

/-- The part of stage `n` seen from stage `m`. -/
def reach (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (n m : ℕ) (h : n ≤ m) : Submodule 𝕜 (A n) :=
  LinearMap.range (downTo bond h)

@[simp]
theorem reach_self (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (n : ℕ) :
    reach bond n n (le_refl n) = ⊤ := by
  rw [reach, downTo_self, LinearMap.range_eq_top]
  exact Function.surjective_id

theorem reach_succ_le (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) {n m : ℕ} (h : n ≤ m)
    (h' : n ≤ m + 1) : reach bond n (m + 1) h' ≤ reach bond n m h := by
  rw [reach, reach, downTo_succ bond h h']
  rintro x ⟨y, rfl⟩
  exact ⟨bond m y, rfl⟩

/-- The reach decreases as the source stage rises. -/
theorem reach_antitone (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) {n m₁ m₂ : ℕ} (h₁ : n ≤ m₁)
    (h₁₂ : m₁ ≤ m₂) (h₂ : n ≤ m₂) : reach bond n m₂ h₂ ≤ reach bond n m₁ h₁ := by
  induction m₂, h₁₂ using Nat.le_induction with
  | base => exact le_of_eq (by congr)
  | succ m hm ih =>
    exact le_trans (reach_succ_le bond (le_trans h₁ hm) h₂) (ih (le_trans h₁ hm))

/-- **Peeling at the bottom, on ranges.**  The reach of stage `m` into stage `n` is the image
under the bond of its reach into stage `n + 1`. -/
theorem map_bond_reach (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) {n m : ℕ} (h : n + 1 ≤ m) :
    Submodule.map (bond n) (reach bond (n + 1) m h)
      = reach bond n m (le_trans (Nat.le_succ n) h) := by
  rw [reach, reach, ← LinearMap.range_comp, ← downTo_shift bond h]

/-- **The Mittag-Leffler condition.**  Every stage's chain of reaches is eventually constant. -/
def HasStableImages (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) : Prop :=
  ∀ n : ℕ, ∃ K : ℕ, ∃ hK : n ≤ K, ∀ m (h : K ≤ m),
    reach bond n m (le_trans hK h) = reach bond n K hK

/-! ## The two extremes -/

theorem reach_eq_top_of_surjective (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (hsurj : ∀ n, Function.Surjective (bond n)) {n m : ℕ} (h : n ≤ m) :
    reach bond n m h = ⊤ := by
  induction m, h using Nat.le_induction with
  | base => exact reach_self bond n
  | succ m hm ih =>
    rw [reach, downTo_succ bond hm, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (hsurj m), Submodule.map_top]
    exact ih

theorem reach_eq_bot_of_zero_bond (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (hzero : ∀ n, bond n = 0) {n m : ℕ} (h : n + 1 ≤ m) :
    reach bond n m (le_trans (Nat.le_succ n) h) = ⊥ := by
  have hbase : reach bond n (n + 1) (Nat.le_succ n) = ⊥ := by
    rw [reach, downTo_succ bond (le_refl n) (Nat.le_succ n), LinearMap.range_comp,
      LinearMap.range_eq_bot.mpr (hzero n), Submodule.map_bot]
  have hle := reach_antitone bond (Nat.le_succ n) h (le_trans (Nat.le_succ n) h)
  rw [hbase] at hle
  exact le_antisymm hle bot_le

/-- Onto bonds are Mittag-Leffler. -/
theorem hasStableImages_of_surjective (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (hsurj : ∀ n, Function.Surjective (bond n)) : HasStableImages bond := fun n =>
  ⟨n, le_refl n, fun m h => by
    rw [reach_eq_top_of_surjective bond hsurj, reach_eq_top_of_surjective bond hsurj]⟩

/-- Zero bonds are Mittag-Leffler. -/
theorem hasStableImages_of_zero_bond (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (hzero : ∀ n, bond n = 0) : HasStableImages bond := fun n =>
  ⟨n + 1, Nat.le_succ n, fun m h => by
    rw [reach_eq_bot_of_zero_bond bond hzero h]
    exact (reach_eq_bot_of_zero_bond bond hzero (le_refl (n + 1))).symm⟩

end BoundaryMigration

end GaloisForLFunctions.HTGeometry
