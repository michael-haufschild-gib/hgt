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

/-! ## Eventually vanishing transitions -/

open scoped Classical in
/-- The composite transition, extended by zero below the diagonal. -/
noncomputable def trans (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (n j : ℕ) : A j →ₗ[𝕜] A n :=
  if h : n ≤ j then downTo bond h else 0

theorem trans_of_le (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) {n j : ℕ} (h : n ≤ j) :
    trans bond n j = downTo bond h := by
  rw [trans, dif_pos h]

@[simp]
theorem trans_self (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (n : ℕ) :
    trans bond n n = LinearMap.id := by
  rw [trans_of_le bond (le_refl n), downTo_self]

/-- Peeling a bond at the bottom, for the total transition. -/
theorem trans_shift (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) {n j : ℕ} (h : n + 1 ≤ j) :
    trans bond n j = (bond n).comp (trans bond (n + 1) j) := by
  rw [trans_of_le bond (le_trans (Nat.le_succ n) h), trans_of_le bond h, downTo_shift bond h]

/-- The truncated correction sum. -/
noncomputable def partialSum (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (b : ∀ n, A n) (n N : ℕ) : A n :=
  ∑ j ∈ Finset.Ico n N, trans bond n j (b j)

/-- Extending the truncation beyond the vanishing threshold changes nothing. -/
theorem partialSum_eq_of_le (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (b : ∀ n, A n) {K : ℕ → ℕ}
    (hzero : ∀ n j, K n ≤ j → trans bond n j = 0) {n N N' : ℕ} (hnN : n ≤ N) (hKN : K n ≤ N)
    (hNN' : N ≤ N') : partialSum bond b n N = partialSum bond b n N' := by
  have hsplit := Finset.sum_Ico_consecutive (fun j => trans bond n j (b j)) hnN hNN'
  have hvanish : ∑ j ∈ Finset.Ico N N', trans bond n j (b j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hKj : K n ≤ j := le_trans hKN (Finset.mem_Ico.mp hj).1
    rw [hzero n j hKj]
    rfl
  rw [partialSum, partialSum, ← hsplit, hvanish, add_zero]

/-- The truncated sums telescope. -/
theorem partialSum_sub (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (b : ∀ n, A n) {n N : ℕ}
    (hnN : n < N) :
    partialSum bond b n N - bond n (partialSum bond b (n + 1) N) = b n := by
  have hbot := Finset.sum_eq_sum_Ico_succ_bot hnN fun j => trans bond n j (b j)
  have hmap : bond n (partialSum bond b (n + 1) N)
      = ∑ j ∈ Finset.Ico (n + 1) N, trans bond n j (b j) := by
    rw [partialSum, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [trans_shift bond (Finset.mem_Ico.mp hj).1]
    rfl
  rw [partialSum, hbot, hmap, trans_self]
  simp

/-- **Eventually vanishing transitions force derived vanishing.**  If from every stage the
composite into a fixed earlier stage is eventually zero, then the Roos difference is onto: the
correction sum is finite, and it telescopes. -/
theorem inverseDifference_surjective_of_eventually_zero (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (K : ℕ → ℕ) (hK : ∀ n, n < K n) (hzero : ∀ n j, K n ≤ j → trans bond n j = 0) :
    Function.Surjective (inverseDifference A bond) := by
  intro b
  refine ⟨fun n => partialSum bond b n (K n), ?_⟩
  funext n
  show partialSum bond b n (K n) - bond n (partialSum bond b (n + 1) (K (n + 1))) = b n
  set N : ℕ := max (K n) (K (n + 1)) with hN
  have h1 : partialSum bond b n (K n) = partialSum bond b n N :=
    partialSum_eq_of_le bond b hzero (le_of_lt (hK n)) (le_refl _) (le_max_left _ _)
  have h2 : partialSum bond b (n + 1) (K (n + 1)) = partialSum bond b (n + 1) N :=
    partialSum_eq_of_le bond b hzero (le_of_lt (hK (n + 1))) (le_refl _) (le_max_right _ _)
  rw [h1, h2]
  exact partialSum_sub bond b (lt_of_lt_of_le (hK n) (le_max_left _ _))

/-- The same statement for the derived limit itself. -/
theorem derivedLimitOne_subsingleton_of_eventually_zero (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (K : ℕ → ℕ) (hK : ∀ n, n < K n) (hzero : ∀ n j, K n ≤ j → trans bond n j = 0) :
    Subsingleton (DerivedLimitOne A bond) := by
  change Subsingleton ((∀ n, A n) ⧸ LinearMap.range (inverseDifference A bond))
  rw [Submodule.Quotient.subsingleton_iff]
  exact LinearMap.range_eq_top.mpr
    (inverseDifference_surjective_of_eventually_zero bond K hK hzero)

/-- The zero-bond tower of `ShilovBoundaryMigrationDefect.lean` is the extreme case: its
transitions vanish after one step. -/
theorem derivedLimitOne_subsingleton_of_zero_bond_via_transitions
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (hzero : ∀ n, bond n = 0) :
    Subsingleton (DerivedLimitOne A bond) :=
  derivedLimitOne_subsingleton_of_eventually_zero bond (fun n => n + 1)
    (fun n => Nat.lt_succ_self n) fun n j hj => by
      rw [trans_shift bond hj, hzero n, LinearMap.zero_comp]

/-! ## Mittag-Leffler vanishing -/

theorem trans_apply_mem_reach (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) {n j : ℕ} (h : n ≤ j) (x : A j) :
    trans bond n j x ∈ reach bond n j h := by
  rw [trans_of_le bond h, reach]
  exact ⟨x, rfl⟩

/-- The stable images form a sub-tower on which the bonds are onto. -/
theorem map_bond_stable (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) {K : ℕ → ℕ} {hK : ∀ n, n ≤ K n}
    (hstab : ∀ n m (h : K n ≤ m), reach bond n m (le_trans (hK n) h) = reach bond n (K n) (hK n))
    (n : ℕ) :
    Submodule.map (bond n) (reach bond (n + 1) (K (n + 1)) (hK (n + 1)))
      = reach bond n (K n) (hK n) := by
  have hMn : K n ≤ max (K n) (K (n + 1)) := le_max_left _ _
  have hMn1 : K (n + 1) ≤ max (K n) (K (n + 1)) := le_max_right _ _
  have h1 : reach bond (n + 1) (K (n + 1)) (hK (n + 1))
      = reach bond (n + 1) (max (K n) (K (n + 1))) (le_trans (hK (n + 1)) hMn1) :=
    (hstab (n + 1) _ hMn1).symm
  have h2 := map_bond_reach bond (le_trans (hK (n + 1)) hMn1)
  rw [h1, h2]
  exact hstab n _ hMn

/-- **Mittag-Leffler vanishing.**  A tower whose reaches stabilise has surjective Roos difference.
The correction sum solves the equation up to the stable part, and the stable sub-tower has onto
bonds, so the residue is corrected there. -/
theorem inverseDifference_surjective_of_hasStableImages (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (hst : HasStableImages bond) : Function.Surjective (inverseDifference A bond) := by
  classical
  choose K hK hstab using hst
  set B : ∀ n, Submodule 𝕜 (A n) := fun n => reach bond n (K n) (hK n) with hB
  have hsub : ∀ n (x : A (n + 1)), x ∈ B (n + 1) → bond n x ∈ B n := by
    intro n x hx
    simp only [hB] at hx ⊢
    rw [← map_bond_stable bond (hK := hK) hstab n]
    exact Submodule.mem_map_of_mem hx
  have hbondsurj : ∀ n, Function.Surjective (restrictedBond A bond B hsub n) := by
    intro n y
    have hy : (y : A n) ∈ Submodule.map (bond n) (B (n + 1)) := by
      simp only [hB]
      rw [map_bond_stable bond (hK := hK) hstab n]
      exact y.2
    obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨w, hw⟩, Subtype.ext hwy⟩
  intro b
  -- the correction sum, and its defect from a common truncation
  have hdiff : ∀ n M, K n ≤ M →
      partialSum bond b n M - partialSum bond b n (K n) ∈ B n := by
    intro n M hM
    have hsplit := Finset.sum_Ico_consecutive (fun j => trans bond n j (b j)) (hK n) hM
    have hmem : ∑ j ∈ Finset.Ico (K n) M, trans bond n j (b j) ∈ B n := by
      refine Submodule.sum_mem _ fun j hj => ?_
      have hKj : K n ≤ j := (Finset.mem_Ico.mp hj).1
      have hnj : n ≤ j := le_trans (hK n) hKj
      have := trans_apply_mem_reach bond hnj (b j)
      rwa [hstab n j hKj] at this
    have : partialSum bond b n M
        = partialSum bond b n (K n) + ∑ j ∈ Finset.Ico (K n) M, trans bond n j (b j) := by
      rw [partialSum, partialSum, ← hsplit]
    rw [this, add_sub_cancel_left]
    exact hmem
  set y : ∀ n, A n := fun n => partialSum bond b n (K n) with hy
  have hc : ∀ n, y n - bond n (y (n + 1)) - b n ∈ B n := by
    intro n
    set M : ℕ := max (K n) (K (n + 1)) with hM
    have hnM : n < M := lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self n) (hK (n + 1)))
      (le_max_right _ _)
    have htel := partialSum_sub bond b hnM
    have h1 : partialSum bond b n M - y n ∈ B n := hdiff n M (le_max_left _ _)
    have h2 : partialSum bond b (n + 1) M - y (n + 1) ∈ B (n + 1) :=
      hdiff (n + 1) M (le_max_right _ _)
    have h3 : bond n (partialSum bond b (n + 1) M - y (n + 1)) ∈ B n := hsub n _ h2
    rw [map_sub] at h3
    have hkey : y n - bond n (y (n + 1)) - b n
        = -(partialSum bond b n M - y n)
          + (bond n (partialSum bond b (n + 1) M) - bond n (y (n + 1))) := by
      rw [← htel]
      abel
    rw [hkey]
    exact Submodule.add_mem _ (Submodule.neg_mem _ h1) h3
  -- correct inside the stable sub-tower
  obtain ⟨z, hz⟩ := inverseDifference_surjective (fun n => ↥(B n))
    (restrictedBond A bond B hsub) hbondsurj
    (fun n => ⟨-(y n - bond n (y (n + 1)) - b n), Submodule.neg_mem _ (hc n)⟩)
  refine ⟨fun n => y n + (z n : A n), ?_⟩
  funext n
  have hzn := congrFun hz n
  have hzn' : (z n : A n) - bond n ((z (n + 1) : A (n + 1)))
      = -(y n - bond n (y (n + 1)) - b n) := congrArg Subtype.val hzn
  show y n + (z n : A n) - bond n (y (n + 1) + (z (n + 1) : A (n + 1))) = b n
  rw [map_add, show y n + (z n : A n) - (bond n (y (n + 1)) + bond n (z (n + 1) : A (n + 1)))
      = (y n - bond n (y (n + 1))) + ((z n : A n) - bond n (z (n + 1) : A (n + 1))) from by abel,
    hzn']
  abel

/-- **Mittag-Leffler vanishing, for the derived limit.** -/
theorem derivedLimitOne_subsingleton_of_hasStableImages (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (hst : HasStableImages bond) : Subsingleton (DerivedLimitOne A bond) := by
  change Subsingleton ((∀ n, A n) ⧸ LinearMap.range (inverseDifference A bond))
  rw [Submodule.Quotient.subsingleton_iff]
  exact LinearMap.range_eq_top.mpr (inverseDifference_surjective_of_hasStableImages bond hst)

/-- The onto-bond vanishing theorem is the top of the filtration. -/
theorem derivedLimitOne_subsingleton_of_surjective_via_stable
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (hsurj : ∀ n, Function.Surjective (bond n)) :
    Subsingleton (DerivedLimitOne A bond) :=
  derivedLimitOne_subsingleton_of_hasStableImages bond (hasStableImages_of_surjective bond hsurj)

/-- The zero-bond vanishing theorem is the bottom of the filtration. -/
theorem derivedLimitOne_subsingleton_of_zero_bond_via_stable
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (hzero : ∀ n, bond n = 0) :
    Subsingleton (DerivedLimitOne A bond) :=
  derivedLimitOne_subsingleton_of_hasStableImages bond (hasStableImages_of_zero_bond bond hzero)

end BoundaryMigration

end GaloisForLFunctions.HTGeometry
