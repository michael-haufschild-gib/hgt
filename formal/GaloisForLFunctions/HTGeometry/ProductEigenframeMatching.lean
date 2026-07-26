import GaloisForLFunctions.HTGeometry.ProductGridBlockPattern

/-!
# Matching two product eigenframes

A difference-form family takes the same value at `(u, v)` and at `(u + t, v + t)`, so if a product
grid diagonalises it at every pair of parameters, then for one fixed value of the difference a whole
one-parameter family of product grids diagonalises **one** operator.

When the spectrum is simple each eigenline is unique, so the two grids differ by a correspondence of
grid points, and that correspondence factors through the two index sets separately: a nonzero vector
is proportional to at most one member of a linearly independent family, so the left index of the
image depends only on the left index of the source.

No analyticity is used.  The correspondence is not shown to be the identity — it may permute the
lines — but the *pair* of local factor lines is the same on both sides, which is all a diagonalising
product frame needs, since relabelling basis vectors preserves diagonality.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {K : Type*} [Field K]

/-! ### Difference form -/

/-- A difference-form family is unchanged by translating both parameters. -/
theorem differenceForm_translation_invariant {G M : Type*} [AddGroup G] (T : G → M)
    (u v t : G) : T ((u + t) - (v + t)) = T (u - v) := by
  rw [add_sub_add_right_eq_sub]

/-! ### A vector meets a linearly independent family in at most one index -/

variable {V ι' : Type*} [AddCommGroup V] [Module K V]

/-- A nonzero vector is proportional to at most one member of a linearly independent family. -/
theorem eq_of_eq_smul_of_linearIndependent [DecidableEq ι'] {w : ι' → V}
    (hw : LinearIndependent K w) {v : V} (hv : v ≠ 0) {k l : ι'} {c d : K}
    (hk : v = c • w k) (hl : v = d • w l) : k = l := by
  by_contra hkl
  have hsum : ∑ i ∈ ({k, l} : Finset ι'),
      (fun i => if i = k then c else -d) i • w i = 0 := by
    rw [Finset.sum_pair hkl]
    show (if k = k then c else -d) • w k + (if l = k then c else -d) • w l = 0
    have h1 : (if k = k then c else -d) = c := if_pos rfl
    have h2 : (if l = k then c else -d) = -d := if_neg fun h => hkl h.symm
    rw [h1, h2, neg_smul, ← hk, ← hl]
    simp
  have hc := linearIndependent_iff'.1 hw {k, l} (fun i => if i = k then c else -d) hsum k
    (Finset.mem_insert_self k {l})
  have hc0 : c = 0 := by simpa using hc
  rw [hc0, zero_smul] at hk
  exact hv hk

/-! ### The index correspondence factors -/

variable {I J ι : Type*}

/-- **The left index of the correspondence depends only on the left index.**  Two grid points of the
source frame with the same left index are matched to primed frame vectors with the same left index,
because both left factors are proportional to the same nonzero vector. -/
theorem productEigenframe_left_index_determined [DecidableEq ι] [DecidableEq I]
    (e : Basis ι K (Matrix I J K)) {T : Module.End K (Matrix I J K)} {μ : ι → K}
    (hT : ∀ i, T (e i) = μ i • e i) (hμ : Function.Injective μ)
    {a a' : I → (I → K)} {b b' : J → (J → K)}
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) (ha' : ∀ i, a' i ≠ 0) (hb' : ∀ j, b' j ≠ 0)
    (hindep : LinearIndependent K a')
    {i₀ : I} {j₁ j₂ : J} {k₁ k₂ : I} {l₁ l₂ : J} {n₁ n₂ : ι}
    (hp₁ : T (criticalHorizonSegreTensor (a i₀) (b j₁)) =
      μ n₁ • criticalHorizonSegreTensor (a i₀) (b j₁))
    (hq₁ : T (criticalHorizonSegreTensor (a' k₁) (b' l₁)) =
      μ n₁ • criticalHorizonSegreTensor (a' k₁) (b' l₁))
    (hp₂ : T (criticalHorizonSegreTensor (a i₀) (b j₂)) =
      μ n₂ • criticalHorizonSegreTensor (a i₀) (b j₂))
    (hq₂ : T (criticalHorizonSegreTensor (a' k₂) (b' l₂)) =
      μ n₂ • criticalHorizonSegreTensor (a' k₂) (b' l₂)) :
    k₁ = k₂ := by
  obtain ⟨⟨α₁, _, hα₁⟩, _⟩ :=
    decomposableEigenvector_factors_proportional e hT hμ (ha i₀) (hb j₁) (ha' k₁) (hb' l₁) hp₁ hq₁
  obtain ⟨⟨α₂, _, hα₂⟩, _⟩ :=
    decomposableEigenvector_factors_proportional e hT hμ (ha i₀) (hb j₂) (ha' k₂) (hb' l₂) hp₂ hq₂
  exact eq_of_eq_smul_of_linearIndependent hindep (ha i₀) hα₁ hα₂

/-- **The right index of the correspondence depends only on the right index.** -/
theorem productEigenframe_right_index_determined [DecidableEq ι] [DecidableEq J]
    (e : Basis ι K (Matrix I J K)) {T : Module.End K (Matrix I J K)} {μ : ι → K}
    (hT : ∀ i, T (e i) = μ i • e i) (hμ : Function.Injective μ)
    {a a' : I → (I → K)} {b b' : J → (J → K)}
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) (ha' : ∀ i, a' i ≠ 0) (hb' : ∀ j, b' j ≠ 0)
    (hindep : LinearIndependent K b')
    {j₀ : J} {i₁ i₂ : I} {k₁ k₂ : I} {l₁ l₂ : J} {n₁ n₂ : ι}
    (hp₁ : T (criticalHorizonSegreTensor (a i₁) (b j₀)) =
      μ n₁ • criticalHorizonSegreTensor (a i₁) (b j₀))
    (hq₁ : T (criticalHorizonSegreTensor (a' k₁) (b' l₁)) =
      μ n₁ • criticalHorizonSegreTensor (a' k₁) (b' l₁))
    (hp₂ : T (criticalHorizonSegreTensor (a i₂) (b j₀)) =
      μ n₂ • criticalHorizonSegreTensor (a i₂) (b j₀))
    (hq₂ : T (criticalHorizonSegreTensor (a' k₂) (b' l₂)) =
      μ n₂ • criticalHorizonSegreTensor (a' k₂) (b' l₂)) :
    l₁ = l₂ := by
  obtain ⟨_, ⟨β₁, _, hβ₁⟩⟩ :=
    decomposableEigenvector_factors_proportional e hT hμ (ha i₁) (hb j₀) (ha' k₁) (hb' l₁) hp₁ hq₁
  obtain ⟨_, ⟨β₂, _, hβ₂⟩⟩ :=
    decomposableEigenvector_factors_proportional e hT hμ (ha i₂) (hb j₀) (ha' k₂) (hb' l₂) hp₂ hq₂
  exact eq_of_eq_smul_of_linearIndependent hindep (hb j₀) hβ₁ hβ₂

/-! ### The degenerate patterns

Patterns `3+1` and `2+1+1` of the multiplicity classification contain an eigenvalue of multiplicity
one.  Only that eigenvalue has to be unrepeated for its eigenline to be canonical, so the same index
determination applies with the rest of the spectrum degenerate. -/

/-- **Left index determination at an unrepeated eigenvalue.**  Only the two eigenvalues actually
used are required to be unrepeated; the remaining spectrum may be degenerate. -/
theorem productEigenframe_left_index_determined_of_isolated [DecidableEq ι] [DecidableEq I]
    (e : Basis ι K (Matrix I J K)) {T : Module.End K (Matrix I J K)} {μ : ι → K}
    (hT : ∀ i, T (e i) = μ i • e i)
    {a a' : I → (I → K)} {b b' : J → (J → K)}
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) (ha' : ∀ i, a' i ≠ 0) (hb' : ∀ j, b' j ≠ 0)
    (hindep : LinearIndependent K a')
    {i₀ : I} {j₁ j₂ : J} {k₁ k₂ : I} {l₁ l₂ : J} {n₁ n₂ : ι}
    (hμ₁ : ∀ i, i ≠ n₁ → μ i ≠ μ n₁) (hμ₂ : ∀ i, i ≠ n₂ → μ i ≠ μ n₂)
    (hp₁ : T (criticalHorizonSegreTensor (a i₀) (b j₁)) =
      μ n₁ • criticalHorizonSegreTensor (a i₀) (b j₁))
    (hq₁ : T (criticalHorizonSegreTensor (a' k₁) (b' l₁)) =
      μ n₁ • criticalHorizonSegreTensor (a' k₁) (b' l₁))
    (hp₂ : T (criticalHorizonSegreTensor (a i₀) (b j₂)) =
      μ n₂ • criticalHorizonSegreTensor (a i₀) (b j₂))
    (hq₂ : T (criticalHorizonSegreTensor (a' k₂) (b' l₂)) =
      μ n₂ • criticalHorizonSegreTensor (a' k₂) (b' l₂)) :
    k₁ = k₂ := by
  obtain ⟨⟨α₁, _, hα₁⟩, _⟩ :=
    decomposableEigenvector_factors_proportional_of_isolated e hT hμ₁
      (ha i₀) (hb j₁) (ha' k₁) (hb' l₁) hp₁ hq₁
  obtain ⟨⟨α₂, _, hα₂⟩, _⟩ :=
    decomposableEigenvector_factors_proportional_of_isolated e hT hμ₂
      (ha i₀) (hb j₂) (ha' k₂) (hb' l₂) hp₂ hq₂
  exact eq_of_eq_smul_of_linearIndependent hindep (ha i₀) hα₁ hα₂

/-- **Right index determination at an unrepeated eigenvalue.** -/
theorem productEigenframe_right_index_determined_of_isolated [DecidableEq ι] [DecidableEq J]
    (e : Basis ι K (Matrix I J K)) {T : Module.End K (Matrix I J K)} {μ : ι → K}
    (hT : ∀ i, T (e i) = μ i • e i)
    {a a' : I → (I → K)} {b b' : J → (J → K)}
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) (ha' : ∀ i, a' i ≠ 0) (hb' : ∀ j, b' j ≠ 0)
    (hindep : LinearIndependent K b')
    {j₀ : J} {i₁ i₂ : I} {k₁ k₂ : I} {l₁ l₂ : J} {n₁ n₂ : ι}
    (hμ₁ : ∀ i, i ≠ n₁ → μ i ≠ μ n₁) (hμ₂ : ∀ i, i ≠ n₂ → μ i ≠ μ n₂)
    (hp₁ : T (criticalHorizonSegreTensor (a i₁) (b j₀)) =
      μ n₁ • criticalHorizonSegreTensor (a i₁) (b j₀))
    (hq₁ : T (criticalHorizonSegreTensor (a' k₁) (b' l₁)) =
      μ n₁ • criticalHorizonSegreTensor (a' k₁) (b' l₁))
    (hp₂ : T (criticalHorizonSegreTensor (a i₂) (b j₀)) =
      μ n₂ • criticalHorizonSegreTensor (a i₂) (b j₀))
    (hq₂ : T (criticalHorizonSegreTensor (a' k₂) (b' l₂)) =
      μ n₂ • criticalHorizonSegreTensor (a' k₂) (b' l₂)) :
    l₁ = l₂ := by
  obtain ⟨_, ⟨β₁, _, hβ₁⟩⟩ :=
    decomposableEigenvector_factors_proportional_of_isolated e hT hμ₁
      (ha i₁) (hb j₀) (ha' k₁) (hb' l₁) hp₁ hq₁
  obtain ⟨_, ⟨β₂, _, hβ₂⟩⟩ :=
    decomposableEigenvector_factors_proportional_of_isolated e hT hμ₂
      (ha i₂) (hb j₀) (ha' k₂) (hb' l₂) hp₂ hq₂
  exact eq_of_eq_smul_of_linearIndependent hindep (hb j₀) hβ₁ hβ₂

end GaloisForLFunctions.HTGeometry
