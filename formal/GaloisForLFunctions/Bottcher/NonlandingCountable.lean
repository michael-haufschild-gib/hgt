import Mathlib.Data.Set.Countable
import Mathlib.Logic.Function.Iterate

/-!
# Conditional countability of non-landing external angles

For a quadratic `f_c(z)=z²+c` with `c ∈ M ∖ {0,−2}`, the set of *non-landing* external angles
`E = {θ : I(θ) is not a singleton}` (where `I(θ)` is the principal impression of the external ray at
angle `θ`) is conjectured countable.  Unconditionally that is genuinely open (it needs a countable
"obstruction set" `𝒫 ⊆ J` whose existence is unproved in the Cremer / infinitely-renormalizable
regime — see `T03d`).  What *is* elementary, and is formalized here, is the **conditional reduction**:
given such an obstruction set, `E` is countable.

The mathematical content is purely set-theoretic — it needs only that the angle-doubling map `D`
pulls countable sets back to countable sets (it has finite fibers), phrased abstractly so it applies
to any `D : Angle → Angle` with that property.

- `countable_preimage_of_countable_fibers` — a countable-fiber map preserves countability under `⁻¹'`.
- `countable_iterate_preimage` / `countable_iUnion_iterate_preimage` — iterated pullbacks stay countable.
- `countable_nonlanding_of_obstruction` — the conditional reduction: obstruction set `⟹` `E` countable.
- `countable_nonlanding_union_seed_of_obstruction` — adjoining a countable "bad-loop seed" `B`.
-/

open Set Function

namespace Bottcher

/-- A map with countable fibers pulls countable sets back to countable sets:
`(D ⁻¹' S)` is countable whenever `S` is and every fiber `D ⁻¹' {x}` is countable.  (For the
angle-doubling map `D θ = 2θ` the fibers are two-point sets, hence countable.) -/
theorem countable_preimage_of_countable_fibers {α β : Type*} {D : α → β}
    (hfib : ∀ x, (D ⁻¹' {x}).Countable) {S : Set β} (hS : S.Countable) :
    (D ⁻¹' S).Countable := by
  have hEq : D ⁻¹' S = ⋃ x ∈ S, D ⁻¹' {x} := by
    ext a; simp [Set.mem_preimage]
  rw [hEq]
  exact hS.biUnion (fun x _ => hfib x)

/-- Every iterate of a map with countable pullbacks pulls a countable set back to a countable set. -/
theorem countable_iterate_preimage {α : Type*} {D : α → α}
    (hD : ∀ s : Set α, s.Countable → (D ⁻¹' s).Countable) :
    ∀ (n : ℕ) {S : Set α}, S.Countable → ((D^[n]) ⁻¹' S).Countable := by
  intro n
  induction n with
  | zero => intro S hS; simpa using hS
  | succ k ih =>
      intro S hS
      rw [Function.iterate_succ', Set.preimage_comp]
      exact ih (hD S hS)

/-- The union over all forward iterates of the pullback of a countable set stays countable. -/
theorem countable_iUnion_iterate_preimage {α : Type*} {D : α → α}
    (hD : ∀ s : Set α, s.Countable → (D ⁻¹' s).Countable)
    {S : Set α} (hS : S.Countable) :
    (⋃ n : ℕ, (D^[n]) ⁻¹' S).Countable :=
  Set.countable_iUnion (fun n => countable_iterate_preimage hD n hS)

/-- **Conditional countability of non-landing angles.**  Let `D : Angle → Angle` be the angle-doubling
map (assumed here only to have countable pullbacks, `hD`), `I : Angle → Set J` the impression map, and
`Θ(p) = {θ | p ∈ I θ}` the angle-fiber of a point `p`.  Suppose there is a countable obstruction set
`P ⊆ J` with

* (a) `Θ(p)` countable for every `p ∈ P`, and
* (b) every non-landing angle `θ ∈ E` has some forward iterate `Dⁿθ` whose impression meets `P`.

Then `E` is countable.  Proof: (b) gives `E ⊆ ⋃ₙ D⁻ⁿ(Θ(P))`; `Θ(P) = ⋃_{p∈P} Θ(p)` is a countable
union of countable sets by (a); and countable pullbacks of `D` keep each `D⁻ⁿ(Θ(P))` — hence their
union — countable. -/
theorem countable_nonlanding_of_obstruction
    {Angle J : Type*} {D : Angle → Angle} {I : Angle → Set J}
    (hD : ∀ s : Set Angle, s.Countable → (D ⁻¹' s).Countable)
    {P : Set J} (hP : P.Countable)
    (hfib : ∀ p ∈ P, {θ | p ∈ I θ}.Countable)
    {E : Set Angle}
    (hobs : ∀ θ ∈ E, ∃ (n : ℕ) (p : J), p ∈ P ∧ p ∈ I (D^[n] θ)) :
    E.Countable := by
  set ΘP : Set Angle := ⋃ p ∈ P, {θ | p ∈ I θ} with hΘ
  have hΘc : ΘP.Countable := hP.biUnion (fun p hp => hfib p hp)
  have hsub : E ⊆ ⋃ n : ℕ, (D^[n]) ⁻¹' ΘP := by
    intro θ hθ
    obtain ⟨n, p, hp, hpI⟩ := hobs θ hθ
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_biUnion hp hpI⟩
  exact (countable_iUnion_iterate_preimage hD hΘc).mono hsub

/-- **Bad-loop seed corollary.**  Under the same obstruction hypotheses, adjoining a countable seed set
`B` of angles together with all its backward iterates keeps the exceptional set countable:
`E ∪ ⋃ₙ D⁻ⁿ(B)` is countable. -/
theorem countable_nonlanding_union_seed_of_obstruction
    {Angle J : Type*} {D : Angle → Angle} {I : Angle → Set J}
    (hD : ∀ s : Set Angle, s.Countable → (D ⁻¹' s).Countable)
    {P : Set J} (hP : P.Countable)
    (hfib : ∀ p ∈ P, {θ | p ∈ I θ}.Countable)
    {E : Set Angle}
    (hobs : ∀ θ ∈ E, ∃ (n : ℕ) (p : J), p ∈ P ∧ p ∈ I (D^[n] θ))
    {B : Set Angle} (hB : B.Countable) :
    (E ∪ ⋃ n : ℕ, (D^[n]) ⁻¹' B).Countable :=
  (countable_nonlanding_of_obstruction hD hP hfib hobs).union
    (countable_iUnion_iterate_preimage hD hB)

end Bottcher
