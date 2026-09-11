import Mathlib.RingTheory.Length

/-!
# Length along a tower of submodules

Mathlib has additivity of `Module.length` in a short exact sequence, but not the form a filtration
argument actually uses: for `A ≤ B ≤ Q`,

```text
length (B / A) + length (Q / B) = length (Q / A).
```

This leaf supplies that, by exhibiting the short exact sequence
`0 → B/A → Q/A → Q/B → 0` explicitly — the first map is `liftQ` of the inclusion, the second is
`liftQ` of the projection — and it records that `Module.length` is a linear-equivalence invariant,
which mathlib also leaves implicit.

Both are stated over an arbitrary ring, with no commutativity and no finiteness hypothesis: the
identity holds in `ℕ∞` with `⊤` on both sides when the lengths are infinite, because mathlib's
`Module.length_eq_add_of_exact` already handles that case.
-/

/-- Length is additive along a tower of submodules. -/
theorem Module.length_quotient_add_length_quotient {R Q : Type*} [Ring R] [AddCommGroup Q]
    [Module R Q] (A B : Submodule R Q) (h : A ≤ B) :
    Module.length R (↥B ⧸ Submodule.comap B.subtype A) + Module.length R (Q ⧸ B) =
      Module.length R (Q ⧸ A) := by
  classical
  have hker : Submodule.comap B.subtype A ≤
      LinearMap.ker (A.mkQ.comp B.subtype) := by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero A).2 hx
  set f : (↥B ⧸ Submodule.comap B.subtype A) →ₗ[R] Q ⧸ A :=
    Submodule.liftQ _ (A.mkQ.comp B.subtype) hker with hfdef
  have hker2 : A ≤ LinearMap.ker B.mkQ := by
    intro x hx
    simp only [LinearMap.mem_ker, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero B).2 (h hx)
  set g : (Q ⧸ A) →ₗ[R] Q ⧸ B := Submodule.liftQ _ B.mkQ hker2 with hgdef
  have hfapp : ∀ x : ↥B, f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x : Q) := by
    intro x; rfl
  have hgapp : ∀ x : Q, g (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
    intro x; rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [hfapp x] at hy
      have hxA : (x : Q) ∈ A := (Submodule.Quotient.mk_eq_zero A).1 hy
      exact (Submodule.Quotient.mk_eq_zero _).2 hxA
  have hgsurj : Function.Surjective g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, hgapp x⟩
  have hrange : ∀ z, g (f z) = 0 := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H w =>
      rw [hfapp w, hgapp (w : Q)]
      exact (Submodule.Quotient.mk_eq_zero B).2 w.2
  have hexact : Function.Exact f g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      constructor
      · intro hy
        rw [hgapp x] at hy
        have hxB : x ∈ B := (Submodule.Quotient.mk_eq_zero B).1 hy
        exact ⟨Submodule.Quotient.mk ⟨x, hxB⟩, hfapp ⟨x, hxB⟩⟩
      · rintro ⟨z, hz⟩
        rw [← hz]
        exact hrange z
  exact (Module.length_eq_add_of_exact f g hfinj hgsurj hexact).symm

/-- Length is preserved by a linear equivalence. -/
theorem Module.length_eq_of_linearEquiv {R M N : Type*} [Ring R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (e : M ≃ₗ[R] N) :
    Module.length R M = Module.length R N :=
  le_antisymm (Module.length_le_of_injective e.toLinearMap e.injective)
    (Module.length_le_of_injective e.symm.toLinearMap e.symm.injective)
