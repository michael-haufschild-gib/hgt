import Mathlib

/-!
# A bounded sum of nonnegative terms is never weaker than its terms

Many spectral criteria have the shape

```text
∃ C, ∀ x,   ∑_i h_i(x)  ≤  C ,
```

with `h_i ≥ 0` indexed by the members of a spectrum.  Such a criterion looks like a global,
cancellation-friendly statement: one bounded quantity rather than infinitely many.  It is not.
Because the terms are nonnegative, each of them is dominated by the sum, so a uniform bound on the
sum is a uniform bound on **every** term simultaneously — with the same constant.

Consequently, if for each index the uniform boundedness of its own term already characterises some
property `P i`, then the sum criterion implies `∀ i, P i` outright.  It can be strictly *stronger*
than that conjunction (boundedness of every term does not return boundedness of the sum), but it
can never be weaker.

The design consequence is sharp: **no criterion of this shape is a weakening of the per-member
statement it is built from.** Choosing a cleverer index set, a cleverer weight, or a cleverer test
vector cannot help, because nonnegativity has already destroyed all cancellation between members.
Any genuine weakening must therefore give up termwise nonnegativity — which is exactly what makes
the signed versions hard.
-/

namespace GaloisForLFunctions

/-- A nonnegative summable family is dominated termwise by its sum. -/
theorem term_le_tsum_of_nonneg {ι : Type*} {h : ι → ℝ}
    (hs : Summable h) (hnn : ∀ i, 0 ≤ h i) (i : ι) :
    h i ≤ ∑' j, h j :=
  hs.le_tsum i fun j _ => hnn j

/-- **A bounded nonnegative sum bounds every term, uniformly and with the same constant.** -/
theorem term_le_of_tsum_le {ι X : Type*} {h : ι → X → ℝ} {C : ℝ}
    (hs : ∀ x, Summable fun i => h i x) (hnn : ∀ i x, 0 ≤ h i x)
    (hbdd : ∀ x, (∑' i, h i x) ≤ C) (i : ι) (x : X) :
    h i x ≤ C :=
  le_trans (term_le_tsum_of_nonneg (hs x) (fun j => hnn j x) i) (hbdd x)

/-- **The sum criterion implies the per-member criterion.**  If a uniform bound holds for the sum,
then each member admits a uniform bound on its own term. -/
theorem forall_exists_bound_of_tsum_bound {ι X : Type*} {h : ι → X → ℝ}
    (hs : ∀ x, Summable fun i => h i x) (hnn : ∀ i x, 0 ≤ h i x)
    (hbdd : ∃ C : ℝ, ∀ x, (∑' i, h i x) ≤ C) :
    ∀ i : ι, ∃ C : ℝ, ∀ x : X, h i x ≤ C := by
  obtain ⟨C, hC⟩ := hbdd
  exact fun i => ⟨C, fun x => term_le_of_tsum_le hs hnn hC i x⟩

/-- **The family-level no-go.**  Suppose that for each member, uniform boundedness of its own term
characterises a property `P`.  Then a uniform bound on the sum forces `P` at every member.  A
criterion of this shape is therefore at least as strong as the conjunction of its per-member
statements, and can never serve as a weakening of it. -/
theorem forall_prop_of_tsum_bound {ι X : Type*} {h : ι → X → ℝ} {P : ι → Prop}
    (hs : ∀ x, Summable fun i => h i x) (hnn : ∀ i x, 0 ≤ h i x)
    (hchar : ∀ i, (∃ C : ℝ, ∀ x : X, h i x ≤ C) → P i)
    (hbdd : ∃ C : ℝ, ∀ x, (∑' i, h i x) ≤ C) :
    ∀ i : ι, P i :=
  fun i => hchar i (forall_exists_bound_of_tsum_bound hs hnn hbdd i)

/-- **Equivalence when the per-member statement also returns the sum bound.**  If in addition the
conjunction of per-member properties implies the sum bound, the two are equivalent — the criterion
is then exactly the per-member conjunction, with no slack in either direction. -/
theorem tsum_bound_iff_forall_prop {ι X : Type*} {h : ι → X → ℝ} {P : ι → Prop}
    (hs : ∀ x, Summable fun i => h i x) (hnn : ∀ i x, 0 ≤ h i x)
    (hchar : ∀ i, (∃ C : ℝ, ∀ x : X, h i x ≤ C) → P i)
    (hback : (∀ i, P i) → ∃ C : ℝ, ∀ x, (∑' i, h i x) ≤ C) :
    (∃ C : ℝ, ∀ x, (∑' i, h i x) ≤ C) ↔ ∀ i, P i :=
  ⟨fun hbdd => forall_prop_of_tsum_bound hs hnn hchar hbdd, hback⟩

/-- **Nonnegativity is what destroys the cancellation.**  Without it the conclusion fails: an
explicit signed family whose sum is identically zero, hence uniformly bounded, while one of its
terms is unbounded.  So the no-go above is exactly a statement about nonnegative criteria, and any
route that hopes to gain from cancellation must abandon termwise nonnegativity. -/
theorem exists_signed_family_bounded_sum_unbounded_term :
    ∃ h : Fin 2 → ℝ → ℝ,
      (∀ x, (∑ i, h i x) = 0) ∧ ¬ (∃ C : ℝ, ∀ x : ℝ, h 0 x ≤ C) := by
  refine ⟨![fun x => x, fun x => -x], fun x => by simp [Fin.sum_univ_two], ?_⟩
  rintro ⟨C, hC⟩
  have h1 : C + 1 ≤ C := by simpa using hC (C + 1)
  linarith


/-! ### Growing index sets, and the exponential mechanism

The criteria that actually appear index a **finite but growing** family: the bound is on
`∑_{i ∈ S x} h i x` where the index set `S x` expands with the parameter.  The conclusion is
unchanged — a member of the index set is dominated by the sum as soon as it enters it — and the
usual way the per-member bound then forces a sign is that the member grows exponentially in the
parameter, so boundedness pins its rate to be nonpositive. -/

/-- **A bounded nonnegative finite sum bounds each of its members.**  The index set may vary with
the parameter; the bound applies to any member once it belongs. -/
theorem term_le_of_finset_sum_le {ι X : Type*} [DecidableEq ι]
    {h : ι → X → ℝ} {S : X → Finset ι} {C : ℝ}
    (hnn : ∀ i x, 0 ≤ h i x) (hbdd : ∀ x, (∑ i ∈ S x, h i x) ≤ C)
    (i : ι) (x : X) (hi : i ∈ S x) : h i x ≤ C :=
  le_trans (Finset.single_le_sum (fun j _ => hnn j x) hi) (hbdd x)

/-- **Boundedness of an exponential pins its rate.**  If a positive multiple of `exp(n·d)` stays
bounded along the naturals, then `d ≤ 0`.  This is the step that turns a per-member bound into a
sign condition on that member. -/
theorem rate_nonpos_of_eventually_bounded {c d C : ℝ} (hc : 0 < c)
    (hbdd : ∀ᶠ n : ℕ in Filter.atTop, c * Real.exp ((n : ℝ) * d) ≤ C) :
    d ≤ 0 := by
  by_contra hd
  rw [not_le] at hd
  have hgrow : Filter.Tendsto (fun n : ℕ => c * Real.exp ((n : ℝ) * d)) Filter.atTop
      Filter.atTop := by
    refine Filter.Tendsto.const_mul_atTop hc ?_
    refine Real.tendsto_exp_atTop.comp ?_
    exact Filter.Tendsto.atTop_mul_const hd tendsto_natCast_atTop_atTop
  obtain ⟨n, hn⟩ := (hgrow.eventually_gt_atTop C).and hbdd |>.exists
  exact absurd hn.1 (not_lt.mpr hn.2)

/-- **The composite no-go for growing exponential families.**  A criterion bounding a finite sum of
positive exponentials — the shape of every "bounded thermal diagonal" or "bounded projective
section" criterion — forces every rate to be nonpositive, one member at a time.  It is therefore
exactly the conjunction of its per-member sign conditions and cannot be weaker than them. -/
theorem rates_nonpos_of_bounded_exponential_family {ι : Type*} [DecidableEq ι]
    {c : ι → ℝ} {d : ι → ℝ} {S : ℕ → Finset ι} {C : ℝ}
    (hc : ∀ i, 0 < c i)
    (hbdd : ∀ n : ℕ, (∑ i ∈ S n, c i * Real.exp ((n : ℝ) * d i)) ≤ C)
    (hmem : ∀ i, ∀ᶠ n : ℕ in Filter.atTop, i ∈ S n) :
    ∀ i, d i ≤ 0 := by
  intro i
  refine rate_nonpos_of_eventually_bounded (C := C) (hc i) ?_
  filter_upwards [hmem i] with n hn
  exact term_le_of_finset_sum_le (X := ℕ) (S := S) (C := C)
    (h := fun j (m : ℕ) => c j * Real.exp ((m : ℝ) * d j))
    (fun j m => le_of_lt (mul_pos (hc j) (Real.exp_pos _))) hbdd i n hn


end GaloisForLFunctions
