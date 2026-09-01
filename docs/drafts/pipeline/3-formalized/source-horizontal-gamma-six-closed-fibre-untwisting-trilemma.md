# Source Γ₆ closed-fibre untwisting trilemma

- **ID:** RH-SOURCE-G6-CLOSED-FIBRE-TRILEMMA
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** In any commutative algebra over a field, an automorphic untwisting of `x-u` to `x-1` preserves a proper fibre ideal containing `x-a` iff `u=1`; hence no grade-universal fibre-preserving algebraic enlargement exists.

## Goal

Kill
`commutative algebraic enlargement/localization retaining a closed source fibre → Γ₆ holonomy untwisting → fixed-source Stokes descent → shared HB/FZZ-P/PW-B/RBH Ward → RH`.

## Gates

- [x] 0 → 1 in-progress: corpus-derived from the finite/total localization dichotomy; exact chain fixed
- [x] 1 → 2 fully-proven: dependency-closed proof; `[PAPER-PROVED]`
- [x] 2 → 3 formalized: exact Lean theorem; direct check and targeted build pass; standard axioms only; umbrella wired
- [ ] 3 → 4 publication-ready

## Hostile loop

- `[CONJECTURE]` An infinite non-field algebraic enlargement can untwist every Γ₆ holonomy while retaining one fixed proper closed fibre.
- `[FALSIFIED]` Evaluating the intertwining equation at `f=1` forces `φ(x)=x+(u-1)`. If `x-a` lies in a proper ideal `I` and `φ(I)⊆I`, then `(u-1)·1∈I`; for `u≠1` this is a unit, so `I=⊤`.
- Stronger survivor: fibre-preserving untwisting exists exactly at `u=1`, over every field and commutative algebra, without finiteness, reducedness, domain, or localization hypotheses.
- Verdict: `SURVIVES PRELIMINARY ATTACK` as exact Γ₆ route closure. Parent affine-group/localization facts are standard; targeted corpus and literature searches found no four-route application.

## Paper theorem

Let `K` be a field, `A` a commutative `K`-algebra, `x∈A`, `u,a∈K`, and `I⊊A` an ideal with `x-a∈I`. For a `K`-algebra automorphism `φ`, put
`B_u(f)=(x-u)f` and say `φ` untwists `u` when `φ(B_u(f))=B_1(φ(f))` for every `f`.
Then

`∃ φ, φ untwists u ∧ φ(I)⊆I  ↔  u=1`.

Consequently there is no family of fibre-preserving untwistings indexed by every `u∈K` when `K` is nontrivial.

## Proof

If `φ` untwists, set `f=1`. Since `φ` fixes coefficients,
`φ(x)-u=x-1`, hence `φ(x)=x+(u-1)`. From `x-a∈I` and forward invariance,
`φ(x-a)=(x-a)+(u-1)∈I`. Subtracting `x-a` gives `(u-1)·1∈I`.
If `u≠1`, this scalar is a unit with inverse `(u-1)⁻¹`, so `1∈I`, contradicting `I⊊A`. Thus `u=1`.
Conversely, at `u=1` the identity automorphism intertwines `B_1` with itself and preserves `I`.
For the family statement, specialize to `u=0`, which is nontrivial in a field.

## No-go closure

- **Exact killing mechanism:** nontrivial untwisting translates the distinguished affine coordinate and therefore moves every proper source fibre.
- **Strongest positive survivor:** exact fibre-preserving classification `untwisting at u ↔ u=1` for arbitrary commutative source algebras.
- **New insight:** the localization survivor cannot be “infinite, non-field, closed-fibre retaining” if it is still algebraic and automorphic; viable source dynamics must cease to be fibre-preserving algebraic gauge transport.
- **Status:** `[LEAN-PROVED]` as `sourceHorizontalGammaSixClosedFibreAlgebraicUntwistingRouteKilled`; proof survives zero-ring, arbitrary-characteristic, nonreduced, and forward-invariance edge cases; standard axioms only.
