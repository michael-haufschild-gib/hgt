# 33 — The Dictionary Base: k = 1 as Sign Reading, L as Seam Product

**Register: SEARCH** (statements precise, proofs in outline from banked Lean bricks;
Lean plumbing is the executable next step). Task #131, items (2) and (3).

## 1. The k = 1 base case: deck class = sign ratio on the seam [proof in outline]

Ξ(t) := xi(1/2 + it) is real (reflection symmetry, banked in Reflection/
ReflectionParity). Let W be a window with chart basepoints p± ON the critical line,
Ξ ≠ 0 there.

> **(K1) [statement].** The level-2 deck class of the window satisfies
> deckClass(W; 2) = sign(Ξ(p₊))·sign(Ξ(p₋)) ∈ {±1}: it equals −1 iff the number of
> xi-zeros enclosed by W, counted with multiplicity, is odd. In particular the k = 1
> rung datum is the classical sign-change reading of Ξ across the window.

*Outline.* At a basepoint with Ξ(p) > 0 choose the square root real-positive; with
Ξ(p) < 0 choose it on a fixed branch. The deck class (DeckCocycle: quotient of the two
chart roots at the shared basepoints) is ±1 by `deckClass_pow_eq_one` (n = 2), and
equals +1 iff the two real-branch choices glue, which by the intermediate-value/
continuation argument along the seam happens iff Ξ has an even number of sign changes
between p₋ and p₊ — i.e. even enclosed odd-multiplicity count. The central point is
covered by `xi_central_order_even` / `xi_deckClass_central_sq_trivial`
(ReflectionParity): the center contributes trivially, as (ID) requires. Lean target:
`deckClass_eq_sign_ratio` in a new DictionaryBase.lean, from `deckClass`,
`deckClass_pow_eq_one`, the realness of Ξ, and `xi_deckClass_central_sq_trivial`. ∎

## 2. L as seam product [proof in outline]

Doc 18's (ID) counts L(W) = on-line zeros (with multiplicity) in the window. The seam
machinery reads this WITHOUT counting: `xiDescent_seam_jump` (SeamCocycle) gives, at
each seam crossing x₀, the jump of the descended cocycle across the u-plane slit; the
jump datum at x₀ is exactly the local multiplicity's parity contribution.

> **(K2) [statement].** For a window whose boundary meets the critical line
> transversally at two points, L(W) mod 2^k equals the product of the seam-jump data
> (SeamCocycle) accumulated along ∂W ∩ {Re s = 1/2}, and the mod-4 window relation
> D ≡ L (doc 18) is the cocycle identity: the deck class computed through the upper
> chart equals the seam product times the deck class through the lower chart
> (`seam_jump` composed along the window boundary).

*Outline.* Each on-line zero descends to a slit-boundary zero of xiDescent
(UPlaneDescent); `xiDescent_seam_jump` quantifies the cocycle discontinuity across the
slit at −t₀²; composing the jumps along the traversed seam segment gives the total
= Σ multiplicities mod 2^k, i.e. L(W)'s rung datum; the window identity (ID)
(`window_identity`, WindowRelation) then reads D ≡ L + 2N. Lean target:
`seam_product_eq_L` chaining `seam_jump` along a finite crossing list. ∎

## 3. What #131 needs after this

Only the Lean plumbing of (K1) and (K2) — both statements are now precise, and every
ingredient names a banked theorem. With them, the dictionary D-as-deck-class /
L-as-seam-product / k = 1-as-sign-reading is complete, and doc 22's reduction plugs
into the machine-checked window relation end to end: the ladder rung on a dominated
window = a finite certified truncation reading (transport, doc 32) whose exactness is
the (S-mono) arc (docs 25–31). Next object: DictionaryBase.lean.
