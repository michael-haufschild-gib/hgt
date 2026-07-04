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

## 4. (K1) machine-checked — the seam continuation dissolved [PROVED HERE]

The continuation argument of §1's outline is not needed. Choosing the second chart root
as the LINE MIRROR of the first — g₂ = conj ∘ g₁ ∘ lineReflect, analytic by Schwarz
reflection — makes the chart ratio at an on-line basepoint p equal to
g₁(p)/conj(g₁(p)) = sign Ξ(p) pointwise; `deckClass_root_indep` then transfers the value
to EVERY root pair on the mirror-symmetric cover. Banked in DictionarySign.lean
(axiom-clean, gate green):

- `xi_deckClass_eq_sign_product` — **(K1)**: deckClass(g₁,g₂;p₊,p₋) =
  sign Ξ(p₊)·sign Ξ(p₋) for arbitrary analytic square roots of ξ on a chart and its
  mirror; with `mirrorRoot_analyticOnNhd`, `mirrorRoot_pow`, `xi_lineReflect`,
  `xi_im_eq_zero_on_line` (reality of Ξ), and the pointwise
  `deckClass_mirror_eq_sign_product` (generic carrier with the real FE).
- DictionaryBase.lean gained `sq_conj_ratio_of_pos/neg` (z/conj z = ±1 by carrier sign).

The odd-enclosed-count clause of (K1) is separate wiring: compose the sign product with
`deckClass_eq_one_iff_exists_root` + `exists_root_iff_orders_dvd` + the reflection
pairing (`xi_orderAt_conj`/`xi_orderAt_one_sub`) — it lives with (K2), item (3)'s
seam-product chain. Next object: the (K2) chain (`seam_jump` composed along a finite
crossing list against `window_identity`).

## 5. The count clause machine-checked too [PROVED HERE]

`xi_sign_product_eq_parity` (DictionarySign.lean, axiom-clean): on a critical-line-
centered window with peeled factorization ξ = ∏(z−ρᵢ)^{mᵢ}·h on the ball,

> sign Ξ(p₊) · sign Ξ(p₋) = (−1)^{Σ mᵢ}

at the seam basepoints p± = a ± ((r₀+R)/2)i — the classical "Ξ changes sign across the
window iff the enclosed count is odd", with NO argument principle: the sign product IS
the deck class (§4) and the deck class counts the enclosed order (`deckClass_multi_zero`).
The geometric key: for Re a = 1/2 the line mirror acts on the recentered variable as
w ↦ −w̄, so it maps chartRA onto chartLA exactly (`lineReflect_preimage_chartRA`).
(K1) is now COMPLETE — both the sign reading and the count clause. Remaining in #131:
(K2) only — the seam-product chain along multi-crossing boundaries.

## 6. (K2) base level machine-checked: the rung datum reads L(W) [PROVED HERE]

`xi_sign_product_eq_onLine_parity` (DictionarySign.lean, axiom-clean): for a
reflection-closed enclosed configuration with reflection-invariant multiplicities,

> sign Ξ(p₊) · sign Ξ(p₋) = (−1)^{L(W)},   L(W) = Σ_{on-line} m_z.

Proof = §5's parity theorem composed with `window_identity` (D = L + 2N): off-line
zeros pair under the mirror and cancel mod 2 — the k = 1 deck class is blind to them.
This is D ≡ L (mod 2) realized as cocycle arithmetic, and it upgrades §5 to the exact
classical form: the sign change counts ONLY on-line zeros, unconditionally.

Dictionary status: D-as-deck-class banked at every level (XiDeck); k = 1-as-sign-reading
banked (§§4–5); L-as-seam-product banked at k = 1 (this section). The residual (K2) item
is the LEVEL-4 seam reading (the bridge's (WR_1) is mod 4; the level-2 class sees only
mod 2): chain `xiDescent_seam_jump` at n = 4 along the crossing list — OR verify that
#130's consumption path goes through the germ-extension packaging
(`rhLadder_iff_germ_extends`, #137), which bypasses the seam representation entirely.
That check is the next dictionary move.

## 7. The decision closed: the dictionary is complete AND provably maximal [PROVED HERE]

The §6 residual asked: level-4 seam chain, or germ-extension consumption? Answer:
NEITHER — and the reason is a theorem.

**The blindness no-go** (`deckClass_blind_to_split`, DictionarySign.lean, axiom-clean):
the deck class at EVERY level n depends only on the TOTAL enclosed multiplicity —
positions never enter `deckClass_multi_zero`'s value. Since the sign product equals the
deck class (§4), the full instrument set the dictionary can supply — deck data at all
levels plus seam sign data — assigns IDENTICAL values to a near-line mirror pair
(cellD = 2, cellL = 0, cellN = 1) and an on-line pair (cellD = 2, cellL = 2, cellN = 0).
These differ exactly by an N-parity flip. Consequence: doc 22's seam-side transport
(L mod 4 under domination) is NOT derivable from deck/sign transport at any level or
cell refinement; a level-4 seam chain would inherit the same blindness.

**Where the mod-4 bit lives.** The two invisible configurations are separated by ONE
real datum: the discriminant sign of the local quadratic factor on the seam — real
roots (on-line pair) vs conjugate roots (mirror pair). That is precisely the DISC
reading (#132), and its exactness on recentered carriers is precisely the (SPUR-R)
arc (#135, docs 23–31). The routing of the bridge through DISC is therefore FORCED by
the geometry, not chosen for convenience: the discriminant bit is the minimal
instrument beyond the dictionary, and the (S-mono) theorem is its certification.

**#131 closes.** The dictionary supplies everything it can: D-as-deck-class at every
level (XiDeck), k = 1 sign reading both halves (§§4–5), L-parity reading (§6), seam
transport under domination (SeamTransport), and the maximality no-go (§7). All
machine-checked. The bridge's remaining burden lives entirely in the already-carded
DISC lane: (SPUR-R) exactness write-out (#135/#138) + the doc 22 reduction instances.
Next object: the constants write-out of the (S-mono) arc — now the unique load-bearing
open item of the whole chain.
