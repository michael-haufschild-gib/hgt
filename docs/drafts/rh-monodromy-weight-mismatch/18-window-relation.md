# 18 — The Window Relation: RH as Equality of Two Boundary Invariants

**Register: SEARCH** (the reformulation is elementary once stated — promotion to Lean
is carded; the open core is §5). This document completes the constraint-not-flow
reduction begun in docs 15–16: (OC1′)'s family variable is DISSOLVED, and the ladder
becomes a per-window relation between two exact boundary invariants of ζ itself.

## 1. The bookkeeping identity

Fix a disk window W = closed ball centered at c = 1/2 + iT (ON the critical line),
with ξ zero-free on ∂W and on the two edge arcs where ∂W meets the line. FE ∧ reality
act on W (both symmetries fix c and preserve W). The zeros of ξ in W split as:

- on-line zeros, total order L(W) := Σ ord;
- off-line zeros in conjugate-FE pairs {ρ, 1 − ρ̄} of EQUAL order (banked:
  `xi_orderAt_conj`, `xi_orderAt_one_sub`) — one member right of the line, one left;
  right-half total order N(W) := Σ_{Re ρ > 1/2} ord.

With D(W) := total enclosed order,

> **(ID)  D(W) = L(W) + 2·N(W)** — an identity, not an estimate.

## 2. The relation, graded over the ladder

> **(WR_k)  D(W) ≡ L(W)  (mod 2^{k+1})** for every admissible line-centered window W.

**Claim (elementary).** RH_{2^k} ⟺ (WR_k) for all admissible W; hence
**RH ⟺ ∀k (WR_k)**.

*Proof shape.* (⟸) Shrink W around a single hypothetical pair {ρ, 1−ρ̄} of order m:
L = 0, D = 2m, so (WR_k) reads 2m ≡ 0 (mod 2^{k+1}), i.e. 2^k ∣ m — the rung, per
zero. (⟹) If every off-line order is divisible by 2^k, then N(W) ≡ 0 (mod 2^k) for
every W, and (ID) gives (WR_k). ∎

## 3. Both sides are exact boundary data (banked dictionaries)

- **D(W) mod 2^{k+1}** is the DECK CLASS of ξ's local roots at level n = 2^{k+1} on
  the annulus charts around W (`deckClass_multi_zero`, `xi_deckClass`); by holography
  (`deckClass_eq_exp_circleAverage_slope`) it is computable from **|ξ| on two circles**
  — pure boundary modulus.
- **L(W) mod 2^{k+1}** is the SEAM LEDGER at level k+1: the product of seam jumps
  across the on-line zeros inside W equals the ratio of the seam gluing classes at the
  two edge segments (`seam_jump`, `xiDescent_seam_jump` on the u-plane carrier, where
  the window's line diameter is a slit interval). At k = 1 (n = 2) the seam class per
  segment is literally the SIGN of Ξ on that segment — the ledger is Hardy's
  sign-change bookkeeping; at higher k it is the ℤ/2^{k+1} refinement by 2^{k+1}-th
  root gluing (arg-of-ξ data on the line, coarsened exactly).

So (WR_k) is a required equality of two ℤ/2^{k+1}-valued invariants, each read from
constraint-side data (modulus on circles; gluing on the line) — **the bulk is pinned
by the boundary; nothing is propagated. No family, no flow, no events.**

## 4. Filter checks

- **D–H filter ✓ (discriminates correctly):** at the banked certified D–H zero, a
  small window has D = 2, L = 0: (WR_1) FAILS for D–H — as it must, since D–H has
  simple off-line zeros. Whatever proves the ζ-instance of (WR_k) has to consume the
  Euler structure; FE ∧ reality alone are exactly what (ID) already used.
- **Symmetry discount ✓ (consistent, sharpened):** doc 14 §2 said symmetric data is
  blind at k ≤ 2; (WR_k) shows HOW the blindness is broken — not by asymmetric
  windows but by coupling the symmetric total (D) with the finer seam invariant (L)
  one dyadic level up. Reading right-half parity costs exactly one extra rung — the
  coherent-tower structure appearing in the bookkeeping itself.
- **Regularity wall ✓:** both invariants are exact (monodromy/divisor data); neither
  factors through value-distribution classes.

## 5. The open core, relocated once more — and named

> **(WR-core)** Prove D(W) ≡ L(W) (mod 4) for ζ's windows (k = 1 first): an exact
> identity of ζ tying the circle-average/modulus data of |ξ| to the ℤ/4 gluing data
> of ξ on the critical line.

Honesty: (WR_1) ⟺ RH_2 — RH-grade as always; Bagchi-consistency is not evaded. What
changed is the SHAPE of the missing input: not an estimate, not a family control —
one exact relation between two boundary-computable torsion invariants of a single
function. The Euler product must enter as the bridge between the multiplicative
boundary modulus (D-side; note log|ξ| on circles is where Euler factors are additive)
and the line-gluing data (L-side; arg-type data, where the FE lives). This is the
sharpest constraint-not-flow form the lane has produced: the wall's registers
(measure, recurrence, statistics) cannot even express the relation.

**Next moves.** (i) Lean: `window_relation_iff_ladder` — (ID) + the §2 equivalence
from banked pairing/equivariance lemmas; then wire the two dictionary readings
(deck class at n = 2^{k+1}; seam ratio at k+1). (ii) Compute both invariants for ζ in
a few windows numerically at k = 1 (pre-register: relation HOLDS — RH is true in
tested ranges; the value is instrument calibration, especially the L-side ℤ/4
reading). (iii) Hunt the bridge identity: what multiplicative exact structure equates
the two readings — starting from the fact that both are LOGARITHMIC data of ξ read on
the two boundary strata (circle vs line) of the same window.
