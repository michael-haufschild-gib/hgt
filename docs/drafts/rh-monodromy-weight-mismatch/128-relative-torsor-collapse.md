# 128 — The relative torsor collapses: freeness is deck-invisibility [ROUTE KILLED]

Formal home: `formal/GaloisForLFunctions/RHTower/RelativeTorsor.lean`
(all endpoints axiom-clean: `[propext, Classical.choice, Quot.sound]`; full `MainTheorems` gate green).

Doc 127 §6, reframed into the charter's verified-absent registers (approach §10), named the one
object left standing: the **relative `2^k`-root torsor of ξ measured against the free `{σ_p}` tower
as reference frame** — read in the coarse-monodromy register (the deck class `w_k`), not the value/
order register the disjoint-carrier kill closed. This document constructs that object and drives it
to a decision. It collapses, and the reason is structural, not a matter of effort.

## 1. The construction

The finite Euler truncation `eulerPartial P` carries a **global single-valued `2^k`-th root**
`eulerRoot k P` on the right half-plane, unconditionally (`exists_global_pow_root_eulerPartial`,
doc 104) — the free tower. Dress ξ by it: the relative carrier is `relCarrier P = xi · eulerPartial P`,
and a local `2^k`-root `G` of ξ on a slit chart becomes a local root of the relative carrier by
`G · eulerRoot k P` (`relRoot_pow`). The relative torsor is the deck cocycle of these dressed roots —
ξ's obstructed torsor measured *relative to* the free reference frame.

## 2. The collapse [PROVED HERE]

The reference root `eulerRoot k P` is a finite product of exponentials, hence **nonvanishing at every
point of ℂ** (`eulerRoot_ne_zero`) — no domain restriction, no hypothesis on the primes. The deck
class is the ratio of the two chart roots (`deckClass g₁ g₂ pP pM = (g₁pP/g₂pP)/(g₁pM/g₂pM)`).
Multiplying **both** chart roots by one global nonvanishing factor cancels in that ratio
(`deckClass_mul_global`). Therefore:

- `relative_deckClass_eq`: `deckClass (G₁·eulerRoot) (G₂·eulerRoot) = deckClass G₁ G₂`, at **every**
  basepoint, unconditionally.
- `relative_deckClass_eq_xi`: on the slit charts around any zero `ρ₀`, the relative deck class equals
  ξ's own, `exp(2πi·m/2^k)` with `m = ord_{ρ₀} ξ` (via `xi_deckClass`). The reference frame moved
  nothing.
- `relative_torsor_trivial_iff_ladder`: the relative torsor is trivial **iff** ξ's is — iff the
  divisibility clause `2^k ∣ ord_{ρ₀} ξ` that `RHLadder k` quantifies over holds
  (`xi_deckClass_eq_one_iff_ladder_dvd`).

Measuring ξ relative to the free `{σ_p}` reference returns ξ. The relative torsor **is** `RHLadder k`;
it cannot be an independent constraint on it — it is the same statement.

## 3. Why — freeness and contribution are mutually exclusive [PROVED HERE]

The deck class sees only **monodromy**: a global, single-valued factor appears identically in both
charts and cancels. The reference frame's own deck class is trivial (`reference_own_deckClass_one`) —
that is exactly what "free tower" means: a single-valued global root, no monodromy. So a reference
frame can contribute to the relative monodromy **only if it carries monodromy of its own**; the
`{σ_p}` tower's defining property — the very freeness that made it the natural reference (doc 104:
`exists_global_pow_root_eulerPartial`) — is the absence of monodromy. **Freeness is
deck-invisibility.** The free reference cannot break the tautology it was meant to break.

This is not the circularity of doc 106 §4 restated by hand; it is proved: the collapse holds at every
basepoint of ℂ (`relative_deckClass_eq` needs only `eulerRoot_ne_zero`, which is unconditional). There
is no pinned annulus at which the free reference carries a nontrivial class.

## 4. The dichotomy — every non-collapsing variant is a non-free reference or a flow

| Relative construction | Status |
|---|---|
| multiplicative dressing `ξ · eulerPartial P` | collapses — reference deck-trivial (§2, here) |
| quotient `ξ / eulerPartial P` | dressing by `eulerPartial⁻¹`, also global nonvanishing — same collapse |
| torsor difference in `H¹` | `deckClass(ξ) − deckClass(ref) = deckClass(ξ) − 0`; reference class is `0` (`reference_own_deckClass_one`) — same collapse |
| reference differing between charts | a reference **with** monodromy — not the free `{σ_p}` tower |
| cross-wall comparison (reference continued past `Re s = 1`) | a **flow** — the finite tower is free only as a finite product; `ζ`'s product needs `Re s > 1` (doc 104), and continuing it is the flow the mantra refuses |

Every torsor-level combination of ξ with the free reference collapses to ξ's class, because a free
(globally rooted) object is a coboundary in the deck cocycle. The only non-collapse needs a reference
that is itself obstructed — not the free `{σ_p}` tower — or a continuation across the wall — a flow.

## 5. What this closes and what it opens

The reframed route of doc 127 §6 is closed: the free `{σ_p}` tower **cannot** do reference-frame work
ξ's own tower cannot do for itself; being free, it does no deck work at all. The escape that motivated
it is discharged negatively, in the charter's own coarse-monodromy register (approach §10 item 2),
bridging divisor → monodromy throughout (never divisor → relation; `ω = 0 ⇏ RH`, approach §2.4 —
respected: every statement here is about the deck class `w_k`, never a relation ideal).

The forward move follows from the proof, not against it. Since a *free* reference is inert, a live
reference must **carry its own arithmetic monodromy**, disjoint from ξ's, so that the difference class
is nontrivial and non-circular. The free `{σ_p}` tower is the wrong object for that role precisely
because it is free.

This collapse, together with the pinned-source exhaustion (`SigmaDivisorExhaustion.lean`,
built on doc 127) and the jet triviality (`SigmaDivisorJet.lean`), fixes the surviving algebraic
shape exactly: a **torsion seam presentation** `Rⁿ --A--> Rⁿ → Q`, `det A = Xᵐ`, whose defect
`Δ_p` has boundary `tr(adj(A)·Δ_p) mod Xᵐ` — fake defects `Δ_p = A·H_p + Xᵐ·K_p` vanish
(`FittingSeamBoundary.lean`), so a live boundary forces `Δ_p ∉ A·End + (Xᵐ)`. But that object is a
**coker/torsion** module, and bare `𝓜⁺` is finite-free — it has no torsion slot. The route is
therefore killed inside the current category; reopening it is a **one-layer change to the definition
of `𝓜⁺` objects/morphisms** (a p-labelled torsion seam presentation), after which the first theorem
is `Δ_p ∉ A·End + (Xᵐ)`, not recurrence. This is recorded as the charter amendment (approach §13).
The `{σ_p}`-divisor route is closed until 𝓜⁺ is extended; the live program remains the Wave-5
conservation/parity fronts on the **exact deck charge**, which need no `{σ_p}`-graded refinement.
