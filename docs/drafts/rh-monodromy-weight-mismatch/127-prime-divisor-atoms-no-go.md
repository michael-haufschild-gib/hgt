# 127 — No {σ_p}-graded refinement of the divisor at a pinned annulus [ROUTE KILLED]

Formal home: `formal/GaloisForLFunctions/RHTower/PrimeDivisorAtomsNoGo.lean`
(all endpoints axiom-clean: `[propext, Classical.choice, Quot.sound]`).
Companion (algebraic jet side, concurrent): `formal/GaloisForLFunctions/RHTower/SigmaDivisorJet.lean`.

Doc 106 §5 named the one object that would escape all three prior kills: a `{σ_p}`-graded refinement
of the ξ-divisor, finer than the multiplicity, that is **not** a symmetry character (escapes the
exponent-2 kill, doc 106), **not** a positivity (escapes the real-axis blindness, doc 105), read at
**one pinned annulus** (no flow). This document attacks that object. Sharpened to the source
direction — a non-flow, non-positivity, non-character **source map** from `{σ_p}` into local divisor
atoms — it does not survive: the prime side is analytically trivial throughout `Re s > 0`, so the
source map is the zero map exactly where the divisor is nonzero.

Attack angle (entropy-selected): cartography + the "invariant" move. The Euler product is a **prime
atlas** — one local chart per prime, each with genuine content only on `Re s > 1`. The invariant
preserved under the prime projection is that *every chart assigns valuation 0 to every strip point*;
the divisor is the "curvature" no flat chart carries.

## 1. Two readings of the same object

**Extraction** (read the divisor, decompose by primes): attach to `m(ρ) = ord_ρ ξ` a finer
prime-indexed structure. **Source** (the user's sharpening — the stronger form): a map from the
primes into the local divisor atoms at ρ, *manufacturing* atoms from the prime side rather than
extracting them. The source form is stronger because it does not presuppose the divisor is already
decomposable; it asks only that the primes *contribute* atoms. Both are killed by one fact.

## 2. The prime side is a unit at every strip point [PROVED HERE]

Each finite local Euler factor `(1 − p^{−s})⁻¹` is analytic and nonvanishing on the whole right
half-plane, so its analytic order there is `0` (`eulerInvFactor_orderAt_zero`). Hence any finite prime
atlas `eulerPartial P = ∏_{p∈P}(1 − p^{−s})⁻¹` has order `0` at every point of `Re s > 0`
(`eulerPartial_orderAt_zero`) and, in fact, **no zeros there at all**
(`eulerPartial_zeroSet_eq_empty`) — the argument-principle count of any finite prime atlas around any
strip loop is `0`. Multiplying ξ by any finite prime atlas leaves the divisor unchanged
(`xi_divisor_prime_invisible`): `ord_ρ(ξ · eulerPartial P) = ord_ρ ξ`. The prime layers are invisible
to the divisor; no finite set of primes accounts for any part of the multiplicity.

## 3. The kill: the source map is the zero map [PROVED HERE]

A `{σ_p}`-source map into the local divisor atoms at ρ, in its pinned form, assigns to each prime `p`
an atom count `A p` realized as zeros of that prime's own local factor — so `A p ≤ ord_ρ (1 −
p^{−s})⁻¹` (`SigmaSourceMap`). This is exactly the non-flow, non-character, non-positivity form: it
reads only the primes' own analytic content at the fixed point ρ. Since every factor is a unit,
`A p = 0` for every prime (`sigma_source_map_trivial`). At a strip zero the contrast is decisive
(`source_atom_mismatch`):

- the **additive** Euler–Maclaurin carrier resolves the order-`m` zero into `zs.length = m ≥ 1`
  hole-atoms (`emSplit_length_pos_at_xi_zero`);
- every **`{σ_p}`-source map** contributes `A p = 0` atoms, for every prime.

The multiplicative (prime) side sources **zero** divisor atoms exactly where the additive side sources
`m ≥ 1`. That gap *is* the truncation weight mismatch (doc 104), now read as an atom-count mismatch —
not a repairable defect. The concurrent `SigmaDivisorJet` module proves the same triviality
abstractly: a local multiplicative source direction `X^m · h_p` has zero class in the divisor-jet
algebra `R[X]/(X^m)` — a unit factor changes only the local unit, never the jet. The analytic module
here supplies the concrete realization for ζ (its actual prime factors *are* units at every strip
point), so the abstract triviality binds the real object.

## 4. Why the only lift is a flow — disjoint carriers [PROVED HERE]

`prime_content_and_divisor_disjoint`: on `Re s ≥ 1`, where the Euler product converges to a nonzero
value and carries its prime content, ξ has no zeros; on the strip, where ξ's zeros live, every finite
prime atlas is a unit. **No point of ℂ carries both nonzero prime content and a ξ-zero.** The prime
content lives on `Re s > 1`; the zeros live in the strip; the two carriers are disjoint. The only
object linking them is the `P → ∞` limit — analytic continuation across the wall `Re s = 1` — which
is a flow, not a pinned constraint, and is exactly where the finite family stops converging
(doc 104). A source map built from that limit is not of the pinned form; it is the flow the mantra
refuses.

## 5. The exhaustive enumeration — every source of atoms

The direction has these ways to source local divisor atoms from `{σ_p}`, and each is closed:

| Source of atoms | Status |
|---|---|
| zeros of the primes' own local factors (pinned) | zero map — every factor is a unit (§2–3, here) |
| the `∂_s × {σ_p}` weld cross-term (joint local factor) | zero map — the archimedean factor `π^{−s/2}Γ(s/2)` is a unit at every strip point too, so `archimedeanFactor · eulerPartial P` has order 0 (`completed_local_factor_orderAt_zero`, here) |
| local L-factor / idelic divisor at `p` | trivial — ζ is unramified at every finite place (`ε_p = 1`, conductor 1) |
| Dirichlet-character twists `L(s,χ)` | wrong zeros (a different L-function) and a **character** construction (excluded) |
| explicit formula, prime side | aggregate pairing, not per-zero; the Weil route (excluded by the novelty gate) |
| full Euler-product limit `P → ∞` | a **flow** (continuation across the wall) — refused |
| leading Taylor coefficient `ξ^{(m)}(ρ)/m!` graded by primes | the transcendence apex — reduces to the known-open problem, not constructible at a pinned annulus |
| spectral / Hilbert–Pólya operator sourcing the zeros | the arithmetic meaning of the zeros — the known-open apex, not a pinned local reading |

Every source is the zero map (prime factors are units), trivial (unramified), a character, the Weil
route, a flow, or the transcendence/spectral apex. The pinned, non-flow, non-character,
non-positivity source map is closed. Four kills now share **one** root cause: **both** weld sides are
analytically trivial at the strip — the `{σ_p}` side is a unit there (order 0, zero-free, unramified,
freely towered), and so is the `∂_s` archimedean factor `π^{−s/2}Γ(s/2)` (§5 Lean); their finite weld
product is a product of units, order 0. The zero of ζ is emergent only in the infinite-product limit.
So the two sides `∂_s` and `{σ_p}` have **disjoint carriers** — nonzero content lives on `Re s > 1`,
the divisor lives in the strip — and no pinned local reading, of either side or their weld, couples
them. This locates the weld obstruction exactly: it is not a symmetry defect (doc 106), not a
positivity gap (doc 105), but a **carrier-support disjointness**.

## 6. What this opens — reframed into the not-in-literature registers

**The register the kill lives in is the classical one, and that is why it is total.** Every entry in
§5 — order, atom, value, local factor, Taylor coefficient, ε-factor — is a statement about the
**value or the analytic order** of ξ and its factors in the `s`-plane. That is the register every
analytic number theorist already works in; a no-go there is expected, and a rescue there would be a
route others have walked. The disjoint-carrier obstruction is precisely a theorem *about the value/
order register*: in it, `∂_s` and `{σ_p}` cannot meet at a pinned configuration.

**Retraction.** The forward move stated in the previous version of this section — "change to the
adelic/idelic space so the two sides coexist" — is withdrawn. Tate's thesis, Weil's explicit formula
over the adeles, and Connes' spectral realization on the adele class space are exactly that change of
space, and they are heavily worked ground. By the lane's own principle (any route that goes where
researchers have already gone dead-ends sooner or later, and only the verified-absent frames can
carry a solution — approach §10), the adelic reframe is a by-precedent dead end. It is struck.

**The three verified-absent frames (approach §10, items 1–3) are the only non-dead-end ground:**

1. the **RH_{2^k} multiplicity-parity ladder** — grading RH by divisibility of off-line
   multiplicities; nobody does this (everyone's prior is on-line simplicity, which makes the grading
   invisible);
2. the **ℤ/2^k coarse-monodromy cocycle** `w_k` — the *coarsening* is the new degree of freedom;
   verified absent even against Bagchi, whose mechanism uses the count at full magnitude and never
   reduces it;
3. the **weight mismatch by a group action of unbounded order** (q62 template, approach §2.2) —
   a defect killed because the constraint side is invariant under an action under which the defect
   transforms with **unbounded weight**; no positivity (doc 105), no recurrence (Bagchi).

**Reframed question — the change is of register, not of subset of ℂ.** The killed `SigmaSourceMap`
is a *pointwise, local-order* reading (atoms = zeros of factors at ρ). That is exactly the register
this document proves is closed — and it is the register whose object is a **value/order**. The
lane's own not-in-literature object is not a value but a **torsion class**: the deck class of the
`2^k`-th-root torsor `w_k`, read on a **box annulus** encircling the zero (`XiDeck`, `DeckMultiZero`),
unbounded-order-graded over `k`. A contour around a strip zero is *not* a pinned point — it is a
pinned annulus, and the monodromy on it is a global-on-the-annulus quantity that the pointwise
carrier-disjointness does not touch. So the forward move is:

> **Replace the pointwise local-order source map (killed) with a deck-torsor reading of the weld on
> the box annulus, and ask the q62 question there:** is there an action *of unbounded order* on the
> `2^k`-root torsor tower that fixes the constraint data (FE `∂_s` side, Euler-positivity `{σ_p}`
> side) yet scales the divisor defect `w_k` with weight `2^k`? If yes, the off-line defect dies of
> weight mismatch — no positivity, no recurrence, no crossing of the wall.

This obeys §2.4: it bridges **divisor → monodromy** (the cocycle), never divisor → relation, so it
does not trip `ω = 0 ⇏ RH`.

**The precise crux, and its honest hazard.** The `{σ_p}` truncation tower is *free*
(`exists_global_pow_root_eulerPartial`: single-valued `2^k`-root on `Re s > 0`, deck class `0`); ξ's
tower is *obstructed* (deck class `= m mod 2^k`). Read statically, the difference torsor is just ξ's
own class — i.e. `RH_{2^k}` itself: **circular** (this is the same tautology that closed the pinned
symmetry in doc 106 §4). The escape, if there is one, is not the static class but the **relative
class of the two towers pulled to a common annulus base** — the free `{σ_p}` tower as the *reference
frame* against which ξ's obstruction is measured — together with a *genuinely unbounded-order* action
fixing that reference frame. Doc 106 proved the symmetries of the zero configuration in ℂ
(Klein-four, exponent 2) cannot supply the weight; the only unbounded-order action in view is the
deck/Kummer action itself, whose naive weight is the multiplicity (circular). **The open,
not-in-literature question is therefore sharp: is there an unbounded-order action on the relative
`{σ_p}`-vs-ξ root torsor — living in the coarse-monodromy register, not the value register — that
fixes the free reference tower and scales ξ's defect, without reducing to the multiplicity it is
supposed to constrain?** That relative monodromy class is the object to construct; it is not a value,
not an order, not a symmetry character, not a positivity, and not the adelic space — it is the one
thing left standing in the three verified-absent frames, and the burden is exactly to break its
circularity by making the `{σ_p}` free tower do reference-frame work that ξ's own tower cannot do for
itself.
