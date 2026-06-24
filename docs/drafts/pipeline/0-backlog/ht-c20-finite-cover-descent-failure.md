# Finite-cover descent failure — no ramified coordinate change creates a handle

- **ID:** ht-c20-finite-cover-descent-failure
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C20
- **Statement:** A generic local HT germ does not become differentially algebraic after pullback to a finite algebraic cover of the independent variable; finite ramified changes of coordinate create no finite algebraic-differential handle.

## Goal
Block a **hidden finite cover** on which `f` simplifies. Door: algebraic functions simplify on finite covers; HT should resist this descent trick.

## Door grade (hint)
**BRIDGE-likely.** Pullback along `x=φ(t)`, `φ` algebraic, conjugates a differential polynomial; DA is preserved under finite covers, so descent cannot manufacture a handle without one upstairs.

## Approach
Elimination test: if `f∘φ` is DA over `K(t)` then `f` is DA over `K(x)` (DA stable under finite algebraic base change / Kolchin) ⇒ contradiction ⇒ BRIDGE. Methods: 3 reverse, 14 weaken, 18 right theorem (DA descent).

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C20; C30 (base enrichment — same relativity theme).

## Log
- 2026-06-20 — created in 0-backlog from bucket C20.

## 2026-06-24 Haiku strengthening -- finite algebraic covers cannot manufacture DA

### Promptability audit

No computation is involved. This is exactly the kind of statement a direct specialist prompt can recover from
standard differential algebra:

> Does differential algebraicity descend along a finite algebraic extension of the independent-variable field?

Yes. Therefore this card is a proved gatekeeper/source tool, not a candidate for new external knowledge.

### Theorem `[PROVED HERE / STANDARD]`

Let `K` be a differential field of characteristic zero and let `L/K` be an algebraic differential-field extension.
For any element `y` in a common differential extension,

```text
y is differentially algebraic over K  iff  y is differentially algebraic over L.
```

Consequently, if an analytic germ `f(x)` is HT over `C(x)`, then pulling it back along any finite algebraic cover
`x=phi(t)` cannot make it DA over `C(t)`. In particular, finite ramified coordinate changes create no hidden
finite algebraic-differential handle.

### Proof

Use the transcendence-degree criterion for DA elements. The element `y` is DA over a differential field `F` iff

```text
trdeg_F F<y, y', y'', ...> < infinity.
```

Since `L/K` is algebraic, adjoining `L` does not change transcendence degree:

```text
trdeg_K K<y, y', ...> = trdeg_L L<y, y', ...>.
```

Thus the finiteness condition is equivalent over `K` and over `L`. Applying this with
`K=C(x)` and `L=C(t)` algebraic over `K` via `x=phi(t)` proves the finite-cover statement. Ramification is not a
separate escape hatch: it is part of the same algebraic field extension after passing to the cover's local
parameter. ∎

### Local-coordinate corollary

If `phi` is a locally invertible DA coordinate change, then `f` is DA iff `f o phi` is DA. One direction is DA
closure under composition; the other uses DA closure under local inverse and composition. A finite algebraic
coordinate branch is a special case at an unramified point, while the field-extension theorem above covers the
ramified finite-cover formulation.

### Boundary

This theorem separates three categories:

1. **Finite algebraic covers:** cannot hide HT by descent.
2. **Local DA diffeomorphisms:** cannot hide HT by coordinate change.
3. **Arbitrary analytic local diffeomorphisms:** can erase HT completely, since a locally univalent HT germ `H`
   satisfies `H o H^{-1}=id` on a local inverse branch.

So HT is invariant under the DA pseudogroup but not under the full analytic pseudogroup. This is a useful native
boundary for the project, but its proof uses standard DA closure/descent; do not promote it as a significant new
HT theorem without an additional global constraint beyond local finite covers.

### Source anchor

Ait El Manssour--Sattelberger--Teguia, *D-Algebraic Functions* (arXiv:2301.02512), Lemma 3.4 gives the
transcendence-degree criterion; Propositions 3.8 and 3.11 give closure under composition and functional inverse.
The finite algebraic extension descent above is the same criterion applied before and after algebraic base change.
