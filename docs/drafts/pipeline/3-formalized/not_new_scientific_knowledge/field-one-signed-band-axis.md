# The signed band axis and its base-change relation

- **ID:** field-one-signed-band-axis
- **Stage:** 3-formalized
- **Type:** THEOREM / CONSTRUCTION (Lean)
- **Labels:** `[LITERATURE] [BRIDGE] [PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Depends on:** `field-one-multiplicative-core`,
  `field-one-additive-fork`
- **Source:** Baker–Jin–Lorscheid, *New building blocks for F₁-geometry:
  bands and band schemes* (JLMS 2025).
- **Statement:** The initial band is

  `F₁±={0,1,−1}`

  with null set consisting of balanced formal sums of `1` and `−1`. Its
  pointed-monoid carrier is not the two-element multiplicative core. Forgetting
  null relations yields the signed multiplicative extension whose contracted
  ring algebra is the group ring `R[C₂]`; imposing the null relation
  `1+(−1)=0` specializes the signed generator to `−1` and returns `R`.

## Definitions

For a pointed monoid `B`, its ambient semiring `B⁺` consists of finite formal
sums of nonzero elements of `B`; the monoid zero is identified with the empty
sum.

A band is a pointed monoid `B` with a semiring ideal `N_B⊆B⁺`, the null set,
such that every `a∈B` has a unique `b∈B` with `a+b∈N_B`. The element is written
`−a`.

For `F₁±`, nonzero multiplication is the cyclic group
`C₂={1,−1}` and

`N_(F₁±)={n·1+n·(−1) | n∈N}`.

## Complete paper proof

### Band axioms

Balanced sums contain the empty sum. Sums of balanced sums are balanced.
Multiplication by `1` preserves both counts, while multiplication by `−1`
swaps them; multiplication by zero gives the empty sum. Thus the balanced
sums form an ideal of the ambient semiring.

For `a=0`, only `b=0` makes `a+b` null because a singleton nonzero sign is
unbalanced. For `a=1`, equality of positive and negative counts forces
`b=−1`; for `a=−1`, it forces `b=1`. Therefore every element has a unique
additive inverse. This constructs a band.

Given any band `B`, a morphism from `F₁±` must send `0` to `0`, `1` to `1`,
and `−1` to the unique additive inverse of `1`. These values preserve
multiplication because band axioms imply `(-1)²=1`, and preserve every
balanced null sum. Hence the morphism exists and is unique: `F₁±` is initial
in bands. If all nonzero elements are required to be invertible, the same
proof gives initiality in idylls.

### Carrier separation

The pointed monoid underlying `F₁±` has three distinct elements. The
multiplicative core `F₁={0,1}` has two. Hence no pointed-monoid isomorphism
exists between them. There is a multiplicative collapse

`F₁± → F₁`, `−1↦1`,

but it forgets the null relation. As a band morphism its natural two-element
target is instead the Krasner hyperfield, whose null set contains every
formal sum with at least two copies of `1`.

### Base-change distinction

Forget the null relation. The nonzero monoid is `C₂`, so contracted scalar
extension is the group algebra

`R[C₂] ≃ R[u]/(u²−1)`.

The band null relation adds `1+u=0`, equivalently `u=−1`. Therefore band base
extension is

`R[u]/(u²−1,u+1) ≃ R[u]/(u+1) ≃ R`.

The first isomorphism follows since `u+1=0` implies `u²−1=0`; the second is
evaluation at `u=−1`. Thus forgetting relational addition changes scalar
extension and cannot be treated as harmless erasure. ∎

## Hostile audit

1. **`F₁±=F₁` — `FALSE`.** Their carriers and universal properties differ.
2. **Sign collapse preserves band data — `FALSE` without a Krasner-type
   target null set.**
3. **Multiplicative and band base extension coincide — `FALSE`.** They are
   `R[C₂]` and `R`, respectively.
4. **Bands settle every approach — `FALSE`.** They organize relational
   addition and matroid/tropical applications, but do not replace λ-descent,
   generalized rings, `Γ`-rings, or analytic sites.
5. **Latest module theory makes bands equivalent to hyperring schemes —
   `FALSE`.** Current 2026 work proves robust categorical properties for band
   modules while reporting incompatibility with affine hyperring scheme
   theories.

**Verdict:** `REDISCOVERED` / `BRIDGE`.

## Gates

- [x] 0 → 1: current band definition and initial objects audited.
- [x] 1 → 2: band axioms, carrier separation, and base-change distinction
  proved on paper.
- [x] 2 → 3: signed carrier, separation, and evaluation quotient formalized;
  axiom audit complete.
- [ ] 3 → 4: publication-ready extraction.

## Lean certificate

- **Module:** `GaloisForLFunctions.HTGeometry.FieldOneSignedAxis`
- **Theorems:** `signedNull_add`, `signedNull_scalar`,
  `signed_additiveInverse_unique`, `no_signed_embedding_into_fieldOne`,
  `no_signed_equiv_fieldOne`, `no_literal_common_carrier`,
  `signedBandBaseChangeEquiv`, `signedBandGenerator_specializes`
- **Audit:** direct `lake env lean` and final targeted `lake build` passed;
  `#print axioms` reports only standard Lean principles.

## No-go closure

- **Exact killing theorem:** an atlas node cannot be identified with its
  multiplicative shadow when forgotten null relations change base extension.
- **Strongest positive survivor:** enhancements should carry an explicit
  forgetful map plus a record of which scalar-extension relations are lost.
- **Status:** survivor is `[PAPER-PROVED] [LEAN-FORMALIZED]`.

## Log

- 2026-07-26 — current 2025 band and 2026 band-module literature audited;
  carrier and base-change separation proved.
- 2026-07-26 — formalized unconditionally; targeted build, axiom audit, and
  project lint passed; relational-addition axis integrated without treating
  it as a universal replacement.
