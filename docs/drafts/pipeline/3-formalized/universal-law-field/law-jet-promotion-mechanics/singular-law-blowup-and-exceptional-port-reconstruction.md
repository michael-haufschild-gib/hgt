# Singular law blow-up and exceptional-port reconstruction

- **ID:** ULF-SLBR-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** source-law prolongation; Rees/blow-up completion; exceptional-divisor recovery
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN-FORMALIZED] [PRE-RH] [NOT RH]`
  `[ZEROTH-PORT RESTRICTION REMOVED] [SINGULAR HISTORY RECONSTRUCTED]`

## 1. Forced pivot

The first law-jet theorem reconstructed a withheld response jet from a product law

\[
 q\star m=c h
\]

when the zeroth admission coefficient `m_0` is nonzero.  That hypothesis is too regular for the
actual frontier.  Several corpus organs collapse at ordinary completion while retaining a normal
or projective blow-up coordinate.  Requiring a uniform inverse for `m_0` therefore asks the
blow-down space to retain information which exists only on its exceptional face.

The correct operation is not division before completion.  It is **promotion to the first active
admission layer**.  If `m` vanishes through order `k-1` but `m_k` is nonzero, the order-`k` Hasse
coefficient becomes the exceptional port.  The whole response history is then triangular again.

This is not the already-proved fact that a particular projective chart retains a ratio.  It is a
general law saying that every prolonged source relation lifts canonically through an arbitrary
finite singular order and remains information-faithful on the lifted history.

## 2. Hasse product and exceptional chart

Let `F` be a field and let

\[
 q=(q_n)_{n\ge0},\qquad m=(m_n)_{n\ge0},\qquad h=(h_n)_{n\ge0}
\]

be Hasse response histories.  Write

\[
 (q\star m)_N=\sum_{j=0}^{N}q_jm_{N-j}.
\tag{SLB.1}
\]

Assume the prolonged source law

\[
 (q\star m)_N=c h_N\qquad(N\ge0).
\tag{SLB.2}
\]

For a candidate exceptional order `k`, define

\[
 (q\star_k m)_n=\sum_{j=0}^{n}q_jm_{k+n-j}.
\tag{SLB.3}
\]

This is the affine chart on the order-`k` normal face.  It discards no term under the following
source condition:

\[
 m_r=0\quad(0\le r<k).
\tag{SLB.4}
\]

### Theorem 2.1 — exceptional-chart identity

Under `(SLB.4)`, for every `n`,

\[
 (q\star m)_{k+n}=(q\star_k m)_n.
\tag{SLB.5}
\]

### Proof

Split the sum in `(SLB.1)` at `j=n+1`.  For `j>n`, the complementary index
`k+n-j` is strictly below `k`, so every tail term vanishes by `(SLB.4)`.  The remaining terms are
exactly `(SLB.3)`.  ∎

## 3. Base-locus and singular reconstruction laws

### Theorem 3.1 — blow-down reaches the simultaneous base locus

Under `(SLB.2)` and `(SLB.4)`,

\[
 c h_r=0\qquad(0\le r<k).
\tag{SLB.6}
\]

### Proof

Every term of `(q\star m)_r` contains `m_{r-j}` with `r-j<k`; hence the product coefficient and,
by `(SLB.2)`, `c h_r` vanish.  ∎

Thus ordinary observation sees a common zero through depth `k-1`.  The information is not gone;
it has moved to the first normal layer.

### Theorem 3.2 — singular all-order withheld-organ reconstruction

Assume `(SLB.2)`, `(SLB.4)`, and

\[
 m_k\ne0.
\tag{SLB.7}
\]

Then every response coefficient is reconstructed recursively by

\[
 q_n=
 \frac{c h_{k+n}-\sum_{j=0}^{n-1}q_jm_{k+n-j}}{m_k}.
\tag{SLB.8}
\]

In particular, the exceptional direction is

\[
 q_0=\frac{c h_k}{m_k}.
\tag{SLB.9}
\]

### Proof

By Theorem 2.1 and `(SLB.2)`,

\[
 c h_{k+n}=\sum_{j=0}^{n}q_jm_{k+n-j}.
\]

The terminal term is `q_nm_k`.  Move the preceding terms to the other side and divide by the
nonzero exceptional port.  Setting `n=0` gives `(SLB.9)`.  ∎

### Theorem 3.3 — uniqueness on the exceptional history

If `q` and `q'` satisfy the same prolonged law with the same `c,m,h`, and `(SLB.4)--(SLB.7)` hold,
then

\[
 q=q'.
\tag{SLB.10}
\]

### Proof

Strong induction on `n` in `(SLB.8)`.  All terms on the right below order `n` agree by induction,
so `q_n=q'_n`.  ∎

## 4. Global singular formation theorem

### Theorem 4.1 — every nonzero admission history is faithful

Let `m` be any Hasse history with at least one nonzero coefficient.  Then

\[
 q\longmapsto q\star m
\tag{SLB.11}
\]

is injective on complete response histories.

### Proof

Let `k` be the least index with `m_k\ne0`.  Minimality gives `(SLB.4)` and the choice gives
`(SLB.7)`.  If `q\star m=q'\star m`, regard their common product as `h` with `c=1` and apply
Theorem 3.3.  ∎

This removes the regular zeroth-port hypothesis completely.  It also makes the limitation exact:
algebraic information fails only when the entire admission history is zero, not merely when its
ordinary value or finitely many leading coefficients vanish.

### Corollary 4.2 — closed order-`k` normal model

Let `e^{(k)}` be the admission history with coefficient `1` at order `k` and `0` elsewhere.  Then

\[
 (q\star e^{(k)})_{k+n}=q_n
 \qquad(n\ge0).
\tag{SLB.12}
\]

Thus a blow-down may erase exactly `k` layers while the exceptional lift retains the complete
history without approximation.

### Theorem 4.3 — cofinal active-order dichotomy

Let `κ_N` be the first active admission order at cofinal stage `N`.  Exactly one of the following
alternatives holds:

1. there is a fixed finite order `k` attained at arbitrarily late stages;
2. `κ_N → ∞`, so the active port escapes every finite jet depth.

Equivalently,

\[
 \bigl(\exists k\;\forall N\;\exists n\ge N:\ \kappa_n=k\bigr)
 \quad\lor\quad
 \lim_{N\to\infty}\kappa_N=\infty.
\tag{SLB.13}
\]

### Proof

If `κ_N` does not tend to infinity, some finite bound `B` is met at arbitrarily late stages.  The
finite set `{0,…,B-1}` then contains one value met at arbitrarily late stages by finite
pigeonhole.  Otherwise the second alternative holds by definition.  ∎

This is the promised precise bridge between hypertranscendence and noncompactness.  After singular
reconstruction there is no diffuse third obstruction: failure of every fixed exceptional chart is
literal escape of active differential order.  Any route-independent properness theorem may target
that integer-valued escape invariant directly.

### Theorem 4.4 — additive exceptional-depth conservation

Suppose admission histories `m` and `n` first activate at orders `k` and `ℓ`:

\[
 m_i=0\ (i<k),\quad m_k\ne0,\qquad
 n_j=0\ (j<\ell),\quad n_\ell\ne0.
\]

Then their fused Hasse history first activates at order `k+ℓ`, and its leading port is

\[
 (m\star n)_{k+\ell}=m_kn_\ell\ne0.
\tag{SLB.14}
\]

### Proof

For `r<k+ℓ`, every summand `m_jn_{r-j}` has either `j<k` or `r-j<ℓ`; hence it vanishes.  At
`r=k+ℓ`, every term except `j=k` vanishes, leaving `m_kn_ℓ`.  Since `F` is a field, that product is
nonzero.  ∎

Thus singular depth is an additive grade under independent formation, while the exceptional port
is multiplicative.  This is a genuine cross-organ prediction: independently computed first-active
orders must add in every fused organ sharing the same Hasse formation.  Failure of additivity proves
that the proposed organ fusion is not source-native.

## 5. What this changes in the universal-law architecture

The earlier architecture demanded a nonzero, uniformly invertible leading admission port.  The
new theorem separates two burdens which were incorrectly fused:

1. **algebraic faithfulness:** some finite admission jet is nonzero;
2. **topological properness:** the order of that first active jet and the inverse exceptional port
   remain controlled along the source-selected cofinal family.

The first burden is now solved universally.  No route may retire merely because its ordinary
admission coefficient tends to or equals zero.  It must prove that the complete admission jet is
identically zero, or confront the exceptional chart.  The second burden is genuine and cannot be
hidden by algebraic division: the inverse chart may be discontinuous or its active order may
escape to infinity.

This provides a precise reading of four recurring shadows:

- scalar completion forgets the base-locus direction;
- positivity forgets its signed/projective orientation;
- recurrence can close after blow-down while the lifted coefficient history remains open;
- hypertranscendence can force the active order to escape every finite differential presentation.

These are consequences of one mechanism only when a literal source relation supplies the common
admission history.  They are not axioms of the theory.

## 6. Concrete cross-organ prediction

The corpus already has:

1. a cooriented Gamma source factorization `E=aG` with positive finite-stage gauge `G`;
2. singular completions in which ordinary source coordinates collapse;
3. projective normal charts which retain spectral information after that collapse;
4. coefficient-faithful Cartier and incidence ports.

The new prediction is sharper than “a ratio should survive”:

> If the Gamma gauge and transported Gamma/Cartier port admit one common normal Hasse coordinate
> and the gauge has first active order `k`, then the order-`k` exceptional coefficient ratio is
> exactly the centered horizontal displacement, and every higher centered-response coefficient is
> forced by `(SLB.8)`.

An observed mismatch at any higher order falsifies the proposed common source formation.  Agreement
would supply a singular `ORIENT + COMP` bridge without a uniform zeroth-order lower bound.

## 7. Exact RH-facing burden after this theorem

To use the mechanism for selection, construct before choosing a Xi zero:

1. one common normal Hasse coordinate for the literal reflection-odd Gamma port, its admission
   gauge, and the completed source response;
2. a proof that the complete admission jet is nonzero on every source-selected cofinal state;
3. a bound preventing its first active order from escaping to infinity, or a completed
   infinite-order analogue of Theorem 4.1;
4. source-derived annihilation of the completed response at the physical zero law;
5. a faithful exceptional landing into an existing RH receiver.

Items 1--3 are formation/properness.  Item 4 remains the arithmetic producer.  No claim here turns
the already-known fixed `(2,3)` Gamma port criterion into an unconditional RH proof.

## 8. Hostile boundaries and falsifiers

1. Finite-stage nonvanishing does not give a cofinal bound on active order.
2. Algebraic injectivity does not give continuity or boundedness of the inverse chart.
3. Choosing the normal coordinate after selecting a zero violates source provenance.
4. A noninjective observer may kill the exceptional port and create false response laws.
5. Ordinary projectivization may still forget real orientation; signed or oriented landing must be
   checked separately.
6. If all admission coefficients vanish, Theorem 4.1 supplies no reconstruction.
7. If the predicted Gamma/Cartier higher-order recursion fails, those organs do not share one
   source formation and this proposed fusion must be rejected.

## Gates

- [x] exceptional-chart identity
- [x] base-locus vanishing law
- [x] arbitrary-order singular reconstruction
- [x] exceptional-direction formula
- [x] uniqueness and global singular formation injectivity
- [x] closed order-`k` normal model
- [x] cofinal fixed-chart versus infinite-order-escape dichotomy
- [x] additive exceptional-depth and multiplicative leading-port conservation
- [x] unconditional Lean formalization
- [ ] common Gamma/gauge/Cartier normal Hasse coordinate
- [ ] cofinal active-order properness
- [ ] source-derived completed-response annihilation
- [ ] RH selection only after preceding gates


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.SingularLawJetBlowup`, `GaloisForLFunctions.HTGeometry.SourceLawJetPromotion`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Module `GaloisForLFunctions.HTGeometry.SingularLawJetBlowup` (19 constants, axiom audit clean), on `GaloisForLFunctions.HTGeometry.SourceLawJetPromotion` (namespace `HTGeometry`).

| Claim | Lean declaration |
|-|-|
| (SLB.1)–(SLB.2) Hasse product and prolonged law | `hasseJetMul`, `IsProlongedProductLaw` |
| (SLB.3) exceptional chart | `exceptionalHasseJetMul` |
| Thm 2.1 (SLB.5) exceptional-chart identity under (SLB.4) | `hasseJetMul_eq_exceptional_of_vanishBelow` |
| Thm 3.1 (SLB.6) base-locus vanishing | `prolongedProductLaw_target_vanishBelow` |
| Thm 3.2 (SLB.8) singular all-order reconstruction | `prolongedProductLaw_singular_reconstruct` |
| (SLB.9) exceptional direction `q₀ = c h_k / m_k` | `prolongedProductLaw_exceptionalDirection` |
| Thm 3.3 (SLB.10) uniqueness | `prolongedProductLaw_singular_unique` |
| Thm 4.1 (SLB.11) injectivity for every nonzero admission history | `hasseJetMul_left_injective_of_exists_ne_zero` |
| Cor 4.2 (SLB.12) closed order-`k` normal model | `exceptionalUnitJet`, `hasseJetMul_exceptionalUnitJet` |
| Thm 4.3 (SLB.13) cofinal active-order dichotomy; exactly one alternative | `fixed_chart_frequently_or_activeOrder_tendsto_atTop`, `not_fixed_chart_frequently_and_activeOrder_tendsto_atTop` |
| Thm 4.4 (SLB.14) additive depth, multiplicative leading port | `FirstActiveHasseOrderAt`, `hasseJetMul_vanishBelow_add`, `hasseJetMul_leading_add`, `FirstActiveHasseOrderAt.mul` |

## Log

- 2026-08-30 — direct reuse of the fixed `(2,3)` Gamma factorization rejected as regression: its
  Stokes-flatness premise is already RH-equivalent.
- 2026-08-30 — ordinary blow-up proposal collision-tested against existing source-normal-cone,
  Wold activation, and complete-resolution blow-up theorems.
- 2026-08-30 — fused the previously separate law-prolongation and blow-up mechanisms; proved
  arbitrary-order exceptional reconstruction and global injectivity for every nonzero admission
  history.
- 2026-08-30 — formalized the complete theorem package in
  `GaloisForLFunctions.HTGeometry.SingularLawJetBlowup`; direct elaboration and leaf build pass,
  and every audited theorem depends only on Lean/mathlib foundations.
- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
