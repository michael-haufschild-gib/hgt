# Horizontal-singleton zero fibers have positive density and satisfy RH pointwise

- **ID:** `horizontal-singleton-zero-fibers`
- **Stage:** 2-fully-proven / not-new-scientific-knowledge
- **Type:** THEOREM / BRIDGE
- **Scientific status:** `[PAPER-PROVED] [LEAN-POINTWISE-PROVED] [BRIDGE] [INSIGNIFICANT AS A STANDALONE PAPER]`
- **Statement:** Let `h(gamma)` be the total analytic multiplicity of all nontrivial zeta zeros
  with imaginary part `gamma`, and let `H_1(T)` count the positive ordinates at most `T` for which
  `h(gamma)=1`. Every such fiber consists of one simple critical-line zero. Moreover
  `H_1(T) >= N_{0,s}(T) - (N(T)-N_0(T))/2`. Consequently at least `0.116158438` of all
  nontrivial-zero copies lie in singleton horizontal fibers in lower density.

## Goal

Produce a non-vacuous intrinsic group of zeta zeros whose members lie on the critical line for a
reason different from their original mollifier or sign-change discovery. Membership is defined in
the full zero divisor by horizontal isolation, without inserting `Re rho=1/2`. The pointwise forcing
mechanism is the fixed-point law for functional-equation reflection, while positive density is a
separate global counting theorem.

## Exact definitions

For `T>0`, let:

- `N(T)` count all nontrivial zeros `rho=beta+i gamma` with `0<gamma<=T`, with multiplicity;
- `N_0(T)` count those copies with `beta=1/2`;
- `N_{0,s}(T)` count simple critical-line zeros;
- `h(gamma)` be the sum of multiplicities over every zero with imaginary part `gamma`;
- `H_1(T)=#{gamma in (0,T] : h(gamma)=1}`.

The endpoint convention is immaterial asymptotically but must be identical in every finite
inequality.

## Paper proof

### Pointwise fiber theorem

`[PAPER-PROVED]` Functional equation and Schwarz symmetry send a zero
`rho=beta+i gamma` of multiplicity `m` to

```text
rho^star = 1-conj(rho) = 1-beta+i gamma
```

with the same multiplicity. Thus reflection acts within each horizontal fiber. If `h(gamma)=1`,
the reflected zero copy must equal the original copy, so `beta=1/2`; total fiber multiplicity one
also makes the zero simple.

### Finite counting inequality

`[PAPER-PROVED]` Start with the `N_{0,s}(T)` simple critical-line ordinates. If one is not
a singleton horizontal fiber, every additional zero at that ordinate is off the line: another copy
at the central point would contradict simplicity. Every off-line copy brings its distinct reflected
copy at the same ordinate with equal multiplicity. Hence each spoiled simple critical ordinate
consumes at least two copies counted by `N(T)-N_0(T)`. Distinct ordinates consume disjoint copies, so

```text
2 (N_{0,s}(T)-H_1(T)) <= N(T)-N_0(T),
H_1(T) >= N_{0,s}(T) - (N(T)-N_0(T))/2.                 (1)
```

Consequently, if

```text
liminf N_0(T)/N(T) >= kappa,
liminf N_{0,s}(T)/N(T) >= kappa_star,
```

then

```text
liminf H_1(T)/N(T) >= kappa_star-(1-kappa)/2.           (2)
```

Pratt--Robles--Zaharescu--Zeindler prove the unconditional bounds

```text
kappa >= 0.417293962,
kappa_star >= 0.407511457.
```

Therefore `(2)` gives the exact advertised decimal lower bound

```text
0.407511457 + 0.417293962/2 - 1/2 = 0.116158438.
```

The liminf passage is valid because for real-valued functions `a,b`,
`liminf(a+b) >= liminf a + liminf b`, and multiplication by the positive scalar `1/2` commutes
with `liminf`. The identical strict or closed height convention is used in all four finite counts.

## Why this is a group theorem rather than an RH restatement

The predicate `h(gamma)=1` does not mention the critical line and can fail under RH-independent
horizontal collisions. Equation `(1)` is not a tautological recount of `N_0`: it removes every
simple critical zero whose ordinate is shared with any hypothetical off-line pair and still leaves
a positive candidate density. The proof of location for a surviving member uses only the
fixed-point structure of functional-equation reflection.

## Primary-source and novelty audit

- Pratt--Robles--Zaharescu--Zeindler, *More than five-twelfths of the zeros of zeta are on the
  critical line*, Research in the Mathematical Sciences 7 (2020), Article 2,
  DOI `10.1007/s40687-019-0199-8`: defines `N`, `N_0`, and `kappa`, identifies `kappa_star` as the
  simple-critical-zero proportion, and proves the two exact constants used above.
- H. M. Bui, *Critical zeros of the Riemann zeta-function*, arXiv:`1410.2433`: explicitly defines
  `kappa_star = liminf N_0^*(T)/N(T)` with `N_0^*` counting simple critical zeros.
- Goldston--Lee--Schettler--Suriajaya, arXiv:`2503.15449v4`, section 7, and
  Goldston--Suriajaya, arXiv:`2511.20059v2`, section 7: define horizontal multiplicity and explicitly
  note that horizontal multiplicity one means one simple critical zero.
- Neither horizontal-multiplicity paper derives the unconditional inequality `(1)` or the
  `0.116158438` lower density. Their density theorems use HMH, PCC, or a narrow-box hypothesis.
  Searches for the exact constant and same-ordinate charging formula found no prior statement.
  This is encouraging but is not a proof of novelty.

## Dual-gate verdict

**Verdict: `BRIDGE / INSIGNIFICANT AS A STANDALONE PAPER`.**

The exact decimal corollary may be absent from the searched literature, but its proof is a routine
two-line combination of the already-published PRZZ proportions with the elementary reflection
pairing already explicit in the horizontal-multiplicity papers. It introduces no new analytic
estimate, no new zero-detecting mechanism, no source-side invariant, and no improvement in the
known proportion of critical or simple-critical zeros. It therefore fails the significance gate
even if priority for the displayed inequality were eventually established.

The result is worth retaining as corpus support and as a normalization check for future horizontal
multiplicity work. It is not new scientific knowledge worth submitting as its own paper. A
paper-worthy successor must prove a new unconditional horizontal-multiplicity estimate from source
data, improve a known zero proportion, or construct a non-vacuous source-defined stratum not
obtained by filtering already-known critical zeros.

## Hostile attacks closed

1. `[CLOSED]` `N_0^*` counts simple critical zeros and its normalization is `N_0^*/N`; this is
   explicit in Bui and is the `kappa_star` quantity used by PRZZ.
2. `[SEARCH CLOSED; NOVELTY STILL UNVERIFIED]` No unconditional singleton-fiber density or exact
   charging inequality was found in the recent horizontal-multiplicity literature or citation
   descendants searched.
3. `[CLOSED]` A spoiled simple central ordinate consumes at least two off-line copies: a second
   central copy contradicts simplicity, while every off-line copy has a distinct equal-order
   reflection. Distinct ordinates give disjoint charges.
4. `[LIMITATION]` Distinguish intrinsic zero-group membership from a source-produced certificate. The
   theorem gives a genuine group and positive density, but deciding membership may still require
   full-divisor information.
5. `[CLOSED]` The corpus comparison found no prior positive-density horizontal-singleton theorem.
   Fixed-window, multiplicity-ladder, susceptibility, and completed-flux objects are consumers or
   conditional source packages; finite passports prove that finite local labels cannot select the
   line.

## Lean target

The exact actual-Xi pointwise theorem is formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/HorizontalSingletonZeroFiber.lean`:

- `two_le_xiHorizontalMultiplicity_of_offLine`;
- `xiHorizontalSingletonZero_re_eq_half`;
- `xiHorizontalSingletonZero_order_eq_one`.

The finite global charging inequality `(1)` and the asymptotic numerical corollary are not promoted
to Lean declarations until the project's zero-counting API and the cited analytic proportion
bounds have unconditional formal providers. No hypothesis wrapper or axiom substitutes for them.

## Gates

- [x] 0 -> 1: exact intrinsic group, pointwise mechanism, finite charging inequality, hostile tests,
      and source/target distinction stated
- [x] external primary-source audit of both density inputs and the horizontal-multiplicity parent
- [x] hostile proof audit of `(1)` and liminf passage `(2)`
- [x] 1 -> 2: dependency-closed paper theorem with exact published constants and citations
- [x] exact unconditional Xi pointwise group theorem and simplicity theorem in Lean
- [ ] formalize the finite global counting law and its analytic density inputs before 2 -> 3
- [x] scientific novelty and significance audit: bridge-grade and not standalone-paper worthy

## Log

- 2026-07-17 — Created from the zero-group audit. The first live candidate is the horizontal
  singleton fiber, not a proof-labelled partition: pointwise location comes from symmetry, while
  positive density is charged against the globally available critical/simple-critical proportions.
- 2026-07-17 — Hostile primary-source audit closed the paper theorem with lower density
  `0.116158438`. Pointwise critical-line placement and simplicity were formalized for the actual Xi
  divisor. The card remains in `needs-audit`: the quantitative corollary appears absent from the
  searched literature but the dual novelty/significance gate is not yet closed.
- 2026-07-17 — Corrective dual-gate audit: demoted to `not_new_scientific_knowledge`. The theorem is
  correct and useful, but the quantitative statement is a routine corollary of PRZZ plus elementary
  reflection pairing and is not worth a standalone paper.

## Lean status update (2026-08-19)

`formal/GaloisForLFunctions/RHTower/HorizontalSingletonFiberCharging.lean` now formalizes the
**finite global counting law** and the **density passage**, unconditionally and with no hypothesis
wrapper, on the actual `xi` divisor:

- `xiZeroCount`, `xiCriticalZeroCount`, `xiOffLineZeroCount`, `xiSimpleCriticalZeroCount`,
  `xiSingletonFiberCount` — the four counts `N`, `N₀`, `N − N₀`, `N₀,s`, `H₁` at height `T`,
  built from the existing `stripFinsetLe` Xi-divisor API;
- `criticalFiber_eq_singleton` — an ordinate carries at most one critical-line point;
- `two_le_offLineFiber_sum` — a spoiled simple critical ordinate consumes at least two off-line
  copies (the reflection-charging step);
- `two_mul_xiSimpleCriticalZeroCount_le` — inequality `(1)` in the form
  `2·N₀,s(T) ≤ 2·H₁(T) + (N(T) − N₀(T))`;
- `xiSimpleCriticalZeroCount_sub_le_xiSingletonFiberCount` — the same over `ℝ` in the card's
  displayed form;
- `xiSimpleCriticalRatio_sub_le_xiSingletonFiberRatio` — the normalized law, valid also at heights
  with `N(T) = 0`;
- `le_liminf_xiSingletonFiberRatio` — the liminf passage `(2)`;
- `prattRoblesZaharescuZeindler_singleton_density` — the exact `0.116158438` corollary as an
  unconditional implication from the two published proportions.

`#print axioms` on all of these gives only `propext, Classical.choice, Quot.sound`.

Remaining for 2 -> 3: unconditional Lean providers for the two **cited analytic density inputs**
(`κ ≥ 0.417293962` and `κ_* ≥ 0.407511457`, Pratt--Robles--Zaharescu--Zeindler).  These are not
proved by this card; they are the mollified-moment lane whose substrate is being built on
`hardy-critical-line-moment-anchor`.
