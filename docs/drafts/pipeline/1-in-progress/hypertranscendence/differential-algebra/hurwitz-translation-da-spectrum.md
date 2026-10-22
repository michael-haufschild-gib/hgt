# The translation DA spectrum of the Hurwitz zeta function

- **ID:** `hurwitz-translation-da-spectrum`
- **Stage:** 1-in-progress — my own conjecture, easy direction proved, hard direction open
- **Type:** CONJECTURE + partial theorem / DA-SPECTRUM CLASSIFICATION
- **Author of this card:** this agent. Not derived from any existing registry entry; the
  elliptic-gamma rank-three card is cited only as the *rank-three analogue in a different variable*,
  and no part of its proof is used.

## Statement

Fix `s ∈ ℂ \ ℤ`. For `h ∈ ℂ` put

```text
d_h(z) = H(s, z+h) - H(s, z)
```

where `H(s, ·)` is the Hurwitz zeta function in its second variable. Define the **translation DA
spectrum**

```text
Spec_DA(H(s,·)) = { h ∈ ℂ : d_h is differentially algebraic over ℂ(z) }.
```

> **CONJECTURE.** `Spec_DA(H(s,·)) = ℤ` for every `s ∉ ℤ`.
>
> **Matroid form.** For `h_1,…,h_n ∈ ℂ`, `dtrdeg_{ℂ(z)} ℂ(z)⟨d_{h_1},…,d_{h_n}⟩_δ` equals the number
> of distinct nonzero cosets among `h_i + ℤ` in `ℂ/ℤ`.

## Why this direction is not covered by existing work

The corpus's `IntegerTranslationDifferentialMatroid` classifies the family `{H(s+k, ·)}` by
translations of the **exponent** `s`. The present card translates the **argument** `z`. These are
different group actions on different variables, and neither matroid implies the other. Literature
audit (recorded below) found Hölder's hypertranscendence of `Γ` and the modern difference-Galois
machinery, but no determination of this spectrum.

## The structural step `[PROVED HERE]`

Let `σ` denote shift by one in `z`. From the defining recursion `H(s,z+1) - H(s,z) = -z^{-s}`:

```text
σ(d_h) - d_h = [H(s,z+h+1) - H(s,z+h)] - [H(s,z+1) - H(s,z)]
             = -(z+h)^{-s} + z^{-s}
             = z^{-s} - (z+h)^{-s}  =:  b_h(z).
```

**Every translation defect is a solution of a first-order inhomogeneous `σ`-difference equation whose
inhomogeneity lies in the explicit differentially algebraic field `ℂ(z, z^{-s}, (z+h)^{-s})`.**

This is the reduction the whole card rests on. It converts a hypertranscendence question about a
zeta-type function into a *telescoping* question about an explicit elementary inhomogeneity.

## Easy direction `[PROVED HERE]`

`ℤ ⊆ Spec_DA`. Iterating the recursion, for `n ≥ 1`

```text
d_n(z) = H(s,z+n) - H(s,z) = - Σ_{k=0}^{n-1} (z+k)^{-s},
```

and `d_{-n}(z) = + Σ_{k=1}^{n} (z-k)^{-s}`, `d_0 = 0`. Each `(z+k)^{-s}` is DA over `ℂ(z)`: it
satisfies the first-order algebraic ODE `(z+k) y' + s y = 0`. Differentially algebraic meromorphic
functions form a differential field, so a finite sum is DA. Hence `d_n` is DA for every `n ∈ ℤ`.

*(This direction alone is elementary and is not claimed as new — it is the iterated recursion. It is
recorded because the Lean formalization needs it, and because the conjecture's content is the
converse.)*

## The converse — proof modulo one independence input `[PROVED HERE, conditional]`

### Correction to the criterion

Hardouin--Singer must be stated with **constant-coefficient** operators. With `ℂ(z)`-coefficients the
criterion is vacuous: `L = zδ + 1` annihilates `1/z`, so `L(b) = 0 = σ(0) - 0` would make `ψ`
differentially algebraic, contradicting Hölder. The correct form: a solution `y` of `σ(y) - y = b` is
DA over `K` **iff** there are `L = Σ c_i δ^i` with `c_i ∈ ℂ` not all zero, and `g ∈ K`, with
`L(b) = σ(g) - g`.

### The argument

Put `u_k = (z+k)^{-s}` and `v_k = (z+h+k)^{-s}`, so `σ u_k = u_{k+1}`, `σ v_k = v_{k+1}`, and
`K = ℂ(z)({u_k}, {v_k})` is both `σ`- and `δ`-stable (`δ u_k = -s (z+k)^{-1} u_k`). For constant
`c_i`,

```text
L(b_h) = P(z) u_0 - Q(z) v_0,
P = Σ_i c_i a_i z^{-i},   Q = Σ_i c_i a_i (z+h)^{-i},   a_i = ∏_{j<i} (-s-j).
```

Suppose `h ∉ ℤ`, so the index families `{u_k}` and `{v_k}` are disjoint. Take `g` linear in the
generators, `g = Σ_k p_k(z) u_k + Σ_k q_k(z) v_k` (the reduction to the linear part is step (R) below).
Since `σ(p_k u_k) = p_k(z+1) u_{k+1}`,

```text
σ(g) - g = Σ_k [ p_{k-1}(z+1) - p_k(z) ] u_k  +  Σ_k [ q_{k-1}(z+1) - q_k(z) ] v_k.
```

Matching against `P u_0 - Q v_0` forces `p_{k-1}(z+1) = p_k(z)` for **every** `k ≠ 0`. Only finitely
many `p_k` are nonzero, so descending from the top index kills every `p_k` with `k ≥ 0`, and ascending
from the bottom kills every `p_k` with `k ≤ -1`. The remaining `k = 0` equation then reads
`p_{-1}(z+1) - p_0(z) = P`, i.e. `0 - 0 = P`. Hence

```text
P ≡ 0  ⟹  c_i a_i = 0 for all i  ⟹  c_i = 0 for all i  (since s ∉ ℤ makes a_i ≠ 0)  ⟹  L = 0.
```

So no admissible `L` exists and `d_h` is hypertranscendental.

### Why the spectrum is exactly `ℤ` — the mechanism

The argument uses **only** the disjointness of the two `σ`-orbits of branch points. When `h ∈ ℤ` the
families coincide (`v_k = u_{k+h}`), the telescoping chain is no longer broken at `k = 0`, and the
argument correctly fails. The spectrum is `ℤ` precisely because `ℤ` is the set of translations that
identify the two branch orbits.

## `[OPEN CORE]` — the remaining inputs

**(R) Reduction to the linear part.** `g` a priori is an arbitrary element of `K`, not linear in the
generators. Needed: `σ(g) - g ∈ ℂ(z)u_0 + ℂ(z)v_0` forces `g` to lie in the `ℂ(z)`-span of the
generators. Since `σ` shifts indices, a nonzero monomial of higher degree cannot cancel between
`σ(g)` and `g`; the plan is a leading-monomial argument in a shift-compatible order.

**(I) Algebraic independence of the shifted power family.** The displayed matching requires
`{u_k} ∪ {v_k}` to be algebraically independent over `ℂ(z)`. This **fails for rational `s`**: if
`s = p/q` then `u_k^q = (z+k)^{-p} ∈ ℂ(z)`, so every `u_k` is algebraic over `ℂ(z)`. Hence the theorem
as stated needs `s ∉ ℚ`, or a separate treatment of rational `s`. Ax-type results should supply
independence for `s ∉ ℚ`; this must be pinned down, not assumed.

**Revised statement.** `Spec_DA(H(s,·)) = ℤ` for `s ∉ ℚ`. The case `s ∈ ℚ \ ℤ` is open and may have a
genuinely different answer — that is now a second, sharper question this card raises.

## Superseded text below (kept for the record)

### Earlier framing of the open core

> For `h ∉ ℤ`, `d_h` is hypertranscendental over `ℂ(z)`.

### Proposed proof strategy (mine, to be developed)

By the Hardouin–Singer criterion for first-order inhomogeneous difference equations, a solution `y`
of `σ(y) - y = b` is DA over the base iff there exist a nonzero `L ∈ ℂ(z)[δ]` and `g` in the base
with

```text
L(b) = σ(g) - g.
```

So the conjecture reduces to: **for `h ∉ ℤ` there is no nonzero linear differential operator `L` over
`ℂ(z)` and no `g` in the base field with `L(z^{-s} - (z+h)^{-s}) = σ(g) - g`.**

The obstruction to exploit is the **orbit separation of branch points**. `z^{-s}` is singular on the
`σ`-orbit `-ℕ`; `(z+h)^{-s}` on the orbit `-h-ℕ`. For `h ∉ ℤ` these orbits are disjoint. Applying `L`
preserves each singular support inside its orbit, while `σ(g) - g` has a telescoping singular
structure tied to a *single* orbit at a time. The plan is to show that the `-h-ℤ` orbit contribution
cannot be produced by `σ(g) - g` unless it is already telescoping, forcing `h ∈ ℤ`.

Risk to check before investing: the analogous statement for `Γ` itself — the spectrum of the digamma
`ψ` under translation — may be classical. The searches below did not find it, but this is the first
thing to settle.

## Literature audit (performed before writing this card)

- Hölder (1886): `Γ` is hypertranscendental; the mechanism is the difference equation
  `Γ(z+1) = zΓ(z)`.
- Mordukhai-Boltovskoi and Ostrowski (1920): hypertranscendence of `ζ(s,x)`; Hilbert's conjecture.
- Postnikov: Dirichlet `L`-functions are algebraically differentially independent.
- Modern machinery: difference-Galois criteria for hypertranscendence
  (Hardouin–Singer; and *Hypertranscendence and q-difference equations over elliptic function
  fields*, arXiv:2409.10092).
- **Not found:** any determination of the translation DA spectrum of the Hurwitz zeta in `z`, or of
  the digamma. `[NOVELTY UNVERIFIED]`

## Lean route

1. The structural step and the easy direction are formalizable now: the closed form for `d_n`, the
   first-order ODE for `(z+k)^{-s}`, and closure of DA under finite sums.
2. The converse needs the Hardouin–Singer criterion, which is **not in the corpus or mathlib**.
   Formalizing that criterion is the real Lean bottleneck and is the honest long-horizon task.
3. Per this project's own standard: formalizing only step 1 would be theatre, since step 1 is the
   textbook recursion. The Lean deliverable is the converse.

## Status

`[CONJECTURE]` with the structural reduction proved. No novelty claimed until the digamma case is
settled against the literature and the converse is proved.
