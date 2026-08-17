# PA9 Turan Ratio Has A Universal Newton Floor

- **ID:** pa9-turan-newton-floor
- **Stage:** 3-formalized
- **Type:** THEOREM (paper), proof-route normalization correction
- **Source:** random formula-graph node 34/100, `PA9` in `docs/consolidated/revision01/formulas-graph.md`
- **Statement:** For any Laguerre-Polya / elementary-symmetric coefficient sequence coming from positive divisor atoms, the Turan ratio

```text
g_n = a_n^2/(a_{n-1}a_{n+1})
```

has the universal Newton floor

```text
g_n >= (n+1)/n.
```

Therefore the PA9 observation `g_n - 1 ~ c/n` contains a forced `1/n` contribution before any xi-specific positivity information appears. The source-specific PA9 margin is the de-biased residual

```text
g_n / ((n+1)/n) - 1,
```

or, to first order, `n(g_n-1)-1`.

## Goal

Correct the interpretation of PA9. The raw normalized Turan margin is scale-free, but it is not yet source-specific. A unit amount of the observed `1/n` decay is forced by Newton's inequalities for any positive elementary-symmetric coefficient sequence. The proof-route should not treat the raw constant in `n(g_n-1)` as a completed-divisor margin.

## Gates

- [x] 0 -> 1 in-progress: random formula selected and checked against existing Turan/no-margin corpus
- [x] 1 -> 2 fully-proven: Newton-floor proof complete
- [x] 2 -> 3 formalized: **DONE (2026-08-16)** — `GaloisForLFunctions.newton_floor_finite`,
  `GaloisForLFunctions.turan_ratio_newton_floor`, `GaloisForLFunctions.newton_floor_limit` in
  `formal/GaloisForLFunctions/RHTower/TuranNewtonFloor.lean`, on top of the new
  `formal/GaloisForLFunctions/HTGeometry/NewtonInequalities.lean`; `lake build` green; axiom
  footprint `[propext, Classical.choice, Quot.sound]`
- [ ] 3 -> 4 publication-ready: fold into the Jensen/Turan normalization notes

## Proof

[PROVED HERE]

Let `x_1,...,x_N >= 0`, and let `e_n` be the elementary symmetric polynomials in these variables. Newton's inequalities in normalized form give

```text
(e_n / binom(N,n))^2
  >= (e_{n-1} / binom(N,n-1)) (e_{n+1} / binom(N,n+1)).
```

Rearranging,

```text
e_n^2/(e_{n-1}e_{n+1})
  >= binom(N,n)^2 / (binom(N,n-1)binom(N,n+1))
  = ((n+1)/n) ((N-n+1)/(N-n)).
```

Now let an infinite positive divisor atom sequence have finite elementary symmetric coefficients `a_n=e_n(x_1,x_2,...)`. Apply the finite inequality to the first `N` atoms and let `N -> infinity`. The coefficients `e_j^{(N)}` converge to `a_j` for each fixed `j`, and

```text
((n+1)/n) ((N-n+1)/(N-n)) -> (n+1)/n.
```

Thus

```text
g_n = a_n^2/(a_{n-1}a_{n+1}) >= (n+1)/n.
```

This applies to the Laguerre-Polya / RH-side reading of `Xi` coefficients, where the coefficients are elementary symmetric functions of positive reciprocal zero-square atoms.

## Route Consequence

PA9's raw no-margin display

```text
g_n - 1 ~ c/n
```

should be split into

```text
g_n - 1
  = 1/n + source_residual_n + lower-order terms.
```

The first term is universal Newton/binomial geometry. The residual

```text
g_n / ((n+1)/n) - 1
```

is the part that can carry xi-specific information. A Turan/Jensen experiment that reports only `g_n-1` or `n(g_n-1)` overstates the available source-built positivity margin by including the universal floor.

This does not weaken the PA9 no-margin message. It sharpens it: after removing the floor, the residual margin is smaller and still decays, so the uniform Jensen/Turan apex has even less spare margin than the raw PA9 line suggests.

## Computation

The script recomputes the first Xi Maclaurin coefficients and prints both the raw and floor-divided margins:

- `computations/2026-06-21-conway-pa9-newton-floor.py`
- `computations/2026-06-21-conway-pa9-newton-floor.txt`

For the tested range, `n(g_n-1)-1` is positive and slowly rising from about `0.15` to `0.36`, while the floor-divided residual is only a few percent by `n=15`.

## Log

- 2026-06-21 -- Conway: created from random formula-graph node 34/100 (`PA9`). Prior work already had the raw Turan no-margin trend; this card isolates the universal Newton component that must be divided out before treating PA9 as source-specific evidence.

## Lean formalization — 2026-08-16

**Modules** (both new, both wired into their umbrellas, both built, every headline theorem with
axiom footprint `[propext, Classical.choice, Quot.sound]` — no `sorry`, no added axiom, no
hypothesis beyond the card's own):

* `formal/GaloisForLFunctions/HTGeometry/NewtonInequalities.lean` — **Newton's inequalities**, which
  mathlib does not have in any form;
* `formal/GaloisForLFunctions/RHTower/TuranNewtonFloor.lean` — the elementary-symmetric
  specialisation and the Turán floor.

| Paper step (§) | Lean name | Statement |
|-|-|-|
| Newton's inequalities in normalised form | **`SignAlternation.newton_inequality`** | for a real-rooted `p` of degree `d`, `A_{k-1}A_{k+1} ≤ A_k²` where `A_k = c_{d-k}/C(d,k)` |
| — real-rootedness under `d/dt` | `SignAlternation.hyperbolic_derivative` | from mathlib's `Polynomial.card_roots_le_derivative` |
| — real-rootedness under reversal | `SignAlternation.hyperbolic_reverse`, `reverse_X_sub_C`, `natDegree_reverse_eq` | the reverse of a split polynomial with nonzero constant term splits, with reciprocal roots |
| — the two coefficient transports | `SignAlternation.newtonCoeff_derivative` (`A_k ↦ d·A_k`), `SignAlternation.newtonCoeff_reverse` (`A_k ↦ A_{d-k}`) | with the binomial identity `(d−k)·C(d,k) = d·C(d−1,k)` (`choose_sub_mul`) |
| — the degree-two base | `SignAlternation.newton_quadratic` | the discriminant of a real-rooted quadratic |
| `∏(t+x_i) = Σ e_k t^{N−k}` | `prodLinear`, `natDegree_prodLinear`, `hyperbolic_prodLinear`, `newtonCoeff_prodLinear` | the generating polynomial is real-rooted with `A_j = e_j/C(N,j)` |
| **the card's displayed inequality** | **`newton_esymm`** | `(e_{n-1}/C(N,n−1))(e_{n+1}/C(N,n+1)) ≤ (e_n/C(N,n))²` |
| the binomial rearrangement | `choose_turan_identity` | `C(N,n)²·n·(N−n) = C(N,n−1)C(N,n+1)(n+1)(N−n+1)` |
| **the universal floor, finite** | **`newton_floor_finite`** | `(n+1)·e_{n−1}e_{n+1} ≤ n·e_n²` for **any** real family — the cleared, hypothesis-free form of `g_n ≥ (n+1)/n` |
| **the floor as a ratio** | **`turan_ratio_newton_floor`** | `g_n = e_n²/(e_{n−1}e_{n+1}) ≥ (n+1)/n` for positive atoms (`esymmFin_pos`) |
| **`N → ∞`** | **`newton_floor_limit`** | the floor survives the limit of the truncations of an infinite atom sequence |

### A sharpening of the paper argument

The card obtains the floor by first proving the sharper finite bound
`g_n ≥ ((n+1)/n)((N−n+1)/(N−n))` and then letting `N → ∞`.  The Lean proof records that the *cleared*
form `(n+1)e_{n−1}e_{n+1} ≤ n e_n²` already holds for **every finite `N`** — the extra factor
`(N−n+1)/(N−n) ≥ 1` is discarded inside `newton_floor_finite` — so the limit statement
(`newton_floor_limit`) needs only the convergence of the truncated coefficients, exactly the card's
hypothesis "an infinite positive divisor atom sequence with finite elementary symmetric
coefficients".  The finite bound is also hypothesis-free in the sign of the atoms; positivity is
needed only to divide and obtain the ratio form.

### Not formalized (and not an obligation)

The "Schur-Threshold Side Note" rate `a_d = 2 log d + o(1)` is labelled a **CONJECTURE** on the card
and is explicitly "not used in the theorem above".

## Log (cont.)

- 2026-08-16 (Leaner) — **→ 3-formalized.**  Newton's inequalities were built from scratch
  (mathlib gap) as the reusable module `HTGeometry/NewtonInequalities.lean`, together with the two
  operations that preserve real-rootedness (differentiation and reversal); the card's floor and its
  ratio and limit forms follow.
