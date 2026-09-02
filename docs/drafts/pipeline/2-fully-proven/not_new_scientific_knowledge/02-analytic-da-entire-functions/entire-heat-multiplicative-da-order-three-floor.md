# Entire-Heat Multiplicative DA Anchors Have Differential Order at Least Three

- **ID:** entire-heat-multiplicative-da-order-three-floor
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM (paper) / BRIDGE / ROUTE NO-GO
- **Scientific status:** `[BRIDGE]` — a direct heat-decay consequence of the classical Valiron-Zimogljad-Strelitz growth wall for algebraic differential equations of order at most two
- **Statement:** An infinite-spectrum one-sided periodic heat orbit that is entire for every complex time cannot have a first- or second-order DA anchor in its multiplicative Fourier coordinate.

## Goal

Determine how much algebraic-differential complexity is forced by entire backward heat evolution before using arithmetic information about the Fourier coefficients. The theorem concerns general complex amplitudes. Its downstream consequence applies only to heat-route implementations whose DA test is imposed on the ordinary generating function in the multiplicative Fourier coordinate.

## Gates

- [x] Exact one-sided periodic heat class fixed.
- [x] Complete unconditional paper proof.
- [x] No arithmetic or coefficient-height hypothesis.
- [x] Parent-theory gate: **FAILS scientific novelty.** Once the zero-order estimate is written down, the conclusion is an immediate application of the classical order-two growth theorem.
- [ ] Formalization: **in progress.**  Step 1 is Lean-proved in central-index form
  (`HTGeometry/EntireHeatDifferentialOrderFloor.lean`): the literal heat summability hypothesis
  gives `ν(r) = o(log r)`.  Order zero and order one are now excluded unconditionally; the latter
  follows from the exact compiler in `HTGeometry/FirstOrderCoefficientDecomposition.lean` and the
  corpus Newton-face theorem.  The four-variable order-two compiler is also Lean-proved in
  `HTGeometry/SecondOrderCoefficientDecomposition.lean`.  Remaining step is the genuine
  Valiron--Zimogljad--Strelitz minimal-relation reduction when the homogeneous top symbol vanishes
  on the monomial jet model; see `_STAGE3-LEDGER.md`.

## Theorem `[PROVED HERE] [BRIDGE]`

Let `(a_n)_(n>=0)` be complex numbers and suppose

`u(t,z) = sum_(n>=0) a_n exp(-4 pi^2 n^2 t) exp(2 pi i n z)`

converges locally uniformly on `C^2`. Define the multiplicative anchor

`h(w)=sum_(n>=0) a_n w^n`.

Then either:

1. `h` is a polynomial, equivalently `a_n=0` for all sufficiently large `n`; or
2. `h` is transcendental entire and satisfies no algebraic differential equation of differential order at most two over `C(w)`.

Consequently, if the infinite-spectrum anchor `h` is DA, its minimal algebraic-differential order is at least three.

## Proof

### 1. Entire backward time gives zero logarithmic type at the quadratic scale

For every `A>0`, evaluate the orbit at `t_A=-A/(4 pi^2)`. The resulting power series

`h_A(w)=sum_(n>=0) a_n exp(A n^2) w^n`

is entire. Cauchy's estimate on `|w|=1` gives a constant `M_A>0` such that

`|a_n| <= M_A exp(-A n^2)`                                                    `(1)`

for all `n`.

For `r>=1`, put `L=log r`. Completing the square in the maximum-modulus estimate gives

`M_h(r) <= M_A sum_(n>=0) exp(-A n^2+nL)`

`        <= M_A C_A exp(L^2/(4A))`,                                           `(2)`

where `C_A` is a finite Gaussian-sum constant independent of `r`. Hence

`limsup_(r->infinity) log M_h(r)/(log r)^2 <= 1/(4A)`.

Since `A>0` is arbitrary,

`log M_h(r)=o((log r)^2)`.                                                     `(3)`

In particular, a nonpolynomial `h` is a transcendental entire function of ordinary order zero.

### 2. Differential orders zero, one, and two are impossible

An order-zero algebraic differential equation is an algebraic equation over `C(w)`; an entire solution is algebraic entire and therefore a polynomial.

The Valiron-Zimogljad-Strelitz theorem states that every transcendental entire solution of an algebraic differential equation of differential order at most two with rational-function coefficients has positive ordinary order. Applied over `C(w)`, this contradicts (3).

Thus a nonpolynomial `h` satisfies no ADE of order at most two. If it is DA at all, its minimal ADE order is at least three. `square`

## Exact route consequence

The theorem rules out the following heat-route implementation:

1. encode the deformation by a one-sided integer-frequency heat series;
2. require joint entireness for all complex time, including arbitrarily far backward time;
3. detect the proposed arithmetic phase by a first- or second-order ADE for the multiplicative Fourier anchor `h(w)`.

For an infinite source, such an ADE cannot occur at any anchor to which the same entire-complex-time estimate applies. A DA escape, if one exists, begins only at differential order three.

The theorem does not rule out the actual de Bruijn-Newman deformation, which has a continuous Fourier kernel and whose phase concerns zero reality rather than low-order differential algebraicity in a multiplicative lattice coordinate. It also does not exclude DA anchors of differential order at least three.

## Parent and sharpness audit

1. G. Valiron constructed a transcendental entire order-zero solution of a third-order algebraic differential equation: *Sur les fonctions entieres d'ordre nul et les equations differentielles*, Bull. Soc. Math. France 53 (1925), 34-42.
2. V. V. Zimogljad proved that every transcendental entire solution of a second-order algebraic differential equation with rational-function coefficients has positive order.
3. Sh. Strelitz gave a unified account and another proof in *Three Theorems on the Growth of Entire Transcendental Solutions of Algebraic Differential Equations*, Canad. J. Math. 35 (1983), 1110-1128.
4. Valiron's example shows that the differential-order threshold `3` is sharp for the parent zero-order growth theorem. It does not show sharpness inside the stricter super-Gaussian heat class (3).

## Successor residue

`[OPEN CORE]` Decide whether the stronger growth condition `log M_h(r)=o((log r)^2)` excludes transcendental DA entire functions of every finite differential order. Equivalently, decide whether a nonpolynomial DA entire series can have Taylor coefficients satisfying `|a_n|=O_A(exp(-A n^2))` for every `A>0`. A positive answer would remove both the order-three escape and all coefficient arithmetic from the finite-spectrum theorem.

## Log

- 2026-07-11 — Proved the coefficient-free differential-order-three floor and classified it `[BRIDGE]` under the direct-parent gate.
