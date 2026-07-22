# CCM critical-Mellin aperture-resolvent law

- **ID:** `ccm-critical-mellin-aperture-resolvent-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CONNES/CCM SOURCE-SPECIFIC] [NOVELTY UNVERIFIED] [NOT RH]`
- **Source:** `../../1-in-progress/ccm-critical-mellin-adjacent-block-subpower-lower.md`
- **Statement:** Exponential averaging over the CCM rectangular aperture turns the exact
  Volterra--Haar multiplier into a rational resolvent; at unit rate it is `-1/(w+1)` and its causal
  kernel cancels the full Volterra memory exactly.

## Goal

Remove the phase obstruction left by fixed-width critical-Mellin adjacent blocks.  This is a
source-native operation on the actual CCM aperture variable, not an abstract positivity lemma and
not a Suzuki construction.

## Exact theorem

The formalized fixed-width response of a mode `exp(w x)` is

```text
M_L(w)=-(2w+1)(1-exp(-Lw))^2/(2w^2),       Re(w)>0.       (1)
```

For every real `a>0`,

```text
integral_(0,infinity) exp(-aL) M_L(w) dL
 =-(2w+1)/(a(a+w)(a+2w)).                               (2)
```

At the unique unit rate, the Volterra numerator cancels one aperture pole:

```text
integral_(0,infinity) exp(-L) M_L(w) dL=-1/(w+1).        (3)
```

Consequently

```text
Re integral_(0,infinity) exp(-L) M_L(w) dL < 0           (4)
```

throughout the open right half-plane.  Fixed-width faithfulness only said `(1)` is nonzero;
`(3)--(4)` give a uniform half-plane orientation of the detector itself.

## Proof

Expand the Haar square and integrate the three decaying exponentials:

```text
integral_(0,infinity) exp(-aL)(1-exp(-wL))^2 dL
 =1/a-2/(a+w)+1/(a+2w)
 =2w^2/(a(a+w)(a+2w)).                                  (5)
```

Multiplication by `-(2w+1)/(2w^2)` proves `(2)`.  Setting `a=1` cancels
`1+2w=2w+1`, proving `(3)`.  Finally

```text
Re(-1/(w+1))=-(Re(w)+1)/|w+1|^2<0,                      (6)
```

which proves `(4)`.

## Causal kernel collapse

Before modes are taken, width averaging of the adjacent-block operator has causal lag kernel

```text
K(t)=2 exp(-t)-exp(-t/2),       t>=0.                    (7)
```

Its primitive is

```text
integral_0^t K(s)ds=2(exp(-t/2)-exp(-t)).                (8)
```

Hence the Volterra factor in the completed Chebyshev potential cancels exactly:

```text
K(t)+(1/2) integral_0^t K(s)ds=exp(-t).                 (9)
```

If

```text
e(x)=(psi(exp x)-exp x)exp(-x/2),
J(x)=integral_0^infinity exp(-t)e(x-t)dt,
```

then the unit-rate aperture average of the completed-error adjacent block is `-J(x)`.  The change
of variables `y=exp(x-t)` gives the exact source form

```text
J(log X)=X^(-1) integral_0^X (psi(y)-y)y^(-1/2)dy.      (10)
```

Thus aperture averaging does not hide the prime source: it replaces the Volterra--Haar detector by
one positive causal resolvent of the normalized Chebyshev error.

## Admissible-aperture tail

The rectangular source identity only needs widths `0<L<=x/2`.  For a mode with
`0<Re(w)<1/2`, the omitted tail is exactly

```text
-(2w+1)/(2w^2) * [
  exp((w-1/2)x)
  -2 exp((w/2-1/2)x)/(1+w)
  +exp(-x/2)/(1+2w)].                                   (11)
```

Every exponent in `(11)` has negative real part.  Therefore admissible truncation changes the
resolvent response by `o(1)` for every possible off-critical zeta mode.  The aperture boundary
cannot restore the fixed-width phase obstruction.

## Hostile audit

This does **not** prove RH.  Negative real part of the scalar multiplier does not orient an
arbitrary complex residue amplitude, and `(10)` has no known unconditional one-sided subpower
bound.  Claiming sign from `(4)` alone would silently assume a source-sector theorem.

The result closes two real subfrontiers:

1. detector phase on the entire positive-growth half-plane;
2. loss caused by restricting to admissible widths.

The surviving RH core is source membership: prove a one-sided subpower law for `(10)` directly
from von Mangoldt and Gamma data.  This is recorded in
`../../1-in-progress/ccm-aperture-resolvent-riesz-sector.md`.

## Novelty audit

Internal exact-phrase, formula, and concept searches found no aperture-averaged CCM multiplier,
unit resolvent cancellation, or causal kernel identity `(9)`.  Targeted searches of the primary
Connes--Consani--Moscovici `Zeta Spectral Triples`, Connes--Consani `Weil positivity and Trace
formula`, `Quasi-inner functions and local factors`, and `The Scaling Hamiltonian` found no
occurrence of aperture averaging, Haar/Volterra averaging, or `(3)`.  Laplace integration itself is
classical; priority for this CCM application is not established.  Status remains
`[NOVELTY UNVERIFIED]` pending expert and full-text bibliography audit.

## Gates

- [x] 0 → 1: source-native operation and exact frontier stated
- [x] 1 → 2: dependency-closed symbolic proof, no zero hypothesis
- [x] 2 → 3: core `(2)--(9)` and general exact aperture-tail transfer are formalized; asymptotic
  decay of the specialized tail remains a paper corollary
- [ ] 3 → 4: external priority and publication audit

## Log

- 2026-07-22 — derived general aperture law, unit resolvent collapse, causal kernel identity, and
  admissible-tail theorem; hostile audit separated detector phase from source-sector sign.
