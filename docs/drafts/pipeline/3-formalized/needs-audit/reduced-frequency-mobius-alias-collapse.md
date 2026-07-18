# Reduced-frequency Möbius alias collapse for reducible CRT roots

- **ID:** `reduced-frequency-mobius-alias-collapse`
- **Stage:** 3-formalized
- **Type:** `[FORMALIZED] [NOVELTY UNVERIFIED] [GENERAL FINITE INCIDENCE THEOREM]`
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md`, equations `(PF1)`--`(PF13)`
- **Statement:** A complete Möbius family of Poisson aliases with one reduced rational frequency
  factors exactly into its primitive CRT root response and the Euler survival product on every
  inactive prime coordinate.

## Exact theorem

Let `Q` be squarefree, let `q | Q`, and let `a,h` be arbitrary integers.  For `n>=1` define

```text
R_(n,h)={r mod n : n | r(r+h)},
nu_h(n)=#R_(n,h),
S_(n,h)(k)=sum_(r in R_(n,h)) exp(2 pi i k r/n).
```

Then

```text
sum_(d | Q/q) mu(qd)/(qd) S_(qd,h)(ad)
 =mu(q)/q S_(q,h)(a)
    product_(p | Q/q) (1-nu_h(p)/p).                 (A1)
```

Every divisor in `(A1)` is automatically coprime to `q`.  The theorem includes the zero alias:
for `q=1,a=0`, its right side is the fixed-gap Euler survival product

```text
product_(p | Q)(1-nu_h(p)/p).                         (A2)
```

## Dependency-closed proof

Fix `d | Q/q`.  Squarefreeness of `Q` gives `(q,d)=1`.  The Chinese remainder equivalence sends
the root set `R_(qd,h)` bijectively to `R_(q,h) x R_(d,h)`.  Under that equivalence the phase at
frequency `ad` is

```text
exp(2 pi i ad r/(qd))=exp(2 pi i a r_q/q),             (A3)
```

so it is constant on the second root coordinate.  Therefore

```text
S_(qd,h)(ad)=nu_h(d) S_(q,h)(a).                       (A4)
```

Since `(q,d)=1`, multiplicativity of the Möbius function gives
`mu(qd)=mu(q)mu(d)`.  Substituting `(A4)` into the left side of `(A1)` leaves

```text
mu(q)/q S_(q,h)(a)
  sum_(d | Q/q) mu(d)nu_h(d)/d.                        (A5)
```

The root count is multiplicative on coprime moduli by the same CRT bijection.  Because `Q/q` is
squarefree, the divisor sum in `(A5)` is the finite Euler expansion

```text
sum_(d | Q/q) mu(d)nu_h(d)/d
 =product_(p | Q/q)(1-nu_h(p)/p),                      (A6)
```

which proves `(A1)`.

No primality relation between `h` and `Q` is used.  If `p | h`, then `nu_h(p)=1`; otherwise
`nu_h(p)=2`.  Both cases are already absorbed by the root set and the CRT proof.

## Hostile audit

- **Zero frequency:** `q=1,a=0` gives `(A2)` rather than an omitted exceptional term.
- **Shared factors with the gap:** primes dividing `h` change `nu_h(p)` but do not break `(A4)`.
- **Negative frequency:** complex conjugation changes neither the CRT lifting nor the factorization.
- **Nonprimitive frequency:** no coprimality hypothesis on `(a,q)` is needed.  If they share a
  factor, `(A1)` remains true and can subsequently be collapsed to the genuinely reduced
  denominator.
- **No analytic estimate is smuggled in:** `(A1)` is a finite identity.  It supplies no bound for
  the remaining sum over primitive denominators and numerators.
- **No RH conclusion:** the primitive responses `S_(q,h)(a)` and the physical support cutoff remain.

Verdict: `SURVIVES PRELIMINARY ATTACK` as an exact finite theorem.  Scientific priority is not yet
audited, so it is not labelled new scientific knowledge.

## Mathematical delta and Lean-discovered strengthening

The earlier modulus-by-modulus large-sieve representation estimates many copies of the same
rational frequency separately.  Equation `(A1)` proves that future Möbius dressing joins all such
copies first and replaces them by one primitive response multiplied by an Euler survival factor.
This is not the homogeneous ANOVA deletion: the active primitive denominator `q` and its two CRT
ridges remain.

Formal statement design removed two unnecessary restrictions from the original conjecture:

1. `a` need not be coprime to `q`.  This is essential in the causal application: the
   first-crossing prime can remain anchored in `q` even when it divides the Fourier frequency.
2. In Boolean-coordinate form the inactive coordinates need only be pairwise coprime and nonzero;
   they need not individually be prime and no global squarefree modulus is required.

The maximal anchored form is also formalized: for a protected factor `c`, squarefree coprime
complement `m`, and `d=gcd(m,|k|)`, the theorem extracts exactly `d` while leaving every factor of
`c` active.  The remaining complement `m/d` is coprime to `|k/d|`.

The classical divisor theorem `(A1)` and this stronger finite-coordinate theorem are both now
formalized.  The strengthening is mathematically substantive because reducing `a/q` before
regrouping can erase the first-crossing label in `(PF10)`.

`[CONJECTURE]` After exact reduced-frequency collapse, the complete-period and incomplete-support
parts admit a common primitive-denominator decomposition in which the moving zero-mode switch is
only the `q=1,a=0` boundary face.

`[OPEN CORE]` Prove or refute that common decomposition without extending centered modes into
inactive physical channels.  If it exists, determine whether its Euler survival factors give a
real gain after summing over `h`, rather than merely reallocating `FCRJ`.

## Gates

- [x] 0 -> 1: exact source-pure claim and hostile tests fixed
- [x] 1 -> 2: proof `(A3)`--`(A6)` is dependency-closed
- [x] 2 -> 3: exact finite Möbius/Euler alias theorem
- [x] CRT-root specialization engine formalized as
  `RHTower.quadraticCongruenceRootSum_mul_alias`
- [x] classical divisor form formalized as
  `RHTower.quadraticCongruence_reducedFrequencyAliasCollapse_of_dvd_squarefree`
- [x] stronger pairwise-coprime Boolean form formalized as
  `RHTower.quadraticRootFiniteMobiusAliasCollapse`
- [x] maximal causally anchored normal form formalized as
  `RHTower.quadraticCongruenceRootSumTotal_causalGCDReduction`
- [x] owned-module narrow build passes; `#print axioms` for the lifting, divisor, and Boolean
  collapse theorems reports only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] priority audit against finite harmonic-analysis and sieve literature
