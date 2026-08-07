# Suzuki critical wall-field square-root weld

- **ID:** `suzuki-critical-wall-field-square-root-weld`
- **Stage:** 3 — formalized in Lean 4
- **Formalized companion:** `./suzuki-critical-wall-field-square-root-weld-formalized.md`
- **Type:** SOURCE WELD / FAR-ENTRY-GAMMA CLASSIFICATION / FAILED IDENTIFICATION SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:** `suzuki-critical-entry-wall-quarter-shift-green-law.md`,
  `suzuki-critical-aperture-quarter-shift-current.md`,
  `suzuki-causal-hinge-boundary-tail-green-law.md`
- **RH used:** no
- **Computation used:** no
- **Primary sources:** M. Suzuki, arXiv:2206.03682v4, Theorem 1.1; M. Suzuki,
  arXiv:2606.09096v1, equations (1.9)--(1.11), (2.9)--(2.11), Sections 6 and 8.2--8.3

## Frontier correction

S57 called the observer-dependent product

```text
A_e(h,b;p)=GammaBare_e(p)*I_cubic(h,b;p,e)               (1)
```

an endpoint amplitude.  This cannot be the literal Suzuki deficiency endpoint trace:
`v_(a,lambda)(-a)` is fixed by restricted-Weil resolvent and wall aperture, whereas `b` is an
independently chosen observer aperture in Möbius true-aperture Hilbert geometry.

The failed identification exposes a stronger positive survivor.  Gamma boundary before observer
pairing is the common wall field linking all three previously separate channels: prime entry,
universal far hinge, and quarter-shift aperture current.

## Theorem A: one bare critical wall field `[PAPER-PROVED]`

Fix prime `p`, depth `e`, and put

```text
n=p^(e+1),
a_e=log(n)/2,
b_e=sqrt[(log p)/n * exp(log(n)/2)],
omega_e(t)=conj(xiGammaEulerHeightBoundaryFeature(-1/2,t;(p,e))).  (2)
```

Expanding the source definition and conjugating gives

```text
omega_e(t)=b_e exp(i t a_e).                             (3)
```

Thus `b_e` is observer-independent real wall amplitude and `omega_e` is its causal entry-wall
phase.  No observer feature occurs in `(2)--(3)`.

### Proof

At `u=-1/2`, Gamma density is

```text
(log p)/n * exp(-u log n)=(log p)/n * exp(log n/2).
```

The original height phase is `exp(-i t log n/2)`.  Complex conjugation fixes the real square root
and reverses phase.  Since `a_e=log n/2`, this proves `(3)`.

## Theorem B: wall field is exact square root of far hinge `[PAPER-PROVED]`

The real wall amplitude satisfies

```text
b_e^2=Lambda(n)/sqrt(n).                                (4)
```

Consequently its **complex bilinear square** is

```text
omega_e(t)^2
 =Lambda(n)/sqrt(n) * exp(i t log n).                   (5)
```

The Xi-real far delayed-hinge atom from the parent Green theorem is therefore exactly

```text
J_e(t)
 =-i [Lambda(n)/sqrt(n)] exp(i t log n)/t^2
 =-i omega_e(t)^2/t^2.                                 (6)
```

For `t!=0`, denominator-matched form is

```text
t^2 J_e(t)=-i omega_e(t)^2.                             (7)
```

### Proof

Because `n>0`,

```text
exp(log n/2)=sqrt(n),
n=sqrt(n)^2.
```

Squaring `b_e` in `(2)` and cancelling one square root gives

```text
b_e^2=(log p)/sqrt(n).
```

The prime-power identity `Lambda(p^(e+1))=log p` proves `(4)`.  Squaring `(3)` and using
`2a_e=log n` proves `(5)`.  Substitution into exact far-hinge definition proves `(6)--(7)`.

This square is deliberately not `|omega_e|^2`: it retains full delay phase.  Hence theorem does
not contradict parent's phase-aligned negative Pick diagonal and does not assert atomwise
positivity.

## Theorem C: same field drives entry and observed current `[PAPER-PROVED]`

Insert real endpoint trace `b_e` at prime-power wall `a_e`.  S56's near/far third-jet law and
`(3)` give

```text
DeltaBare_3(p,e;t)=t^2 exp(i t a_e)b_e=t^2 omega_e(t).  (8)
```

Let `I_e(h,b;p)=I_cubic(h,b;p,e)` be cubically normalized observer innovation.  Existing critical
quarter-shift atom is exactly

```text
T_e(h,b,t;p)=omega_e(t) I_e(h,b;p).                     (9)
```

Therefore observed entry forcing is

```text
DeltaObs_3(p,e;t)
 =t^2 T_e(h,b,t;p)
 =DeltaBare_3(p,e;t) I_e(h,b;p).                       (10)
```

Equations `(5)`, `(8)`, and `(10)` are the square-root weld:

```text
far hinge numerator      = omega_e^2,
bare entry third jet     = t^2 omega_e,
observed entry third jet = t^2 omega_e I_e.            (11)
```

One field, not three unrelated leakage coordinates, controls far, entry, and Gamma/aperture
channels.

## Theorem D: observer product is not a universal endpoint trace `[PAPER-PROVED]`

Fix `h>0`, prime `p`, and depth zero.  On `b>0`, map

```text
b -> A_0(h,b;p)=b_0 I_0(h,b;p)                          (12)
```

is injective.  Hence no observer-independent scalar endpoint trace can equal `(12)` at two
distinct positive observer apertures.

### Proof

For `q=p^-1` and `r_b=exp(-(h b/2)log p)`, source definition gives

```text
I_0(h,b;p)
 =(h sqrt h)^-1 * q/(1+q) * (1-r_b)^2.                 (13)
```

Every factor outside `(1-r_b)^2` is strictly positive.  Also `0<r_b<1` and
`b -> r_b` is injective.  Equality of `(12)` at `b_1,b_2>0` therefore gives
`(1-r_(b_1))^2=(1-r_(b_2))^2`.  Both bases are positive, so they are equal; hence the disk nodes
and then apertures are equal.

## Hostile audit

1. **Norm-square substitution fails.**  Replacing `omega_e^2` by `|omega_e|^2` erases far-delay
   phase and is false.
2. **Quarter-turn is forced.**  Xi-real far atom is `-i omega_e^2/t^2`; dropping `-i` changes Pick
   sign and source coordinate.
3. **Spectral center is singular.**  `(6)` is algebraic under field division convention, while
   denominator cancellation `(7)` requires `t!=0`.
4. **No standalone Hilbert vector.**  Bare critical wall field remains nonsummable in prime
   Hilbert norm.  Only observer pairing `(9)` has completed topology.
5. **No deficiency equality assumed.**  `b_e` is source-selected Gamma wall amplitude, not a
   resolvent response.  Actual endpoint must first apply restricted-Weil resolvent and boundary
   observation.
6. **No atomwise Gram.**  Parent theorem's negative phase-aligned far Pick diagonal remains valid.
   Square-root weld calls for a joint symmetric-square/observer block, not positive direct sum.
7. **Prime-power normalization.**  `(4)` uses exact `Lambda(p^(e+1))=log p`; no prime number theorem
   or estimate occurs.

Verdict: `SURVIVES PRELIMINARY ATTACK`.

## New scientific consequence and corrected open core

Previous frontier asked to assemble universal far tail, near-entry reporter, and critical
Gamma/aperture current as if independent.  They are exact polynomial degrees of one wall field:
quadratic, linear, and observer-paired linear.  Correct candidate producer is therefore a joint
symmetric-square/observer Schur block built from `omega_e`, not an atomwise positive prime Gram and
not equality of deficiency trace with observer product.

### `SUZUKI-WALL-SYMMETRIC-SQUARE-WARD` `[CONJECTURE]`

At recurrence-selected logarithmic apertures, insert actual affine-sewn restricted-Weil endpoint
traces into bare slot `(8)`.  Pair residual linearly with `I_e`, while representing universal far
tail by symmetric square `(5)` and retaining polar--Gamma continuum plus midpoint/holonomy debts.
Prove resulting fixed-width rectangular Ward defect uniformly lower bounded.

The next attempted implication was:

```text
actual normalized deficiency wall trace = b_e
```

but later resolvent-dressing audit rejects it as source-type error: `b_e` is input coordinate and
deficiency endpoint depends on shift and spectral level.  Correct successor is
`suzuki-critical-wall-field-resolvent-dressing-law.md`: identify actual boundary observation of
resolvent-dressed field, then prove mixed compensation residual uniformly lower bounded.  Identity
`(5)` still supplies far-tail weld; no independent far-channel matching remains.

## Novelty audit

- Complex square-root algebra and prime-power von Mangoldt identity are classical `[BRIDGE]`.
- Suzuki 2022 supplies delayed-hinge coefficient; Suzuki 2026 supplies restricted-Weil deficiency
  construction.  Neither paper defines corpus's Gamma--Euler wall field or Möbius innovation.
- Internal search found quarter-shift current, entry-wall phase, and far-hinge law separately, but
  no identity `(5)--(11)` recognizing them as quadratic and linear degrees of one wall field.
- Targeted arXiv search found no Suzuki follow-up or other source stating this wall-field weld.

Candidate novelty is exact source-specific synthesis and resulting correction of RH producer;
external priority remains unverified.

## Formalization gates

- [x] exact paper derivation and source-type audit
- [x] complex square-root/far-hinge identity
- [x] bare/observed entry factorization
- [x] observer injectivity no-go
- [x] exact unconditional Lean formalization
- [ ] actual deficiency wall matching or residual semiboundedness
- [ ] rectangular Ward-defect lower bound and RH
