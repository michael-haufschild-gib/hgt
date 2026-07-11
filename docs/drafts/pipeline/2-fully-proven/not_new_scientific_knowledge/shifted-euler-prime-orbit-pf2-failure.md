# Shifted Euler prime-orbit coefficients fail PF2

- **ID:** `shifted-euler-prime-orbit-pf2-failure`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** COUNTEREXAMPLE THEOREM (paper),
  `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `shifted-euler-quotient-twisted-cocycle-flatness.md`; Suzuki's explicit causal kernel
- **Statement:** Although every coefficient of the shifted Euler quotient is positive for positive
  transverse shift, even one prime-power orbit fails the weakest nontrivial Pólya-frequency
  condition.  Therefore coefficient positivity cannot be upgraded automatically to a
  variation-diminishing dilation law capable of preserving the sign of the archimedean kernel.

## Setup

Fix a prime `p` and `omega>0`, and put

```text
x=p^omega>1.
```

The local Euler factor of

```text
zeta(s-omega)/zeta(s+omega)
```

is

```text
(1-x^(-1)z)/(1-xz)=sum_(k>=0)a_k z^k,
```

where `z=p^(-s)`.  Hence

```text
a_0=1,
a_k=x^k-x^(k-2) for k>=1.                               (1)
```

Every `a_k` is positive.

## Theorem: the first PF2 minor is negative

The adjacent Toeplitz minor satisfies

```text
det [[a_1,a_2],[a_0,a_1]]
 =a_1^2-a_0 a_2
 =x^(-2)-1<0.                                           (2)
```

Consequently `(a_k)` is not PF2, and therefore is not PF-infinity.

### Proof

From `(1)`,

```text
a_1=x-x^(-1),
a_2=x^2-1.
```

Thus

```text
a_1^2-a_2
 =(x-x^(-1))^2-(x^2-1)
 =x^(-2)-1.
```

Since `x>1`, this is negative.  A PF2 sequence has every order-two Toeplitz minor nonnegative, so
the local sequence fails PF2.

## Route C consequence

Suzuki's causal source is a positive dilation mixture

```text
h_omega(x)=x^(-1) sum_(n<=x)c_omega(n)g_omega(n/x),
```

with `c_omega(n)>0`.  Positivity alone does not make this mixture variation-diminishing.  Any such
argument would in particular require nonnegative order-two minors on each prime-power orbit, and
`(2)` disproves that requirement.

This does not prove that the actual Suzuki tail changes sign, nor does it refute every possible
prime--archimedean estimate.  It closes only the proposed automatic implication

```text
positive shifted-Euler coefficients
  -> total positivity / variation diminution
  -> eventual one-sign Suzuki tail.
```

A surviving sign theorem must exploit quantitative cancellation between the exact prime dilation
mixture and the gamma/theta kernel; coefficient positivity by itself is insufficient.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The falsifier is a two-by-two determinant of a geometric local
Euler sequence.  It is useful route control but not a new result in total positivity or analytic
number theory.

## Gates

- [x] 0 -> 1: coefficient-positivity-to-sign proposal and its local PF2 falsifier isolated.
- [x] 1 -> 2: exact local coefficients and negative minor proved on paper.
- [ ] 2 -> 3: no Lean formalization selected; the actual prime--archimedean boundary estimate is
  not this elementary minor.
- [ ] 3 -> 4: no scientific-novelty claim.
