# Literal one-prime terminal pruning is a two-site involution

- **ID:** `suzuki-one-prime-terminal-pruned-propagator`
- **Stage:** 3 — formalized in Lean 4
- **Type:** LITERAL SOURCE PRUNING / FINITE PROPAGATOR / PRIOR-PROOF REPAIR
- **Scientific status:** `[PROVED HERE] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Inputs:** `suzuki-literal-paired-source-assembly.md`,
  `suzuki-one-prime-rough-primitive-hardy-closure.md`

## 1. Correction and result

The earlier one-prime Hardy argument tried to control the continuous group of the infinite
weighted Laurent adjacency on `ell2(Z)`. The discrete weighted-shift estimate does not prove that
continuous polynomial group bound. That interpolation bridge is unnecessary for the literal
source.

For every aperture

```text
2a < log 3,                                                   (1)
```

Suzuki's canonical spatial cutoff eventually kills every one-prime valuation coordinate except
`n=0,1`. On each rooted puncture channel, the terminal prime block is therefore either zero or the
two-site matrix

```text
          [ 0    r   ]
B_r =     [ r^-1 0   ],      r = 2^(2/3).                    (2)
```

It satisfies

```text
B_r^2 = I,                                                   (3)
exp(-it B_r) = cos(t) I - i sin(t) B_r,                      (4)
sup_t ||exp(-it B_r)|| <= 1 + ||B_r||.                       (5)
```

The same bound holds after multiplying `B_r` by the literal real prime coefficient. Thus the
actual terminal one-prime group has degree zero, not merely degree `2/3`. This supplies the missing
continuous propagator required by the vector-valued Gamma block without complex interpolation or
an infinite-lattice premise.

## 2. Exact terminal support

Write

```text
d_n = n log 2,
x_(+,n) = a-d_n,
x_(-,n) = -a+d_n.                                          (6)
```

For either root,

```text
x_(epsilon,n) in [-a,a]  iff  0 <= d_n <= 2a.              (7)
```

Since

```text
log 3 < log 4 = 2 log 2,                                   (8)
```

conditions `(1)` and `(7)` imply `0 <= n < 2`, hence

```text
n in {0,1}.                                                 (9)
```

Strict interior membership forces `n=1`. Site `n=0` is the physical root. At the resonant
aperture `2a=log 2`, site `n=1` is the opposite endpoint rather than an interior site; including it
in `{0,1}` handles this case without division by the endpoint gap.

There is a uniform aperture-independent gap to every other center. Put

```text
delta = min(log 2, 2 log 2-log 3) > 0.                      (10)
```

If `n` is neither zero nor one, then for both rooted center families

```text
x_(epsilon,n) <= -a-delta  or  x_(epsilon,n) >= a+delta.    (11)
```

Indeed, `n<=-1` gives a gap at least `log 2`; `n>=2` gives a gap at least
`2 log 2-2a > 2 log 2-log 3`.

For puncture orientation `|o|<=1`, once

```text
exp(-L) < delta,                                            (12)
```

equation `(11)` implies

```text
x_(epsilon,n)+o exp(-L) notin (-a,a).                      (13)
```

The canonical scale-buffered cutoff is nonzero exactly on the open aperture, so `(13)` proves
that all coordinates outside `{0,1}` vanish identically on the terminal ray. This is uniform in
the infinitely many discarded valuations; it is not a coordinatewise limiting argument.

## 3. Channel classification

If `2a<log 2`, only the root site survives and every compressed prime block is zero. If
`2a=log 2`, sites zero and one are opposite boundary roots, but their inward puncture orientations
are opposite; each fixed-orientation compressed block is again one-site and zero.

If

```text
log 2 < 2a < log 3,                                       (14)
```

site one is strictly interior. For each root:

- the inward root orientation retains sites zero and one and carries `B_r`;
- the other orientation retains only site one and carries the zero block.

The two roots therefore give a direct sum of two copies of `B_r` and two zero blocks. A direct sum
does not change the frequency-growth degree.

## 4. Literal weighted compression

The rank-one carrier weight is

```text
w(n)=(1+|n|)^(-2/3).                                      (15)
```

For the forward and backward weighted shifts,

```text
w(0)/w(1)=2^(2/3)=r,
w(1)/w(0)=r^-1.                                           (16)
```

If `f` is supported on `{0,1}`, compression of the full symmetric weighted shift gives

```text
(S_+ + S_-)f at n=0 = r f(1),
(S_+ + S_-)f at n=1 = r^-1 f(0).                          (17)
```

This is exactly `(2)`, so the finite matrix is not a replacement model. It is the coordinate
compression of the previously constructed literal fractional shifts after the canonical physical
cutoff.

## 5. Exact continuous group

Equation `(3)` follows immediately from the reciprocal off-diagonal entries. Hence the even and
odd exponential series give

```text
exp(-it B_r)=cos(t)I-i sinc(t)t B_r
             =cos(t)I-i sin(t)B_r.                       (18)
```

Using `|cos t|<=1` and `|sin t|<=1` in any submultiplicative matrix norm gives `(5)`. For a real
literal coupling `c`, replace `t` by `ct` and obtain the same constant.

The scalar/eigenvalue part of Suzuki's Gamma symbol is a real scalar multiple of the identity. Its
imaginary-frequency exponential is a scalar phase and commutes with `(18)`, so it contributes norm
one. Thus the full terminal prime/scalar propagator is uniformly bounded.

## 6. Consequence for the Gamma block

The one-block kernel estimate in the earlier Hardy card is repaired by setting the actual terminal
transport degree to

```text
kappa_group = 0.                                          (19)
```

At Gamma height `sigma=3/4`, the slow exponent is `p=5/4`. The homogeneous/lower-end tail becomes

```text
x^(-p)=x^(-5/4),                                          (20)
```

whose square is integrable. The `N`th near-end remainder is `x^(1-N)`; already `N=2` is
square-integrable. The existing three-step argument remains valid with room to spare.

The exponent `2/3` is still useful for assembling the uncut infinite source and its event terms,
but it is a finite condition number on the terminal block, not continuous frequency growth. This
separates source summability from propagator growth and closes the actual one-prime operator gap.

## 7. Hostile audit

1. **No discrete-to-continuous leap.** The continuous exponential is evaluated from the exact
   involution.
2. **No infinite-lattice theorem.** Canonical physical cutoff gives uniform terminal support
   `{0,1}`.
3. **No resonance omission.** `2a=log 2` is included as an opposite-boundary collision.
4. **No replacement carrier.** Equation `(17)` identifies the finite matrix with the literal
   weighted shifts.
5. **No self-adjointness fiction.** `B_r` is generally nonnormal in the ambient Euclidean metric;
   boundedness follows from `B_r^2=I`, not from claiming it self-adjoint.
6. **No RH claim.** Higher-rank apertures, recurrence-infinite transfer, completed/raw Evans
   identification, P/I producers, and whole Route O remain open.

## 8. Lean target

`SuzukiOnePrimeTerminalPrunedPropagator.lean` formalizes unconditionally:

- closed-aperture confinement to `{0,1}`;
- uniform off-terminal gap and exact canonical-cutoff vanishing;
- literal fractional-shift compression to `B_r`;
- `B_r^2=I`;
- exact exponential and uniform norm bound, including arbitrary real prime coupling.

