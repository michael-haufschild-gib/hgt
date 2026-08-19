# The normalized Möbius carrier has an exponential critical boundary layer

- **ID:** `mobius-critical-exponential-boundary-layer-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [SEARCH] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Source:** `mobius-channel-critical-mass-escape-law.md`
- **Statement:** Under the exact squared-norm distribution of the normalized Möbius channel, the
  rescaled logarithmic divisor coordinate `2 omega log d` converges in law to a mean-one
  exponential random variable as `omega` decreases to zero.  Hence the arithmetic mass occupies
  the sharp critical aperture `log d` of order `1/(2 omega)`.

## 1. The channel probability law

For `omega>0`, define a probability measure on the positive integers by

```text
P_omega{d}
 =zeta(2+4omega)/zeta(1+2omega)
   mu(d)^2 d^(-1-2omega).                                (1)
```

This is normalized because

```text
sum_(d>=1)mu(d)^2d^(-sigma)=zeta(sigma)/zeta(2sigma),    (2)
```

with `sigma=1+2omega`.

Equation `(1)` is not an auxiliary probabilistic model.  It is exactly the distribution of the
squared divisor-coordinate norms of the normalized Möbius analysis channel after division by its
total squared norm:

```text
||(C_omega f)_d||^2/||C_omega f||^2=P_omega{d}           (3)
```

for every nonzero input `f`.

## 2. Exponential boundary-layer theorem

Let

```text
Y_omega(d)=2omega log d.                                  (4)
```

Then, under `P_omega`,

```text
Y_omega => Exp(1)                                        (5)
```

as `omega` decreases to zero.  Equivalently, for every `u>=0`,

```text
E_omega[exp(-uY_omega)] ->1/(1+u),                       (6)
```

and for every `0<=a<b`,

```text
P_omega{a<=2omega log d<=b}->e^(-a)-e^(-b).              (7)
```

### Proof

Using `(1)`--`(2)`, the Laplace transform is exactly

```text
E_omega[exp(-uY_omega)]
 = zeta(1+2omega(1+u)) zeta(2+4omega)
   /(
      zeta(2+4omega(1+u)) zeta(1+2omega)
    ).                                                    (8)
```

The Laurent expansion

```text
zeta(1+epsilon)=1/epsilon+O(1)                            (9)
```

gives

```text
zeta(1+2omega(1+u))/zeta(1+2omega)->1/(1+u),             (10)
```

while continuity of zeta on the real line to the right of one gives

```text
zeta(2+4omega)/zeta(2+4omega(1+u))->1.                   (11)
```

Equations `(8)`--`(11)` prove `(6)`.  The limit is the Laplace transform of the mean-one
exponential law and is continuous at zero, so the continuity theorem for Laplace transforms gives
`(5)`.  The exponential law has no atoms, hence `(7)` follows.

## 3. Sharp aperture quantiles

For every fixed `c>=0`, equation `(7)` gives

```text
P_omega{d<=exp(c/(2omega))}->1-e^(-c),                   (12)

P_omega{d>exp(c/(2omega))}->e^(-c).                      (13)
```

Thus:

1. every fixed divisor cutoff captures asymptotically zero mass;
2. a cutoff with `log D_omega=o(1/omega)` still captures asymptotically zero mass;
3. the window `D_omega=exp(c/(2omega))` captures the nontrivial fraction `1-e^(-c)`;
4. to capture asymptotically all mass one needs `2omega log D_omega` to tend to infinity.

This is the exact logarithmic boundary layer of the Möbius channel.  The scale is not an artifact of
an estimate: it is the limiting distribution of the channel norm itself.

## 4. Positive carrier consequence

Any finite-prime or finite-divisor Hilbert--Pólya approximation which represents the normalized
Möbius channel with asymptotically retained norm must grow its logarithmic aperture according to

```text
omega log D_omega -> infinity                            (14)
```

for full mass transport, or according to

```text
2omega log D_omega ->c in (0,infinity)                   (15)
```

to retain the nontrivial fraction `1-e^(-c)`.

The arithmetic state may be stored in a divisor channel, prime-factor incidence space, operator
domain, determinant, or global constraint, but it cannot remain in a fixed compact window.  This
quantifies the noncompact alternative in the bounded-syntax prime-capacity law.

For the coupled floor--Möbius attack, a candidate synthesis/covariance must therefore be tested on
the moving aperture `(12)`, not at a fixed divisor cutoff.  An estimate which is uniform only on
`log d=o(1/omega)` controls asymptotically none of the normalized input mass and cannot prove the
four-unit boundary transfer.

## 5. Scope and novelty

- `[PROVED]` The exact limiting distribution and aperture quantiles follow from the squarefree
  Dirichlet series and the zeta pole.
- `[PROVED]` The law describes the squared-norm distribution of the actual normalized Möbius
  channel.
- `[NOT PROVED]` The archimedean/power-sum synthesis is contractive on this moving aperture.
- `[NOT PROVED]` The theorem does not prove the boundary norm or RH.

The proof is a direct Abelian Laplace-transform argument from classical identities.  Independently
of whether this exact channel formulation has appeared in print, it does not clear the scientific
novelty gate and is classified as a route bridge rather than new scientific knowledge.

## 6. Lean decision

An end-to-end formalization requires the squarefree Dirichlet-series identity, the Laurent limit at
one, probability measures on the integer channel, and Laplace-transform weak convergence.  None is
currently packaged together in the RHTower tree.  A finite-coordinate wrapper would miss the
boundary-layer theorem, so no Lean file is added at this stage.

## Gates

- [x] exact channel probability measure identified
- [x] Laplace transform computed
- [x] exponential weak limit proved
- [x] sharp aperture quantiles proved
- [x] direct Hilbert--Pólya carrier consequence stated
- [x] novelty claim rejected conservatively
- [ ] contractive synthesis on the moving aperture
- [ ] four-unit boundary transfer
- [ ] RH

## Lean formalization (this sweep, complete and unconditional)

`formal/GaloisForLFunctions/RHTower/MobiusCriticalBoundaryLayerQuantiles.lean` and
`.../MobiusCriticalExponentialBoundaryLayerPaperCertificate.lean` certify the card's proved
payload: the squarefree Möbius clock mass `squarefreeMobiusClockMass`, its identification with the
divisor cutoff, and the portmanteau convergence of the clock law to the unit exponential
distribution on closed, open and moving apertures
(`tendsto_squarefreeMobiusClockMass_Icc`, `_Iic`, `_Ioi`, `_Iic_moving`, `_Iic_moving_atTop`).
