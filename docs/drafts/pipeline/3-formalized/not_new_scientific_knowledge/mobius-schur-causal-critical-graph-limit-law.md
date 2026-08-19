# The coupled Möbius source has a strong critical causal graph limit

- **ID:** `mobius-schur-causal-critical-graph-limit-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [SEARCH] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** reciprocal-zeta bounds on `Re s>=1`, Laurent expansion at the zeta pole, and
  Laplace Paley--Wiener theory
- **Statement:** Both terms of the centered signed-Möbius Hardy decomposition converge strongly at
  the critical Euler boundary. Their sum is the canonical causal vector `e^(-t)`. Thus the complete
  Euler-line graph limit exists unconditionally; the only remaining RH-bearing discontinuity is
  the subsequent meromorphic contour shift to the anti-causal divisor boundary.

## 1. The two Hardy components

Put

```text
sigma=1+2omega,
c_omega=1/(1+omega),                                     (1)

K_omega(z)
 =zeta(1+z)/(1+omega+z)-c_omega/z.                       (2)
```

The pole at `z=0` in `(2)` is removable. In the notation of
`mobius-signed-coisometry-schur-transfer-law.md`, the renormalized floor-remainder component is

```text
H_omega(z)=K_omega(z)/zeta(1+2omega+z).                  (3)
```

The centered boundary component is

```text
G_omega(z)
 =c_omega/z(
    1/zeta(1+2omega+z)-1/zeta(1+2omega)
  ).                                                       (4)
```

The exact causal transfer identity is

```text
L F_omega=H_omega+G_omega.                               (5)
```

## 2. Strong floor-remainder limit

Define

```text
H_0(z)
 =1/(1+z)-1/(z zeta(1+z)).                               (6)
```

Then

```text
H_omega->H_0 in H2(Re z>0).                              (7)
```

### Proof

Pointwise convergence on `Re z>0` follows directly from `(2)`--`(3)`. We prove convergence of the
boundary values.

Choose a fixed small `r>0`. The Laurent expansion

```text
zeta(1+z)=1/z+gamma+O(z)                                 (8)
```

shows that the singular terms in `(2)` cancel uniformly for small `omega` and `|z|<=r`; hence

```text
|K_omega(it)|<=C,        |t|<=r.                         (9)
```

The reciprocal has a simple zero at the zeta pole, so

```text
|1/zeta(1+2omega+it)|<=C|2omega+it|                      (10)
```

in the same region. Thus `H_omega(it)` is uniformly bounded for `|t|<=r`.

For `|t|>=r`, the classical line-one bounds give

```text
|zeta(1+it)|<=C log(2+|t|),
|1/zeta(1+2omega+it)|<=C log(2+|t|).                     (11)
```

Equations `(2)`--`(3)` therefore imply

```text
|H_omega(it)|
 <=C log(2+|t|)^2/|t|.                                   (12)
```

The square of `(12)` is integrable away from the origin. Dominated convergence on the boundary
proves `(7)`.

## 3. Complete causal convergence

The centered-boundary theorem proves

```text
G_omega->G_0:=1/(z zeta(1+z))
in H2(Re z>0).                                           (13)
```

Equations `(6)` and `(13)` give the exact cancellation

```text
H_0+G_0=1/(1+z).                                         (14)
```

Combining `(5)`, `(7)`, and `(13)` yields

```text
L F_omega->1/(1+z)
in H2(Re z>0).                                           (15)
```

Under inverse Laplace transformation,

```text
F_omega->e^(-t)
strongly in L2(0,infinity).                              (16)
```

The two limiting time-domain components are

```text
G_0 <-> m_0(t)=sum_(n<=e^t)mu(n)/n,

H_0 <-> e^(-t)-m_0(t).                                  (17)
```

Thus the weighted-Mertens boundary vector and the floor remainder recombine exactly into the
incoming causal pole source.

## 4. The noncommuting square

Let `C_omega` denote Euler-line causal continuation and `B_omega` the meromorphic contour transfer
to the Hardy/divisor boundary. Equation `(16)` proves the top and left sides of the diagram

```text
finite positive-shift source F_omega  --B_omega--> boundary source
              | omega->0                              |
              v                                       v
        causal vector e^(-t)       --B_0--> anti-causal residue profile.    (18)
```

The vertical limit on the left exists strongly. The square need not commute: moving the contour
crosses the poles `z=rho-1-2omega`, and their residues form the off-line divisor profile. Therefore

```text
failure of (18) to commute
 =complete anti-causal contour-jump seam.                (19)
```

This is now the only analytic discontinuity in the coupled source construction. Neither failure
of causal `L2` convergence nor failure of constant-channel renormalization remains available as an
explanation.

## 5. Positive CCM/Connes obligation

A successful construction must extend `(18)` by a pointed residue object and prove

```text
strong causal critical limit
  + orbit-sensitive residue seam
  + nonexpansive pole-to-divisor covariance
  -> ||ell_E||_2<=2
  -> RH.                                                   (20)
```

Ordinary continuity of `B_omega` would be too strong: the Hardy leakage theorem proves a unit-size
operator-norm jump whenever an off-line zero layer crosses the boundary. The required statement is
instead a source-specific bound on the distinguished vector through the noncommuting square.

## 6. Attacks and exact scope

1. Equation `(16)` is entirely causal and does not imply innerness of the shifted quotient.
2. Applying a bounded operator after taking the limit cannot reconstruct the residues lost by
   contour crossing.
3. A symmetric polynomial orbit insertion preserves the causal convergence mechanism while adding
   a residue packet. Therefore the bottom map in `(18)` must be pointed by the exact completed
   source and divisor marking.
4. The theorem does not provide the nonexpansive covariance in `(20)` and does not prove RH.

## 7. Scientific classification and Lean decision

The proof is a dominated-convergence argument using classical line-one zeta bounds. It is a route
bridge, not new scientific knowledge.

The Lean tree lacks the reciprocal-zeta boundary estimates, Laplace Hardy space, and meromorphic
contour graph. Formalizing only the algebraic cancellation `(14)` would not certify the strong
limit `(16)`, so no Lean file is added.

## Gates

- [x] renormalized floor-remainder component isolated
- [x] uniform local pole cancellation proved
- [x] global reciprocal-zeta Hardy majorant proved
- [x] strong floor-remainder limit proved
- [x] complete strong causal critical limit proved
- [x] noncommuting continuation square isolated
- [ ] construct the pointed residue extension of the square
- [ ] prove source-specific nonexpansive pole-to-divisor covariance
- [ ] four-unit boundary energy
- [ ] RH

## Lean formalization (this sweep, complete and unconditional)

Certified in `formal/GaloisForLFunctions/RHTower/MobiusSchurBoundaryPaperCertificate.lean`,
resting on `.../MobiusCenteredSchurBoundary.lean`, `.../MobiusCausalSourceLimit.lean` (equation
`(16)`: the causal pole vector and its boundary transform) and `.../CausalLaplacePlancherel.lean`.
