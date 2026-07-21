# Theta-likelihood normal-crossing prime-face rigidity

- **ID:** `theta-likelihood-normal-crossing-prime-face`
- **Stage:** 3-formalized
- **Type:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [LEAN-PROVED] [UNCONDITIONAL] [NO RH CLAIM]`
- **Parents:** `theta-likelihood-ray-boundary-residue.md`,
  `theta-likelihood-eisenstein-mass-shell-orientation.md`,
  `theta-wigner-eisenstein-orientation-current.md`
- **Formal target:**
  `formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodNormalCrossingPrimeFace.lean`

## Representation correction

The common-temperature prime first layer is not itself a Wigner pair: the two source legs have
temperatures `B(y+t)` and `B(y-t)`, generally unequal.  Attempting to insert the common-`B`
factorization directly into the Fourier/Bezoutian window is therefore invalid.

The stronger replacement uses the two temperatures as normal-crossing coordinates.  It proves
that the common corner conormal transports rigidly along the union of the two actual boundary
faces.

## Exact atomwise desingularization

Put

```text
g_n=n^2-1,
A_n=exp(-3*g_n/2)*n^4,
R_n=exp(-3*g_n/2)*(3/2)*n^2*g_n,
S_n(B)=exp(-B*g_n)*(B*A_n+R_n),
B(x)=pi*exp(2*x)-3/2,
C(x)=4*pi*exp(5*x/2)*exp(-pi*exp(2*x)).                  (1)
```

Then for every real `x` and natural `n`, with no sign hypothesis on `B(x)`,

```text
thetaCuspSourceTerm(x,n)=C(x)*S_n(B(x)).                 (2)
```

Thus `S_n` is not merely a boundary renormalization of a positive-temperature likelihood ratio.
It is the exact entire coefficient of the original theta atom in the intrinsic coordinate.  In
particular,

```text
S_1(B)=B,
S_n(0)=R_n.                                               (3)
```

## Two-temperature product shell

For a product shell `k`, define

```text
Pi_k(B,D;z)
 =sum_(nm=k) S_n(B)S_m(D)
      exp(i*(log(n)-log(m))*z/2),                         (4)
```

and let `Pi_k'(B,D;z)` denote its spectral derivative.  The two-face boundary symbol is

```text
F_k(B;z)=Pi_k(B,0;z)+Pi_k(0,B;z).                        (5)
```

Let `Phi_k` be the unweighted likelihood/Eisenstein mass-shell phase already formalized.

## Theorem: prime-face rigidity

If `p` is prime, then for every real `B` and complex `z`,

```text
F_p(B;z)=B*R_p*Phi_p(z),
F_p'(B;z)=B*R_p*Phi_p'(z).                               (6)
```

Consequently, for every nonzero `B`,

```text
B^(-1)*F_p(B;z)=R_p*Phi_p(z),
B^(-1)*F_p'(B;z)=R_p*Phi_p'(z).                          (7)
```

The normalized prime face is independent of position along the face.  It is exactly the common
corner first-boundary-layer limit previously obtained as `B downarrow 0`.  Hence the corner
conormal is not trapped at the artificial equal-temperature diagonal: it extends canonically
along both two-ended source faces.

If `B>0` and `Im(z)>0`, then `R_p>0` and

```text
Im(F_p'(B;z)*conj(F_p(B;z)))<0.                          (8)
```

## Source-level face theorem

Let `x_*` be the exact point with `B(x_*)=0`.  Define the paired source boundary phase

```text
G_k(x;z)
 =sum_(nm=k)
   [theta_n(x)theta_m(x_*)+theta_n(x_*)theta_m(x)]
   exp(i*(log(n)-log(m))*z/2).                            (9)
```

By `(2)`, `(5)`, and `B(x_*)=0`, for every prime `p`,

```text
G_p(x;z)
 =C(x)C(x_*)B(x)R_p Phi_p(z),                            (10)
G_p'(x;z)
 =C(x)C(x_*)B(x)R_p Phi_p'(z).                           (11)
```

Therefore `B(x)>0` and `Im(z)>0` imply

```text
Im(G_p'(x;z)*conj(G_p(x;z)))<0.                          (12)
```

This is an actual theta-source statement on the two boundary faces, not a statement only about
the auxiliary likelihood response.

## Dependency-closed proof

Write `Y=pi*exp(2*x)=B(x)+3/2`.  The theta atom is

```text
theta_n(x)
 =2*pi*exp(5*x/2)*n^2*(2*Y*n^2-3)*exp(-Y*n^2).          (13)
```

The right side of `(2)` equals

```text
4*pi*exp(5*x/2)*exp(-Y)
 *exp(-B(x)*g_n)*exp(-3*g_n/2)
 *[B(x)*n^4+(3/2)*n^2*g_n].                              (14)
```

Since `Y=B(x)+3/2` and `g_n=n^2-1`, the exponential factors in `(14)` combine to
`exp(-Y*n^2)`, while the bracket becomes

```text
n^2*(Y*n^2-3/2).
```

This turns `(14)` into `(13)` and proves `(2)` by algebra.  No division by `B` occurs.

For a factor pair `nm=p`, primality gives either `(n,m)=(1,p)` or `(p,1)`.  Using `(3)`, in both
cases

```text
S_n(B)S_m(0)+S_n(0)S_m(B)=B*R_p.                        (15)
```

Substitution of `(15)` term by term in `(5)` proves the phase identity in `(6)`.  Differentiating
the finite exponential sum proves the derivative identity.  Division by nonzero `B` gives `(7)`.
The previously formalized strict current of `Phi_p`, multiplied by the positive real square
`(B*R_p)^2`, proves `(8)`.

Finally substitute `(2)` into `(9)`, use `B(x_*)=0`, factor out the positive common
desingularizers, and apply `(6)`.  This proves `(10)`--`(11)`; `(12)` follows from the same positive
real scaling law.  Every sum involved in the shell identities is finite.

## Hostile audit

Verdict: `SURVIVES PRELIMINARY ATTACK` as a source-specific boundary theorem; not an RH proof.

1. **The common-temperature category error is removed.**  Equations `(4)`--`(7)` use independent
   temperatures and then restrict to the two coordinate faces.  No claim identifies
   `B(y+t)=B(y-t)`.
2. **This is stronger than the scalar prime-axis quotient.**  Equation `(10)` is the literal
   theta-atom trace on both boundary faces and holds at every positive opposite-leg temperature.
   Nevertheless, restricting to primes still discards composite interior data; it cannot by
   itself prove global orientation.
3. **The full Wigner integral remains open.**  Boundary-face orientation does not dominate the
   two-temperature interior or the corrected endpoint windows.  A trace-to-bulk theorem is still
   required.
4. **No hidden zero hypothesis occurs.**  Primality, exact theta algebra, and the already proved
   divisor-phase current are the only sign inputs.
5. **The analytic sign is not a real-frequency sign.**  Strict current holds for `Im(z)>0`; the
   physical Wigner divisor character is a real-boundary specialization.

The strongest positive consequence is a rigidity law: after normalization by the ground
coordinate, the prime conormal phase is constant along the complete normal-crossing boundary.
This identifies a source-defined two-ended boundary datum which a future Fourier/Bezoutian
trace-to-bulk theorem can consume without the invalid equal-temperature substitution.

## Prior-art audit

- Hedenmalm's 2026 theta spectral problem supplies the source and boundary-value architecture but
  does not introduce this likelihood coordinate or two-temperature normal-crossing phase.
- Sondow--Dumitrescu gives the horizontal Xi-modulus monotonicity/RH equivalence; it does not
  produce a source boundary current.
- Dimitrov--Xu expresses transform Wronskians through correlation kernels and gives an RH density
  criterion, but does not contain the atom-plus-ray likelihood factorization or `(6)`.
- The algebraic observation that Dirichlet convolution separates units, primes, and composites is
  classical.  Candidate novelty is its exact theta-source realization `(2)`, rigid two-face
  transport `(6)`--`(7)`, and strict source current `(12)`.  Priority remains unverified.

## New open core

`[OPEN CORE]` Prove a source-specific trace-to-bulk identity or positivity law transporting the
paired normal-crossing face current `(12)` through the complete two-temperature Wigner interior
and corrected product-fibre windows.  The theorem must retain composite data rather than factor
through the disconnected prime-axis quotient.

## Gates

- [x] Internal corpus and failed-route audit
- [x] External parent/noncollision audit
- [x] Hostile category and circularity audit
- [x] Dependency-closed paper proof
- [x] Exact Lean formalization
- [x] Axiom, module, index, and lint audit
