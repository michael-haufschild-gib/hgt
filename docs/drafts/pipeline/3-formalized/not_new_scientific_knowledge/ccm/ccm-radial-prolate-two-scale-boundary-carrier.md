# The constrained CCM radial-prolate tail has forced inner and outer scales

- **ID:** `ccm-radial-prolate-two-scale-boundary-carrier`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent sources:** fixed-mode prolate endpoint asymptotics, the constrained two-mode theorem,
  and the exact Fourier leakage identity
- **Statement:** The normalized constrained `h_0`--`h_4` exterior Fourier tail has an inner
  endpoint coordinate `rho=lambda^3(y-lambda)` with derivative limit `-2*pi^2`. The outer
  rescaling `r=lambda(y-lambda)` has total normalized `L2` mass tending to `1/(4*pi)`, although
  tightness on bounded `r` is not asserted. A CCM tail theorem must therefore track the endpoint
  sublayer and the possibly escaping mass profile together.

## Setup

Let

```text
g_lambda=(ell_1 e_(0,lambda)-ell_0 e_(4,lambda))
          /sqrt(ell_0^2+ell_1^2)                                  (1)
```

be the normalized vanishing-integral CCM two-mode source. Let `F` be the unitary Fourier transform
and put

```text
delta_lambda=||(1-P_lambda)F(g_lambda)||_2^2.                      (2)
```

With `d_0=1-chi_0^2` and `d_1=1-chi_4^2`, orthogonality gives the exact formula

```text
delta_lambda
 =(ell_1^2 d_0+ell_0^2 d_1)/(ell_0^2+ell_1^2).                    (3)
```

The constrained-prolate theorem supplies

```text
delta_lambda/d_1(lambda)->8/11.                                   (4)
```

## Boundary height

Inside the band,

```text
F(e_(m,lambda))(y)=chi_m(lambda)e_(m,lambda)(y),  |y|<=lambda.    (5)
```

The endpoint-response theorem gives

```text
|e_(m,lambda)(lambda)|^2/(lambda*d_m(lambda))->2*pi.               (6)
```

Since `d_0/d_1=O(lambda^(-8))`, the `m=0` endpoint is smaller than the `m=4` endpoint by
`O(lambda^(-4))`. Together with `ell_0^2/(ell_0^2+ell_1^2)->8/11`, equations `(1)`, `(5)`--`(6)`
give

```text
|F(g_lambda)(lambda)|^2/(lambda*d_1(lambda))->16*pi/11.            (7)
```

## Outer mass scale

Define the boundary-normalized outer profile

```text
R_lambda(r)
 =F(g_lambda)(lambda+r/lambda)/F(g_lambda)(lambda),   r>=0.        (8)
```

The denominator is nonzero for all sufficiently large `lambda` by `(7)`. Since the Fourier
transform is even,

```text
delta_lambda
 =2 integral_lambda^infinity |F(g_lambda)(y)|^2 dy.
```

The change of variables `y=lambda+r/lambda` gives the exact identity

```text
integral_0^infinity |R_lambda(r)|^2 dr
 =lambda*delta_lambda/(2|F(g_lambda)(lambda)|^2).                  (9)
```

Equations `(4)` and `(7)` therefore prove

```text
integral_0^infinity |R_lambda(r)|^2 dr ->1/(4*pi).                 (10)
```

Thus `r=lambda(y-lambda)` normalizes the **total** exterior mass. Equation `(10)` does not prove
tightness of `|R_lambda|^2dr` on bounded `r`; mass may escape to `r` growing with `lambda`. This
conclusion uses the entire leakage identity and makes no pointwise claim about decay width.

## Inner endpoint scale

Let `kappa_m(c)` be the prolate differential eigenvalue, with `c=2*pi*lambda^2`. The endpoint ODE
gives

```text
e_(m,lambda)'(lambda)/e_(m,lambda)(lambda)
 =(kappa_m(c)-c^2)/(2lambda)
 =-2*pi^2*lambda^3+O_m(lambda).                                  (11)
```

Differentiating `(5)` at the boundary and again using the dominance of the `m=4` endpoint yields

```text
F(g_lambda)'(lambda)/F(g_lambda)(lambda)
 =-2*pi^2*lambda^3+O(lambda).                                    (12)
```

Define the inner profile

```text
I_lambda(rho)
 =F(g_lambda)(lambda+rho/lambda^3)/F(g_lambda)(lambda),  rho>=0.  (13)
```

Then

```text
I_lambda(0)=1,
I_lambda'(0)->-2*pi^2.                                            (14)
```

On the outer coordinate, in contrast,

```text
R_lambda'(0)
 =F(g_lambda)'(lambda)/(lambda F(g_lambda)(lambda))
 ~-2*pi^2*lambda^2.                                               (15)
```

Hence the outer rescaling contains a thinner endpoint sublayer of width `lambda^(-3)` in the
original Fourier variable.

The scale separation is also visible in the exact inner mass:

```text
integral_0^infinity |I_lambda(rho)|^2 drho
 =lambda^3*delta_lambda/(2|F(g_lambda)(lambda)|^2)
 ~lambda^2/(4*pi).                                                (16)
```

The inner scale normalizes the endpoint derivative but not the total leakage mass; the outer scale
normalizes the total mass but has a diverging boundary derivative and may fail to be tight.

## Positive carrier theorem

Equations `(10)` and `(14)`--`(16)` force the architecture of the missing source theorem:

```text
inner radial-prolate endpoint profile at rho=lambda^3(y-lambda)
  matched to
outer mass profile at r=lambda(y-lambda)
  with a uniform transition law
  -> arithmetic dilation correlations in the closed Weil topology.                (17)
```

No fixed endpoint-jet truncation can replace `(17)`. Any one-scale limit used by the proof must
also account for the separate endpoint datum and prove the missing tightness rather than assume it.
The universal total outer mass `1/(4*pi)` supplies an exact normalization for any candidate radial
profile or defect measure. The universal inner slope `-2*pi^2` supplies its matching boundary
datum.

This is the source-side object that must be paired with the weighted all-prime coefficient tail,
the archimedean symbol, and the distinguished divisor/trace moments in the pointed global
incidence topology.

## Novelty audit and classification

### Parent overlap

- The endpoint ODE and fixed-mode asymptotics are classical prolate theory.
- The constants `8/11` and `16*pi/11` come from the repository's constrained source and endpoint
  theorems.
- Equation `(9)` is a change of variables in the exact leakage norm.

### Formula-level parent comparison

Dunster's radial approximation uses a Bessel argument `gamma*sqrt(eta)` with
`eta~2(1-sigma^2)(x-1)` at the radial endpoint. For fixed mode, `gamma=2*pi*lambda^2`, so its
classical inner scale is `x-1` of order `gamma^(-2)`, equivalently `y-lambda` of order
`lambda^(-3)`. The outer mass scale follows directly from the exact leakage norm and endpoint
height. Thus the scale separation is a useful constrained-source specialization of parent theory,
not a new asymptotic regime.

The constants `(10)` and `(14)` sharpen the CCM normalization and materially repair the route, but
the theorem fails the anti-theatre parent-interpolation gate after vocabulary erasure. It is
classified as a bridge. The candidate-new residue remains the arithmetic dilation constant in
`ccm-constrained-endpoint-euler-response-constant.md`.

## References

- D. Slepian, *Some Asymptotic Expansions for Prolate Spheroidal Wave Functions*, J. Math. Phys. 44
  (1965), 99--140.
- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Lean decision

**Correction, 2026-07-27.**  This section previously read "the formal tree has no prolate
integral/differential operator or fixed-mode asymptotic".  Both halves of the first clause are
**false**.  The prolate *integral* operator is `RHTower/ConstrainedProlateOperator.lean`
(`evenTimeBandFourier a = P_a F P_a`, proved compact and self-adjoint, with its concentration and
leakage operators); the prolate *differential* operator is `prolateSLAction` in
`RHTower/FuchsProlateScale.lean`, and its commutation with the integral operator is proved in
`RHTower/SlepianSincCommutation.lean` and `RHTower/SlepianBandCommutation.lean`, with the
consequent invariant-line diagonalization in `RHTower/ProlateDiagonalization.lean`.  What is
genuinely absent is the **fixed-mode asymptotic for the actual eigenvalues** `chi_n(lambda)`:
`RHTower/FuchsProlateScale.lean` formalizes the Fuchs *rate calculus* for the model rate
`A·lambda^(2n+1)·exp(-4 pi lambda^2)` and the prolate-to-Hermite scaling identity, but no theorem
identifies the true `chi_n(lambda)` with that rate.

**Superseded, 2026-08-15.**  "No Lean file is added by this card" is out of date: every equation the
card proves is now formal, in
`formal/GaloisForLFunctions/RHTower/CCMRadialTwoScaleCarrier.lean` (see the Lean status section
below).  The eigenvalue asymptotic remains an import, but it is an input of `(4)` and `(6)`, not of
anything the card derives.

## Lean status

**Formalized, 2026-08-15.**  Module
`formal/GaloisForLFunctions/RHTower/CCMRadialTwoScaleCarrier.lean` (wired, axiom-clean), built over
`CCMRadialGlobalDefectMass` and the corpus's leakage layer.

- **`norm_sq_twoModeExterior`** — equation `(3)`, exactly: for the normalized vanishing-integral
  two-mode source `g = (l_1 e_0 - l_0 e_1)/sqrt(l_0^2+l_1^2)`, orthogonality of the two exterior
  components gives `delta = (l_1^2 d_0 + l_0^2 d_1)/(l_0^2+l_1^2)`.  Stated for an arbitrary linear
  map on a real inner-product space, which is all the proof uses.
- `scaledProfile`, `scaledProfileSq` — the exterior profile at an arbitrary scale,
  `t |-> q(lambda + t/alpha)/q(lambda)`.  Equations `(8)` and `(13)` are the cases
  `alpha = lambda` and `alpha = lambda^3`.
- `integral_Ioi_shift`, `integral_Ioi_dilate` — the two elementary half-line changes of variables.
- **`integral_Ioi_scaledProfileSq`** — equations `(9)` and `(16)` at once:

  ```text
  int_0^infinity |profile at scale alpha|^2 = alpha * delta / (2 |q(lambda)|^2),
  ```

  exactly, for every positive scale.  The card's `(9)` is `alpha = lambda`, its `(16)` is
  `alpha = lambda^3`; no asymptotics enter.
- **`tendsto_integral_Ioi_scaledProfileSq_outer`** — equation `(10)`: the outer scale normalizes the
  total exterior mass, `int_0^infinity |R_lambda|^2 dr -> 1/(4 pi)`, from `(4)` and `(7)` alone.
- **`tendsto_integral_Ioi_scaledProfileSq_inner`** — equation `(16)`: the inner scale does *not*
  normalize the mass, `(int |I_lambda|^2)/lambda^2 -> 1/(4 pi)`.
- `scaledProfile_zero` — `I_lambda(0) = 1`.
- **`hasDerivAt_scaledProfile`** — the endpoint slope of the profile at scale `alpha` is exactly
  `q'(lambda)/(alpha q(lambda))`.
- **`endpointLogDeriv_eq`** — equations `(11)`-`(12)`: in the CCM aperture `c = 2 pi lambda^2`,
  `(kappa - c^2)/(2 lambda) = -2 pi^2 lambda^3 + kappa/(2 lambda)`.  The universal cubic term is the
  aperture, not the eigenvalue.
- **`tendsto_endpointLogDeriv_div_cube`** — equation `(14)`: whenever `kappa_m(c) = o(lambda^4)`,
  the inner-scale slope tends to the universal constant `-2 pi^2`.
- **`outerSlope_eq_sq_mul_innerSlope`** — equation `(15)`, as an identity: the outer slope is
  exactly `lambda^2` times the inner slope, so the outer coordinate's boundary derivative diverges
  at precisely the rate the inner coordinate removes.  The scale separation is algebra, not an
  asymptotic coincidence.

`#print axioms` on all eleven declarations returns exactly
`[propext, Classical.choice, Quot.sound]`.

Imported, not reproved: the constrained-prolate limit `(4)` and the endpoint-response height `(7)`
(both named hypotheses, and both formal in `CCMEndpointResponseConstants` given their own classical
inputs), the finite-Fourier eigenrelation `(5)`, and the eigenvalue asymptotic `kappa_m(c) = O(c)`.
The non-tightness of the outer coordinate, which this card explicitly does *not* assert, is proved
in `ccm-radial-prolate-global-defect-measure`.

## Gates

- [x] constrained leakage mass computed
- [x] boundary height computed
- [x] outer normalized mass proved
- [x] inner normalized slope proved
- [x] scale separation proved
- [ ] matched radial-prolate profile and transition law
- [ ] arithmetic correlations of the matched profile
- [ ] true Weil Rayleigh-excess and parity transfer
