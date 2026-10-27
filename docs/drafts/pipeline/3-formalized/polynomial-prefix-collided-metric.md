# Polynomial integer prefixes for the full collided metric

- **ID:** CDG-POLYNOMIAL-PREFIX-METRIC
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Conjugate-Diagonal Geometry question 2; fixed-strip source geometry.
- **Count:** Strengthening of contribution 1; no separate contribution.
- **Scope:** Finish this existing polynomial-prefix and local-selection work. Start no new contribution. No hgtl7, web searches, or novelty checks.

## Exact construction

Let b be the fixed smooth planar bump `sourceCutoff 0`, equal to one on
the unit disc and supported in the disc of radius two. Put t=n+1 and

```
chiStrip_n(s) = b((Re(s)-1/2) + i Im(s)/(4t)).
```

The cutoff equals one at every actual xi zero with `|Im(s)|<=n+2`.
Its support has `|Re(s)-1/2|<=2`, `|Im(s)|<=8t`, hence lies in the
disc of radius `11t`. Let M>=1 be the sum of one and the supremum norms
of the fixed bump's two first and two pure second derivatives. Set

```
C = ceil(M),
K_n = C t^20,
eta_n = exp(-K_n),
N_n = (C+4) t^20.
```

Use the literal reflected integer theta prefix through `N_n+1`, with
entire amplitude A_N and its first moment B_N=-A_N'. For a real test psi,

```
Q_n(psi) = pi^-1 integral chiStrip_n(s) psi(s)
           eta_n |B_N(s)|^2/(|A_N(s)|^2+eta_n)^2 dA(s).
```

The source, regulator and cutoff depend only on stage. All readings of
nonnegative tests are nonnegative.

## Full-trace endpoint

Write `k_L(d)=2cosh(2Ld)-2`, `S(f)=4(integral|f|+integral|f''|)`, and
let D_j be the actual multiplicity-weighted collided depth moment. The
universal coefficient B>=0 precedes all test/order/stage choices:

```
|Q_n(|F_(twist_tau f)|^2 k_L^j)-D_j(twist_tau f,L)| / 4^j
 <= S(f)^2 [B/t^2 + 40 sourceReferenceTail(n)]
 <= S(f)^2 [B/t^2 + (640/n)(C_xi+log(n+4))].
```

Domain: n>=1, compact C² test f, a>=0 containing its support,
`|tau|<=n/2`, and `a+j|L|<=2log(n+1)`. Consequently, for every epsilon>0,
one stage threshold works for all these choices with S(f)<=1. The trace
retains every actual multiplicity. The zeroth moment computes the collided
form; the first computes its Hecke defect.

## Dependency-closed paper proof

1. The affine cutoff has horizontal derivative one and vertical derivative
   `1/(4t)`. Compact support of the fixed bump bounds its first derivatives
   and Laplacian by M at every stage. No derivative bound is assumed.
2. On the cutoff support and unit complex neighborhoods,
   `|Re(s)-1/2|<=3`. Fourier estimates give
   `|F_f(s-i tau)exp(u(s-1/2))|<=S(f)exp(3(a+|u|))`.
   Unit-circle Cauchy estimates give the same bound for the first derivative.
   The squared-modulus Laplacian formula and exact depth-kernel translation
   recurrence give the test-Laplacian bound
   `4^(j+1) M S(f)^2 exp(6(a+j|L|)) <= 4^(j+1) M S(f)^2 t^12`.
3. The existing xi logarithmic-square estimate, at integer index `11n+9`,
   gives `integral_(disc 11t) (log|xi|)^2 <= C1 t^6` for an actual C1.
   Since C>=M>=1 and n>=1, K>=4. Scalar regularization, area `121pi t^2`,
   and `exp(-K/2)<=2/K` bound the M-weighted local potential error by
   `(121pi+8C1)t^-14`. Write this proved constant as D.
4. Actual theta integrand moduli are ordinate-independent on a fixed
   real-part strip. The existing positive-source envelope and Gaussian
   integer tail bound the M-weighted finite-potential error by
   `C0 M exp(K-(N+1)^2)`, where C0 is obtained from those actual envelopes.
   Now N>=K+4, `(N+1)^2>=3K`, and `M<=K<=exp K`, so this is at most
   `C0 exp(-K)<=C0 t^-20`.
5. Green's identity uses `Delta(half log(|A|^2+eta))=2P_eta`.
   With normalization `1/pi`, the finite-source and regularization errors
   are at most `242 C0 4^j S(f)^2 t^-6` and
   `(2D/pi)4^j S(f)^2 t^-2`, respectively.
6. At every actual zero where chiStrip_n differs from one, the old radial
   cutoff chi_n vanishes. The fixed-strip transform majorant therefore
   bounds the omitted trace by `40*2^j*S(f)^2*sourceReferenceTail(n)`.
   The tail is the already proved actual summable reference density, with
   its arithmetic logarithm-over-radius certificate.
7. Add the three errors, use t^-6<=t^-2 and 2^j<=4^j, and take
   `B=242C0+2D/pi`. The source-reference tail and t^-2 both tend to zero.
   Homogeneity in S(f)^2 gives uniformity over the entire normalized family.

## Shrinking-disc selection

Keep the same prefix and regulator. Put `r_n=1/(16t^6)` and use
`phi_(c,n)(s)=b((s-c)/r_n)`. For `0<=Re c<=1`, `|Im c|<=n/2`,

```
|Q_n(phi_(c,n))-sum_rho m_rho phi_(c,n)(rho)| <= E/t^2,
E = 15488 C0 + 128D/pi.
```

For 0<r<=1/8, every point in the localized support satisfies
`|Re(s)-1/2|<=3/4`, `|Im(s)|<=n+1`. Its compressed-coordinate norm is
at most `3/4+1/4=1`; hence chiStrip_n phi=phi exactly. Rescaling gives
`|Delta phi|<=M/r^2`. Since `1/r_n^2=256t^12`, the finite-source error is
`15488C0/t^6`, and the regularization error is `(128D/pi)/t^2`.
There is no omitted local trace or zero-free-boundary premise.

The smooth bump equals one on the inner closed disc, lies between zero
and one, and vanishes outside the outer closed disc. The actual divisor
has finite mass in that outer disc. Finite summation therefore gives

```
count(closedBall(c,r_n)) <= Q_n(phi_(c,n))+E/t^2,
Q_n(phi_(c,n))-E/t^2 <= count(closedBall(c,2r_n)).
```

Counts retain multiplicity. At stages n>=max(1,ceil(4E)), E/t^2<1/2:
an inner zero forces Q_n>1/2, while Q_n>1/2 forces an outer zero.
The threshold precedes every center choice. This proves a two-radius neighborhood detector, uniformly before the center
is chosen. Both exact Lean endpoints below pass their final source-only check.

## Formal verification

Final source-only checks passed for `PolynomialThetaMetric` (37030) and
`PolynomialThetaLocalSelection` (96188). All six audited endpoint closures
contain only `propext`, `Classical.choice`, `Quot.sound`.

| Exact declaration | Result |
|---|---|
| `polynomialThetaSourceMomentReading_nonneg` | Positivity of every prescribed finite moment reading |
| `exists_polynomialThetaSource_aperture_error_bound` | One universal homogeneous reference-tail certificate |
| `exists_polynomialThetaSource_aperture_logarithmic_bound` | Arithmetic logarithm-over-radius certificate |
| `polynomialThetaSource_uniform_test_aperture_moments` | Uniform normalized growing-family convergence |
| `exists_polynomialThetaLocalReading_mass_sandwich` | Uniform inner/outer full-multiplicity count bounds |
| `polynomialThetaLocalReading_uniform_zero_detector` | Uniform two-radius detector at threshold 1/2 |

Dependency leaves also passed individual Lean checks and standard-only
endpoint axiom audits:

- `SourceStripTransformBounds`, `StripSourceCutoff`, `StripSourceMomentBounds`.
- `RHTower/ThetaCusp/ThetaCuspStripAmplitudeBounds`.
- `PolynomialSourceScale`, `PolynomialSourceError`, `PolynomialThetaPotential`.
- `StripSourceTail`, `PolynomialThetaReadingError`.
- `SourceLocalCutoff`, `SourceLocalTrace`, `PolynomialThetaLocalMetric`.

All finished leaves are imported by their owning umbrellas; no umbrella was
compiled. Olean files were produced only for written importers. Endpoint checks
wrote no oleans. Own completed scratch files were removed. Detailed check
history is retained in `logs/conjugate-diagonal-geometry.md`.

## Boundaries

Polynomial integer atom count is a statement about the prescribed finite
source. It does not bound numerical integration cost or required precision.
Neighborhood selection gives no zero-spacing lower bound or simplicity law.
The conjugate-diagonal current retains positive off-line mass; it supplies
neither successor charge, reflection positivity, capacity payment nor RH.
Existing rescaling and divisor-count machinery are reused, not counted as
separate contributions. Earlier source comparisons are historical; no novelty
audit remains in the authorized closure workflow.
