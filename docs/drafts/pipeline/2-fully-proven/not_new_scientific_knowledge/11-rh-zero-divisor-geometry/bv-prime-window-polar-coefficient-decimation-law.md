# BV prime-window polar coefficient decimation law

- **ID:** `bv-prime-window-polar-coefficient-decimation-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[VALUE RELATION]`, `[TOP-DOWN INTERFACE DISCHARGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `bounded-variation-prime-window-divisor-tomography.md`;
  `bv-prime-window-laurent-orientation-polarization.md`
- **Statement:** Reciprocal integer dilation of a compact-BV prime window becomes exact
  square-index coefficient decimation before continuation.  On each uncensored zeta pole, the
  induced Laurent value is multiplication by the horizontal character `r^(2rho-1)`.  The standard
  Dirichlet--Hardy completion cannot carry these meromorphic sources faithfully.

## 1. Bilateral dilation ladder

Let `W` be a compactly supported BV prime window, let `r>=2` be an integer, and for `j in Z` put

```text
W_j(x)=W(r^j x).                                         (1)
```

Write

```text
M_j(s)=integral_0^infinity W_j(x)x^(-s)dx,
T_j(N)=sum_(k>=1) Lambda(k)/sqrt(k) W_j(N/k),
p_j(N)=2M_j(3/2)sqrt(N)-2T_j(N).                         (2)
```

Every sum defining `T_j(N)` is finite.  A change of variables gives

```text
M_j(s)=r^(j(s-1))M_0(s).                                 (3)
```

Set `q=r^2`.  Then for every `j in Z` and `N>=1`,

```text
p_j(N)=p_(j-2)(qN).                                      (4)
```

### Proof

The finite prime parts agree term by term:

```text
T_(j-2)(qN)
 =sum_k Lambda(k)/sqrt(k) W(r^(j-2)r^2N/k)
 =T_j(N).                                                (5)
```

For the polar part, `(3)` and `sqrt(r^2N)=r sqrt(N)` give

```text
M_(j-2)(3/2)sqrt(qN)
 =r^((j-2)/2)M_0(3/2) r sqrt(N)
 =M_j(3/2)sqrt(N).                                       (6)
```

Equations `(5)` and `(6)` prove `(4)`.

Define coefficient decimation and inflation by

```text
(D_q a)(N)=a(qN),
(S_q a)(M)=a(M/q) if q divides M, and 0 otherwise.       (7)
```

Then `(4)` is the exact source relation

```text
D_q p_(j-2)=p_j,      D_q S_q=1.                         (8)
```

This relation is finite-coefficient algebra.  It uses neither analytic continuation nor any zeta
zero.

## 2. Continued Laurent character

Let `F_j` be the canonical meromorphic continuation of the ordinary Dirichlet series of `p_j`.
The formal BV divisor-tomography theorem gives, at a zeta zero `rho` of multiplicity `m_rho`,

```text
R_j(rho):=Res_(s=rho+1/2) F_j(s)
 =2m_rho M_j(rho+1/2).                                  (9)
```

When `M_0(rho+1/2)!=0`, equations `(3)` and `(9)` imply

```text
R_j(rho)/R_(j-2)(rho)=r^(2rho-1).                       (10)
```

Thus the same operator which is literal square-index decimation on finite coefficients becomes
the horizontal zero character on the one-dimensional Laurent fibre.  Functional-equation
reflection `rho#=1-conjugate(rho)` sends the character to its reciprocal conjugate:

```text
r^(2rho#-1)=1/conjugate(r^(2rho-1)).                    (11)
```

For the reciprocal pair `j=1,-1`, `(4)` and `(10)` read

```text
p_1(N)=p_(-1)(r^2N),
R_1(rho)=r^(2rho-1)R_(-1)(rho).                         (12)
```

This is the finite-coefficient source behind the Laurent orientation polarization.

## 3. Exact off-multiple layer

The operator `P_q=S_qD_q` is the coordinate projection onto indices divisible by `q`.  Therefore

```text
c_(j-2)=(1-P_q)p_(j-2)                                  (13)
```

is supported on indices not divisible by `q`, and its Dirichlet series is

```text
C_(j-2)(s)=F_(j-2)(s)-q^(-s)F_j(s).                    (14)
```

At every uncensored zero pole, `(10)` gives the orientation-free residue split

```text
Res C_(j-2)=(1-r^(-2))R_(j-2).                          (15)
```

Indeed,

```text
q^(-(rho+1/2)) r^(2rho-1)=r^(-2).                      (16)
```

The square-index projection therefore removes the same positive fraction of every Laurent fibre,
independently of zero height, multiplicity, and horizontal location.  Orientation occurs only in
the decimated channel `(10)`, not in the complementary layer `(15)`.

## 4. Weighted coefficient-space law

For `alpha>=0`, let

```text
H_alpha={a : sum_N |a(N)|^2 N^(-2alpha)<infinity}.       (17)
```

Direct reindexing proves

```text
||D_q a||_(H_alpha)<=q^alpha ||a||_(H_alpha).            (18)
```

The normalized operator `q^(-alpha)D_q` is therefore contractive.  If a faithful source-to-pole
realization placed the dilation ladder in `H_alpha`, made Laurent evaluation continuous, and
intertwined `(8)`, its eigenvalue law `(10)` would give

```text
|r^(2rho-1)|<=r^(2alpha),
Re(rho)<=1/2+alpha.                                      (19)
```

Thus polynomial coefficient weight `alpha` can force only the corresponding shifted zero-free
line.  The critical line requires an unshifted, scale-zero completion.

## 5. Dirichlet--Hardy exclusion

The unweighted Dirichlet--Hardy space `H_0` consists of square-summable coefficient sequences.
Its ordinary Dirichlet series is holomorphic on `Re(s)>1/2`.  Consequently:

> If `M_W(rho+1/2)!=0` at any nontrivial zeta zero, then the polar coefficient `p_W` does not
> belong to `H_0`.

Otherwise its `H_0` Dirichlet series would be holomorphic at `rho+1/2`.  It agrees with `F_W` on
`Re(s)>3/2`, so uniqueness of meromorphic continuation would remove the nonzero pole `(9)`, a
contradiction.

The two sharp windows with irrationally related logarithmic widths from the BV tomography theorem
jointly detect the complete nontrivial divisor.  Hence at least one of their canonical coefficient
sequences is unconditionally outside `H_0`.  Standard square-summable coefficient theory cannot be
invoked as the missing positive completion.

This exclusion is positive information about the required object: a successful scale-zero space
must be a singular graph or boundary completion of finite source truncations with an additional
principal-part coordinate.  It cannot be the ordinary Hilbert space of analytic Dirichlet series,
and it cannot quotient out the Laurent fibres whose faithfulness is needed in `(10)`.

## 6. Top-down consequence and exact boundary

For the fixed sharp window `W=1_[1,2]` and `r=2`, its Mellin transform is zero-free on
`Re(s)>1`.  Therefore a source-defined positive boundary quotient satisfying

```text
finite coefficient decimation descends as a contraction,
uncensored Laurent residues extend continuously and faithfully              (20)
```

would give, for every right off-critical zero,

```text
|2^(2rho-1)|<=1 -> Re(rho)<=1/2,                         (21)
```

and functional-equation reflection would prove RH.  Neither condition in `(20)` follows from the
present theorem.  Assuming residue contractivity directly would merely restate the missing
orientation sign.

The live construction problem is recorded separately in
`../../1-in-progress/bv-prime-window-decimation-boundary-contraction-rh.md`.

## Literature calibration

- H. Hedenmalm, P. Lindqvist, and K. Seip, *A Hilbert space of Dirichlet series and systems of
  dilated functions in L2(0,1)*, [arXiv:math/9512211](https://arxiv.org/abs/math/9512211), supplies
  the square-summable coefficient space used in Section 5.
- K. Seip, *Zeros of functions in Hilbert spaces of Dirichlet series*,
  [arXiv:1206.2815](https://arxiv.org/abs/1206.2815), locates the analytic zero theory of that space
  in `Re(s)>1/2`; it does not provide a meromorphic principal-part completion.
- J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, [J. Theor. Nombres Bordeaux 16 (2004)](https://www.numdam.org/articles/10.5802/jtnb.434/),
  supplies source-defined Sonine spaces with zero evaluators, but not the coefficient-decimation
  contraction `(20)`.

## Formal boundary

The continuation and residue laws used in `(9)` are formalized in:

- `formal/GaloisForLFunctions/RHTower/BVPrimeWindowContinuation.lean`;
- `formal/GaloisForLFunctions/RHTower/BVPrimeWindowDivisorTomography.lean`.

`formal/GaloisForLFunctions/RHTower/BVPrimeWindowDilationOrientation.lean` now constructs the
forward and inverse compact-BV windows, proves the reciprocal-pair coefficient decimation `(12)`
for both the finite von-Mangoldt window and the complete prime--polar coefficient, and proves the
continued Laurent character and its oriented squared-norm factorization.  These modules are wired
through `formal/GaloisForLFunctions/RHTower.lean`.  The full bilateral integer ladder and the
off-multiple layer law `(15)` remain paper theorems.

## Gates

- [x] exact finite coefficient decimation law
- [x] exact Laurent character law
- [x] exact off-multiple residue split
- [x] weighted coefficient-space norm law
- [x] ordinary Dirichlet--Hardy completion excluded for every uncensored source
- [x] fixed-window conditional chain to RH isolated
- [x] formalize compact-BV forward/inverse dilation and reciprocal-pair coefficient decimation
- [ ] formalize the full bilateral integer ladder and off-multiple layer law
- [ ] construct the scale-zero source boundary quotient `(20)`
- [ ] prove source-side positivity without divisor-selected weights
- [ ] compose an unconditional proof of RH
