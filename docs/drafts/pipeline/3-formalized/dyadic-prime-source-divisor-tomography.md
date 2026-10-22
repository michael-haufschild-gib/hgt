# One dyadic prime source recovers the complete right Xi divisor

- **ID:** `dyadic-prime-source-divisor-tomography`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / source-defined CCM divisor tomography / `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
  `[NOT AN RH PROOF]`
- **Parents:** the dyadic sharp-window quadrature continuation, logarithmic-derivative residue
  calculus, and the completed Xi/zeta order identity in the critical strip

## Main theorem

Define the source-only dyadic statistic

```text
W(n)=sum_(n/2<k<=n) Lambda(k)/sqrt(k),
S(n)=4(1-1/sqrt(2))*sqrt(n)-2W(n).
```

Its ordinary Dirichlet series on `Re(s)>3/2` equals the canonical continuation
`dyadicSharpPrimeContinuedSource(s)`. This continuation is meromorphic on `Re(s)>1/2`.
On `Re(s)>1`, its simple-pole support is exactly

```text
s=rho+1/2,
Xi(rho)=0,
Re(rho)>1/2.
```

If `rho` has analytic multiplicity `m(rho)`, then

```text
TC_(rho+1/2)(dyadicSharpPrimeContinuedSource)
 =2*M_log2(rho+1/2)*m(rho),
```

where

```text
M_L(s)=A_L(s-1)
```

is the sharp-window Mellin factor. Since `M_log2(s)` is nonzero for `Re(s)>1`, normalization
recovers the exact multiplicity:

```text
TC_(rho+1/2)/(2*M_log2(rho+1/2))=m(rho).
```

Consequently one fixed, source-defined dyadic von-Mangoldt statistic recovers the complete right
off-critical Xi divisor with multiplicity. Its continuation is analytic throughout `Re(s)>1`
if and only if RH holds.

The bundled Lean declaration is

```text
dyadicSharpPrimeSourceDivisorTomography_capstone
```

in

```text
GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowDivisorTomography
```

## Formal strengthening over the previous carrier theorem

The fixed-window Weil observable already recovered the divisor, but its coefficient sequence was
defined from the Xi divisor. The new theorem moves multiplicity-exact tomography to an explicit
prime source. No rectangular Guinand--Weil extension, zero enumeration, divisor-fed coefficient,
finite-prime cutoff path, or abstract explicit-formula premise occurs in `S(n)`.

Thus the positive Connes-route obligation is narrower:

```text
one fixed dyadic prime source
  -> canonical source continuation
  -> complete off-critical divisor with multiplicity
  -> prove the continuation has no poles on Re(s)>1
  -> RH.
```

Equivalently, one may prove a critical negative-part energy bound for `S(n)`. The formalized
one-abscissa theorem already gives the quantitative implication

```text
sum S(n)^-/n^(1+alpha)<infinity
  -> Re(rho)<=1/2+alpha for every Xi zero.
```

At `alpha=0` this would prove RH. The required convergence estimate remains open.

This source transform is a useful exact formal bridge, but it is a direct specialization of the
bounded-variation moving-window Euler logarithmic-derivative transform.  It therefore does not
clear the scientific-novelty gate.  The inverse-tilted dyadic theorem now supplies the stronger
complete-divisor one-source carrier, including critical-line zeros, in
`inverse-tilted-dyadic-prime-full-divisor-tomography.md`.

## Formal proof surface

- `tendsto_shiftedRegularizedZeta_logDeriv_residue`: exact multiplicity residue of the shifted
  pole-filled zeta logarithmic derivative.
- `meromorphicTrailingCoeffAt_shiftedRegularizedZeta_logDeriv`: the trailing coefficient is the
  analytic multiplicity.
- `meromorphicTrailingCoeffAt_dyadicSharpPrimeContinuedSource`: multiplication by the explicit
  Mellin window gives the exact source residue.
- `meromorphicOrderAt_dyadicSharpPrimeContinuedSource_eq_neg_one_iff`: exact simple-pole support,
  with no extraneous poles on `Re(s)>1`.
- `normalizedDyadicSharpPrimeSourceResidue_eq_xiRightMultiplicity`: exact multiplicity recovery.
- `xiRightZeroSupport_eq_image_dyadicSharpPrimeSimplePoleSupport`: support equality after the
  shift by `1/2`.
- `dyadicSharpPrimeSourceDivisorTomography_capstone`: initial series identity, global
  meromorphicity, exact support, normalized multiplicities, and RH holomorphy criterion.

## Boundary

This theorem does not prove the source continuation is analytic on `Re(s)>1`; it proves that this
single source statement is exactly RH. It also does not prove the converse equality between the
positive-excess energy abscissa and the transverse Xi supremum. That converse would require an
RH-quality quantitative Chebyshev estimate or an equivalent source estimate.

## Gates

- [x] source coefficient contains only a finite dyadic von-Mangoldt window and elementary polar
  counterterm
- [x] ordinary Dirichlet series identity on the initial half-plane
- [x] canonical meromorphic continuation on `Re(s)>1/2`
- [x] exact pole support on `Re(s)>1`
- [x] exact analytic multiplicities recovered from normalized pole weights
- [x] RH equivalent to source holomorphy on `Re(s)>1`
- [x] unconditional Lean proof with no project axioms
- [x] parent-theory novelty gate failed; classified as bridge infrastructure
- [ ] critical source estimate proving holomorphy or negative-part energy at exponent zero
- [ ] RH
