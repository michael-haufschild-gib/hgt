# One inverse-tilted dyadic prime source is a complete Xi-divisor carrier

- **ID:** `inverse-tilted-dyadic-prime-full-divisor-tomography`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / source-defined CCM divisor tomography / `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
  `[NOT AN RH PROOF]`
- **Parent theories:** bounded-variation multiplicative quadrature, the Euler logarithmic
  derivative, meromorphic divisor calculus, and the completed Xi/zeta order identity

## Main theorem

For `n >= 1`, define the finite inverse-tilted dyadic prime window

```text
T_-(n)
  = sum_(n/2<k<=n) Lambda(k)/sqrt(k) * k/n
```

and the real prime--polar coefficient

```text
p_-(n)=2 A_(log 2)(3/2) sqrt(n)-2T_-(n),
A_L(s)=(1-exp(-Ls))/s,
```

with the removable value `A_L(0)=L`.  The ordinary Dirichlet series of `p_-` on
`Re(s)>3/2` equals a canonical continuation `Scal_-(s)` meromorphic on `Re(s)>1/2`.

The source window has Mellin multiplier

```text
I_-(s)=A_(log 2)(s).
```

Its entire zero lattice lies on `Re(s)=0`.  Every nontrivial Xi zero satisfies
`0<Re(rho)<1`, so `I_-(rho+1/2)` is nonzero for every such zero.  Consequently

```text
meromorphicOrderAt Scal_- (rho+1/2) = -1,

TC_(rho+1/2)(Scal_-)
  = 2 A_(log 2)(rho+1/2) m_Xi(rho),
```

where `m_Xi(rho)` is the analytic multiplicity.  Conversely, every simple pole of `Scal_-`
in `Re(s)>1/2` is of this form.  Thus the affine map

```text
rho |-> rho+1/2
```

is a canonical equivalence from the complete nontrivial Xi divisor support to the complete
simple-pole support of this one scalar prime source, and

```text
TC_(rho+1/2)(Scal_-)/(2 A_(log 2)(rho+1/2))=m_Xi(rho).
```

The source therefore loses neither zero locations nor multiplicities.  In particular,

```text
RH
  iff every pole of Scal_- in Re(s)>1/2 lies on Re(s)=1.
```

## Strengthened positive CCM carrier law

The complete-divisor carrier does not require two irrationally related sharp widths.  A single
source coordinate suffices once the window is placed so that its Mellin zero divisor is separated
from the shifted Xi strip:

```text
cofinal finite prime window
  + inverse source tilt k/n
  + exact scalar pole-charge cancellation
  + locally uniform quadrature remainder
  + global Mellin noncensorship on Re(s)>1/2
  = complete Xi divisor with exact multiplicity.
```

This is the positive architectural conclusion.  A successful semilocal Connes construction must
couple such a complete source divisor coordinate to its positivity or spectral orientation
mechanism.  The source coordinate itself is already faithful; the remaining RH-bearing theorem is
the line-selection statement for its polar divisor.

## Formal proof surface

The unconditional Lean module is

```text
GaloisForLFunctions.RHTower.CCMInverseTiltedDyadicPrimeTomography
```

Its main declarations are:

- `LSeries_inverseTiltedDyadicRealSourceCoefficient_eq_continuedSource`: exact ordinary
  Dirichlet-series identity on the initial half-plane.
- `meromorphicOn_inverseTiltedDyadicContinuedSource_rightHalf`: continuation throughout
  `Re(s)>1/2`.
- `inverseTiltedDyadicMellin_ne_zero_of_re_pos`: global Mellin noncensorship on the whole
  shifted Xi region.
- `meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one_iff`: exact pole support.
- `normalizedInverseTiltedDyadicResidue_eq_multiplicity`: exact multiplicity recovery.
- `inverseTiltedXiDivisorEquivSimplePoleSupport`: canonical support equivalence.
- `riemannHypothesis_iff_inverseTiltedDyadic_poles_on_line`: exact line-selection criterion.
- `inverseTiltedDyadicPrimeFullDivisorTomography_capstone`: bundled source identity,
  continuation, support, multiplicity, and RH criterion.

## Scientific-status boundary

The inverse tilt strictly strengthens the earlier two-window bridge as a theorem surface, but its
proof still consists of the classical Euler logarithmic-derivative transform, elementary Mellin
zero placement, and standard meromorphic divisor calculus.  It therefore remains bridge
infrastructure and does not contribute scientific novelty to the publication headline.

It also does not prove that the source poles lie on `Re(s)=1`.  That statement is exactly RH.  The
new theorem instead proves that no further source-completeness or Mellin-censorship theorem is
missing: the unresolved burden is purely the Connes line-selection mechanism.

## Gates

- [x] explicit real finite-prime coefficient with no zero input
- [x] exact initial ordinary Dirichlet-series identity
- [x] meromorphic continuation on `Re(s)>1/2`
- [x] a single Mellin multiplier nonzero at every shifted nontrivial Xi zero
- [x] complete pole-support equivalence
- [x] exact analytic multiplicities from normalized Laurent coefficients
- [x] exact RH line-selection equivalence
- [x] unconditional Lean proof without project axioms
- [x] parent-theory novelty gate failed; classified as bridge infrastructure
- [ ] Connes positivity/orientation theorem forcing the pole support onto `Re(s)=1`
- [ ] RH
