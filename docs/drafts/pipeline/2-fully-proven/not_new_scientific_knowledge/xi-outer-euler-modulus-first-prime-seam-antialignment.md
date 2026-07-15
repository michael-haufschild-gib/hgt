# Xi outer-Euler modulus and first-prime seam are exactly antialigned

- **ID:** `xi-outer-euler-modulus-first-prime-seam-antialignment`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent result:** Sondow--Dumitrescu horizontal monotonicity of the modulus of the Riemann
  xi function on a zero-free right half-plane
- **Statement:** On every open-strip fibre, the completed all-prime--Gamma modulus defect at two
  explicit absolute-Euler points has the opposite orientation to the demodulated first-prime seam.
  Thus any source theorem putting these two defects in the same closed half-line forces the common
  seam charge to vanish and proves RH.

## The two source values

Let

```text
rho=beta+i gamma,                 0<beta<1,
h>=1,
s_+(h,rho)=h+conj(rho),
s_-(h,rho)=h+1-rho.                                      (1)
```

Both points have imaginary part `-gamma`, and

```text
Re s_+=h+beta>1,
Re s_-=h+1-beta>1.                                       (2)
```

Consequently every zeta value, Gamma value, and Euler logarithm below lies in its ordinary
absolute-convergence domain.  Define the real outer modulus defect

```text
M_h(rho)
 =log(|xi(s_+(h,rho))|/|xi(s_-(h,rho))|).                 (3)
```

No logarithmic branch is involved in `(3)`: xi has no zero on `Re s>1`, and the logarithm is the
ordinary real logarithm of a positive number.

The common first-prime seam is

```text
C_2(rho)
 =log(2)*(2^(-conj(rho))-2^(-(1-rho))).                   (4)
```

Remove its harmless vertical character and put

```text
d_2(rho)
 =exp(-i gamma log(2))*C_2(rho)/log(2)
 =2^(-beta)-2^(beta-1),                                  (5)
```

which is real.

## Exact antialignment theorem

`[PROVED]` For every `h>=1` and every `rho` in the open critical strip,

```text
sign(M_h(rho))=sign(beta-1/2),
sign(d_2(rho))=-sign(beta-1/2).                           (6)
```

In particular,

```text
M_h(rho)*d_2(rho)<=0,                                    (7)

M_h(rho)*d_2(rho)=0
 <-> M_h(rho)=0
 <-> d_2(rho)=0
 <-> C_2(rho)=0
 <-> beta=1/2.                                            (8)
```

### Proof

The half-plane `Re s>1` is zero-free for xi.  Sondow and Dumitrescu prove that the modulus of xi
is strictly increasing along every horizontal half-line in a zero-free open right half-plane.
The two points in `(1)` lie on the same horizontal line, and

```text
Re s_+-Re s_-=2 beta-1.                                  (9)
```

Strict monotonicity therefore proves the first identity in `(6)` and the `M_h` zero locus in
`(8)`.  Equation `(5)` gives

```text
d_2(rho)
 =2^(-1/2)*(2^(-(beta-1/2))-2^(beta-1/2)),                (10)
```

so strict monotonicity of the real exponential gives the second identity in `(6)` and its zero
locus.  Equations `(7)`--`(8)` follow.

This proof uses strict endpoint comparison only.  It does not require the stronger pointwise
claim that every horizontal derivative of `log|xi|` is strictly positive.

## Explicit absolute-Euler coordinate

Using

```text
xi(s)=1/2*s*(s-1)*pi^(-s/2)*Gamma(s/2)*zeta(s),            (11)
```

the defect `(3)` is the finite expression

```text
M_h(rho)
 =log |s_+(s_+-1)/(s_-(s_--1))|
  -(2 beta-1)/2*log(pi)
  +log |Gamma(s_+/2)/Gamma(s_-/2)|
  +Re sum_(p prime) sum_(m>=1)
       (p^(-m s_+)-p^(-m s_-))/m.                         (12)
```

The double prime-power series converges absolutely by `(2)`.  Thus `(7)` is a relation between
one complete prime--Gamma value and the least nonzero atom of the same Euler source, not a
comparison made after continuing the Euler series into the critical strip.

At the minimal shift `h=1`, the two nodes are especially concrete:

```text
s_+(1,rho)=1+conj(rho),
s_-(1,rho)=2-rho.                                         (13)
```

They are exactly the two zeta exponents appearing in the already formalized rational-Hurwitz
two-fibre response.  Since

```text
rationalHurwitzFiberResponse(2,s)=2^s,                    (14)
```

one also has the same-node order relation

```text
sign log(
  |xi(1+conj(rho))|/|xi(2-rho)|)
 =sign log(
  |rationalHurwitzFiberResponse(2,conj(rho))|
  /|rationalHurwitzFiberResponse(2,1-rho)|).               (15)
```

The inverse Hurwitz response occurring in `C_2` reverses this sign, giving `(7)`.

## Positive top-down chain

Fix any one `h>=1`.  Define the cross-scale alignment assertion

```text
XiOuterPrimeTwoAligned(h) :=
  for every rho in the Xi divisor,
    0<=M_h(rho)*d_2(rho).                                 (16)
```

The unconditional antialignment `(7)` then gives the exact chain

```text
XiOuterPrimeTwoAligned(h)
 -> M_h(rho)*d_2(rho)=0 on every Xi fibre
 -> every common first-prime seam C_2(rho) vanishes
 -> xiHurwitzOrientationEnergy=0
 -> RH.                                                    (17)
```

This changes the remaining assertion from exact value equality to a semidefinite coupling of two
independently defined source scales.  A successful predecessor could therefore be a determinant,
Gram, reflection-positivity, or source-order theorem proving `(16)` directly from the completed
Euler--Gamma construction.

## What is and is not discharged

`[PROVED]` The following interfaces are closed:

- both completed values lie in absolute Euler convergence;
- one fixed shift, in particular `h=1`, is enough;
- their modulus defect has a strict known orientation;
- the phase-normalized first-prime seam has the opposite strict orientation;
- equality of the outer moduli is exactly common-charge vanishing;
- a nonnegative cross-scale alignment is enough; exact equality need not be assumed.

`[OPEN CORE]` Prove `(16)` from a source constraint that is defined before inserting the Xi
divisor.  The functional equation and Schwarz reflection do not do this: under

```text
rho |-> 1-conj(rho),
```

both `M_h` and `d_2` change sign, so their product is reflection-even.  Horizontal monotonicity
alone supplies `(7)`, the opposite inequality.  Assuming `(16)` on Xi fibres without a source
producer would merely restate the desired orientation.

The theorem therefore does not replace the regular-Cauchy source-core positivity route and does
not claim RH.  It supplies a separate, finite, all-values-in-`Re>1` discharge interface for the
same common charge.

## Corpus connections

- `formal/GaloisForLFunctions/RHTower/XiHurwitzRationalFiberSeam.lean`
- `formal/GaloisForLFunctions/RHTower/XiHurwitzAnchorPrimeTwoOrientationEnergy.lean`
- `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/xi-hurwitz-common-charge-orientation-energy-identification.md`
- `docs/drafts/pipeline/5-failed/orbitwise-source-divisor-seam-obstruction.md`
- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/euler-region-pointwise-schur-gap-nonlocal-index-law.md`

## Literature status

The analytic input is a direct specialization of:

- J. Sondow and C. Dumitrescu, *A monotonicity property of Riemann's xi function and a
  reformulation of the Riemann Hypothesis*, Period. Math. Hungar. 60 (2010), 37--40,
  https://arxiv.org/abs/1005.1104.

The antialignment packaging and its connection to the project's first-prime seam are useful route
infrastructure, but they do not clear the novelty gate as independent scientific knowledge.

## Gates

- [x] same-horizontal-line absolute-Euler nodes identified
- [x] strict outer-modulus orientation proved from the literature theorem
- [x] exact demodulated seam orientation proved
- [x] zero loci and common-charge splice proved
- [x] semidefinite cross-scale alignment chain to RH proved
- [x] reflection and circularity audit completed
- [ ] source theorem proving the nonnegative cross-scale alignment
- [ ] Lean formalization; intentionally deferred under the active no-computation boundary

