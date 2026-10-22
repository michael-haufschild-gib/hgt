# Conjecture: paired Gamma--logistic transport upgrades every matched flat interior tail

- **ID:** `suzuki-paired-gamma-logistic-flat-sector-conjecture`
- **Stage:** 1-in-progress
- **Type:** REGULAR-SINGULAR CLASSIFICATION / NONSELFADJOINT HARDY GAP
- **Scientific status:** `[CONJECTURE] [OPEN CORE] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Inputs:** `suzuki-paired-seam-carleman-logistic-normal-form.md`,
  `suzuki-interior-seam-indicial-dipole-exclusion.md`,
  `suzuki-forced-gamma-upper-strip-gluing.md`,
  `suzuki-gamma-weighted-tail-coercivity.md`

## 0. Retraction of premature nonselfadjoint theorem status

The residue calculation and self-adjoint/subcritical-polynomial-group version survive. The claimed extension
from self-adjoint \(B\) to an arbitrary bounded nonnormal \(B\) does not.

Section 4 asserted that the operator-valued fundamental matrix and its inverse have polynomial
growth on horizontal frequency lines. Its \(B\)-factor is

```text
exp(-i z B/2).                                           (0a)
```

Boundedness of \(B\) permits exponential growth in \(\operatorname{Re}z\); polynomial growth
requires an additional two-sided group bound. Moreover, group-growth degree \(\kappa\) is
compatible with a shifted line of height \(\sigma\) only when \(\kappa<\sigma\): the squared
Gamma carrier has exact tail \(|x|^{-1-2\sigma}\), while transport costs
\(|x|^{2\kappa}\). The exponential valuation carrier used for finite
recurrence has an asymptotic nonreciprocal prime adjacency of Hatano--Nelson type and hence a
complex elliptic limit spectrum. It does not satisfy the claimed polynomial bound.

Therefore:

```text
residue -P_sym and local charge classification;          [PAPER-PROVED]
self-adjoint or degree-kappa<sigma B strip theorem;      [PAPER-PROVED]
arbitrary polynomial-degree B strip theorem;             [FALSE]
arbitrary bounded nonnormal B strip theorem;             [OPEN / PROOF FALSE]
Suzuki exponential-weight flat-sector upgrade;           [OPEN].             (0b)
```

See `suzuki-exponential-orbit-hatano-nelson-hard-wall.md` and
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-polynomial-carrier-gamma-dimension-wall.md`.

**Subsequent positive reduction.** The hard wall applies to the direct frequency fundamental
matrix, not to every formulation of the primitive-forced equation.
`../../../3-formalized/new_scientific_knowledge/suzuki/suzuki-primitive-flux-nonnormal-graph-reduction.md`
introduces

```text
Y=(2L+R-B)F-G
```

for a right side \(G'+H\). It proves the exact flux system and a weighted graph estimate in which
arbitrary nonnormal \(B\) costs only \(\|B\|\). The subsequent
`../../../3-formalized/new_scientific_knowledge/suzuki/suzuki-flat-primitive-flux-volterra-liouville.md`
proves flat-tempered flux Liouville.  Complementary primitive flux subsequently closes
physical-root derivative propagation, and
`../../../3-formalized/new_scientific_knowledge/suzuki/suzuki-flat-flux-charge-automaticity.md`
shows the flat terminal charge is automatic and the physical zero-extension has no independent
`1/log` dipole. Literal source assembly is now proved, and formalized dyadic orbit charts close
compact-middle coverage. Rank-one rough-primitive admission is now paper-closed on `2a<log 3`.
Remaining finite-type theorem is higher-rank analytic admission, not another interior ellipticity
theorem.

## 1. Result

The paired interior-seam equation has exactly two frequency-zero charges:

```text
symmetric pole      <-> common seam value,
antisymmetric log   <-> 1/log dipole jump.              (1)
```

After subtracting the common value and imposing continuity of the complete source, both charges
vanish.  Every remaining flat tail is forced into the positive Gamma strip; no slow
all-orders-flat channel remains.

Let \(X\) be a complex Hilbert space, let \(B\in\mathcal B(X)\), and work on
\(X\oplus X\). For the proved version assume the two-sided group bound of degree \(\kappa\ge0\)

```text
||exp(-i x B/2)||+||exp(i x B/2)||
 <=C(1+|x|)^kappa,         x in R.                      (1a)
```

Self-adjoint \(B\), or a boundedly invertible similarity of one, satisfies `(1a)`. Let

```text
J(x_+,x_-)=(x_-,x_+),
P_sym=(I+J)/2,
P_anti=(I-J)/2.                                         (2)
```

Let \(R\) be the literal Gamma remainder, with Fourier multiplier

```text
r(z)=psi(1+i z)+psi(1-i z)+2 EulerGamma,                 (3)
```

and let \(K\) be logistic convolution, with multiplier

```text
khat(z)=pi z/sinh(pi z),        khat(0)=1.               (4)
```

Consider on a terminal logarithmic ray the paired equation

```text
(2L I+R-B)F'(L)+F(L)-K J F(L)=H(L).                     (5)
```

Assume:

1. \(F,H\) are tempered and `(5)` holds in distributions after a terminal cutoff;
2. the positive- and negative-frequency solutions have the standard boundary values supplied by
   the exact Gamma factorization;
3. the symmetric pole coefficient is zero (the common seam value has been subtracted);
4. the antisymmetric source moment at frequency zero is zero, equivalently the complete
   physical source has no step jump at the seam;
5. \(H\) has a holomorphic Fourier--Laplace continuation and the quantitative block source norm
   through one strip \(0<\Im z<\delta\).

Then the two real-frequency solutions glue holomorphically through \(z=0\) throughout

```text
0<Im z<min(1,delta).                                    (6)
```

If the block source norm is finite at
\(\kappa<\sigma<\min(1,\delta)\), then

```text
exp(sigma L)F in L2.                                    (7)
```

If, in addition, \(H\) belongs to weighted \(L^2\) on the terminal ray, then

```text
exp(sigma L)F' in L2.                                   (8)
```

In particular, every paired tail flat beyond all inverse-log orders is upgraded to the physical
Gamma strip after the two matching conditions.  It cannot remain at an intermediate rate such as
\(e^{-\sqrt L}\).  Nonzero exponentially decaying tails driven by the compact initial segment are
allowed.  The result is independent of self-adjointness of \(B\); only \(\|B\|<\infty\) enters the
weighted derivative estimate after `(7)`. The shifted-\(L^2\) estimate `(7)` uses `(1a)` and
the sharp inequality \(\kappa<\sigma\). If \(\kappa\ge1\), no direct uniform shifted line exists
inside the literal Gamma strip.

For the weighted Suzuki orbit carrier, \(X\) is the valuation Hilbert space and \(B\) is its
bounded nonnormal prime adjacency. It is not known to satisfy `(1a)`; the exponential radial
weight has a Hatano--Nelson hard wall. Therefore flat-sector annihilation on that carrier remains
open by the direct Hardy proof. The primitive-flux formulation supplies a second live proof
architecture that establishes shifted value/flux \(L^2\) without `(1a)`; root derivative
propagation remains.

## 2. Exact frequency ODE

Use the Fourier convention

```text
f(z)=integral_R exp(-i z L)F(L)dL.                      (9)
```

Then

```text
F' -> i z f,
L F' ->i d/dz(i z f)=-f-z f'.                          (10)
```

Fourier transformation of `(5)` gives

```text
-2z f'
 +[-I+i z(r(z)I-B)-khat(z)J]f
 =h(z).                                                 (11)
```

For \(z\ne0\),

```text
f'
 ={-[I+khat(z)J]/(2z)
    +(i/2)[r(z)I-B]}f
   -h(z)/(2z).                                          (12)
```

Both \(r\) and \(\widehat k\) are even and holomorphic on \(|\Im z|<1\), with

```text
r(0)=0,
khat(z)=1+O(z^2).                                       (13)
```

Hence `(12)` has a regular singular point at zero with residue

```text
A_0=-(I+J)/2=-P_sym.                                    (14)
```

This residue is exact and unaffected by \(B\), because the prime coupling is multiplied by
\(z\).

## 3. Charge classification at frequency zero

On the symmetric subspace, `(14)` has eigenvalue \(-1\).  A homogeneous solution may therefore
contain

```text
z^(-1)c_sym.                                            (15)
```

Its inverse transform is a common constant on the two orientations.  Subtracting \(u(0)\) in the
paired physical profiles sets \(c_{\rm sym}=0\).

On the antisymmetric subspace, `(14)` has eigenvalue zero.  A homogeneous solution may contain a
constant

```text
c_anti.                                                 (16)
```

Its inverse boundary asymptotic is the antisymmetric \(1/L\) dipole classified in the predecessor
card.  The logarithmic jump sends that dipole to a nonzero physical step.  Continuity of the
complete source sets \(c_{\rm anti}=0\).

The inhomogeneous term has one further compatibility.  Project `(12)` antisymmetrically.  Since
the residue vanishes there,

```text
P_anti f'
 =-P_anti h(0)/(2z)+holomorphic terms.                  (17)
```

Thus absence of a logarithm is equivalent to

```text
P_anti h(0)=0.                                          (18)
```

Equation `(18)` is the frequency form of zero source jump.  It is not an added analytic
assumption in Suzuki's local equation: scalar multiplication, polar convolution, and unmatched
prime descendants are continuous; exact marked descendants occur on both equations with their
prescribed one-sided source and are removed grade by grade before the flat remainder is formed.

After `(15)`--`(18)` vanish, Frobenius theory for Banach-valued regular-singular ODEs gives one
holomorphic solution through \(z=0\).  No conormal expansion of the original \(F\) is assumed.

## 4. Gluing through the exact strip

Away from zero, the coefficient in `(12)` is holomorphic wherever \(r\), \(\widehat k\), and
\(h\) are.  The first poles of both source multipliers are at height one:

```text
r:       Gamma poles at z=+/-i,
khat:    sinh(pi z)=0 at z=+/-i.                        (19)
```

The bounded operator \(B\) is entire and changes no finite strip singularity, so local holomorphic
continuation through `(6)` survives for arbitrary bounded \(B\). Global Hardy control on
horizontal lines is separate and uses `(1a)`.

This is the paired analogue of zero half-log Gamma gluing.  Its zero-frequency matching data are
the value/dipole pair `(1)`, not one scalar half-log charge.

## 5. Quantitative shifted \(L^2\)

Take a terminal cutoff \(\chi\).  The commutators with \(R\) and \(K\) have exponential tails:
their kernels decay like \(e^{-|L-M|}\).  The prime operator \(B\) acts only in carrier
coordinates and commutes with the physical cutoff.  Hence the cutoff equation has a block source
in the same norm as the predecessor Gamma wall theorem.

Holomorphic gluing through height \(\sigma\), the block source norm, and `(1a)` give the
Paley--Wiener/Hardy estimate `(7)` only when \(\kappa<\sigma\). On every closed substrip the
\(B\)-factor and its inverse cost \((1+|x|)^\kappa\), while the squared scalar Gamma carrier has
exact decay \(|x|^{-1-2\sigma}\). Their product is integrable exactly for
\(\kappa<\sigma\). Source moments alone do not remove a free homogeneous coefficient.

Without `(1a)`, the factor \(\exp(-ixB/2)\) can grow exponentially. Temperedness of a realized
solution may impose stable/unstable cancellations, but proving those cancellations is an
exponential-dichotomy/Evans theorem absent from this card.

This is now a classification of the direct fundamental-matrix method only. Primitive-flux
augmentation cancels the derivative of the rough source before estimating the graph and never
forms \(\exp(-ixB/2)\). It yields weighted uniqueness in the graph class for arbitrary bounded
\(B\), but the upgrade of an all-orders-flat tempered solution into that class remains open.

No implication from strip holomorphy alone is asserted; the quantitative source norm remains
load-bearing.

## 6. Weighted derivative

Conjugate `(5)` by \(e^{\sigma L}\).  The shifted Gamma lower bound is

```text
Re <R_sigma v,v>>=-kappa_sigma||v||^2.                  (20)
```

The logistic operator satisfies

```text
||K_sigma||
 <=m_sigma=pi sigma/sin(pi sigma),       0<sigma<1.      (21)
```

For the derivative term, boundedness of \(B\) gives

```text
|Re <Bv,v>|<=||B||||v||^2.                              (22)
```

Move the zero-order terms, including \(K_\sigma JF\), to the right and use `(7)`.  On a terminal
ray where

```text
2L_0>kappa_sigma+||B||+1,                               (23)
```

the weak mollifier energy estimate yields

```text
||e^(sigma L)F'||_2
 <=C[
   ||e^(sigma L)H||_2
   +(1+m_sigma)||e^(sigma L)F||_2
   +cutoff norm].                                       (24)
```

This proves `(8)`. Ordinary self-adjointness of \(B\) is not used in the derivative step;
boundedness is enough after `(7)`. `QED`

## 7. Flat-sector exclusion

Suppose both matching charges vanish, the noncompact source is Gamma-subcritical, and the
two-sided group degree satisfies \(\kappa<1\). A terminally
homogeneous equation still acquires compact forcing after the cutoff used to put it on the whole
line; this forcing must not be deleted.  Sections 4--6 apply to that compact source and give, for
every permitted \(\kappa<\sigma<1\),

```text
exp(sigma L)F in H1 on a shorter terminal ray.           (25)
```

Thus a nonzero exponentially decaying particular tail may survive, but no intermediate
all-orders-flat sector does.  In particular \(e^{-\sqrt L}\), or any tail outside every positive
Gamma weight, cannot solve the matched paired equation with Gamma-subcritical source.

This is exactly the conclusion needed for spatial regularity.  A whole-line homogeneous
\(L^2\)-Liouville statement would require additional skew/self-adjoint structure and is neither
asserted nor used here.

## 8. Exact frontier movement

The completed trace-zero gate now factors as

```text
local paired Carleman normal form;                       [PROVED]
finite-grade root-only conormal support;                 [PROVED]
paired regular-singular charge classification;          [PROVED]
all-orders-flat paired weighted upgrade for kappa<sigma; [PROVED]
tempered weighted physical orbit carrier;               [PROVED]
finite-type aperture admission;                         [PROVED]

Suzuki flat-tempered primitive-flux Liouville;           [PROVED]
physical-root primitive derivative propagation;         [PROVED]
physical dipole and flat terminal charge;                [AUTOMATIC]

literal infinite paired-orbit equation;                 [PROVED]
finite-to-flat expansion;                              [OPEN]
total marked-descendant source matching;               [PROVED]

exceptional recurrence-infinite passage;                [OPEN]
nonzero-root Evans return/raw Evans positivity.          [OPEN RH CORE]       (26)
```

The direct analytic flat-sector proof is closed only for transport whose polynomial degree is
strictly below the chosen Gamma height. A radial all-vector polynomial carrier can satisfy this
and lattice square summability only in valuation ranks zero and one. The
exponential valuation carrier introduces either a nonnormal dichotomy gate or the sharper
primitive-flux Liouville gate before source assembly suffices.

## 9. Hostile audit

1. **No source realization assumed silently.**  `(5)` is the explicit hypothesis still to be
   derived from every completed mode.
2. **No scalar trace substituted.**  Paired value and dipole charges are classified separately.
3. **No strip-to-\(L^2\) leap.**  Quantitative block source norm is assumed and used.
4. **Nonnormal and degree gaps exposed.** Boundedness suffices for derivative coercivity, not
   Hardy transfer; arbitrary polynomial degree is also insufficient.
5. **No conormality premise.**  Regular-singular frequency theory upgrades the flat sector
   directly.
6. **No false tail Liouville claim.**  Compact cutoff forcing may generate a nonzero
   exponentially decaying tail; `(25)` is weighted regularity, not vanishing.
7. **No all-aperture or RH claim.**  Assembly, exceptional apertures, and Evans sign remain.

## 10. Novelty boundary

Regular-singular ODEs, Gamma factorization, logistic Fourier transforms, and weighted energy
estimates are classical separately.  Candidate-new source knowledge is the exact paired Suzuki
classification

```text
residue = -P_sym,
zero eigenchannel = physical dipole,
source continuity removes its logarithmic compatibility,
both first poles occur at height one,
there is no third flat interior corona.                  (27)
```

Corpus search found scalar Gamma gluing and the one-sided flat Carleman obstruction, but not the
paired ODE `(12)`, charge law `(14)`--`(18)`, or Liouville conclusion `(25)`.  External priority
remains unaudited.

## 11. Lean decision

Faithful formalization requires vector-valued Fourier transform, digamma and logistic meromorphic
multipliers, Banach-valued regular-singular ODEs, strip Hardy theory, and weak weighted energy.
These are not present in the formal tree.  Formalizing residue matrix algebra alone would not
certify gluing or `(25)` and is rejected.  The correct Lean target begins after the literal
paired-orbit source identity is paper-complete.

## Gates

- [x] derive exact paired frequency ODE
- [x] compute residue `-P_sym`
- [x] identify common-value and dipole charges
- [x] identify zero source-jump compatibility
- [x] glue through the exact common strip
- [x] prove quantitative shifted `L2` under degree `kappa < sigma` two-sided group growth
- [x] classify the sharp Gamma/lattice collision and its rank-one survivor
- [x] prove weighted derivative once shifted \(L^2\) is known, allowing bounded nonnormal coupling
- [x] identify missing polynomial-group/exponential-dichotomy hypothesis
- [x] replace intrinsic Hatano-wall wording by exact primitive-flux graph reduction
- [x] prove flat-tempered primitive-flux Volterra Liouville
- [x] prove physical-root primitive derivative propagation
- [x] prove physical dipole and flat terminal charge vanish automatically
- [x] derive the literal infinite paired-orbit equation from every completed mode
- [ ] prove arbitrary finite-order expansion to the flat residual
- [x] prove total marked-descendant source matching in literal assembly
- [ ] pass recurrence-infinite apertures
- [ ] prove trace-zero completed modes enter `H1_0`
- [ ] prove completed Evans injectivity
- [ ] RH or whole-Connes no-go
