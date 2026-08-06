# Euler--Hedenmalm Gamma Stokes transgression

- **ID:** `euler-hedenmalm-gamma-stokes-transgression`
- **Stage:** 2-fully-proven / Mellin--Stokes core formalized, full Euler--Mobius theorem open
- **Type:** THEOREM / ROOT-LEVEL EULER--MOBIUS--GAMMA BOUNDARY WELD
- **Scientific status:** `[PROVED HERE] [LEAN CORE VERIFIED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  `hedenmalm-theta-source-compressed-inverse-determinant.md`;
  `prime-tail-hedenmalm-wiener-hopf-transgression.md`;
  `hedenmalm-theta-flat-borel-holonomy-law.md`;
  `../../5-failed/xi-taylor-theta-tail-core-density-current.md`;
  `../../3-formalized/new_scientific_knowledge/theta-cusp-finite-shell-seam-cancellation.md`.

## Question

The corpus separately has:

1. the literal integer-dilation synthesis of the theta source and its ordinary Mobius inverse on
   a Gaussian tail;
2. Hedenmalm's two-ended root mode at every Xi zero;
3. the universal essential Borel character carried by its flat tail.

Does the Mobius inverse of the **actual Hedenmalm root**, rather than of the source density, have a
closed form?  If so, where exactly is the Xi divisor created?

## Setup

Use the corpus normalization

```text
k(x) = 2 VarTheta_00(i exp(2x)),
XiC(alpha) = integral_R exp(i alpha x) k(x) dx
           = xi(1/2 + i alpha).
```

Let the literal first theta atom be

```text
h(x) = thetaCuspSourceTerm x 1
     = 2 pi exp(x/2)
         (2 pi exp(4x) - 3 exp(2x)) exp(-pi exp(2x)).       (1)
```

For a function with sufficient right-tail decay define the ordinary Euler and Mobius dilation
operators

```text
(E f)(x) = sum_(n>=1) n^(-1/2) f(x+log n),
(M f)(x) = sum_(n>=1) mu(n)n^(-1/2) f(x+log n).             (2)
```

The atom scaling law is

```text
thetaCuspSourceTerm x n = n^(-1/2) h(x+log n),              (3)
```

and hence `k=E h`.  Put

```text
s_alpha = 1/2 + i alpha,
H(alpha) = integral_R exp(i alpha x)h(x)dx
         = (1/2)s_alpha(s_alpha-1)
             pi^(-s_alpha/2) Gamma(s_alpha/2).              (4)
```

Thus `H` is nonzero throughout the open critical strip and

```text
XiC(alpha)=H(alpha) zeta(s_alpha).                          (5)
```

For a rapidly decreasing source `f`, define its causal and anti-causal first-order Green
responses

```text
R^-_alpha f(x)
  = exp(-i alpha x) integral_(-infinity)^x exp(i alpha y)f(y)dy,

R^+_alpha f(x)
  =-exp(-i alpha x) integral_x^(infinity) exp(i alpha y)f(y)dy. (6)
```

Both solve `(partial_x+i alpha)v=f`, but they differ by a homogeneous Stokes jump.

## Theorem

Let `alpha` satisfy `|Im alpha|<1/2` and put

```text
v^-_alpha=R^-_alpha h,       v^+_alpha=R^+_alpha h,
u^-_alpha=R^-_alpha k,       u^+_alpha=R^+_alpha k.        (7)
```

Then the following statements hold.

### 1. Ordinary anti-causal Euler transgression

The anti-causal seed response has super-Gaussian right-tail decay.  Its Euler synthesis converges
absolutely, and

```text
E v^+_alpha = u^+_alpha.                                   (8)
```

No zero is used in `(8)`.

### 2. Exact ordinary Mobius inverse on the root tail

The double series defining `M E v^+_alpha` is absolutely convergent and

```text
M u^+_alpha = M E v^+_alpha = v^+_alpha.                   (9)
```

Thus the ordinary-integer inverse of the Hedenmalm anti-causal mode is not an abstract conormal:
it is the literal first-Gamma-atom Green response.

### 3. The divisor is a killed Gamma Stokes jump

The two seed responses have the exact nonzero jump

```text
v^-_alpha-v^+_alpha = H(alpha) exp(-i alpha x).             (10)
```

Define the completed Euler action on this one-dimensional asymptotic extension, for every alpha
in the strip, by

```text
E^reg_alpha(v^+_alpha+c exp(-i alpha x))
  := E v^+_alpha+c zeta(s_alpha)exp(-i alpha x).            (11)
```

This is the analytic continuation of the ordinary Euler multiplier from `Re s_alpha>1`.  Equations
`(4)`--`(5)` give

```text
E^reg_alpha(v^-_alpha-v^+_alpha)
  = XiC(alpha) exp(-i alpha x).                             (12)
```

Consequently, if `XiC(alpha)=0`, then

```text
u_alpha:=u^-_alpha=u^+_alpha=E v^+_alpha
                         =E^reg_alpha v^-_alpha,            (13)

M u_alpha=v^+_alpha,
[M u_alpha]_Stokes=-H(alpha)[exp(-i alpha x)] != 0.          (14)
```

The equality of the two Hedenmalm boundary solutions is therefore not present in the Gamma seed.
It is created exactly when completed infinite Euler synthesis annihilates the nonzero causal versus
anti-causal Stokes class.

### 4. Multiplicity is Stokes-kernel jet length

Suppose `alpha_0` is a zero of `XiC` of analytic order `m`.  The analytic Stokes family

```text
J_alpha(x)=H(alpha)exp(-i alpha x)                         (15)
```

satisfies

```text
partial_alpha^r [E^reg_alpha J_alpha]_(alpha=alpha_0)=0
                                           for 0<=r<m,     (16)
```

while its order-`m` jet is nonzero.  The input jets

```text
J_(alpha_0), J'_(alpha_0), ..., J^(m-1)_(alpha_0)          (17)
```

are linearly independent modulo lower polynomial degree because the coefficient of
`x^r exp(-i alpha_0 x)` in the `r`th jet is `(-i)^r H(alpha_0) != 0`.  Hence analytic
multiplicity is exactly the length of the killed Gamma Stokes jet, without a simplicity
assumption.

### 5. Literal prime incidence survives

For the normalized integer shift

```text
(T_n f)(x)=n^(-1/2)f(x+log n),                             (18)
```

the homogeneous Stokes class has character

```text
T_n exp(-i alpha x)=n^(-s_alpha)exp(-i alpha x).           (19)
```

Differentiating `(19)` supplies the full `log n` Jordan package on the multiplicity jets.  Also

```text
E=product_p (I-T_p)^(-1),       M=product_p(I-T_p)         (20)
```

on their common rapidly decreasing source core.  Therefore `(14)` is fibrewise ordinary-prime
incidence, not merely an aggregate trace identity.

## Proof

Equation `(3)` follows by substituting `(1)` and using

```text
exp(x+log n)=n exp x.
```

Every polynomial power of `n` combines to the common factor `n^(-1/2)`.  Summing `(3)` gives
`k=E h`; the theta Gaussian makes the series and all source derivatives locally normally
convergent.

For `(4)`, substitute `t=exp x`.  The two Gamma integrals are

```text
integral_0^infinity t^(s+4) exp(-pi t^2) dt/t,
integral_0^infinity t^(s+2) exp(-pi t^2) dt/t.
```

Using

```text
integral_0^infinity t^a exp(-pi t^2)dt/t
  =(1/2)pi^(-a/2)Gamma(a/2)
```

and the Gamma recurrence reduces their combination to the right side of `(4)`.  Gamma has no
zeros and `s_alpha` is neither `0` nor `1` in the open strip, so `H(alpha)!=0`.  Ordinary Mellin
interchange first proves `(5)` on `Re s_alpha>1`; analytic continuation gives it throughout the
strip.

To prove `(8)`, expand the right side of `(6)` and use `k=E h`.  Absolute Gaussian domination
permits Tonelli/Fubini.  In the `n`th summand change variables `z=y+log n`:

```text
n^(-1/2) exp(-i alpha y) exp(i alpha z)
  =exp(-i alpha y)n^(-s_alpha)exp(i alpha(z-log n)+i alpha log n),
```

or directly collect the factor `n^(-1/2-i alpha)=n^(-s_alpha)`.  This gives exactly the Euler
sum of `R^+_alpha h` and proves `(8)`.

For `(9)`, expand the absolutely convergent double series and group by `r=mn`:

```text
M E v^+_alpha(x)
 =sum_(r>=1)r^(-1/2)v^+_alpha(x+log r) sum_(m|r)mu(m)
 =v^+_alpha(x).                                           (21)
```

The first equality is justified because `v^+_alpha` inherits super-Gaussian decay at `+infinity`;
the second is finite divisor Mobius inversion.

Adding the two complementary integrals in `(6)` proves `(10)`.  Multiplying `(10)` by the
analytically continued Euler character gives `(12)`.  At a Xi zero the same complementary-integral
identity for `k` gives `u^-_alpha=u^+_alpha`, proving `(13)`--`(14)`.

Equation `(12)` is the analytic-family identity

```text
E^reg_alpha J_alpha=XiC(alpha)exp(-i alpha x).             (22)
```

The order statement `(16)` follows by differentiating `(22)`.  At order `m`, the only surviving
Leibniz term contains `XiC^(m)(alpha_0)`, which is nonzero.  Differentiating `(15)` gives a triangular
family in the basis `x^r exp(-i alpha_0 x)` with diagonal coefficients
`(-i)^rH(alpha_0)`, proving independence and the multiplicity clause.  Finally `(19)` is direct,
and finite Euler products followed by source-core convergence prove `(20)`.

## What this changes

This closes a root-level weld that the existing corpus did not contain.

- Density-level Mobius inversion was already exact but returned the original density and produced
  no orientation.
- The prime-translation anomaly already attached `n^(-s)` to every conormal, but did not identify
  its ordinary-integer inverse as a concrete Gamma mode.
- The essential inverse-flow trace was aggregate-prime faithful, but did not give a prime-resolved
  preimage of each Hedenmalm root.
- The two-prime interval frame gave algebraic conormal nonannihilation, but not the full Euler/Mobius
  Stokes class.

Equations `(13)`--`(20)` now say what the divisor **is** in this chart:

> A Xi zero is a nonzero causal/anti-causal Gamma Stokes jet that becomes exact only after the
> analytically completed, infinite ordinary-integer Euler synthesis.

This explains in one mechanism why every finite Rees jet misses the divisor, why the Mobius inverse
is regular on one tail but singular on the other, why essential Borel holonomy is unavoidable, why
prime incidence survives, and why Hedenmalm's positive bulk does not orient the zero.

## Exact remaining RH theorem

The fixed self-adjoint translation generator `D=-i partial_x` acts on the Stokes character by

```text
D exp(-i alpha x)=-alpha exp(-i alpha x).                 (23)
```

The character is tempered on the full real line exactly when `alpha` is real.  Therefore RH would
follow from one source theorem:

> Prove that the source-defined Euler/Mobius transgression `(14)`, before choosing a zero, extends
> every killed Stokes jet nontrivially into one common tempered spectral boundary on which the
> translation generator is self-adjoint and source reflection is Hilbert adjunction.

The theorem above supplies construction, nonannihilation, multiplicity, Gamma pointing, and literal
prime incidence in the larger exponential Stokes boundary.  It does **not** prove the category
change from exponential Stokes class to tempered self-adjoint boundary.  That category change is
now the sole RH-bearing clause in this weld.

## Collision with the first-clock and all-prime recurrence criteria

The current active revision of
`../../4-publication-ready/riemann-source-modular-superselection/main.tex` proves that the literal
first CCM clock is asymptotically Bohr almost periodic exactly on the RH fibre.  Independently,
`BilateralAllPrimeIndLimit.lean` proves that the unique strict all-prime sewing conormal is
moderate exactly when `Re(s)=1/2`.  These are global-clock and prime-orbit readings of the same
remaining condition:

```text
Bohr recurrence of the completed source clock
  = bilateral moderation of the all-prime conormal
  = temperedness of the Gamma Stokes character.          (24)
```

Equation `(24)` is a consumer identification, not a source proof.  The first-clock theorem
explicitly does not assert existence of its Bohr asymptote, and the all-prime theorem does not
assert moderation of Xi-kernel fibres.  Countable channel summability cannot bridge the gap:
pointwise `ell^1` completion can retain an arbitrary exponential character while its bilateral
orbit grows exponentially.  The required new theorem must control the complete two-sided orbit,
not merely construct infinitely many summable source channels.

## Hostile audit

1. **Not RH.**  A hypothetical off-line zero gives a perfectly nonzero but non-tempered Stokes
   character.  Nothing above excludes it.
2. **No disguised bounded operator.**  `E^reg` is an analytic continuation on a one-dimensional
   asymptotic extension.  It is not a bounded Euler sum on the causal mode.
3. **No illegal Mobius inversion.**  `M` is applied only to the anti-causal mode with
   super-Gaussian right-tail decay.  Applying it directly to the causal mode would cross the same
   continuation wall and is not asserted.
4. **No target-fed definition.**  Equations `(1)`--`(12)` define analytic families for every
   strip parameter.  A Xi zero is used only to identify the kernel fibre.
5. **No positivity claim.**  The Stokes boundary is exponential, not a positive Hilbert spectral
   boundary.  Giving it a zero-dependent norm would be circular.
6. **Generic-source falsifier survives.**  Replacing the theta Euler synthesis by a generalized
   source with off-line transform zeros produces the same killed-jump mechanism.  Literal
   ordinary-integer incidence and Gamma seed are necessary for the stated weld but do not by
   themselves force temperedness.
7. **Normalization.**  The card uses `k=2 VarTheta_00` and the corpus atom `(1)`, for which `(4)`--
   `(5)` are exact.  This avoids an inessential factor ambiguity among printed theta conventions.

## Literature boundary

Hedenmalm constructs the dilation-sum source, theta boundary pencil, and complex root modes, but
does not apply the ordinary Mobius inverse to those modes or identify a Xi root as an Euler-killed
Gamma causal/anti-causal Stokes jet (arXiv:2606.17494).  Burnol's co-Poisson/Sonine theory supplies
the closest classical boundary technology and divisor evaluators, but the initial audit found no
statement matching `(8)`--`(20)` (arXiv:math/0203120).  Dilation sums, Mellin factorization,
Gamma recurrence, causal Green operators, and Mobius inversion are classical parent ingredients.
Novelty remains unverified pending a focused co-Poisson and Wiener--Hopf audit.

## Lean status

`formal/GaloisForLFunctions/RHTower/EulerHedenmalmGammaStokesTransgression.lean` now proves
unconditionally:

- Mellin convergence of the literal first theta atom on `Re(s)>0`;
- its exact Mellin transform `archFactor(s)`;
- the causal/anti-causal complementary-integral Stokes jump;
- nonvanishing of that jump in the open strip;
- annihilation by the completed Euler multiplier exactly at Xi zeros;
- the literal integer-dilation character;
- preservation of analytic multiplicity; and
- the centered Hedenmalm logarithmic character.

Targeted `lake env lean`, target-only `lake build`, and `#print axioms` audits pass.  The audited
public theorems use only `propext`, `Classical.choice`, and `Quot.sound`.  Full-project lint is
currently blocked by shared umbrella reachability for several concurrently added modules; no
forbidden declaration occurs in this module.

This is a dependency-closed formalization of the Mellin--Stokes core, not yet of the full paper
theorem.  A faithful completion must still include:

1. the literal atom scaling `(3)`;
2. the actual anti-causal integral and Gaussian interchange `(8)`;
3. the absolutely convergent double-series Mobius inverse `(9)`;
4. the full analytic Stokes jet independence law `(16)`--`(17)`.

Formalizing only the scalar identity `XiC=H*zeta`, or an abstract structure with `(8)` assumed as a
field, would not formalize the new result.

## Gates

- [x] source-pure formulation before zero specialization
- [x] complete paper proof
- [x] direct Gamma seed identified
- [x] ordinary anti-causal Euler transgression
- [x] ordinary Mobius inverse with absolute-convergence justification
- [x] nonzero Stokes class and exact Xi annihilator
- [x] multiplicity and prime-incidence jets
- [x] RH-bearing temperedness clause separated
- [x] Mellin--Stokes core formalized and axiom-audited
- [ ] focused literature audit
- [ ] literal Lean formalization
- [ ] source proof of common tempered boundary

## Log

- 2026-08-01 -- Combined the newly proved Hedenmalm compressed inverse, quantile boundary defect,
  root-level prime anomaly, theta Borel holonomy, and pre-existing theta Mobius inverse.  The
  divisor moved from an unnamed completion defect to the explicit kernel of completed Euler
  synthesis on the nonzero Gamma Stokes jump.

## Lean: the literal atom scaling and the ordinary anti-causal Euler transgression

`formal/GaloisForLFunctions/RHTower/EulerHedenmalmMobiusStokesInverse.lean` closes items 1 and 2 of
the completion list, unconditionally and `#print axioms` clean:

```text
normalizedLogDilation n f x            = n^(-1/2) f (x + log n);                        -- T_n
normalizedLogDilation_thetaAtomSeed    : T_n h = thetaCuspSourceTerm . n;                -- (3)
eulerDilationSynthesis f x             = sum_(n>=1) T_n f x;                             -- E
eulerDilationSynthesis_thetaAtomSeed   : E h = k;
stokesPhase alpha y                    = exp(i alpha y);
antiCausalGreen alpha f x              = -exp(-i alpha x) int_x^infty exp(i alpha y) f y dy;
setIntegral_Ioi_comp_add_right         : half-line translation of the Green integral;
integrableOn_stokesPhase_mul_sourceTerm: each phase-weighted atom is integrable on every (x,infty);
integrableOn_stokesPhase_mul_source    : so is the completed source, for |Im alpha| < 1;
summable_integral_norm_phaseAtom       : sum_n int_x^infty ||phase . atom_n|| < infinity;
normalizedLogDilation_antiCausalGreen  : T_n R^+_alpha h = -exp(-i alpha x) int_x^infty
                                           exp(i alpha y) thetaCuspSourceTerm y n dy;
eulerDilationSynthesis_antiCausalGreen : E R^+_alpha h = R^+_alpha k.                    -- (8)
```

The interchange in `(8)` is the genuine Tonelli step of the paper proof: the atom bound
`exp y |h_n(y)| <= C exp(-(pi/2) n^2)` on the positive half-line and the compact-window majorant
`thetaCuspSourceMajorant` on `(x,0]` together make `sum_n int_x^infty ||.||` finite, so
`hasSum_integral_of_summable_integral_norm` applies with no extra hypothesis.

- 2026-08-06 -- items 1 and 2 of the completion list are formalized.  Still open: the absolutely
  convergent double-series Möbius inverse `(9)` and the analytic Stokes jet independence
  `(16)`--`(17)`.
