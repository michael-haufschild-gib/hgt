# The geometric hypertranscendental CDD theory has a finite real-TBA obstruction

- **ID:** `geometric-cdd-finite-real-tba-obstruction`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** CANDIDATE THEOREM / FINITE-VOLUME QFT / ANALYTIC HAGEDORN OBSTRUCTION
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [SIGNIFICANCE GATE OPEN]`
- **Scope:** general hypertranscendental factorizing QFT; no RH or distinguished special-function
  input; no numerical evidence
- **Parents:** `geometric-cdd-hypertranscendental-local-qft.md` and
  `hypertranscendental-scattering-elliptic-uv-boundary.md`
- **Statement:** The scalar fermionic TBA equation for the geometric HT scattering law has a real
  finite-free-energy primary solution for all sufficiently large circle radii, but no real
  finite-free-energy solution below an explicit positive radius.  The proof is analytic and uses
  the strictly positive lower envelope of the exact Wigner--Smith kernel.  It establishes a finite
  real-thermodynamic obstruction without assuming the numerically observed square-root branch
  point.

## Why this is the next physical gate

The parent QFT theorem reconstructs a local, interacting, asymptotically complete Haag--Kastler net
from the regular scattering function.  That result does not determine its finite-volume
thermodynamics.  Existing CDD/TBA literature finds Hagedorn turning points numerically for finite
and elliptic infinite resonance towers, but explicitly leaves a general analytic proof open.

The geometric phase-delay kernel is stronger than an integrable positive kernel: it never decays
to zero at large rapidity.  Its one-sided shell completion approaches a positive elliptic cycle.
The theorem below converts that nondecay into a rigorous obstruction to real TBA solutions at
small radius.

## Scattering kernel

Fix `0<q<1` and `C>1`.  For real rapidity let

```text
S_(q,C)(theta)=exp(i delta_(q,C)(theta)),

delta_(q,C)(theta)
  = pi + 4 sum_(k>=0) arctan(q^k sinh(theta)/C).            (1)
```

The scalar TBA kernel is

```text
phi_(q,C)(theta)
  = -i d/dtheta log S_(q,C)(theta)
  = delta_(q,C)'(theta)
  = (4 cosh(theta)/C) sum_(k>=0)
      q^k/(1+(q^k sinh(theta)/C)^2).                        (2)
```

It is even, continuous, strictly positive, and bounded.  Boundedness follows either directly by
splitting the geometric series at the unique shell nearest unit scale or from the locally uniform
elliptic ultraviolet limit proved on the parent card.

## Theorem A -- an explicit global positive floor `[PROVED]`

Define

```text
c_(q,C)=min(2/C, 4q/(1+q^2)) > 0.                          (3)
```

Then

```text
phi_(q,C)(theta) >= c_(q,C)        for every theta in R.   (4)
```

By evenness it is enough to take `theta>=0` and put `x=sinh(theta)/C`.

If `0<=x<=1`, retain only the `k=0` term in `(2)`:

```text
phi_(q,C)(theta)
  >= 4 cosh(theta)/(C(1+x^2))
  >= 2/C.                                                   (5)
```

If `x>=1`, use the logarithmic phase reporter

```text
T_q(x)=4 sum_(k>=0) q^k x/(1+q^(2k)x^2),
phi_(q,C)(theta)=coth(theta) T_q(x) >= T_q(x).             (6)
```

Choose the unique `n>=0` for which

```text
1 <= q^n x < q^(-1).                                      (7)
```

The `n`th term and monotonicity of `4y/(1+y^2)` on `[1,infinity)` give

```text
T_q(x) >= 4q^n x/(1+(q^n x)^2) >= 4q/(1+q^2).             (8)
```

Equations `(5)` and `(8)` prove `(4)`.  The floor is conservative; its role is to be uniform and
explicit, not optimal.

For completeness, the matching global upper bound is also elementary.  If `x<=1`, sum `(2)`
geometrically and use `cosh(theta)<=sqrt(1+C^2)`.  If `x>=1`, use the index `n` from `(7)` and the
bound

```text
4y/(1+y^2) <= 4 min(y,y^(-1)).
```

The shells below and above `n` are two geometric tails, each bounded by `4/(1-q)`.  Since
`coth(theta)<=sqrt(1+C^2)/C` on this region, one obtains

```text
sup_theta phi_(q,C)(theta)
  <= 8 sqrt(1+C^2)/(C(1-q)) < infinity.                   (8a)
```

Thus both the positive floor and the boundedness used below are proved directly from the shell
law; neither is inferred from numerical plots of the ultraviolet cycle.

## General no-real-solution lemma `[PROVED]`

Let `phi : R -> R` be a measurable kernel with

```text
phi(theta) >= c > 0.                                      (9)
```

Consider the fermionic scalar TBA equation at dimensionless radius `r>0`,

```text
epsilon(theta)
  = r cosh(theta)
    - integral phi(theta-theta')
        log(1+exp(-epsilon(theta'))) dtheta'/(2pi).        (10)
```

A **real finite-free-energy solution** means a real measurable `epsilon` for which

```text
L(theta)=log(1+exp(-epsilon(theta))) > 0,
A=integral L(theta) dtheta/(2pi) < infinity,               (11)
```

and the convolution in `(10)` is finite.

From `(9)`--`(11)`,

```text
epsilon(theta) <= r cosh(theta)-cA.                        (12)
```

Since `u |-> log(1+exp(-u))` is decreasing, integrating `(12)` yields

```text
A >= F_r(A),

F_r(A)=integral log(1+exp(cA-r cosh(theta))) dtheta/(2pi). (13)
```

For `A>=0`, differentiation under the integral is justified by the exponential rapidity tail and
gives

```text
F_r'(A)
  = c integral [1+exp(r cosh(theta)-cA)]^(-1) dtheta/(2pi)
  >= c J(r),

J(r)=integral [1+exp(r cosh(theta))]^(-1) dtheta/(2pi).    (14)
```

If

```text
c J(r) >= 1,                                               (15)
```

then `F_r(A)>=F_r(0)+A>A` for every `A>=0`, contradicting `(13)`.  Therefore `(10)` has no real
finite-free-energy solution whenever `(15)` holds.

This lemma is not perturbative.  It excludes every real branch satisfying the physical
integrability condition `(11)`, not only the fixed point reached by standard iteration.

## Theorem B -- explicit positive exclusion radius `[PROVED]`

For `0<r<=1` and

```text
|theta| <= log(1/r),
```

one has

```text
r cosh(theta) <= (1+r^2)/2 <= 1.                           (16)
```

Consequently

```text
J(r) >= log(1/r)/(pi(1+exp(1))).                           (17)
```

Set

```text
r_excl(q,C)
  = exp(-pi(1+exp(1))/c_(q,C)) > 0.                        (18)
```

Equations `(15)`--`(18)` prove:

```text
0 < r <= r_excl(q,C)
  => no real finite-free-energy solution of the TBA.       (19)
```

The bound `(18)` is deliberately non-sharp.  It proves a nonzero finite-temperature obstruction
without fitting a critical radius or solving the nonlinear equation numerically.

## Theorem C -- the physical primary branch exists at large radius `[PROVED]`

Let

```text
M=sup_theta phi_(q,C)(theta)<infinity.                     (20)
```

Write `epsilon(theta)=r cosh(theta)+h(theta)` and consider the closed unit ball
`||h||_infinity<=1`.  The fixed-point map for `(10)` is

```text
G_r(h)(theta)
  = - integral phi_(q,C)(theta-theta')
      log(1+exp(-r cosh(theta')-h(theta'))) dtheta'/(2pi). (21)
```

For `r>1`, every `h` in the ball satisfies

```text
0 < log(1+exp(-r cosh(theta)-h(theta)))
  <= exp(1-r cosh(theta)).                                 (22)
```

Hence both the self-map bound and the Lipschitz constant of `G_r` are at most

```text
kappa_r
  = M exp(1) integral exp(-r cosh(theta)) dtheta/(2pi).    (23)
```

The integral in `(23)` tends to zero as `r` tends to infinity.  Choose `r_large` so that
`kappa_r<1` for `r>=r_large`.  Then `G_r` maps the unit ball into itself and is a contraction.
Banach's fixed-point theorem supplies a unique real primary solution in that ball for every such
`r`.

Combining Theorems B and C gives a genuine finite-radius separation:

```text
large r:                         real primary TBA branch,
0<r<=r_excl(q,C):               no real physical branch.  (24)
```

## Physical consequence

The exact local QFT exists on infinite Minkowski space, but its fermionic finite-volume TBA cannot
remain real down to arbitrarily small circumference.  In the standard CDD/TBA interpretation this
is a rigorous **Hagedorn obstruction**: ordinary real equilibrium thermodynamics terminates at a
finite scale.

This is independent physics beyond relabeling the S-matrix as HT.  The chain is

```text
one-sided geometric CDD completion
  -> positive nondecaying Wigner--Smith kernel
  -> scalar self-consistency amplification
  -> finite real-thermodynamic obstruction.                (25)
```

The theorem also sharpens the apparent tension between algebraic locality and non-Wilsonian
thermodynamics.  Lechner locality and finite-volume Hagedorn obstruction can coexist: the former
is a statement about local observable algebras, while the latter is a statement about the growth
encoded by the finite-size ground-state equation.

## Anti-theatre and novelty gate

Published parents:

1. the fermionic scalar TBA equation and its finite-size energy interpretation are standard;
2. finite CDD and elliptic infinite-resonance models have numerically observed turning points and
   complex continuations;
3. the resonance-minus-bound-state integral criterion permits a secondary large-radius branch;
4. the geometric parent card already proves the positive elliptic ultraviolet delay cycle.

The candidate new residue is the comparison theorem `(9)`--`(19)` and its application to the
one-sided HT model: a positive lower envelope of the exact phase kernel analytically excludes all
real finite-free-energy TBA solutions below an explicit radius.  Focused searches found numerical
turning-point evidence and asymptotic branch criteria, but not this no-real-solution inequality.
That is negative evidence, not a priority proof.

Hypertranscendence is not claimed to cause Hagedorn behavior.  The DA bilateral elliptic kernel
also has a positive lower envelope.  The thermodynamic obstruction is controlled by persistent
positive delay, while HT distinguishes the one-sided finite-energy boundary completion from its
DA ultraviolet cycle.  Conflating those two statements would be theatre.

## What is not proved

1. The exact optimal critical radius is not determined; `(18)` is only an explicit exclusion
   interval.
2. The topology of the full real solution set is not classified.  In particular, the theorem does
   not prove that exactly two branches meet at one square-root turning point.
3. The complex TBA continuation and its ultraviolet effective central charge are not constructed.
4. A Tauberian theorem converting `(19)` into an exact asymptotic density-of-states coefficient is
   not supplied.
5. The result does not derive a microscopic Lagrangian or the infinite-current topological source.

These are now separate, falsifiable problems.  The existence of a finite real-thermodynamic
obstruction no longer depends on them.

## Lean boundary

The reusable theorem surface is an integral-inequality no-go for nonlinear TBA fixed points.  It
requires real integration on the whole line, exponential-tail differentiation under the integral,
and a convolution interface.  The current HTGeometry corpus proves the scattering kernel and its
finite phase positivity, but not the infinite analytic bounds needed by `(4)` and `(20)`.

Formalizing only the elementary constant estimate would not certify the TBA theorem.  A Lean batch
should begin only after the paper audit fixes the solution class and packages the infinite kernel
as a bounded measurable function with positive floor.  No conditional theorem or axiom placeholder
is acceptable.

No Lean edit, build, scratch compilation, lint, axiom check, or numerical computation was run.

## Primary literature

- G. Camilo, T. Fleury, M. Lencses, S. Negro, and A. Zamolodchikov, *On Factorizable S-matrices,
  Generalized T bar T, and the Hagedorn Transition*, JHEP **10** (2021) 062,
  <https://arxiv.org/abs/2106.11999>.
- L. Cordova, S. Negro, and F. I. Schaposnik Massolo, *Thermodynamic Bethe Ansatz past turning
  points: the (elliptic) sinh-Gordon model*, JHEP **01** (2022) 035,
  <https://arxiv.org/abs/2110.14666>.
- G. Lechner, *Construction of Quantum Field Theories with Factorizing S-Matrices*,
  <https://arxiv.org/abs/math-ph/0601022>.
