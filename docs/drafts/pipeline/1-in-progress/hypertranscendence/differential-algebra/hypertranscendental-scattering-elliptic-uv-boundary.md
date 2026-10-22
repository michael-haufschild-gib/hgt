# Hypertranscendental scattering as an elliptic ultraviolet boundary completion

- **ID:** `hypertranscendental-scattering-elliptic-uv-boundary`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM / CONSTRUCTIVE QFT / DIFFERENTIAL-ALGEBRAIC RG CLASS
- **Scientific status:** `[PAPER CORE PROVED] [PHYSICAL EXISTENCE BRIDGE]`
  `[NOVELTY UNVERIFIED] [SIGNIFICANCE GATE OPEN]`
- **Parent:** `geometric-cdd-hypertranscendental-local-qft.md`
- **Companion:** `geometric-cdd-higher-spin-completion-fracture.md`
- **Scope:** general hypertranscendence in a canonical scattering observable; no RH or selected
  special-function input
- **Statement:** A regular factorizing QFT can have an exact hypertranscendental dimensionless
  phase-delay kernel while its ultraviolet scaling profile is a nonconstant differentially
  algebraic Jacobi elliptic cycle.  Hypertranscendence is carried by the one-sided infrared
  boundary completion, not by the limiting cycle itself.

## Exact scattering family

Fix `0 < q < 1` and `C > 1`.  Put

```text
P_q(t) = product_(k>=0) ((1-q^k t)/(1+q^k t))^2,
t(theta) = -i sinh(theta)/C,
S_(q,C)(theta) = -P_q(t(theta)).                           (1)
```

The product is the one-sided scale orbit of a reality-paired CDD zero.  It satisfies

```text
P_q(t) = ((1-t)/(1+t))^2 P_q(qt).                         (2)
```

The zeros stay on `Im(theta)=pi/2` and escape in real rapidity.  The poles stay on
`Im(theta)=-pi/2` and `Im(theta)=3pi/2`.  A sector decomposition using `(2)` proves boundedness
on every enlarged strip

```text
-kappa < Im(theta) < pi+kappa,       0 < kappa < pi/2.     (3)
```

Thus `S_(q,C)` is a regular scattering function.  It has `S_(q,C)(0)=-1`, so Lechner's modular
nuclearity theorem supplies observables in arbitrarily small double cones.  The reconstructed
two-dimensional Haag--Kastler theory is local, Reeh--Schlieder, asymptotically complete, and
interacting because its scattering operator is nonidentity.

The first-order homogeneous `q`-difference equation `(2)`, the infinite divisor, and the
Adamczewski--Dreyfus--Hardouin dichotomy prove that `P_q`, hence the scattering law in the
canonical crossing coordinate, is hypertranscendental.

## Exact real-axis reporter

For `x=sinh(theta)/C > 0`, choose the continuous unwrapped phase

```text
S_(q,C)(theta) = exp(i delta_(q,C)(theta)),
delta_(q,C)(theta) = pi + 4 sum_(k>=0) arctan(q^k x).       (4)
```

The dimensionless logarithmic-energy phase-delay kernel is

```text
T_q(x) = d delta / d(log x)
       = 4 sum_(k>=0) q^k x/(1+q^(2k)x^2).                 (5)
```

Every term is positive.  It obeys the one-shell constraint

```text
T_q(x) = 4x/(1+x^2) + T_q(qx),                             (6)
T_q(0) = 0.                                                (7)
```

The meromorphic continuation of `(5)` has a noncancelled pole at each
`x=+/- i q^(-k)`.  It is therefore not rational.  Homogenizing `(6)` and applying the same
rational-or-hypertranscendental theorem gives

```text
T_q is hypertranscendental over C(x),                      (8)
```

for the Euler derivation.  Equivalently, `(8)` follows from the exact logarithmic-derivative
equivalence for `P_q`.  The HT quantity is a real-axis scattering reporter, not merely a complex
divisor label.

## Ultraviolet elliptic cycle

Write `q=exp(-a)`, `a>0`.  For a fixed logarithmic residue `r` and integer `N>=0`, set

```text
x_N = exp(Na+r).
```

Then `(5)` reindexes exactly as

```text
T_q(x_N) = 2 sum_(j>=-N) sech(r-aj).                       (9)
```

The omitted negative tail is absolutely and locally uniformly summable.  Hence

```text
lim_(N->infinity) T_q(exp(Na+r))
  = T_a^UV(r)
  = 2 sum_(j in Z) sech(r-aj).                             (10)
```

The limit is positive, nonconstant, and `a`-periodic.  Poisson summation gives

```text
T_a^UV(r)
  = (2pi/a) sum_(m in Z)
      exp(2pi i m r/a) / cosh(pi^2 m/a).                   (11)
```

Let `K=K(k)` and `K'=K(sqrt(1-k^2))`, where the unique modulus `0<k<1` is chosen by

```text
K'/K = pi/a.
```

The Fourier expansion of Jacobi `dn` identifies `(11)` as

```text
T_a^UV(r) = (4K/a) dn(2Kr/a,k).                            (12)
```

Consequently the ultraviolet cycle is differentially algebraic: after rescaling, it satisfies
the first-order algebraic differential equation

```text
(dn')^2 = (1-dn^2)(dn^2-(1-k^2)).                          (13)
```

Equations `(8)` and `(12)` prove a strict differential-algebraic boundary fracture:

```text
exact finite-energy scattering delay:  HT,
ultraviolet limit cycle:                DA elliptic.       (14)
```

## Physical interpretation

The one-sided shell law is selected by the infrared boundary condition `(7)`.  Removing that
boundary and extending the shell tower in both scale directions produces the bilateral elliptic
cycle `(10)`.  The hypertranscendental law is therefore a boundary-completed energy-scale
trajectory from a trivial infrared response to a differentially algebraic ultraviolet cycle.
This is a theorem about an exact scattering observable under energy rescaling, not yet an
identification of rapidity with Wilsonian RG time.

This corrects two tempting but false slogans:

1. discrete scale invariance does not itself imply hypertranscendence; its exact elliptic cycle is
   differentially algebraic;
2. hypertranscendence need not survive an ultraviolet scaling limit; it can be the global
   finite-energy compatibility defect between an infrared boundary and a simple asymptotic phase.

The standard rapidity scattering kernel `d delta/d theta` differs from `(5)` by the
algebraic-positive factor `coth(theta)`, which tends to one at high energy.  It has the same
ultraviolet cycle.  The Wigner--Smith delay `d delta/d E_cm` differs by a further algebraic
kinematic Jacobian and is still HT at finite energy; the dimensionless scaled delay
`E_cm d delta/d E_cm`, rather than the raw dimensionful delay, carries the nonzero elliptic
ultraviolet profile.

## Anti-theatre and parent-theory gate

The individual ingredients are classical:

- one-sided `q`-Pochhammer products and their theta/elliptic bilateral completions;
- Poisson summation of a `sech` lattice;
- Jacobi elliptic Fourier series;
- elliptic factorizing S-matrices and Russian-doll resonance towers;
- Lechner's constructive inverse-scattering theorem;
- the rational-or-HT theorem for linear `q`-difference equations.

The formula-level search found exact elliptic cyclic S-matrices and `q`-deformed integrable
S-matrices, but not the one-sided regular product `(1)` together with `(8)`--`(14)` in a rigorously
reconstructed local QFT.  That is negative search evidence, not a priority proof.  The result must
not be advertised as new mathematics merely because a one-sided product is rewritten as a
physical phase.

Generalized-`T bar T` and CDD/TBA literature shows that finite and infinite CDD towers can have
Hagedorn or non-Wilsonian ultraviolet thermodynamics, including elliptic models.  The Lechner
construction proves algebraic locality and arbitrarily small local observables; it does not by
itself prove a conformal ultraviolet fixed point, a regular thermal partition function at every
temperature, or absence of a Hagedorn radius.  Hypertranscendence is not claimed to characterize
any of those phenomena.

## Significance and Fields/Nobel gate

The proved existence statement is potentially publication-worthy: it separates the exact
differential-algebraic class of a measurable scattering observable from the class of its RG
limit cycle inside a local, interacting, asymptotically complete QFT.

It is not yet Fields/Nobel-level.  That gate requires a universality theorem:

```text
rational CDD q-coboundary  <=>  finite differential closure,
non-coboundary regular one-sided scale orbit  =>  hypertranscendental boundary completion,
bilateral ultraviolet completion  =>  a classified DA elliptic cycle.         (15)
```

The classification must cover matrix-valued factorizing scattering, prove stability under
physically admissible perturbations, and derive the one-shell cocycle from a source-minimal
Lagrangian or operator-algebraic renormalization law rather than selecting its divisor afterward.

## Unconditional Lean gate

The corpus proves the finite CDD constraint, inversion, rapidity crossing, finite phase derivative,
and strict positivity in `GeometricCDDConstraint.lean`.  It now also proves in
`GeometricCDDBoundarySelection.lean` the infinite-series convergence and shell constraint,
continuity at the infrared endpoint, vanishing of every continuous contractive scale-invariant
defect, and uniqueness of `(5)` from `(6)`--`(7)`.  These theorems are unconditional and the exact
module/axiom checks pass.  The external HT dichotomy, meromorphic continuation, and elliptic
ultraviolet limit remain explicit paper interfaces.

## Primary literature

- G. Lechner, *Construction of Quantum Field Theories with Factorizing S-Matrices*,
  <https://arxiv.org/abs/math-ph/0601022>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin,
  *Hypertranscendence and linear difference equations*,
  <https://arxiv.org/abs/1910.01874>.
- G. Mussardo and S. Penati, *A Quantum Field Theory with Infinite Resonance States*,
  <https://arxiv.org/abs/hep-th/9907039>.
- A. LeClair and G. Sierra,
  *Renormalization group limit-cycles and field theories for elliptic S-matrices*,
  <https://arxiv.org/abs/hep-th/0403178>.
- P. G. O. Freund and A. V. Zabrodin, *A Hierarchical Array of Integrable Models*,
  <https://arxiv.org/abs/hep-th/9208033>.
- G. Camilo, T. Fleury, M. Lencses, S. Negro, and A. Zamolodchikov, *On Factorizable S-matrices,
  Generalized TTbar, and the Hagedorn Transition*, <https://arxiv.org/abs/2106.11999>.
- L. Cordova, S. Negro, and F. I. Schaposnik Massolo, *Thermodynamic Bethe Ansatz past turning
  points: the (elliptic) sinh-Gordon model*, <https://arxiv.org/abs/2110.14666>.
