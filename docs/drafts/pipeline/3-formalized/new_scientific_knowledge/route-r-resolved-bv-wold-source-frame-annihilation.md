# Route R resolved BV--Wold source-frame annihilation

- **ID:** `route-r-resolved-bv-wold-source-frame-annihilation`
- **Stage:** 3 — formalized in Lean 4
- **Type:** SOURCE-FRAME RESOLUTION / ACTUAL-XI-LANDING ANNIHILATION / SCALAR-DESCENT NO-GO
- **Status:** `[FROZEN] [PAPER PROOF CLOSED] [LEAN FORMALIZED] [SCALAR ANNIHILATION NOT PROVED] [NOT RH]`
- **Parent:** `route-r-prime-depth-bv-wold-curved-source-differential.md`

## Frontier correction

The unnormalized alternating coefficient

```text
theta(i,j)=m_i lambda_j-m_j lambda_i
```

is genuinely non-coboundary, but that fact does not make
`exp(a theta(i,j))` an actual source transport.  Source composition retains
the endpoint clock normalizations.  Since every prime/depth clock is
strictly positive, put

```text
phi_i=m_i/lambda_i.
```

Then the exact normalized identity is

```text
theta(i,j)/(lambda_i lambda_j)=phi_i-phi_j.              (1)
```

Thus the source-normalized extension coefficient is a vertex coboundary.
The nonzero triangle curvature of `theta` is created precisely by deleting
the endpoint clock factors before scalar exponentiation.

## Resolved source frame

For real horizontal parameter `a`, define the determinant-one source frame

```text
G_i(a) = [[1/lambda_i, a m_i],
          [0,            lambda_i]].
```

Its transition is

```text
T_a(i,j)=G_i(a)^(-1)G_j(a)
        = [[lambda_i/lambda_j, -a theta(i,j)],
           [0,                 lambda_j/lambda_i]].       (2)
```

Direct multiplication, using

```text
lambda_i theta(j,k)+lambda_k theta(i,j)
  =lambda_j theta(i,k),                                  (3)
```

gives

```text
T_a(i,j)T_a(j,k)=T_a(i,k).                               (4)
```

Equation `(4)` is source-derived flatness.  It does not require an Xi zero,
critical-line premise, or scalar determinant.  The off-diagonal coefficient
still retains both endpoint masses and clocks; flatness is supplied by the
two diagonal clock characters, not by erasing provenance.

## Resolved differential and actual Xi landing

Let resolved zero-cochains take values in `C^2` and define

```text
(D0_a f)(i,j)       =T_a(i,j)f(j)-f(i),
(D1_a omega)(i,j,k) =T_a(i,j)omega(j,k)-omega(i,k)+omega(i,j).
```

Equation `(4)` gives the unconditional identity

```text
D1_a D0_a=0                                                   (5)
```

on every resolved section.

At an actual Xi divisor copy `rho`, let `r_rho` be its analytic
multiplicity and let

```text
c_rho=XiC^(r_rho)(z_rho) != 0.
```

The internally promoted physical Möbius--theta coface converges to
`c_rho` before divisor scalarization.  Hence

```text
L_rho(i)=(0,c_rho)                                      (6)
```

is the nonzero leading vertical Xi conormal in every resolved prime/depth
frame.  Specializing `a=2 Re(rho)-1`, equations `(4)--(6)` prove

```text
D1 D0 L_rho=0                                           (7)
```

unconditionally on the actual Xi landing.

## Why `(7)` is not the requested scalar RH annihilation

The diagonal clock ratios in `(2)` are essential.  Normalizing the
projective extension coordinate divides the off-diagonal entry by
`lambda_i lambda_j`, and `(1)` makes the result a vertex gauge.  The
previous scalar transport instead discards those ratios and uses

```text
U_a(i,j)=exp(a theta(i,j)).                              (8)
```

On the exact three-depth witness, `(8)` composes if and only if `a=0`.
Therefore descent of resolved flatness `(4)` to scalar flatness of `(8)` at
an actual divisor copy is equivalent to `Re(rho)=1/2`.  It is not a
consequence of `(7)`.

The same obstruction kills every scalar repair obtained by multiplying the
actual leading conormal by a nowhere-zero regular, Gamma, Hellinger, or
`det2` gauge: the curved-square law is curvature times the terminal landing
value, and the latter remains nonzero.  A valid RH step must construct an
independent equal-grade off-diagonal boundary whose scalar descent cancels
the clock-ratio defect.  Merely invoking the resolved source identity
`D1 D0=0` would be source-provenance theatre.

## Scientific content

This is a positive construction and a no-go boundary:

1. the literal BV mass and Wold--Gamma clock determine a canonical
   determinant-one triangular source frame;
2. its off-diagonal transition is exactly the previously constructed
   nonseparable coefficient;
3. its resolved covariant differential annihilates the actual nonzero Xi
   conormal unconditionally;
4. source normalization turns that coefficient into a coboundary;
5. the existing curved scalar differential is therefore a nonfunctorial
   scalar reporter, and compatibility of its descent with resolved
   annihilation is already the RH-bearing assertion.

This moves the frontier from “prove `D1 D0=0` somehow” to one exact missing
object: a source-defined equal-grade scalar-descent boundary not generated
by the triangular clock normalization and not a nowhere-zero landing gauge.

## Hostile falsifiers

1. Reject the frame if any `lambda_i` can vanish.
2. Reject source flatness if `(3)` or `(4)` fails.
3. Reject “actual Xi landing” if `c_rho` is allowed to vanish or is inserted
   without the existing cofinal physical source limit.
4. Do not infer scalar flatness from resolved flatness.
5. Do not call a common `Xi` factor, a zero landing vector, or a nowhere-zero
   scalar gauge an annihilator.
6. Do not claim RH from `(7)`; scalar descent remains open and is
   RH-strength.

## Gates

- [x] exact statement frozen before Lean work
- [x] dependency-closed algebraic proof
- [x] actual leading conormal identified and proved nonzero in existing corpus
- [x] external exact-collision audit
- [x] unconditional Lean formalization
- [x] targeted module build
- [x] standard-axiom audit
- [x] imported by `GaloisForLFunctions.RHTower`
- [ ] scalar equal-grade boundary
- [ ] RH

## Formal artifact and audit

Formalization:
`formal/GaloisForLFunctions/RHTower/PrimeDepthBVWoldResolvedXiLandingAnnihilation.lean`.
Targeted `lake build` passed.  Axiom prints for transport composition,
cofinal Xi landing, resolved annihilation, and scalar-annihilation/RH
equivalence contain only `propext`, `Classical.choice`, and `Quot.sound`.
Repository-wide lint still exits on unrelated pre-existing modules missing
from the RHTower umbrella; this module is imported by that umbrella and is
not among the reported unreachable modules.

## External boundary

Targeted searches found parent theories for discrete flat connections and
regularized-determinant multiplicative anomalies, including the Wodzicki
residue description of zeta-determinant anomalies.  No located source
contains the exact BV-depth/Wold-clock triangular frame `(2)`, normalized
coboundary `(1)`, actual leading-Xi-conormal landing `(6)`, or the resulting
resolved-flat/scalar-curved descent boundary.  Novelty is claimed only for
that arithmetic specialization and exact no-go; triangular gauge transport,
covariant nilpotence for a flat connection, and determinant anomalies are
parent mathematics.
