# Theta-Cusp Robin Anomalous Stein--Ward Law

- **ID:** theta-cusp-robin-anomalous-stein-ward
- **Stage:** 3-formalized
- **Type:** PHYSICS VALUE BRIDGE
- **Physics source:** half-line anomalous Ehrenfest/Ward identities and Robin quantum bootstrap
- **Target:** the independent `k=0,n=1` relaxed fourth-moment hypothesis

## Formalized claim

For a half-line density `rho` satisfying `rho'=-2 W rho`, vector field `P`, and test function
`f`, let `c` be the endpoint current

```text
c = lim_(x -> 0+) f(x) P(x) rho(x).
```

If the current vanishes at infinity, integration by parts gives the anomaly-corrected covariance

```text
integral f (P W-P'/2) rho
  = (1/2) (c + integral f' P rho).                       (A)
```

The theorem
`HTGeometry.integral_Ioi_mul_halfLineSteinScore_with_boundary` formalizes `(A)`; the existing
`HTGeometry.integral_Ioi_mul_halfLineSteinScore` is now its `c=0` specialization.  The first
Born--Witten theta atom is Robin rather than Dirichlet, so its translation field `P=1` has
nonzero endpoint charge.  The theorem
`thetaCuspBornWitten_monomial_anomalousSteinWard` specializes it to

```text
integral x^m B_1(x) chi_1(x)^2
  = (1/2) ((if m=0 then chi_1(0)^2 else 0)
      + m * integral x^(m-1) chi_1(x)^2).                (B)
```

## Utility gate

- `(A)` removes the forced zero-current hypothesis from the reusable half-line Stein API.
- `(B)` gives exact source-specific mixed position--superpotential values in the non-Dirichlet
  state that carries the relaxed fourth-moment gap.
- `thetaCuspBornWitten_odd_superpotential_moment` identifies every odd mixed value with an existing
  Morse Born moment:

```text
integral x^(2j+1) B_n(x) chi_n(x)^2
  = (2j+1)/2 * thetaCuspMorseBornMoment j n.             (C)
```

- `thetaCusp_firstAtom_relaxed_iff_superpotentialMoment` transports the live relaxed condition to
  the exact Ward coordinates, and
  `forall_primeArchSourceTraceHankel_linear_nonneg_of_bornWittenSuperpotentialMoment` applies that
  interface directly to the existing linear Hankel consumer.
- This transport does not discharge the relaxed condition.  A useful next certificate must combine
  `(B)` or `(C)` with a proved source inequality; merely renaming the original fourth-moment
  inequality is not a closure.

## Competing routes and attack

- `[REJECTED FOR THE TARGET CONSTANT]` The curvature floor and its ordinary Brascamp--Lieb
  consequence are too weak to prove the buffered ratio.
- `[SEARCH]` The anomaly mechanism and Robin contact term are known from the half-line quantum
  bootstrap literature.
- `[BRIDGE]` The theta specialization and its direct connection to the live `k=0` consumer are
  project-specific formal value relations.
- `[REJECTED]` Treating the mixed Ward values as moments of a positive measure is invalid:
  `thetaCuspFirstBornWittenSuperpotential_zero_neg` proves `B_1(0) < 0`.  Positivity of the
  integrated odd values follows from `(C)`, not pointwise positivity of `B_1 chi_1^2`.
- `[OPEN CORE]` Find a source inequality for the superpotential values in `(B)` strong enough to
  imply the relaxed fourth-moment bound.

## Gates

- [x] live-corpus and failed-route audit
- [x] primary physics mechanism identified
- [x] direct target state identified
- [x] prove the generic boundary-current Stein identity
- [x] prove Born--Witten mixed-value integrability and endpoint current
- [x] formalize the monomial anomaly recurrence
- [x] connect the exact Ward values to the existing relaxed-moment and Hankel interfaces
- [ ] prove the relaxed fourth-moment hypothesis

## Lean surface

- `formal/GaloisForLFunctions/HTGeometry/HalfLineSteinRobertson.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchThetaBornWittenRobinSteinWard.lean`

## Primary source

Berenstein--Hulsey, *Anomalous Bootstrap on the Half Line*, arXiv:2206.01765.

## Full-source and Xi-jet application

The atomwise law now applies to the complete theta source rather than only the dominant first
atom.  Define

```text
F_j = sum_n integral_(0,infinity)
  x^(2j+1) B_n(x) chi_n(x)^2 dx.
```

Lean proves the exact all-atom value relation

```text
F_j = (2j+1)/(4 pi) * thetaCuspRawEvenMoment j.           (D)
```

The endpoint anomaly also sums exactly:

```text
sum_n integral B_n(x) chi_n(x)^2 dx
  = thetaCuspFullSource(0)/(2 pi).                        (E)
```

Consequently the live full-source relaxed condition has the equivalent natural Ward form

```text
ThetaCuspRelaxedFourthMomentConcentration
  <-> 16 F_0 F_2 <= 25 F_1^2,                            (F)
```

and every even central Xi jet is an all-atom superpotential value:

```text
XiC^(2j)(0) = (-1)^j * 4 pi/(2j+1) * F_j.                (G)
```

This is a direct application to the existing raw-moment, ratio-split, and Xi-jet corpus.  It is
not a new hypothesis surface: `(D)` rewrites the values already consumed by those modules, `(E)`
retains the Robin endpoint charge, and `(F)` removes the nonstructural coefficient `45` in favor
of the odd Ward coefficients `1,3,5`.

Principal declarations:

- `thetaCuspFullBornWittenTranslationContactCharge_eq`
- `thetaCuspFullBornWittenSuperpotentialMoment_eq_rawEvenMoment`
- `thetaCuspFullBornWittenSuperpotentialMoment_nonneg`
- `thetaCuspRelaxedFourthMomentConcentration_iff_fullBornWittenSuperpotentialMoment`
- `iteratedDeriv_XiC_zero_eq_fullBornWittenSuperpotentialMoment`

## Boundary Witten comparison audit

Le Peutrec's boundary Witten-Laplacian theorem applies to the flat half-line in the absolute
Neumann sector and gives the weighted curvature estimate

```text
Var_rho(f) <= integral f'(x)^2 / (2 B_1'(x)) rho(x) dx.
```

For `f(x)=x^2`, this produces the correct weighted second-moment object, but high-precision
pre-certification gives approximately

```text
weighted right-hand side                 5.598294917e-4
right-hand side needed for the target    3.037831350e-4.
```

Thus the valid boundary Brascamp--Lieb theorem misses the required constant by a factor about
`1.84`; its finite-dimensional Bakry--Emery strengthening also misses.  No theorem wrapper was
added for this failed target transfer.

Supersymmetry identifies the global Poincare constant with the Dirichlet ground energy of the
partner Hamiltonian.  Numerical spectral pre-certification gives approximately `47.8437`, while
the moment transfer would require at least `48.14`.  Therefore a global partner-gap attack is not
a viable route to this particular fourth-moment constant; a source-observable-specific estimate
is required.  These numerical values are route-selection evidence, not Lean theorems.

The rationally extended Morse systems of Quesne were also checked.  Their solvable ground states
use rational polynomial ratios, whereas the source amplitude contains the factor
`sqrt(t-3/2)`.  No exact spectrum or shape-invariance transfer to the theta Born--Witten state was
found, so none is asserted.

Additional primary sources:

- D. Le Peutrec, *On Witten Laplacians and Brascamp--Lieb's inequality on manifolds with boundary*,
  arXiv:1607.08714.
- C. Quesne, *Revisiting (quasi-)exactly solvable rational extensions of the Morse potential*,
  arXiv:1203.1812.
