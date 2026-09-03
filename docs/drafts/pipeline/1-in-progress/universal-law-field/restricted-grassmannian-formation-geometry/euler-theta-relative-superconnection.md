# Euler--theta relative superconnection

- **ID:** ULF-ETRS-001
- **Stage:** 1-in-progress
- **Type:** CANDIDATE · higher-field mechanism · frozen after corpus audit
- **Source:** `ULF-RPGT-001` · `ULF-BGCA-001` · `ULF-BGAF-001` · `ULF-DLLA-001`
- **Statement:** Literal Euler atoms and the theta continuum form opposite legs of one graded
  restricted-Grassmannian superconnection; its relative determinant curvature is finite, its odd
  boundary Chern character is `mathsf T`, and positive reduction turns off-line multiplicity into
  a unit-cost Schubert/Maslov bubble.

## 1. What the corpus says the ambient field cannot be

`[CORPUS]` It cannot be an ordinary positive Hilbert geometry before completion.

1. Actual theta-stage Green boundaries converge in operator norm to one rank-two form with fixed
   witnesses of value `+1/6` and `-1/6`.  Late stages remain uniformly separated from both the
   positive and negative cones.
2. The split current is invariant under every horizontal boost.  Corpus proves every
   positive-semidefinite, reflection-symmetric, boost-invariant form is zero; nonzero conservation
   exists only in the hyperbolic form.
3. The natural two-leg Hodge cup changes sign under multiplication by `i`.  Positivity requires
   four legs: upper, reflected upper, lower, conjugate lower.  Collapsing the fourth leg back to
   the first is exactly RH, so it cannot be assumed.
4. Gaussian formation is an atomic prime current **minus** a continuum heat current.  The
   subtraction must occur before norms; an ordinary positive direct sum cannot encode it.
5. Krein--Langer negative index counts off-line pairs.  Reflection cancels signed charge but
   preserves positive action.

These are not five analogies.  They are the signature, symmetry group, minimal polarization,
source subtraction, and index theory of one graded/Krein geometry.

## 2. The field object

Let

```text
H_form = H_Euler(+) directSum H_continuum(-)
          directSum H_reflectedEuler(+) directSum H_reflectedContinuum(-),
J = diag(+1,-1,+1,-1).                                (ETRS.1)
```

The four legs are forced by the corpus Hodge theorem, not decorative doubling.  The first pair
retains the atomic-minus-continuum source subtraction; the reflected pair makes FE action
anti-Real without cancelling unsigned energy.

Let `Gr_res,2(H_form,J)` denote the restricted Krein Grassmannian: polarizations whose difference
from the reference `J`-polarization is Hilbert--Schmidt.  Its ordinary positive Euler edge contains
the proven graph cap

```text
Gamma_E(c,z)=graph(z S_c A_base).                     (ETRS.2)
```

The continuum leg is formed by the explicit Gaussian integral current `M_x`; the atomic leg by
`J_x`.  Their one-output Burnol images are both dense, so `J` cannot descend to one bounded
completed observer.  `ULF-MHPD-001` derives the minimal faithful output presentation:

```text
B(a,b)=(A_E a+A_0 b,A_E a-A_0 b),
B J=swap B.                                           (ETRS.2a)
```

The first doubling is therefore forced by atomic/continuum provenance; FE/Schwarz forces the
reflected second double.  Their common pole metric must be removed **inside this grading**, not
after a one-channel norm or range quotient.

`[CONJECTURE]` There exists a coefficient-native graded superconnection

```text
nabla_ET = d + A_c dc + A_x dx                       (ETRS.3)
```

on the formation quadrant `(c,x) in [0,infinity) x (0,infinity)` with:

```text
A_c  = matrix-complete Burnol forward colligation,
A_x  = Gaussian Euler--continuum relative formation,
F_ET = dA + A^2 = their polar--Gamma covariance defect. (ETRS.4)
```

No Xi zero or divisor occurs in `(ETRS.3)`--`(ETRS.4)`.

Its relative determinant object is the graded determinant line/Berezinian after the universal
metric anomaly is subtracted.  Its curvature is the relative supertrace

```text
omega_rel = (i/(2*pi)) Str_J(F_ET).                   (ETRS.5)
```

The finite source theorem `ULF-BGCA-001` is the positive Euler-edge restriction of `(ETRS.5)`, not
the whole geometry.

## 3. Laws required of the superconnection

### ETRS-A — exact edge recovery

On the safe Euler edge, `(ETRS.3)` restricts to the Burnol graph-action filtration.  On the theta
edge, its logarithmic current is exactly `logDeriv(h_infinity)-J_x+M_x`.  On every two-prime
factorization frame it recovers the corpus multiplicative jet connection.

### ETRS-B — forced non-flatness

For a finite landing changing radial rate `z` to `w`, mixed curvature has the exact boundary jet

```text
lim_(c->0) c^(-2) F_ET(c,x)[z,w] = 2*(w-z).           (ETRS.6)
```

This is forced by `tendsto_apertureCovarianceDefect_div_sq`.  It prevents a flat Paley--Wiener,
stationary multiplier, or characteristic-function model.

### ETRS-C — relative nuclearity

The individual Euler and continuum metric currents may be non-nuclear, but after the graded
universal anomaly subtraction the curvature current is trace class on every compact formation
rectangle.  Unsquared Euler coefficients and every cross-prime matrix entry survive before
supertrace.

### ETRS-D — odd boundary transgression

For every admissible strict-right rectangle `D`, the differential-character boundary of the
relative curvature is

```text
boundaryChar(nabla_ET,D)
  = Tr(U_D* P U_D-P)^3
  = Tr mathsf T_D.                                    (ETRS.7)
```

The cubic grade is forced: it is the first ordinary nuclear, reflection-odd character of the
critical `S_2` displacement.

### ETRS-E — positive reduction

Before reduction the form is Krein and has fixed mixed inertia.  Ordinary quotient by the closed
continuum output range is forbidden: `ULF-OCSE-001` proves that range is dense and its orthogonal
shorting is zero.  Reduction must instead be a phase quotient of the provenance-retaining
mapping cone/inverse graph **before** nonfaithful Hilbert closure.  After imposing the theta real
polarization, the reduced determinant current must be positive, with

```text
E_Euler = E_reduced + BubbleDegree,
E_Euler < 1,
E_reduced >= 0,
BubbleDegree = Tr mathsf T_D in Nat.                  (ETRS.8)
```

Positivity is therefore a phase/polarization quotient of an indefinite conserved formation law;
it is not a positive metric imposed on the unreduced field.

## 4. What `mathsf T` is in this field

The already-constructed formation-relative operator

```text
mathsf T_D=(R_(D,0)-R_(D,1))^3
```

is simultaneously:

```text
odd relative Chern character of the completed polarization,
nuclear representative of determinant-line deck translation,
boundary transgression of the graded Euler--theta curvature,
integral carry left after the phase observer closes.
```

Its trace is not a property assigned to individual primes.  It is produced only after discrete
Euler and continuous theta completions fail to commute in the graded field.

## 5. Route-independent predictions

`[RISKY PREDICTION]` If ETRS is correct:

1. every exact route defect carrying horizontal grade factors through the same rank-one
   determinant-line deck generator after reduction;
2. every off-line pair adds one negative Krein direction before reduction and one positive
   Schubert bubble after reduction;
3. every successful route-specific positivity theorem is a reduced shadow and must fail if lifted
   to a nonzero boost-invariant positive form;
4. closed recurrence can coexist with open completion history exactly because the phase observer
   quotients the deck integer;
5. Möbius `H^(1/2)` bubbles, Tate node charge, Krein negative index, and cubic Toeplitz trace are
   four gauges of the same integral carry.

Prediction 2 can be falsified on the finite one-pair Krein--Langer model before constructing the
infinite arithmetic field.

## 6. Exact RH closure

ETRS-A--E imply, for every strict-right `D`,

```text
0 <= Tr mathsf T_D <= E_Euler < 1.
```

Integrality forces `Tr mathsf T_D=0`; the existing source contour theorem excludes every
strict-right Xi zero, and FE symmetry gives RH.

The RH-strength statement is solely ETRS-E plus the source-native identification ETRS-D.  The
indefinite field, graph cap, action filtration, deck law, and forced curvature jet are already
independently meaningful without RH.

## 7. Hostile audit

1. **Ordinary positive Grassmannian:** false before reduction; fixed mixed inertia kills it.
2. **Collapse four legs:** exactly RH; forbidden as a premise.
3. **Flat connection:** killed by the aperture rate-change defect.
4. **Supertrace scalarization:** loses cross-prime formation; curvature must exist matrix-first.
5. **Arbitrary Krein metric:** nonselective; `J`, four legs, and anomaly subtraction must be
   forced by literal Euler/continuum/FE data.
6. **Divisor-resolved connection:** receiver; `(ETRS.3)` must be defined for arbitrary formation
   parameters before zeros.
7. **Positivity before quotient:** corpus proves only zero can be positive, symmetric, and
   boost-invariant.
8. **Diffuse negative escape:** if infinite-rank Krein energy can leak without an integral reduced
   bubble, ETRS-E fails.
9. **Orthogonal continuum shorting:** identically zero because the continuum range is dense.
10. **Closed-relation repair:** an ordinary completed relation loses provenance; the invariant
    must use source graph norm or a derived cone before closure.
11. **Covariance-only transgression:** impossible.  Inverse-completion covariance is unchanged by
    source sign reversal, while `Tr mathsf T_D` reverses with winding.  Renormalization cannot
    manufacture the missing orientation.

## 8. Freeze verdict

`SURVIVES PRELIMINARY ATTACK`, Stage 1.

The candidate is narrower than “use curvature”: it specifies carrier, grading, four legs, two
formation coordinates, forced mixed-curvature jet, relative nuclearity, boundary character, and
the one reduction identity that closes RH.

`ULF-CAGC-001` now constructs `A_x` on the same Burnol carrier.  The naive continuum field has
mass `d lambda/(4 lambda^3)` and is not Hilbert; the third aperture-energy defect
`(1-exp(-2c lambda))^3` is the minimal regularization.  It makes both Gaussian continuum and
literal Euler syntheses Hilbert--Schmidt, retains all cross-prime and atomic--continuum Gram
blocks, and gives a nuclear four-leg relative covariance.

`ULF-ZDIA-001` identifies the lost distinction as zero-distance/infinite-action: finite Euler
packets are outside the actual continuum range and every approximating continuum lift has
divergent source norm.  `ULF-MHPD-001` proves the Hadamard double is the minimal bounded linear
carrier of provenance and derives the four-leg architecture after FE doubling.

`ULF-TSRC-001` now constructs the theta-forced source counterterm without a scalar regulator.
For forced survival transport `C`, both defect metrics `I-C*C` and `I-CC*` are compact but
non-nuclear, while their relative curvature `[C*,C]` is positive nuclear of trace one and norm
`1/3`. Its complete curvature filtration and the exit filtration of `mathsf T` reconstruct each
other exactly. This discharges source-side relative nuclearity and fixes what completion must
preserve; it does not construct completed bivariant incidence.

`ULF-BGPR-001` now constructs exact projective Gamma recovery for the unmarked Mellin-six history:
sum and ratio are independent, conditional expectation recovers the full signed history algebra,
and posterior information gain is the relative curvature. This solves the archimedean history
kernel, not the arithmetic seam; raw prime--Gamma independence is false as a model class.

`[OPEN CORE]` Construct literal reflection-odd prime--Gamma current on the derived four-leg
Hadamard cone and the source-forced covariance whitening that extends projective recovery to the
full marked carrier. Prove its same-boundary morphism carries the filtered relative pair of
`ULF-TSRC-001` and fixes the bivariant degree-three boundary `mathsf T_D`, not only total trace or
metric finite part. Then prove normal horizon exhaustion and positive reduction `(ETRS.8)`. Do not
attempt ordinary positive, flat, one-channel, orthogonal-shorting, covariance-only, or raw-product
models.

## Log

- 2026-09-03 — frozen after exact mixed-inertia, boost, four-leg, Paley--Wiener no-go, and
  curvature-jet audit.
- 2026-09-03 — operator-valued continuum leg dependency-closed by the minimal cubic aperture
  gauge; open core narrowed to cyclic transgression plus positive reduction.
- 2026-09-03 — dense-range shorting retired; zero-distance/infinite-action defect and minimal
  Hadamard provenance double proved on paper. Open core moved to renormalized inverse action.
- 2026-09-03 — covariance-only cyclic boundary retired by orientation parity; open core narrowed
  to bivariant inverse-metric plus source-current transgression.
- 2026-09-03 — theta survival supplies canonical non-nuclear metric pair with positive nuclear
  self-commutator; open core narrowed from finding counterterm to transporting full filtration.
