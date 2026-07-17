# Sectoral Kolchin signatures give a physical phase diagram for hypertranscendental quantum fields

- **ID:** `sectoral-kolchin-signature-quantum-fields`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** CANDIDATE THEOREM / FOUNDATIONAL DEFINITION / QFT CLASSIFICATION
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [SIGNIFICANCE GATE OPEN]`
- **Scope:** general hypertranscendental quantum fields; no RH or distinguished special-function
  input
- **Statement:** Differential-algebraic jet growth is a sectoral physical invariant rather than a
  property of a QFT without qualification.  Positive generalized-free fields can have an HT
  spectral sector with no interaction, finite CDD theories can have interacting but DA scattering,
  and a geometric CDD theory has interacting HT scattering.  These three exact controls separate
  spectral complexity, interaction, and on-shell differential complexity.

## Goal

Replace the statement

```text
this QFT contains a hypertranscendental function
```

by a coordinate-stable signature that records where the differential complexity lives.  The
minimal physically distinct sectors are:

```text
two-point spectral response,
on-shell connected scattering,
compact-local vacuum-to-particle form factors,
higher connected off-shell response.
```

The theorem below completely separates the first two.  The compact-local form-factor transfer is
now proved, including an operator-independent locality lower bound.  The exact remaining bridge is
from these local matrix elements to the face-complete higher connected response.

## Definition -- one-reporter Kolchin slope

Let `(K,D)` be a characteristic-zero differential field, let `L` be a differential extension, and
let `f in L`.  Define the finite jet rank

```text
kappa_f(r) = trdeg_K K(f,Df,...,D^r f).                    (1)
```

For one reporter there is an exact dichotomy:

```text
f differentially algebraic over K  =>  kappa_f(r) is bounded,
f hypertranscendental over K        =>  kappa_f(r)=r+1.     (2)
```

Hence the normalized Kolchin slope exists and is

```text
sigma_K(f) = lim_(r->infinity) kappa_f(r)/(r+1)
           = 0 for DA f,
           = 1 for HT f.                                  (3)
```

The proof of `(2)` is standard differential algebra.  Hypertranscendence means that every finite
jet packet is algebraically independent.  If `f` is differentially algebraic, choose a minimal
differential polynomial.  Its nonzero separant makes every sufficiently high derivative algebraic
over one fixed finite initial jet field, so the transcendence degrees are uniformly bounded.

For a multiplet of reporters one retains the whole function `r |-> kappa(r)` rather than only its
normalized leading slope.

## Physical sector bases

The base field is part of the physical statement.

### Spectral sector

For a scalar Euclidean two-point response use

```text
K_spec = C(s),       D_spec=d/ds,                           (4)
```

where `s` is momentum squared.  Algebraic mass and normalization parameters may be adjoined
without changing the DA/HT class.

### Scattering sector

For one-species factorizing scattering use the canonical crossing coordinate

```text
t=-i sinh(theta)/C,
K_scatt=C(t),       D_scatt=d/dt.                          (5)
```

The scattering signature is

```text
sigma_scatt(Q) = sigma_(K_scatt)(S_Q(t)).                  (6)
```

An algebraic center-of-mass-energy coordinate gives the same class after the corresponding
algebraic differential base change.  No invariance under arbitrary analytic reparametrization is
claimed.

### Compact-local two-particle form-factor sector

For a compact-local observable `A` with nonzero two-particle vacuum form factor, use center
rapidity `u` and the same crossing coordinate `t`:

```text
K_ff2=C(u,t),       D_ff2=d/dt,       D_ff2(u)=0,
sigma_ff2(A)=sigma_(K_ff2)(Fhat_A(u,t)).
```

The operator-independent local floor is

```text
sigma_loc,2(Q)
  = inf {sigma_ff2(A) : A compact-local, P_2 A Omega != 0}.
```

Reeh--Schlieder makes the set nonempty.  The exact Watson exchange quotient proves the Kolchin
locality inequality

```text
sigma_loc,2(Q) >= sigma_scatt(Q).                          (6a)
```

## Reporter invariance `[PROVED]`

The signature is unchanged by the physically admissible reporter changes used here.

1. If `g=(a f+b)/(c f+d)` with `a,b,c,d in K` and `ad-bc != 0`, then
   `K<g>=K<f>` as differential fields.  Therefore `f` and `g` have the same DA/HT class and the
   same Kolchin slope.
2. Multiplication by a nonzero `u in K` preserves every finite jet field up to an invertible
   triangular change: Leibniz' rule expresses the jets of `uf` through those of `f`, and those of
   `f=u^(-1)(uf)` through those of `uf`.
3. A compatible algebraic differential extension of the kinematic base preserves differential
   algebraicity and hypertranscendence.  Differential algebraic dependence descends through an
   algebraic coefficient extension by elimination.
4. A local invertible field redefinition does not change the physical S-matrix.  Thus the
   scattering signature is also insensitive to ordinary interpolating-field and local-counterterm
   choices for which the equivalence theorem applies.

Items 1--3 are algebraic.  Item 4 uses the standard physical invariance of the S-matrix; it is not
an assertion that a genuine CDD deformation is a field redefinition.

## The exact sectoral phase diagram `[PROVED]`

### Control 0 -- ordinary free field

A free scalar of one mass has rational propagator `(s+m^2)^(-1)`, constant scattering, and

```text
sigma_spec=0,       sigma_scatt=0,       interaction=0.    (7)
```

### Control 1 -- HT spectral response without interaction

For `0<a,b<1`, the positive compact Kallen--Lehmann measure

```text
rho_(a,b)=(1-a) sum_(k>=0) a^k delta_(b^k)                (8)
```

defines a local scalar generalized free field.  Its mass resolvent

```text
R_(a,b)(z)=(1-a) sum_(k>=0) a^k/(1-zb^k)                  (9)
```

satisfies a rational linear `b`-difference equation and has infinitely many poles.  The
Adamczewski--Dreyfus--Hardouin theorem therefore gives

```text
sigma_spec=1.                                               (10)
```

Its generating functional is Gaussian and every connected correlator above order two vanishes.
Thus interaction is zero despite maximal one-reporter spectral jet growth.

### Control 2 -- interaction with DA scattering

Fix `0<lambda<1` and put

```text
S_fin(theta)=(sinh(theta)-i lambda)/(sinh(theta)+i lambda). (11)
```

This is a nonconstant regular factorizing scattering function with `S_fin(0)=-1`.  Lechner's
inverse-scattering theorem constructs an asymptotically complete local interacting QFT with
observables in arbitrarily small double cones and scattering operator determined by `(11)`.
In the crossing coordinate `t=-i sinh(theta)/lambda`, `(11)` is rational.  Hence

```text
sigma_scatt=0,       interaction=1.                        (12)
```

Interaction therefore does not force HT scattering.

### Control 3 -- interaction with HT scattering

Fix `0<q<1`, `C>1`, and define

```text
P_q(t)=product_(k>=0) ((1-q^k t)/(1+q^k t))^2,
S_(q,C)(theta)=-P_q(-i sinh(theta)/C).                     (13)
```

The enlarged-strip proof in `geometric-cdd-hypertranscendental-local-qft.md` makes `(13)` a
regular scattering function with `S_(q,C)(0)=-1`.  The same constructive theorem therefore gives
a local, asymptotically complete, interacting QFT.  The exact constraint

```text
P_q(t)=((1-t)/(1+t))^2 P_q(qt)                             (14)
```

and the infinite divisor put `P_q` on the HT branch of the published rational-or-HT theorem.
Consequently

```text
sigma_scatt=1,       interaction=1.                        (15)
```

The compact-local forcing theorem in
`compact-local-form-factor-hypertranscendence-forcing.md` strengthens `(15)` to

```text
sigma_loc,2=sigma_scatt=1.                                (15a)
```

Every nonzero compact-local vacuum-to-two-particle form factor is HT in the relative crossing
coordinate, and such form factors are dense in the two-particle Hilbert sector.

`hypertranscendental-collision-phase-complexity-production.md` gives the complementary dynamical
statement.  For every nonzero DA incoming two-particle packet, the outgoing packet has maximal
relative Kolchin slope one over the complete incoming differential field, although elastic
unitarity leaves its pointwise momentum probability unchanged.  Scattering HT is coherent phase
information rather than classical probability complexity.

The logarithmic phase derivative has the same HT class as `S`, and the rapidity or energy
phase-delay reporter differs only by a nonzero algebraic kinematic Jacobian.  Thus `(15)` is
visible in a real-axis scattering observable.  More strongly,
`wigner-smith-finite-resolution-law-escape.md` proves that finite-bandwidth wave packets measure
exact smoothings of this delay and that, as the bandwidth is refined, those physical traces
eventually exclude every fixed finite differential-law window with a positive finite-data noise
margin.  No fixed smoothed trace is assumed to remain HT.

## What the theorem changes

There is no scalar label `HT QFT` with a stable physical meaning.  The minimal signature is
sectoral:

```text
Sigma(Q)=(sigma_spec, sigma_scatt, sigma_loc,2, sigma_conn, ...).              (16)
```

The controls prove:

```text
spectral HT does not imply interaction;
interaction does not imply scattering HT;
scattering HT is physically realizable in a local interacting QFT;
local two-particle form-factor complexity cannot lie below scattering complexity.             (17)
```

The sector location, not merely the occurrence of a special function, is the physical content.

## Anti-theatre and novelty gate

The following are parent results and are not new knowledge:

- Kolchin jet-growth and differential dimension;
- generalized free fields and Kallen--Lehmann positivity;
- finite and infinite CDD factors;
- Lechner's inverse-scattering construction;
- the rational-or-HT theorem for linear difference equations.

The candidate new contribution is the sectoral signature `(16)`, the exact control diagram
`(7)`--`(15)`, and its use as a physical falsifier of unqualified HT claims.  Focused searches for
`Kolchin S-matrix`, `differential-algebraic scattering profile`, and `differential transcendence
S-matrix` found difference-Galois papers about special functions but no QFT sector invariant of
this form.  That is negative search evidence, not a novelty proof.

The compact-local form-factor theorem now supplies an intrinsic operator-independent locality
inequality `(6a)`.  This is a foundational law for the local matrix-element sector, but not yet a
Fields/Nobel-level theorem: the inequality must be strengthened to the face-complete connected
sector or to a multireporter locality/positivity bound.

## Exact open core -- LSZ/Haag--Ruelle transfer

`[CONJECTURE -- ONSHELL-TO-OFFSHELL KOLCHIN TRANSFER]` Let a massive local QFT have an isolated
one-particle species and a derivation-preserving LSZ or Haag--Ruelle reporter from a connected
four-point source field to the elastic amplitude.  If the one- and two-point base maps to a DA
kinematic field and the reporter commutes with the chosen kinematic derivation, then

```text
HT elastic amplitude
  => positive face-complete Wick--Kolchin growth in the connected four-point sector.           (18)
```

The algebraic contrapositive is immediate: a differential-algebraic higher connected field cannot
have an HT image under a differential-algebraic, derivation-preserving reporter.  The hard content
is physical:

1. construct the reporter on an intrinsic local source category;
2. prove compatibility with connected truncation, amputation, and the kinematic derivation;
3. show that wavefunction normalization, local counterterms, and field redefinitions land in the
   neutral two-point base;
4. apply it to the geometric CDD Haag--Kastler net without assuming explicit point fields that the
   inverse-scattering construction does not provide.

A proof of `(18)` would close Open Core 2 of `wick-kolchin-interaction-spectrum.md` using a
rigorously interacting continuum QFT rather than a toy integral or selected special function.

### Proved wedge-sector precursor

`wedge-pfg-four-point-exchange-carrier.md` computes the connected four-point function of
Lechner's polarization-free generator directly from the ZF relations.  Its exact two-rapidity
coefficient is

```text
K_4(theta,eta)=S_2(theta-eta)-1.
```

Thus coefficient extraction is already an injective, derivation-compatible reporter and an HT
scattering function gives an HT connected four-point coefficient with no asymptotic or
form-factor limit.  This proves the desired transfer for an explicit wedge-local source in the
same reconstructed continuum QFT.

It does not prove `(18)`: the polarization-free generator is not compactly localized when
`S_2 != 1`.  The remaining problem is no longer to find an interacting connected carrier, but to
transport this exact wedge coefficient into an intrinsic compact-local source category without
allowing the Haag--Ruelle limit to hide a DA-to-HT jump.

### Proved compact-local transfer and locality bound

`compact-local-form-factor-hypertranscendence-forcing.md` avoids the asymptotic limit entirely.
For every compact-local `A`, its analytic two-particle form factor obeys

```text
Fhat_A(u,-t)=S_2(t) Fhat_A(u,t).
```

If a nonzero `Fhat_A` were DA, its reflected quotient would make `S_2` DA.  Hence HT scattering
forces every nonzero compact-local two-particle form factor to be HT.  Reeh--Schlieder makes these
form factors dense, and taking the infimum over local operators proves `(6a)`.

This closes compact-local existence, abundance, and the first locality inequality.  It still does
not prove `(18)`: a two-particle form factor is a local matrix-element sector, not the intrinsic
face-complete connected four-point profile.

## Lean boundary

The existing corpus already contains the reusable finite skeleton:

- `HypertranscendentalHorizonFunctionField.lean` proves algebraic independence of every finite
  jet packet of an HT element;
- `WickKolchinProfile.lean` defines finite relative connected-sector rank and proves embedding and
  algebraic-counterterm invariance;
- `SourceLogarithmicBoundary.lean` proves the HT equivalence for a nonzero reporter and its
  logarithmic derivative;
- `GeometricCDDConstraint.lean` and `GeometricCDDBoundarySelection.lean` formalize the finite CDD
  algebra and the unique one-sided shell response.

No new Lean wrapper is justified for `(1)`--`(3)`: the finite algebraic content already exists.
Formalization should resume only when `(18)` supplies a new unconditional theorem interface.  The
external infinite-product, difference-Galois, and constructive-QFT theorems remain explicit paper
interfaces.

## Primary literature

- G. Lechner, *Construction of Quantum Field Theories with Factorizing S-Matrices*,
  <https://arxiv.org/abs/math-ph/0601022>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
  equations*, <https://arxiv.org/abs/1910.01874>.
- M. Duetsch and K.-H. Rehren, *Generalized free fields and the AdS-CFT correspondence*,
  <https://arxiv.org/abs/math-ph/0209035>.
- F. A. Smirnov and A. B. Zamolodchikov, *On space of integrable quantum field theories*,
  <https://arxiv.org/abs/1608.05499>.
- G. Camilo, T. Fleury, M. Lencses, S. Negro, and A. Zamolodchikov, *On Factorizable S-matrices,
  Generalized TTbar, and the Hagedorn Transition*, <https://arxiv.org/abs/2106.11999>.

## Gates

- [x] source-pure general HT/QFT statement
- [x] exact differential-algebraic profile and reporter invariance
- [x] positive noninteracting HT control
- [x] DA interacting scattering control
- [x] HT interacting scattering control
- [x] complete paper proof from stated parent theorems
- [x] exact wedge-local connected four-point coefficient transfer
- [x] compact-local form-factor HT transfer and abundance
- [x] operator-independent Kolchin locality inequality in the form-factor sector
- [x] collision phase-complexity production law and probability blindness
- [ ] formula- and definition-level external novelty audit
- [ ] LSZ/Haag--Ruelle transfer theorem
- [ ] locality or positivity inequality for the connected-sector profile
- [ ] independent physics and differential-algebra review
