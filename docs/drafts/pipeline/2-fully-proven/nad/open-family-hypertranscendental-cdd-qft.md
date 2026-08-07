# An open family of regular CDD shell orbits gives local QFTs with hypertranscendental scattering

- **ID:** `open-family-hypertranscendental-cdd-qft`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** CANDIDATE THEOREM / CONSTRUCTIVE QFT / ROBUST PHYSICAL HT EXISTENCE
- **Scientific status:** `[PROVED HERE] [PHYSICAL EXISTENCE BRIDGE] [NOVELTY UNVERIFIED]`
- **Scope:** general hypertranscendental scattering in local interacting QFT; no RH or
  distinguished special-function input
- **New source parent:** `q-ladder-reflectionless-reciprocal-jost-qft.md`
- **Statement:** Every finite positive rational CDD shell seed generates a finite-parameter open
  family of regular one-sided scale-orbit scattering functions.  Every member reconstructs a
  local asymptotically complete interacting QFT and has HT scattering; the conclusion survives
  arbitrary finite regular rational CDD dressing.

## Goal

Remove the fine-tuning objection from the geometric CDD existence theorem.  The physical carrier
of HT should occupy a stable family inside the regular inverse-scattering class, not be one formula
selected after its divisor is known.

This theorem proves parametric and finite-CDD stability.  The reciprocal-Jost parent now derives
the whole finite positive shell family as determinants of local reflectionless quantum-mechanical
scattering matrices.  What remains open is a common physical dynamics that implements the
reciprocal lift into the relativistic QFT.

## Construction

Fix

```text
0<q<1,
A={a_1,...,a_N} with every a_j>0,
m_1,...,m_N positive integers,
C min_j(a_j)>1.                                            (1)
```

Define the finite rational shell

```text
B_A(t)=product_(j=1)^N ((a_j-t)/(a_j+t))^(2m_j)            (2)
```

and its one-sided scale orbit

```text
P_(q,A)(t)=product_(k>=0) B_A(q^k t),
S_(q,A,C)(theta)=-P_(q,A)(-i sinh(theta)/C).               (3)
```

Repeated or `q`-commensurable `a_j` are allowed; they only change multiplicities.  The even
exponents implement the paired rapidity zeros required by the scalar reality condition.

## Claim A -- exact rational decimation constraint `[PROVED]`

Since `B_A(0)=1` and `B_A(q^k t)=1+O(q^k t)` locally uniformly, `(3)` converges normally near the
origin and meromorphically on the plane.  Reindexing gives

```text
P_(q,A)(t)=B_A(t) P_(q,A)(qt).                             (4)
```

Moreover,

```text
B_A(-t)=B_A(t)^(-1),
P_(q,A)(-t)=P_(q,A)(t)^(-1).                               (5)
```

The divisor contains zeros at `a_j q^(-k)` and poles at `-a_j q^(-k)`, with the stated
multiplicities.  Positive zeros cannot cancel negative poles, so the divisor is infinite.

## Claim B -- regular factorizing scattering `[PROVED]`

Put `t_C(theta)=-i sinh(theta)/C`.  For real `theta`, `t_C(theta)` is imaginary, so each factor in
`(2)` has modulus one.  For `0<Im(theta)<pi`,

```text
Re(t_C(theta))=cosh(Re theta) sin(Im theta)/C>0.            (6)
```

For `a>0` and `Re(t)>0`,

```text
|a-t|<|a+t|.                                               (7)
```

Thus finite partial products are bounded by one in the physical strip.  Equations `(5)` and
`t_C(theta+i pi)=-t_C(theta)=t_C(-theta)` give unitarity, hermitian analyticity, and crossing.

The poles satisfy

```text
sinh(theta)=-i C a_j q^(-k).                               (8)
```

Condition `(1)` puts their nearest imaginary parts at `-pi/2` and `3pi/2`; zeros lie on
`Im(theta)=pi/2`.  Hence there is no pole on

```text
-kappa<Im(theta)<pi+kappa,       0<kappa<pi/2.             (9)
```

For boundedness on `(9)`, factor the product as

```text
P_(q,A)(t)=product_j
  [ product_(k>=0) ((1-q^k t/a_j)/(1+q^k t/a_j))^2 ]^m_j. (10)
```

Each bracket is a rescaled copy of the audited single-orbit product.  Its rational orbit-reduction
proof gives a uniform upper and lower bound on every closed enlarged substrip.  A finite product
of these bounds proves that `(3)` is regular in Lechner's sense.  Finally,

```text
S_(q,A,C)(0)=-1.                                          (11)
```

Therefore modular nuclearity holds at every positive splitting distance.

## Claim C -- hypertranscendence `[PROVED]`

Equation `(4)` is a first-order homogeneous linear `q`-difference equation over `C(t)`.  The germ
`P_(q,A)` belongs to `C[[t]]`.  The Adamczewski--Dreyfus--Hardouin theorem says that it is either
ramified rational or hypertranscendental.

An ordinary power-series germ that is ramified rational descends to `C(t)`.  But `(3)` has the
infinite noncancelled divisor described after `(5)`, so it is not rational.  Hence

```text
P_(q,A) is HT over C(t).                                   (12)
```

The conclusion is for the canonical crossing coordinate.  Algebraic rapidity-energy changes are
allowed after adjoining the corresponding algebraic kinematic base; arbitrary analytic changes
are not.

## Claim D -- local interacting QFT `[PROVED FROM PARENT THEOREM]`

Claims B and `(11)` place `S_(q,A,C)` in the fermionic regular scattering class.  Lechner's
inverse-scattering construction therefore supplies:

- a Haag--Kastler net with observables in arbitrarily small double cones;
- the Reeh--Schlieder property;
- asymptotic completeness;
- a scattering operator equal to the factorized operator built from `(3)`.

The function `(3)` is nonconstant, so the reconstructed scattering operator is not a free
constant scattering operator.  The model is interacting and its exact scattering law is HT.

## Claim E -- robustness `[PROVED]`

For fixed multiplicities and fixed `N`, the strict inequalities `(1)` define an open parameter
region in `(q,C,a_1,...,a_N)`.  Claims A--D hold at every point of this region.  Therefore HT local
scattering is not confined to an isolated parameter value.

Let `R(t)` be any nonzero rational finite CDD dressing for which

```text
theta |-> R(t_C(theta)) S_(q,A,C)(theta)                   (13)
```

remains in the regular `S(0)=-1` scattering class.  If `(13)` were DA over `C(t)`, division by the
rational factor `R` would make `P_(q,A)` DA, contradicting `(12)`.  Thus every admissible finite
regular CDD dressing also has HT scattering and reconstructs a local interacting QFT.

This is stability under finite physical CDD perturbations, not under arbitrary functional or
infinite deformations.

## Real-axis reporter

For real `theta`, put `x=sinh(theta)/C`.  An unwrapped phase is

```text
delta(theta)=pi+4 sum_j m_j sum_(k>=0)
  arctan(q^k x/a_j).                                      (14)
```

Its derivative is strictly positive:

```text
delta'(theta)=4 cosh(theta)/C sum_j m_j sum_(k>=0)
  (q^k/a_j)/(1+(q^k x/a_j)^2)>0.                          (15)
```

The logarithmic-derivative equivalence transfers `(12)` to the dimensionless phase-delay
reporter.  Multiplication by the nonzero algebraic rapidity or center-of-mass-energy Jacobian does
not remove HT away from threshold.

## Local Hamiltonian source for the whole family `[PROVED]`

Fix an auxiliary spectral scale `Lambda>0` and put

```text
kappa_j = Lambda/(C a_j).                                  (16)
```

For each `j`, the infinite-soliton inverse-scattering theorem constructs a smooth real
reflectionless Schrodinger Hamiltonian whose bound-state wave numbers are

```text
{kappa_j q^n : n>=0}                                      (17)
```

and whose transmission coefficient is

```text
T_j(k)=product_(n>=0)
  (k+i kappa_j q^n)/(k-i kappa_j q^n).                    (18)
```

At reciprocal momentum `k=Lambda/sinh(theta)`, direct substitution gives

```text
T_j(Lambda/sinh(theta))
 = product_(n>=0)
    (C a_j+i q^n sinh(theta))/(C a_j-i q^n sinh(theta))
 = product_(n>=0)
    (a_j-q^n t_C(theta))/(a_j+q^n t_C(theta)).             (19)
```

The left/right scattering matrix of one reflectionless channel is `diag(T_j,T_j)`, so its
determinant is `T_j^2`.  Take `m_j` direct-sum copies of the `j`th channel and then the direct sum
over `j`.  Its full scattering determinant at reciprocal momentum is exactly

```text
det S_Sch^total(Lambda/sinh(theta)) = P_(q,A)(t_C(theta)). (20)
```

Consequently

```text
S_(q,A,C)(theta)
  = -det S_Sch^total(Lambda/sinh(theta)).                   (21)
```

Thus every member of the open QFT family has a smooth local multichannel quantum-mechanical
ancestor.  The even multiplicities `2m_j` are the two asymptotic directions times channel
multiplicity, not repeated eigenvalues of one scalar Schrodinger operator.

This is an exact source at the Hamiltonian and scattering-data levels.  It does not yet identify
the direct-sum quantum-mechanical system with the interacting Haag--Kastler QFT or derive the
reciprocal momentum map from shared microscopic dynamics.

The active child `../../1-in-progress/feshbach-reciprocal-jost-interface.md` now derives reciprocal
spectral momentum from a local massless Schur channel and identifies its Fredholm boundary response
with inverse Jost transmission.  The proved sibling
`../not_new_scientific_knowledge/reciprocal-q-ladder-kallen-lehmann-field.md` also gives a positive
local generalized-free QFT from the reciprocal bound spectrum.  These close the origin of the
inversion and positive two-point existence, but not their promotion to the interacting bulk
two-particle amplitude `(21)`.

## Anti-theatre and novelty gate

The theorem materially strengthens physical existence but is assembled from parent results:

- rational finite CDD factors and their one-sided products;
- bounded-inner-function geometry on a strip;
- the published rational-or-HT `q`-difference theorem;
- the published constructive inverse-scattering theorem.

The candidate novelty is the open-family theorem, the exact regularity region `(1)`, and the
finite-CDD stability statement.  Formula-level searches found `q`-deformed Jost functions,
infinite CDD towers, elliptic resonance models, and arbitrary infinite pole coordinates, but did
not find `(2)`--`(21)` as a regular local-QFT HT family with the reciprocal Hamiltonian source.
That is negative search evidence, not a
priority proof.

The theorem is significant because it establishes robust physical reality.  Equations `(16)`--
`(21)` remove the narrower objection that the rational shell exists only at the S-matrix level.
The remaining source problem is the reciprocal quantum-mechanics-to-QFT duality, not the existence
of a local Hamiltonian carrying the shell.

## Exact open core

`[CONJECTURE -- RECIPROCAL JOST DUALITY]` Promote the massless Schur interface of
`../../1-in-progress/feshbach-reciprocal-jost-interface.md` to a positive non-Gaussian local
interface, modular inclusion, or operator-flow functor that sends the multichannel reflectionless
problem `(16)`--`(20)` to the relativistic factorizing QFT and realizes `(21)` on asymptotic states.

A proof must establish:

1. a Hilbert-space or local-algebra map, not only equality of scalar functions;
2. the determinant sign and the identification of the Schur momentum with relativistic
   `sinh(theta)` on asymptotic states;
3. preservation of locality, positivity, and the asymptotic particle interpretation;
4. stability under symmetry-preserving local perturbations beyond finite CDD dressing;
5. compatibility with the sectoral Kolchin signature and its future LSZ transfer.

Without this, the present theorem is a robust local-Hamiltonian and inverse-scattering existence
family rather than a dynamically predicted universality class.

## Lean boundary

The current HTGeometry corpus already formalizes the one-seed finite algebra, crossing identities,
shell constraint, boundary selection, and finite-jet HT consequences.  The passage from one seed
to the finite product `(2)` is a mechanical finite-product wrapper and does not justify a new Lean
module.  The load-bearing new content is analytic: normal convergence, enlarged-strip bounds, the
external difference-Galois dichotomy, and constructive-QFT reconstruction.

No Lean build is justified until one of those infinite analytic interfaces or the source-minimal
shell law receives an unconditional reusable theorem surface.

## Primary literature

- G. Lechner, *Construction of Quantum Field Theories with Factorizing S-Matrices*,
  <https://arxiv.org/abs/math-ph/0601022>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
  equations*, <https://arxiv.org/abs/1910.01874>.
- P. G. O. Freund and A. V. Zabrodin, *A Hierarchical Array of Integrable Models*,
  <https://arxiv.org/abs/hep-th/9208033>.
- F. Gesztesy, W. Karwowski, and Z. X. Zhao, *New types of soliton solutions*,
  <https://arxiv.org/abs/math/9210215>.
- G. Mussardo and S. Penati, *A Quantum Field Theory with Infinite Resonance States*,
  <https://arxiv.org/abs/hep-th/9907039>.
- F. A. Smirnov and A. B. Zamolodchikov, *On space of integrable quantum field theories*,
  <https://arxiv.org/abs/1608.05499>.

## Gates

- [x] complete finite-seed paper proof
- [x] exact regularity and nuclearity hypotheses checked against the source theorem
- [x] unconditional HT conclusion from the published difference-Galois theorem
- [x] open parameter region
- [x] finite regular CDD stability
- [x] real-axis observable reporter
- [x] local multichannel reflectionless-Hamiltonian source
- [x] reciprocal determinant identity for the full finite-shell family
- [ ] external formula-level novelty audit
- [ ] reciprocal Jost duality derived dynamically
- [ ] matrix-valued factorizing extension
- [ ] independent analytic and QFT review
