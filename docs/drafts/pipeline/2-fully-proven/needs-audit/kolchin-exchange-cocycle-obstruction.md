# Hypertranscendental scattering is an obstruction to differential-algebraic exchange trivialization

- **ID:** `kolchin-exchange-cocycle-obstruction`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** QFT INSTANTIATION / BRIDGE / FOUNDATIONAL GEOMETRY
- **Scientific status:** `[PROVED HERE] [GENERAL DA-GAUGE CURVATURE IS EXISTING INFRASTRUCTURE]`
  `[QFT INSTANTIATION NOVELTY UNVERIFIED] [PHYSICAL ADMISSIBILITY CATEGORY OPEN]`
- **Scope:** general scalar factorizing exchange cocycles, with the geometric CDD family as an exact
  finite/global discriminator; no RH or distinguished special-function input
- **Statement:** A regular scalar scattering function is analytically and unitarily gauge-
  equivalent to a constant Bose/Fermi exchange law, but an HT scattering function admits no
  differential-algebraic exchange gauge.  Finite CDD products are DA-trivial, whereas the
  geometric infinite completion is not DA-gauge-equivalent to any finite truncation.  HT is thus
  an obstruction class of multiparticle assembly that is invisible to abstract Hilbert-space
  equivalence.

## Founding question

What mathematical structure carries the physical HT when all `S_2`-symmetric Fock spaces are
abstractly isomorphic to ordinary Bose or Fermi Fock space?

The answer is not a new Hilbert-space topology.  It is the complexity of the multiplier required
to trivialize the exchange constraint.  The relevant category remembers whether that multiplier
obeys a finite algebraic-differential law.

## Exchange cocycles

Let `t` be an odd crossing coordinate and let `iota(t)=-t`.  A scalar exchange law is a nonzero
meromorphic function satisfying

```text
S(t) S(-t)=1.                                               (1)
```

This is the multiplicative `Z/2` cocycle condition.  A two-particle section obeys

```text
psi(-t)=S(t) psi(t).                                       (2)
```

For a nonzero multiplier `g`, the change of frame

```text
phi(t)=g(t) psi(t)
```

changes the exchange cocycle to

```text
T(t)=g(-t) S(t)/g(t).                                      (3)
```

Call `(3)` a **differential-algebraic exchange gauge** when `g` is DA over the chosen kinematic
base `K=C(t)`.  Two cocycles are **DA-gauge equivalent** when they are related by such a `g`.

Equation `(3)` is the one-particle-coordinate shadow of the multiplier intertwiners on every
`S`-symmetric `n`-particle sector.

## Analytic/Hilbert triviality `[PARENT THEOREM]`

For a regular scattering function with `epsilon=S(0) in {+1,-1}`, Lechner constructs the unique
odd analytic phase shift with

```text
S(v)=epsilon exp(2 i delta(v)),       delta(0)=0.           (4)
```

The multipliers

```text
Y_n(theta_1,...,theta_n)
  = product_(k<l) [epsilon exp(i delta(theta_k-theta_l))]    (5)
```

are bounded on the relevant Hardy tube and unitary on `L^2`.  They intertwine the
`S`-permutation representation with the constant `epsilon` Bose/Fermi representation.  Hence the
direct sum `Y=direct_sum Y_n` maps the full `S`-symmetric Fock space unitarily onto the constant-
statistics Fock space.

In two-particle relative coordinate, the elementary factor `y` in `(5)` satisfies

```text
S(t)=epsilon y(t)/y(-t).                                   (6)
```

Thus the exchange cocycle is analytically and Hilbert-space trivial.  This is an explicit
multiplicative Hilbert-90 trivialization, not a topological obstruction.

## Kolchin obstruction theorem `[PROVED]`

Let `S` and `T` be exchange cocycles and suppose `(3)` holds with a nonzero DA multiplier `g`.
Reflection preserves differential algebraicity, and DA elements form a field.  Therefore

```text
T(t)/S(t)=g(-t)/g(t)                                       (7)
```

is DA over `C(t)`.  Consequently:

```text
T/S HT  =>  S and T are not DA-gauge equivalent.           (8)
```

In particular, if `S` is HT and `epsilon` is constant, then `epsilon/S` is HT by Mobius reporter
invariance, so

```text
S HT  =>  no DA multiplier trivializes S to epsilon.       (9)
```

Every analytic trivializer of an HT cocycle is therefore itself HT.  Applied to Lechner's
canonical half-phase:

```text
S HT  =>  y=epsilon exp(i delta) is HT.                    (10)
```

The abstract unitary equivalence exists, but it cannot be implemented inside the differential-
algebraic multiplier category.

## Operator-level realization -- the HT Jordan--Wigner string `[PROVED]`

Let

```text
y(v)=epsilon exp(i delta(v)),
Y_n(theta_1,...,theta_n)=product_(k<l)y(theta_k-theta_l).
```

Conjugate the `S`-symmetric creation operator by Lechner's unitary `Y`.  Since `Y` intertwines the
`S`-symmetrizer with the constant-`epsilon` symmetrizer and

```text
Y_(n+1)(theta_0,...,theta_n)
  = [product_(j=1)^n y(theta_0-theta_j)]
    Y_n(theta_1,...,theta_n),                              (10a)
```

one obtains on the finite-particle domain

```text
(Y z_S^dagger(psi) Y^* Phi)_(n+1)
  = sqrt(n+1) P_(n+1)^epsilon
      [psi(theta_0)
       product_(j=1)^n y(theta_0-theta_j)
       Phi_n(theta_1,...,theta_n)].                        (10b)
```

Thus the Hilbert-space trivialization turns the ZF creator into an ordinary Bose/Fermi creator
dressed by a number-dependent pair-phase string.  The one-to-two-particle step already contains
the elementary multiplier `y(theta_0-theta_1)`.

For a finite CDD truncation this string can be chosen algebraic/DA.  For an HT completion, `(10)`
forces every analytic half-phase `y` to be HT.  The physical carrier in the constant-statistics
frame is therefore an HT Jordan--Wigner-type dressing string, not a modified one-particle
Hamiltonian.

## Multiparticle obstruction `[PROVED]`

Suppose an `n`-particle multiplication gauge is assembled from one pair factor,

```text
G_n(theta_1,...,theta_n)=product_(k<l) g(theta_k-theta_l),  (11)
```

and intertwines the `S`-symmetric sector with a `T`-symmetric sector.  Restricting the adjacent-
transposition identity to the exchanged pair gives exactly `(3)`.  Hence `(8)` obstructs such a DA
factorwise intertwiner simultaneously for every `n>=2`.

More generally, any DA multiplication intertwiner whose adjacent-exchange quotient is defined
would make `T/S` DA.  The obstruction is already complete on the two-particle face; adding more
particles cannot remove it.

## Exact finite/global fracture

For the finite geometric CDD truncation

```text
P_(q,N)(t)=product_(k=0)^(N-1) ((1-q^k t)/(1+q^k t))^2,
S_N(t)=-P_(q,N)(t),                                        (12)
```

`S_N` is rational.  A local algebraic square root of `S_N/(-1)` gives a DA half-phase, so every
finite truncation is DA-gauge trivial.

For the infinite completion

```text
P_q(t)=product_(k>=0) ((1-q^k t)/(1+q^k t))^2,
S_infinity(t)=-P_q(t),                                     (13)
```

the rational-or-HT theorem makes `S_infinity` HT.  Hence `(9)` proves that it is not DA-gauge
trivial.  More sharply,

```text
S_infinity(t)/S_N(t)=P_q(q^N t).                           (14)
```

Rational scaling preserves HT, so `(14)` is HT.  By `(8)`:

```text
for every finite N,
S_infinity is not DA-gauge equivalent to S_N.              (15)
```

This is an exact global-completion phase change.  Every finite theory lies in the DA-trivial
exchange class, while their convergent infinite completion leaves that class.

## Physical meaning

The scattering Hilbert spaces alone do not see the fracture: Lechner's `Y` gives a unitary
identification with constant-statistics Fock space.  The Poincare representation is likewise not
the carrier; the multipliers depend only on rapidity differences.  The complexity becomes
physical when one asks for a frame compatible with finite differential-law observables, ZF
generators, form factors, and localization data.

Define the **Kolchin exchange class** of `S` to be its orbit under DA exchange gauges `(3)`.  Then

```text
finite CDD laws:       constant Kolchin exchange class,
geometric HT limit:   nonconstant Kolchin exchange class.  (16)
```

This implements the founding metaphor literally: the one-particle flow remains free, while the
nontrivial object is a constraint-gluing class on multiparticle configuration space.

`compact-local-form-factor-hypertranscendence-forcing.md` gives the local observable consequence:
every nonzero compact-local two-particle form factor is a section of this exchange class and is
forced HT.

## Anti-theatre attacks

1. **Hilbert 90 renamed.**  Analytic cocycle triviality is parent mathematics, and Lechner's
   explicit unitary is parent QFT.  The local corpus also already contains a general DA-cocycle
   curvature law and DA-gauge invariance/blindness theorems.  The candidate new content is only
   their exact ZF/Lechner realization, the operator string `(10b)`, and the finite/global QFT
   fracture `(15)`.
2. **Topological phase claimed.**  False.  The cocycle is analytically and unitarily trivial.  The
   obstruction exists only after restricting admissible gauges by differential-algebraic
   complexity.
3. **Physical equivalence disproved.**  Not established.  Failure of DA multiplier equivalence is
   weaker than inequivalence of Haag--Kastler nets and stronger than bare Hilbert-space
   inequivalence.  The physical admissibility of the DA gauge category is an open gate.
4. **Finite/infinite limit rhetoric.**  Equation `(14)` proves the quotient is the scaled HT tail,
   so `(15)` is exact for every truncation.
5. **Phase logarithm used without branches.**  The obstruction theorem `(8)` uses only the
   cocycles and a nonzero multiplier.  Lechner's phase is invoked only on the regular nonvanishing
   strip where its analytic branch is proved to exist.
6. **Factorwise no-go called universal.**  The general multiplication-intertwiner statement
   requires its adjacent-exchange quotient to be a DA meromorphic function.  Nonmultiplicative or
   nonlocal unitary equivalences are not excluded.

## Novelty gate

The literature contains:

- ZF exchange algebras and `S`-symmetric Fock representations;
- unitary phase multipliers intertwining these sectors with Bose/Fermi sectors;
- Drinfeld twists, nonlocal basis transformations, and gauge-equivalent S-matrices;
- group-cohomological and Hilbert-90 descriptions of multiplicative cocycles.

Focused searches found no Kolchin/differential-algebraic restriction on exchange gauges, no
hypertranscendental obstruction class for ZF statistics, and no finite-CDD/infinite-CDD separation
of the form `(15)`.  This is negative search evidence only.  The terminology **Kolchin exchange
class** is provisional until a wider audit of differential Tannakian categories, dynamical
Yang--Baxter twists, and integrable-model basis transformations is complete.

Within the project, the abstract nonflattenability mechanism is not new:
`ht-period-rank-one-scalar-stanley-reisner-principalization.md` already defines DA-gauge-flat
translation cocycles and proves a nonconstant DA-cocycle curvature necessity theorem.
`da-gauge-ht-divisor-blindness.md` and the generic differential-field infrastructure already show
what DA multipliers preserve.  This card is therefore a physical instantiation, not the founding
abstract gauge theorem.

## Significance gate

The QFT specialization supplies an exact invariant that survives after ordinary Hilbert-space
equivalence has erased the distinction.  It explains how HT can be physically real while
propagation remains free and why the infinite completion is not merely a large finite CDD model.

The proof is elementary after the parent theories are aligned.  Fields-scale significance
requires one further theorem: show that DA exchange gauge is the maximal frame-change class
compatible with local observables, or derive a net/OPE/positivity quantity that depends only on the
Kolchin exchange class.

## Exact open core

`[CONJECTURE -- LOCALIZATION FUNCTOR]` The assignment from a regular scattering cocycle to its
Haag--Kastler net factors through analytic exchange gauges only when the gauge preserves a local
source category.  Within that admissible category, DA gauges act trivially on the directed local
Kolchin profile, whereas an HT Kolchin exchange class forces a positive local profile.

Concrete subproblems:

1. characterize multiplication intertwiners that preserve wedge algebras or compact-local
   intersections;
2. decide whether Lechner's HT half-phase fails locality by a quantifiable commutator or modular-
   nuclearity defect;
3. define the matrix-valued nonabelian version using differential-algebraic gauge transformations
   of Yang--Baxter cocycles;
4. compare the class with Drinfeld twists, CDD equivalence, and scattering equivalence in the
   rigorous QFT literature.

## Lean boundary

The corpus has reflection, modular-ratio, rational-reporter, finite jet-independence, and general
DA-cocycle curvature infrastructure.  `MeromorphicExponentialGaugeDA.lean` now also proves the
first-order theorem that a genuine exponential with base-field logarithmic derivative is DA.
These results cover the finite differential-algebra steps; the new physical statement depends on
the choice of admissible exchange gauge and on Lechner's analytic/Hilbert intertwiner.

Formalizing only `(7)`--`(9)` would be a short algebraic wrapper and would not establish the QFT
claim.  No Lean edit is justified until the localization functor or an unconditional physical
gauge interface is proved on paper.

## Primary literature

- G. Lechner, *Construction of Quantum Field Theories with Factorizing S-Matrices*,
  <https://arxiv.org/abs/math-ph/0601022>.
- A. Liguori and M. Mintchev, *Fock Representations of Quantum Fields with Generalized
  Statistics*, <https://arxiv.org/abs/hep-th/9403039>.
- S. Sotiriadis, D. Fioretto, and G. Mussardo, *Zamolodchikov--Faddeev Algebra and Quantum Quenches
  in Integrable Field Theories*, <https://arxiv.org/abs/1112.2963>.
- G. Arutyunov, S. Frolov, and M. Zamaklar, *The Zamolodchikov--Faddeev Algebra for
  `AdS_5 x S^5` Superstring*, <https://arxiv.org/abs/hep-th/0612229>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and Linear Difference
  Equations*, <https://arxiv.org/abs/1910.01874>.

## Gates

- [x] exchange-gauge relation and DA obstruction proved
- [x] Lechner analytic/unitary trivializer verified in the primary source
- [x] conjugated creation operator and HT many-body dressing string derived
- [x] two-particle obstruction lifted to factorwise multiparticle intertwiners
- [x] finite CDD DA-trivial control proved
- [x] infinite/finite quotient identified as the HT geometric tail
- [x] topological, Hilbert, and DA equivalence notions separated
- [ ] wide novelty audit against twists and differential Tannakian theory
- [ ] physical admissibility theorem for DA exchange gauges
- [ ] localization/OPE/profile invariant of the Kolchin exchange class
- [ ] independent operator-algebraic and differential-algebra review
