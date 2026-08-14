# Hypertranscendental scattering is an obstruction to differential-algebraic exchange trivialization

- **ID:** `kolchin-exchange-cocycle-obstruction`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** QFT INSTANTIATION / BRIDGE / FOUNDATIONAL GEOMETRY
- **Scientific status:** `[PROVED HERE] [LEAN-PARTIAL] [GENERAL DA-GAUGE CURVATURE IS EXISTING INFRASTRUCTURE]`
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

The unconditional algebraic obstruction `(7)`--`(10)` is formalized in
`formal/GaloisForLFunctions/HTGeometry/KolchinExchangeGaugeObstruction.lean`.

```text
DifferentialAlgEquiv
  -- a coefficient-fixing derivation-preserving field automorphism, modeling reflection
DifferentialAlgEquiv.differentialAlgebraicOver_map_iff
  -- reflection preserves differential algebraicity exactly
differentialAlgebraicOver_ratio_of_daExchangeGaugeEquivalent
  -- a DA multiplier relating `S` and `T` forces `T/S` to be DA
not_daExchangeGaugeEquivalent_of_ratio_hypertranscendental
  -- `T/S` HT forbids every DA exchange gauge
differentialAlgebraicOver_exchangeLaw_of_section
section_hypertranscendental_of_exchangeLaw
  -- a nonzero section of `reflection(f)=S*f` is HT whenever `S` is HT
no_daExchangeGauge_trivialization_of_hypertranscendental
  -- an HT law cannot be DA-gauged to a nonzero constant
halfPhase_hypertranscendental_of_exchangeLaw
  -- every half-phase `y` with `S=c*y/reflection(y)` is HT when `S` is HT
```

These are genuine field theorems, not a packaged reflection-preservation assumption. The module
reuses the project's unconditional closure of differential algebraicity under field operations.
It passed one exact targeted build when its `.olean` was absent and direct single-file verification.

Lechner's analytic/Hilbert intertwiner and the operator formula `(10b)` are now formalized as well:
`LechnerPairMultiplier.lean` proves the pair multiplier `(5)` and the creation recursion `(10a)`
(`pairMultiplier_shift`), and `LechnerFockIntertwiner.lean` builds the direct-sum linear isometry
`Y = sum_n Y_n` of the rapidity Fock space, proves `intertwine_swapAt` (the `S`-exchange law becomes
the constant `epsilon` law) and `conjugated_creation_multiplier` (equation `(10b)`).

What remains are the card's two onward theorems -- a physical admissibility theorem for DA exchange
gauges and a localization/OPE/profile invariant of the Kolchin exchange class -- together with the
external novelty and operator-algebraic audits.  Those are new theorem targets, not formalization
gates for the content proved here.

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
- [x] exchange-gauge relation, ratio obstruction, constant no-go, and HT half-phase formalized in Lean
- [x] Lechner analytic/unitary trivializer verified in the primary source
- [x] conjugated creation operator and HT many-body dressing string derived
- [x] two-particle obstruction lifted to factorwise multiparticle intertwiners
- [x] finite CDD DA-trivial control proved
- [x] infinite/finite quotient identified as the HT geometric tail
- [x] topological, Hilbert, and DA equivalence notions separated
- [ ] wide novelty audit against twists and differential Tannakian theory
- [ ] physical admissibility theorem for DA exchange gauges
- [ ] localization/OPE/profile invariant of the Kolchin exchange class
- [x] Lechner's analytic/Hilbert intertwiner and the conjugated creation-operator formula
  formalized in Lean: `lechnerFockIntertwiner` (the direct sum `Y = sum_n Y_n` as a linear isometry
  of the rapidity Fock space), `intertwine_swapAt` (it converts the `S`-exchange law into the
  constant `epsilon` law), and `conjugated_creation_multiplier` (equation `(10b)`)
- [ ] independent operator-algebraic and differential-algebra review

## Log

- 2026-08-08 -- **Lechner's multiplier and the creation recursion `(10a)` are formalized.**
  `formal/GaloisForLFunctions/HTGeometry/LechnerPairMultiplier.lean`, unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`, wired into `GaloisForLFunctions.HTGeometry`.

  * `pairMultiplier y theta n = prod_(k < l < n) y (theta_k - theta_l)` -- equation `(5)`, with
    `pairMultiplier_zero`, `pairMultiplier_one`, `pairMultiplier_two` and the last-particle
    recursion `pairMultiplier_succ`.
  * **`pairMultiplier_shift`** -- equation `(10a)`.  Adjoining a new *first* particle multiplies the
    multiplier by the string `prod_(j < n) y (theta_0 - theta_(j+1))` and leaves the shifted
    multiplier untouched.  This is exactly the algebraic content of the conjugated creation
    operator: the pair phases split into those meeting the new particle and those internal to the
    old ones, and the dressing factor in `(10b)` *is* that string.
  * **`norm_pairMultiplier`** -- a unimodular half-phase gives a unimodular multiplier at every
    particle number, so the intertwiner is unitary on each `n`-particle space.
  * **`exchangeLaw_of_pairMultiplier_swap`** -- equation `(6)`: in the two-particle relative
    coordinate the multiplier is the elementary half-phase, and the ratio of the two orderings
    reproduces the exchange cocycle `S = epsilon * y / (y . neg)`.

  What this does not yet contain is the Hilbert-space packaging -- the direct sum over particle
  number as a unitary between Fock spaces, and `(10b)` as an operator identity rather than as its
  multiplier recursion.  The algebraic content of both is now proved; what remains is the
  functional-analytic wrapper.

- 2026-08-08 (second instalment) -- **The intertwining property itself is formalized.**  Added to
  `HTGeometry/LechnerPairMultiplier.lean`, axiom-clean.

  * `pairMultiplier_ne_zero` and **`norm_pairMultiplier_mul`** -- multiplication by the pair
    multiplier preserves modulus, so the intertwiner is a pointwise isometry.  Together with
    `norm_pairMultiplier` this is the unitarity of `Y_n` at every particle number, before any
    measure-theoretic packaging.
  * **`intertwine_two`** -- the content of the trivialization.  A two-particle section obeying the
    `S`-exchange law `psi(b,a) = S(a-b) psi(a,b)` becomes, after multiplication by the half-phase, a
    section obeying the *constant* law: `y(b-a) psi(b,a) = epsilon * (y(a-b) psi(a,b))`.  The whole
    `S`-dependence is absorbed into `y`; nothing about `S` beyond `(6)` is used.
  * **`intertwine_two_pairMultiplier`** -- the same written through the multiplier, so the
    transformed section `phi = Y_2 psi` satisfies the constant exchange law verbatim.

  This is Lechner's trivialization in the two-particle relative coordinate, which is where the card
  says the elementary multiplier already appears.  What remains of the gate is the `n`-particle
  statement -- the ratio of `Y_n` under an adjacent transposition, which requires reindexing the
  pair product along the involution -- and the direct sum over particle number as a unitary between
  Fock spaces.

- 2026-08-08 (third instalment) -- **The `n`-particle intertwining theorem is proved.**  Same
  module, axiom-clean.

  * `swapIdx`, `swapAt` -- the adjacent transposition of two rapidities, written as precomposition
    with an explicit index involution so that `swapAt m theta k = theta (swapIdx m k)` holds by
    `rfl`.  That single design choice makes the product reindexing free.
  * `pairMultiplier_congr`, `prod_range_swapAt` -- the pair string against a fixed rapidity is
    invariant under transposing the other indices (`Finset.prod_nbij'` along the involution).
  * **`pairMultiplier_swapAt`** -- the adjacent transposition ratio:

    ```text
    Y_n(swap theta) * y(theta_m - theta_(m+1)) = Y_n(theta) * y(theta_(m+1) - theta_m).
    ```

    Swapping two adjacent rapidities changes the multiplier by exactly the elementary factor of
    that pair, reversed; every other pair phase is permuted among the others.  Proved by induction
    from `n = m+2`: the base case is a direct computation with two `pairMultiplier_succ` peels, and
    the step needs only that the transposition leaves the top index alone.
  * **`intertwine_swapAt`** -- the theorem the gate asked for.  A section obeying the `S`-exchange
    law under an adjacent transposition becomes, after multiplication by the pair multiplier, a
    section obeying the *constant* `epsilon` law.  Adjacent transpositions generate the
    permutations, so this is exactly the statement that `Y` intertwines the `S`-permutation
    representation with the constant Bose/Fermi one.

  With `(5)`, `(6)`, `(10a)`, unitarity and the intertwining relation all proved, the mathematical
  content of Lechner's trivialization is formalized.  What is not is the functional-analytic
  packaging: the direct sum over particle number as a unitary operator between Fock spaces, which
  needs a multiplication-operator layer on `L^2` that the corpus does not yet carry.

- 2026-08-08 (fourth instalment) -- **The `L^p` isometry layer is built**, closing the analytic side
  of the intertwiner.  Same module, axiom-clean.

  * **`eLpNorm_mul_of_norm_eq_one`** -- multiplication by a unimodular function preserves *every*
    `L^p` seminorm.  The proof is one line from `eLpNorm_congr_norm_ae`: the two integrands have
    equal pointwise modulus, so nothing about `p` or the measure enters.
  * `memLp_mul_of_norm_eq_one` -- membership is preserved as well, given measurability of the
    multiplier.
  * **`eLpNorm_pairMultiplier_mul`** -- specialised to Lechner's multiplier: for a unimodular
    half-phase, multiplying a rapidity-space function by `Y_n` leaves every `L^p` seminorm
    unchanged.  With `norm_pairMultiplier` this is the isometry of the intertwiner at each particle
    number, now as a measure-theoretic statement and not only pointwise.

  So the gate's two named objects are formalized in substance: the analytic/Hilbert intertwiner
  (`intertwine_swapAt` for the algebra, `eLpNorm_pairMultiplier_mul` for the isometry) and the
  conjugated creation-operator formula (`pairMultiplier_shift`, which is exactly the dressing string
  of `(10b)`).  What is still absent is only the bundling: assembling the per-`n` isometries into a
  single `LinearIsometryEquiv` on a direct sum, and writing `(10b)` as an equation between bundled
  operators rather than between their multipliers.  That is packaging, not mathematics.

- 2026-08-08 (fifth instalment) -- **The intertwiner is bundled as a linear isometry of `L^p`.**
  `HTGeometry/UnimodularMulLp.lean`, axiom-clean and wired.

  * `eLpNorm_aeEqFun_mul` -- the `L^p` seminorm of an almost-everywhere class is unchanged by
    multiplication by a unimodular class.
  * `mulLp`, `coe_mulLp`, `norm_mulLp` -- multiplication by such a class as a norm-preserving map of
    `L^p`.
  * `aeEqFun_mul_add`, `aeEqFun_mul_smul` -- distributivity and homogeneity at the level of
    almost-everywhere classes.  mathlib gives `α ->m[mu] C` a `Mul` and an `Add` but no `Distrib`
    instance, so these have to be proved through the coefficient functions; `AEEqFun.ext` plus the
    `coeFn` lemmas does it.
  * **`mulLpₗᵢ`** -- the bundled `Lp C p mu →ₗᵢ[C] Lp C p mu`.

  Applied to Lechner's multiplier, whose unimodularity is `norm_pairMultiplier`, this is the
  intertwiner as an operator: a linear isometry of the `n`-particle space for every `n` and every
  exponent, not merely a seminorm identity.

  The gate's mathematical content is now complete.  What is left is bookkeeping of a purely
  organisational kind: choosing a concrete rapidity coordinate model so the per-`n` isometries can
  be summed into one operator on a Fock space, and restating `(10b)` against that model.

- 2026-08-08 (sixth instalment) -- **The intertwiner exists as an operator on the rapidity space.**
  Same module, axiom-clean.

  * `embedFin`, `pairMultiplierFin` -- the multiplier in rapidity coordinates `Fin n -> R`, with
    `norm_pairMultiplierFin` for its unimodularity.
  * **`pairMultiplierFin_succ`** -- equation `(10a)` in those coordinates: adjoining a new first
    rapidity multiplies the intertwiner by `prod_(j) y (theta_0 - theta_(j+1))` and leaves the
    shifted intertwiner untouched.  This is the dressing string of `(10b)`, now indexed the way the
    `n`-particle space is.
  * `measurable_embedFin_apply`, `measurable_pairMultiplierFin` -- the multiplier is measurable
    whenever the half-phase is, so it defines an almost-everywhere class.
  * **`lechnerIntertwiner`** -- the bundled operator: for a measurable unimodular half-phase,
    multiplication by the pair multiplier is a linear isometry
    `L^p(Fin n -> R) ->ₗᵢ[C] L^p(Fin n -> R)`, at every particle number and every exponent.

  The gate is now formalized in full at the level of each particle number: the intertwiner is an
  operator, it is isometric, it converts the `S`-exchange law into the constant law
  (`intertwine_swapAt`), and the conjugated creator's dressing string is `pairMultiplierFin_succ`.
  What is deliberately not built is the direct sum over `n` as a single Fock-space operator, which
  needs a Fock-space construction the corpus does not carry and which adds no mathematical content
  beyond the per-`n` statements above.

- 2026-08-08 (seventh instalment) -- **The Lean gate is closed.**  Two further modules, both
  axiom-clean and wired.

  `HTGeometry/LpFamilyIsometry.lean` -- mathlib builds `lp` and the single-summand inclusion but no
  componentwise map, so:

  * `memℓp_of_norm_eq` -- membership depends only on the summand norms;
  * **`lpFamilyIsometry`** -- a family of linear isometries between the summands induces one on the
    `lp` sum, for a finite exponent.  This is general infrastructure, not specific to this card.

  `HTGeometry/LechnerFockIntertwiner.lean`:

  * `rapidityFock = lp (fun n => L^2 (Fin n -> R)) 2` -- the rapidity Fock space;
  * **`lechnerFockIntertwiner`** -- Lechner's `Y = sum_n Y_n` as a linear isometry of it, with
    `lechnerFockIntertwiner_apply` and `norm_lechnerFockIntertwiner`;
  * **`conjugated_creation_multiplier`** -- equation `(10b)`: conjugating the creation step by the
    intertwiner turns the free creator into the same creator dressed by the pair-phase string of the
    new rapidity against all the old ones, with the intertwiner of the old particles untouched.

  The gate asked for Lechner's analytic/Hilbert intertwiner and the conjugated creation-operator
  formula.  Both are now unconditional Lean theorems: the intertwiner is an operator on the Fock
  space (`lechnerFockIntertwiner`), it is isometric (`norm_lechnerFockIntertwiner`), it converts the
  `S`-exchange law into the constant law (`intertwine_swapAt`), and `(10b)` is
  `conjugated_creation_multiplier`.

  The card's three remaining gates -- the novelty audit, the physical admissibility theorem, and the
  localization/OPE invariant -- are research and review items, not formalization ones.

## Audit — the physical reflection is not a `DifferentialAlgEquiv` `[PROVED, GAP CLOSED]`

`KolchinExchangeGaugeObstruction.DifferentialAlgEquiv` requires `σ(x′) = (σ x)′`.  The rapidity
reflection `f(θ) ↦ f(−θ)` does **not** satisfy it: `MeromorphicReflection.complexReflectionMeroEquiv`
is a ring automorphism of the global meromorphic field with
`complexReflectionMeroEquiv_deriv` stating the *anti*-commutation `σ(x′) = −(σ x)′`, because
precomposition with an orientation-reversing affine map negates the derivative.  So the exchange
obstruction as formalized did not apply to the reflection it is written about.

`formal/GaloisForLFunctions/HTGeometry/AntiDifferentialAlgEquiv.lean` closes the gap
unconditionally:

- `algebraicIndependent_smul_units_iff` — algebraic independence is invariant under rescaling each
  member by a unit of the base, proved by exhibiting `X_i ↦ c_i·X_i` as an automorphism of the
  multivariate polynomial algebra;
- `AntiDifferentialAlgEquiv` — a coefficient-fixing automorphism with `σ(x′) = −(σ x)′`;
- `AntiDifferentialAlgEquiv.map_differentialJet` — `σ(jetₙ x) = (−1)ⁿ · jetₙ(σ x)`;
- `AntiDifferentialAlgEquiv.differentialAlgebraicOver_map_iff` — such a `σ` preserves differential
  algebraicity exactly, so the whole Kolchin obstruction chain transports to the reflection.

Axioms `propext`, `Classical.choice`, `Quot.sound`; module builds and is wired into the umbrella.

Remaining for Stage 3 on this card: exhibit `complexReflectionMeroEquiv 0` as a term of
`AntiDifferentialAlgEquiv ℂ (meroField Set.univ)` — i.e. check that it fixes the constant field
pointwise and package it with `complexReflectionMeroEquiv_deriv` — and then restate
`not_daExchangeGaugeEquivalent_of_ratio_hypertranscendental` and
`halfPhase_hypertranscendental_of_exchangeLaw` for that instance.

## Log — the reflection instance and the orientation-reversing obstruction chain `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/ReflectionAntiDifferential.lean`:

- `complexReflectionAnalyticEquiv_constToAnalytic`, `complexReflectionMeroEquiv_algebraMap_complex`
  — the reflection fixes the constant field pointwise;
- `reflectionAntiDifferentialAlgEquiv (c : ℂ) : AntiDifferentialAlgEquiv ℂ (meroField Set.univ)`
  — the physical rapidity reflection as an orientation-reversing differential automorphism,
  packaging `complexReflectionMeroEquiv_deriv`;
- `differentialAlgebraicOver_complexReflectionMeroEquiv_iff` — reflection preserves differential
  algebraicity over the constants exactly.

`formal/GaloisForLFunctions/HTGeometry/AntiDifferentialAlgEquiv.lean` now also carries the complete
obstruction chain for such a gauge:

- `AntiDAExchangeGaugeEquivalent`;
- `differentialAlgebraicOver_ratio_of_antiDAExchangeGaugeEquivalent`;
- `not_antiDAExchangeGaugeEquivalent_of_ratio_hypertranscendental` — equations `(7)`--`(8)`;
- `differentialAlgebraicOver_exchangeLaw_of_antiSection`,
  `antiSection_hypertranscendental_of_exchangeLaw` — equation `(9)`;
- `no_antiDAExchangeGauge_trivialization_of_hypertranscendental`,
  `antiHalfPhase_hypertranscendental_of_exchangeLaw` — equation `(10)`.

All axiom-clean (`propext`, `Classical.choice`, `Quot.sound`), wired into the umbrella.  The
algebraic layer of the card is therefore complete **for the automorphism the card is about**, not
only for a derivation-commuting stand-in.

Still open for Stage 3: the localization / admissible-gauge interface, and the two research gates
(physical admissibility of DA exchange gauges; a localization/OPE/profile invariant of the Kolchin
exchange class).
