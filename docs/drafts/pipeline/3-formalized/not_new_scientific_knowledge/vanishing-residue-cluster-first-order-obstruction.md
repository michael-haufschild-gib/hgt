# Vanishing-residue clusters obstruct first-order algebraic differential equations

- **ID:** `vanishing-residue-cluster-first-order-obstruction`
- **Stage:** 3-formalized
- **Type:** GENERAL HT CONSTRAINT THEOREM / FIRST NONLINEAR ORDER BOUND
- **Scientific status:** `[PROVED] [FORMALIZED] [CONCRETE COROLLARY NOT NEW TO CORPUS]`
- **Generic criterion:** `[NOVELTY UNVERIFIED]`
- **Formal owner:** `formal/GaloisForLFunctions/HTGeometry`
- **Primary instance:** `f(z)=Complex.digamma (Complex.Gamma z)`
- **Methods:** symbolic proof and Lean verification only; no numerical computation

## Constraint

Let `f` be holomorphic off a discrete singular set.  Suppose there are infinitely many distinct
cluster centres `a_n` such that, for each `n`, `f` has simple poles `z_(n,m) -> a_n` with nonzero
residues `rho_(n,m) -> 0`.

The theorem target is:

> `f` satisfies no nonzero first-order algebraic differential equation over `C(z)`.

Equivalently, after clearing denominators, no nonzero finite expression

```text
sum_(i,j) A_(i,j)(z) f(z)^i f'(z)^j
```

with `A_(i,j) in C[z]` can vanish identically on the regular locus.

This is a static singularity constraint.  It does not propagate `f` from initial data and does not
assert full hypertranscendence.

## Paper proof

Assume a relation exists.  Give `f^i (f')^j` its simple-pole weight

```text
w(i,j)=i+2j
```

and its residue degree

```text
d(i,j)=i+j.
```

Let `W` be the largest weight occurring with a nonzero coefficient polynomial.  There are only
finitely many weight-`W` coefficient polynomials.  Each has finitely many zeros, so one cluster
centre `a_n` avoids all their zero sets.

At a simple pole `z_(n,m)` with local coordinate `t=z-z_(n,m)`, one has

```text
f = rho_(n,m) t^(-1) + O(1),
f' = -rho_(n,m) t^(-2) + O(t^(-1)).
```

Multiplying the alleged relation by `t^W` and taking `t -> 0` gives

```text
sum_(i+2j=W) (-1)^j A_(i,j)(z_(n,m)) rho_(n,m)^(i+j) = 0.       (1)
```

Among the weight-`W` pairs, the residue degree is injective: if

```text
i+2j=i'+2j'  and  i+j=i'+j',
```

then `i=i'` and `j=j'`.  Hence the pair with maximal `j` is the unique pair of minimal residue
degree `d_*`.  Divide `(1)` by the nonzero `rho_(n,m)^d_*` and let `m -> infinity`.  The unique
minimal-degree term tends to

```text
(-1)^j A_(i,j)(a_n) != 0,
```

while every other term contains a positive power of `rho_(n,m)` and tends to zero.  This
contradicts `(1)`.

Therefore no first-order ADE exists.

## Primary instance: digamma after Gamma

For every `n >= 0`, the inverse-Gamma pole branch supplies simple poles

```text
Gamma(z_(n,m))=-m,
z_(n,m) -> -n,
rho_(n,m)=Res_(z_(n,m)) digamma(Gamma z) -> 0,
rho_(n,m) != 0
```

for all sufficiently large `m`.  The exact asymptotics already proved in the pipeline are

```text
z_(n,m)=-n-((-1)^n/n!)m^(-1)+O(m^(-2)),
rho_(n,m)=((-1)^n/n!)m^(-2)+O(m^(-3)).
```

Thus the theorem gives

```text
not DifferentiallyAlgebraicOfOrder (digamma o Gamma) 1.
```

This is the first nonlinear differential-order exclusion for the composite.  The existing pole
cluster theorem proves algebraic transcendence and non-D-finiteness; the present law excludes
every nonlinear first-order ADE as well.  Full hypertranscendence remains the higher-order tied-
weight problem.

## Boundary attacks

1. **One-centre failure.**  `tan(1/z)` is first-order DA and has simple poles with residues tending
   to zero at the single fixed centre `0`.  Infinitely many centres are load-bearing because they
   let the proof avoid the finitely many coefficient zero sets.
2. **Order-two tie.**  At derivative order two, `f f''` and `(f')^2` have the same pole weight and
   the same residue degree.  The uniqueness step fails exactly there.  The theorem does not hide
   the full HT problem.
3. **Residues bounded away from zero.**  If residues do not vanish, division by the minimal
   residue power does not suppress the other top-weight terms.  Vanishing mass is load-bearing.
4. **Growth substitution.**  No Nevanlinna ceiling is used.  Infinite-order DA functions do not
   affect the proof.
5. **Painleve parent.**  General first-order algebraic-ODE singularity theory may imply a broader
   statement.  The novelty claim is held until primary literature is checked for this exact
   vanishing-residue multi-centre criterion and the `digamma o Gamma` consequence.

## Formalization

The generic theorem is formalized in
`formal/GaloisForLFunctions/HTGeometry/VanishingResidueFirstOrderObstruction.lean`.  It includes:

1. the derivative principal-part theorem for an arbitrary meromorphic simple pole;
2. injectivity of pole weight and residue degree on first-order monomials;
3. the unique minimal-residue-degree top-row limit;
4. the infinite-centre polynomial-zero avoidance argument; and
5. a canonical normal form from `MvPolynomial (Fin 3) C` to finite `(i,j)` rows with coefficients
   in `C[z]`.

The concrete reciprocal-Gamma construction and the repository-level conclusion

```text
not_differentiallyAlgebraicOfOrder_one_digamma_comp_Gamma :
  not DifferentiallyAlgebraicOfOrder (digamma o Gamma) 1
```

are formalized in `formal/GaloisForLFunctions/HTGeometry/DigammaGammaFirstOrder.lean`.

## Source and parent-theory audit

The exact phrases and mathematical signatures of the multi-centre vanishing-residue criterion and
the `digamma o Gamma` corollary were searched in the available primary literature.  No exact prior
statement was located.  This negative search evidence is not a proof of novelty.

- Eremenko's 1982 survey *Meromorphic solutions of algebraic differential equations* gives the
  classical Malmquist/Fuchs parent theory for whole-plane meromorphic solutions of first-order
  algebraic differential equations.  The present application is not meromorphic at its finite
  cluster centres, so that global theorem is not a direct corollary.  Its singularity theory remains
  the broad parent and makes an elementary special-case antecedent plausible.
- Huang--Ng's 2020 composition theorem proves hypertranscendence when a hypertranscendental outer
  function is composed with a nonconstant entire inner function.  Gamma is meromorphic rather than
  entire, and `digamma o Gamma` acquires finite pole-accumulation centres, so their theorem does not
  cover this instance.
- Classical first-order Painleve--Malmquist classification is substantially broader in ambition
  than this criterion.  Until the exact local consequence is checked against that full literature,
  the result remains `[NOVELTY UNVERIFIED]`.
- The internal rediscovery audit found that
  `docs/drafts/pipeline/0-backlog/ht-composition-transcendence-wall.md` already records
  `psi(Gamma)` as not differentially algebraic of order one, attributed there to a movable-log
  singularity argument.  That backlog synthesis supplies no current Lean theorem surface, but it
  is enough to classify the concrete order-one conclusion as formal hardening rather than new
  scientific knowledge.

## Honest significance verdict

The generic theorem is a reusable static constraint and the concrete corollary is a real nonlinear
order exclusion, but the latter is an internal rediscovery and neither proves hypertranscendence.
The order-two tied-weight identity is an explicit surviving core.  Accordingly this card clears
proof and formalization, but does not clear the mission's dual novelty-significance gate and is not
Fields-Medal-level knowledge.

## Gates

- [x] multiple genuinely different constraint candidates compared
- [x] exact first-order theorem isolated
- [x] paper proof and sharp order-two failure written
- [x] primary-literature parent and novelty audit completed; exact novelty remains unverified
- [x] generic finite-row obstruction formalized in Lean
- [x] `digamma o Gamma` order-one corollary formalized in Lean
- [x] targeted Lean build, formal lint, and axiom audit passed
- [ ] full hypertranscendence of `digamma o Gamma` or a general higher-order replacement proved
