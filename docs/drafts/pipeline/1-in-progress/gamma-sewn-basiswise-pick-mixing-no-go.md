# Basiswise quadratic Gamma loss forbids every continuous operator-Pick mixing

- **ID:** `gamma-sewn-basiswise-pick-mixing-no-go`
- **Stage:** 1-in-progress
- **Type:** `[CCM SOURCE NO-GO] [ARBITRARY-DIMENSION OPERATOR-PICK RIGIDITY]`
- **Scientific status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `gamma-sewn-mobius-quadratic-contact-pick-obstruction.md`
- **Exact target:** completed Möbius/Gamma aperture carrier, before Xi divisor or cofinal limit

## Frontier and failed first conjecture

`[CORPUS]` Scalar Gamma sewing has strict interior loss and quadratic lossless-boundary contact, so
its two-aperture Pick determinant is eventually negative. The live escape was non-diagonal mixing
of prime channels.

The first proposed generalization—finite-rank angular derivative controls the active subspace of
an operator-valued Schur function—is `[REDISCOVERED]`: it belongs to operator-valued
Caratheodory--Julia/de Branges--Rovnyak theory. It is also too weak, because a four-unit trace-class
boundary charge may have infinite rank.

The stronger source question is exact and not answered by that slogan:

> Can off-diagonal mixing repair Pick positivity while leaving every prime basis marginal equal to
> the actual quadratic-contact Gamma-sewn multiplier?

## Universal basiswise theorem

Let `H` be an arbitrary real Hilbert space with Hilbert basis `(e_i)_(i in I)`, where `I` may be
infinite. Let `T_x` be bounded operators for `x>0`, converging strongly to the identity on each
basis vector as `x->0+`. Put

```text
D_x(u)=(||u||^2-||T_x u||^2)/(1-exp(-2x)),

K_(x,y)(u,v)
 =( <u,v>-<T_x u,T_y v> )/(1-exp(-(x+y))).              (1)
```

Assume the necessary two-point operator-Pick inequality

```text
K_(x,y)(u,v)^2 <= D_x(u) D_y(v)                          (2)
```

for every `x,y>0` and `u,v in H`. If, for every basis direction,

```text
D_y(e_i) -> 0              as y->0+,                     (3)
```

then

```text
T_x=I for every x>0.                                     (4)
```

No finite-dimensional, finite-rank, compactness, trace-class, or uniform-in-`i` hypothesis occurs.
Condition `(2)` is forced by positivity of the complete operator-valued de Branges--Rovnyak kernel,
so `(4)` applies to every globally operator-Pick-positive family.

## Complete proof

Fix `x>0` and a basis vector `e_i`. Put

```text
h=e_i-T_x^*e_i.                                         (5)
```

Basiswise strong boundary convergence gives `T_y e_i -> e_i`. Hence

```text
K_(x,y)(h,e_i)
 -> ( <h,e_i>-<T_x h,e_i> )/(1-exp(-x))
  = <h,e_i-T_x^*e_i>/(1-exp(-x))
  = ||h||^2/(1-exp(-x)).                                (6)
```

On the other hand, `(2)` and `(3)` give

```text
0 <= K_(x,y)(h,e_i)^2 <= D_x(h)D_y(e_i) -> 0.           (7)
```

Thus the limit in `(6)` is zero. Since `x>0`, its denominator is nonzero, so `h=0`.
Therefore `T_x^*e_i=e_i` for every `i`. Totality of the Hilbert basis gives `T_x^*=I`, hence
`T_x=I`. This proves `(4)`.

The proof is basiswise: charge cannot evade by moving to higher prime indices as `y->0`. Every
fixed direction independently forces the same interior fixed-vector conclusion.

## Actual Gamma-sewn CCM instantiation

For a prime `p`, let

```text
c_p(x)=gammaSewnMobiusValuationContractionMultiplier(x,p).
```

Existing exact source algebra gives

```text
1-c_p(x)=(1-p^(-x))^2 g_p(x),
g_p(0)=3/8.                                               (8)
```

Therefore

```text
(1-c_p(x)^2)/(1-exp(-2x)) -> 0.                          (9)
```

Suppose an arbitrary-dimensional operator family `T_x` converges strongly to the identity on each
prime basis vector, satisfies the operator-Pick inequality `(2)`, and preserves every actual Gamma
marginal

```text
||T_x e_i||=c_(p_i)(x)                                   (10)
```

for `x>0`. Equations `(9)`--`(10)` give `(3)`, so the universal theorem gives `T_x=I`.
But the actual source theorem gives `c_(p_i)(x)<1` for every positive aperture, contradicting
`||T_xe_i||=||e_i||=1`. Hence no such family exists.

This is a no-existence theorem over the entire class, not a conditional construction.

## Scientific consequence and positive survivor

Off-diagonal covariance alone cannot repair scalar Gamma sewing while retaining its primewise
quadratic marginals. Any surviving CCM transport must change at least one load-bearing datum:

```text
create a nonzero first-order marginal boundary defect,
or lose norm-continuity at zero through singular cofinal renormalization,
or leave the common-aperture operator-Pick category,
or modify prime marginals before Gamma scalar trace.                         (11)
```

This sharpens the current survivor from “mix channels non-diagonally” to “non-diagonal mixing must
also alter boundary order or topology.” The explicit channel-resolved Gamma covariance and
higher-subset Fock carriers are not declared dead; their required cofinal weighting must be
singular enough to escape one clause of `(11)`.

## Hostile audit

1. **Rotating/unitary boundary escape:** killed by `T_y e_i->e_i`, not merely convergence of norms;
   operator-norm continuity is not assumed by the strongest theorem.
2. **Charge moving to infinity:** killed basiswise; no uniform convergence over `i` is used.
3. **Off-diagonal covariance:** already included because `T_x` is arbitrary.
4. **Infinite rank:** already included because `I` and `H` are arbitrary.
5. **Circular RH input:** absent; only exact Gamma multiplier laws and Pick positivity are used.
6. **Known parent collision:** abstract mechanism is operator-valued Caratheodory--Julia. Candidate
   novelty is exact infinite-prime Gamma-marginal impossibility and forced escape classification,
   not the parent principle.

## Gates

- [x] exact CCM frontier and failed scalar route audited
- [x] operator-valued parent literature audited
- [x] arbitrary-dimensional paper proof closed
- [x] actual Gamma marginal instantiation closed on paper
- [x] universal theorem formalized in `HTGeometry/BasiswiseBoundaryPickRigidity.lean`
- [x] exact Gamma no-existence theorem formalized in
      `RHTower/GammaSewnBasiswisePickMixingNoGo.lean`
- [x] targeted module build and ordinary-axioms audit
- [ ] repository formal lint: global lint reached unrelated unowned
      `RHTower.FiniteWindowSeamSincUniversalityLaw` umbrella-reachability failure; new modules are
      umbrella-wired and contain no forbidden declarations
- [x] update permanent CCM frontier/no-repeat ledgers

## No-repeat rule

Do not propose off-diagonal mixing that preserves all scalar Gamma marginals and converges strongly
on every prime basis vector at zero in a common-aperture Pick space. Operator Pick positivity
itself forces that family to be the identity, contradicting strict interior Gamma loss.

## Lean certificate (2026-07-22)

Formal declarations:

```text
HTGeometry.continuousLinearMap_eq_id_of_basiswise_boundaryPick
RHTower.tendsto_gammaSewnMobius_commonAperturePickDiagonal_nhdsGT_zero
RHTower.not_exists_gammaSewnMobius_basisMarginal_commonAperturePickFamily
RHTower.not_exists_continuous_gammaSewnMobius_basisMarginal_commonAperturePickFamily
```

The first no-existence theorem assumes only basiswise strong convergence; the second derives that
interface from operator-norm continuity and `T_0=I`. Targeted direct checks and
`lake build GaloisForLFunctions.RHTower.GammaSewnBasiswisePickMixingNoGo` pass. Axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.
