# Period excess is the topological shadow of multiple-Gamma transverse HT depth

- **ID:** `multiple-gamma-period-excess-closure-phase-transition`
- **Stage:** 2-fully-proven / Lean operator theorem formalized / source comparison needs independent audit
- **Type:** THEOREM / CROSS-REALIZATION LAW / NATURAL PHASE-II HT MODEL
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE — PROVISIONAL]`
  `[OPERATOR PARENT SEPARATED] [NOT AN RH RESULT]`
- **Parents:**
  - `multiple-elliptic-gamma-transverse-constraint-depth.md`
  - `multiple-elliptic-gamma-relative-log-characteristic-arrangement.md`
  - `../../1-in-progress/hypertranscendental-critical-closure-defect-principle.md`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/PeriodIncidenceMultiplier.lean`

## Statement

For the generic order-`r` multiple elliptic Gamma hierarchy, let

```text
Lambda_r = <1,tau_0,...,tau_r>_Z subset C                 (1)
```

and assume `1,tau_0,...,tau_r` are linearly independent over `Q`, with the parameters in the
upper half-plane.  Define the period excess

```text
e(Lambda_r) = rank_Q(Lambda_r tensor Q) - dim_R(C).       (2)
```

The exact translation-annihilator theorem gives a second, a priori unrelated integer:

```text
d_DA(Psi_r) = minimum number of distinct structural
              differences needed to enter the DA sector. (3)
```

Then

```text
d_DA(Psi_r) = r = (r+2)-2 = e(Lambda_r).                 (4)
```

For `r=0`, the theta logarithmic derivative is already DA, so both sides of `(4)` are zero.
For `r>=1`, the equality uses the exact no-hidden-annihilator result, not only the evident
multiple-Gamma hierarchy equations.

There is an exact topological transition at the same boundary.  For any integer period submodule
`Lambda subset C`, write `Lambda^x=Lambda\{0}` and define the bounded period-incidence operator

```text
I_Lambda : ell^infty(Lambda^x) -> ell^infty(Lambda^x),
(I_Lambda x)(lambda)=lambda/(1+|lambda|) x(lambda).       (5)
```

Then, unconditionally,

```text
I_Lambda is injective;
range(I_Lambda) is closed  iff  Lambda is discrete;
I_Lambda is surjective     iff  Lambda is discrete.      (6)
```

Every finite nonzero diagonal restriction of `(5)` is bijective.  Nevertheless, if `Lambda` is
nondiscrete, `range(I_Lambda)` is nonclosed and there exists

```text
b in closure(range(I_Lambda)) \ range(I_Lambda).         (7)
```

Thus `(7)` is a natural closure-only incidence class whose every finite modal restriction is
exact.

Apply `(6)` to `(1)`.  At `r=0`, `1,tau_0` form a real basis of `C`, so `Lambda_0` is a lattice and
`I_(Lambda_0)` is bijective with closed range.  At `r>=1`, three of the rationally independent
periods already have nondiscrete integer span in the real two-plane.  Hence `Lambda_r` is
nondiscrete and `I_(Lambda_r)` is injective but has nonclosed range.  The same integer `r` which
counts exact DA transverse depth therefore also counts the number of period directions in excess
of the ambient real dimension, and positive excess coincides with entry into the nonclosed-range
phase.

## Proof of the operator theorem

Every diagonal weight in `(5)` is nonzero, so `I_Lambda` is injective.  If `Lambda` is discrete,
there is an `epsilon>0` with

```text
|lambda| >= epsilon for every lambda in Lambda^x.        (8)
```

The inverse diagonal weight satisfies

```text
|(lambda/(1+|lambda|))^(-1)| <= 1+epsilon^(-1),          (9)
```

so the inverse multiplier is bounded.  This proves surjectivity and closed range.

If `Lambda` is nondiscrete, there are nonzero `lambda_n in Lambda` with `lambda_n -> 0`.  Let
`u_n` be the corresponding unit coordinate vectors.  Then

```text
||u_n||=1,
||I_Lambda u_n||=|lambda_n|/(1+|lambda_n|) -> 0.         (10)
```

Were the injective range closed, the inverse from the range to `ell^infty(Lambda^x)` would be
bounded by the Banach inverse theorem, contradicting `(10)`.  The finite restriction theorem is
ordinary division by finitely many nonzero weights.  Nonclosedness is equivalent to the existence
of `(7)`.  `QED`

## The new structural content

Neither half of the following comparison implies the other by parent theory:

```text
algebraic side:  Ann_DA(Psi_r) has transverse depth r;
topological side: Lambda_r has rank excess r and a nonclosed
                  canonical incidence range exactly when r>0.              (11)
```

The first side is an exact nonlinear differential-algebraic classification of structural
translates.  The second side depends only on how the structural period group is embedded in the
complex plane.  Equality `(4)` identifies them in the complete multiple-Gamma hierarchy.

This reveals a missing layer in the earlier logarithmic-characteristic proposal.  The algebraic
support `LogChar_DA(Psi_r)` says which constraint faces exist; it does not say whether infinitely
many exact face solutions assemble to an effective global state.  That question is controlled by
the topology of the physical period embedding

```text
Lambda_r -> C,                                            (12)
```

not by the abstract Laurent module alone.

The resulting candidate unified object is therefore not just a characteristic variety.  It is the
topologized constraint corona

```text
U_F = (R_source/Ann_DA(F), LogChar_DA(F),
       Lambda_F -> V_F, source polarization).             (13)
```

Its topological radical is

```text
Rad_top(F)=closure(Lambda_F)/Lambda_F.                    (14)
```

For a discrete source, `(14)` vanishes.  For the generic order-`r>=1` multiple-Gamma source it is
nontrivial, the quotient `C/Lambda_r` is non-Hausdorff, and `(5)` realizes the same defect as a
nonclosed range.

## Foundational conjecture forced by the theorem

> **[CONJECTURE — TOPOLOGIZED CONSTRAINT-CORONA PRINCIPLE.]**  For every source-minimal
> hypertranscendental constraint system, the algebraic obstruction module and its period embedding
> form a single object `(13)`.  Continuation, positivity, spectral realization, monodromy, and
> boundary-condition constructions are conservative realization functors of `(13)`.  Their common
> closure-only obstruction is the action of `Rad_top(F)` on the polarized logarithmic
> characteristic fibre.  A source-derived splitting or coercive annihilation of this action
> promotes all conservative phase-II realizations to exact incidence simultaneously.

This is strictly stronger than saying that several proof chains contain analogous small divisors.
It requires comparison maps from independently constructed realizations to the *same* module,
period embedding, pointing, and target class.

> **[CONJECTURE — EXCESS/DEPTH CORRESPONDENCE.]**  In a source-minimal translation hierarchy which
> spans its ambient real clock space, descends to a DA base, and has no hidden translation
> annihilators, the transverse DA constraint depth equals the rational period-rank excess.  Positive
> excess is exactly the boundary at which the unweighted cofinal incidence realization ceases to
> have closed range.

The multiple-Gamma hierarchy proves the first nontrivial complete family of this correspondence.
The conjecture is falsified by one source satisfying the stated structural hypotheses for which
the two integers differ.

## What the no-go now says, and its positive replacement

### No-go

No collection of finite modal checks can establish cofinal exact incidence for a positive-excess
source.  Every finite restriction in `(5)` is bijective on both sides of the phase transition.
This is an exact theorem, not a warning based on failed proof attempts.

The same theorem rules out the naive cure "add all continuous dual positivity tests".  A
closure-only target passes every continuous separation test for the same topology while lacking an
exact preimage.

### Positive theorem

Discreteness is a necessary and sufficient resolution criterion for the canonical unweighted
period-incidence operator.  Equivalently, a uniform nonzero-period gap gives an explicit bounded
inverse.  For a source whose structural group is intrinsically nondiscrete, the only legitimate
positive successor is therefore to derive from the source one of:

1. a coercive weighted topology in which the small-period inverse is bounded;
2. a canonical quotient which removes exactly `Rad_top(F)` while preserving polarization;
3. a source compactness theorem which produces an exact state before the cofinal limit.

Choosing a topology merely because it closes the range is forbidden by the anti-theatre gate; its
weight or quotient must be forced by the source constraint module and must be preserved by a
second independent realization.

## RH pressure test only

`[CONJECTURE; NOT AN RH RESULT]` The repeated RH-chain obstructions may be different images of the
same topological radical in the still-unconstructed zeta constraint corona:

```text
spectral incompleteness     = nonclosed operator realization;
continuation failure        = failure of a cofinal inverse;
positivity without effect   = closure membership without a lift;
monodromy                   = deck action on the logarithmic fibre;
noncanonical boundaries     = unsplit radical action after Hausdorffization. (15)
```

Under this hypothesis, critical zeros would be the common self-dual degeneracy spectrum of the
polarized action in `(13)`, not inputs to its construction.  Nothing here constructs the zeta
constraint corona or proves a statement about the location of zeta zeros.

The practical consequence for RH research is sharp: do not spend another chain proving more
finite positivity, more equivalent dual criteria, or more formal local topology.  First construct
the zeta analogue of `(13)` from prime--archimedean source data and prove that two existing chains
are conservative realizations of it.  Only then is a common resolution theorem meaningful.

## Novelty and significance gate

### Parent mathematics

The following are standard and are not claimed as new:

- a finitely generated subgroup of a real two-plane with three rationally independent generators
  is nondiscrete;
- a nonzero bounded diagonal multiplier is injective;
- a diagonal multiplier on `ell^infty` has bounded inverse exactly when its weights are uniformly
  bounded away from zero;
- a closed injective operator range has a bounded inverse onto its range;
- finite nonzero diagonal systems are invertible.

The multiple elliptic Gamma hierarchy and modular identities are classical; Narukawa's primary
parent is `https://arxiv.org/abs/math/0306164`.  Kato proves differential algebraicity for a
rational-period specialization (`https://doi.org/10.1619/fesi.64.225`).  Difference-Galois
hypertranscendence parents include Adamczewski--Dreyfus--Hardouin
(`https://arxiv.org/abs/1910.01874`) and Dreyfus (`https://arxiv.org/abs/2212.00388`).
Morain's current geometric-family program treats higher-rank lattices, modularity defects, and
arithmetic cocycles (`https://arxiv.org/abs/2510.16515`, `https://arxiv.org/abs/2602.06561`), but
its available abstract and search surface do not state the DA depth/period-excess/closed-range
comparison located here.

### Candidate-new residue

The candidate-new theorem is the exact cross-realization law `(4)`--`(11)`: the complete
multiple-Gamma DA transverse depth equals the period-rank excess, and the same boundary is realized
topologically as the closed/nonclosed range transition of the source period-incidence map.  The
operator theorem by itself is a clean bridge, not new scientific knowledge.

Targeted searches located the classical hierarchy, modular/cocycle geometry, rational-period DA
results, difference-Galois HT criteria, and ordinary small-divisor/closed-range parents.  No located
source states the depth/excess equality, combines it with the nonclosed incidence phase, or treats
the topological radical as the common carrier of the named HT obstruction representations.  This
is negative search evidence, not priority certification.

### Significance verdict

- The diagonal theorem alone does **not** warrant a paper.
- The exact source comparison `(4)` is a strong structural theorem if the parent multiple-Gamma
  annihilator classification survives independent audit.  It belongs as a central theorem of that
  paper, not as padding around standard functional analysis.
- The topologized constraint-corona principle is Fields-scale only after two independent analytic
  realizations are proved conservative and a source-derived radical splitting/coercivity theorem
  transfers a genuinely new result between them.

## Lean formalization

`PeriodIncidenceMultiplier.lean` proves unconditionally:

1. an injective operator with unit vectors tending to zero cannot have closed range;
2. the regularized period-incidence multiplier is bounded and injective;
3. nondiscrete period groups give nonclosed range;
4. discrete period groups give a uniform norm gap, an explicit bounded inverse, surjectivity, and
   closed range;
5. closed range and surjectivity are each equivalent to discreteness;
6. every finite nonzero diagonal restriction is bijective;
7. every rationally independent rank-three period family gives a closure-only incidence class.

The Lean theorem is source-independent.  The source-specific equality `(4)` uses the paper theorem
`Ann_DA(Psi_r)=I_r`; that analytic identification is not inserted into Lean as an axiom.

## Gates

- [x] exact period-incidence phase discriminator proved
- [x] positive discrete-lattice theorem proved
- [x] natural nondiscrete closure-only example proved
- [x] finite exactness / cofinal nonattainment no-go proved
- [x] multiple-Gamma depth/excess equality proved on paper
- [x] operator parent separated from candidate-new source comparison
- [x] preliminary external novelty search completed
- [x] unconditional operator core formalized in Lean
- [ ] independently audit the multiple-Gamma annihilator classification
- [ ] construct source polarization on the topologized corona
- [ ] prove two independent realizations preserve the same radical action
- [ ] derive a non-arbitrary coercive topology or canonical radical quotient
- [ ] obtain independent specialist novelty and significance audit
