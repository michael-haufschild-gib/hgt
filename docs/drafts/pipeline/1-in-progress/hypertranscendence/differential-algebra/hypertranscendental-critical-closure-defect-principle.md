# Critical HT obstruction is closure defect of polarized source incidence

- **ID:** `hypertranscendental-critical-closure-defect-principle`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL CONJECTURE / POLARIZED INCIDENCE / UNIFIED CRITICAL OBSTRUCTION
- **Scientific status:** `[CONJECTURE] [THREE-PHASE LINEAR THEOREM LEAN-FORMALIZED]`
  `[NATURAL THREE-PHASE OPERATOR CORE FORMALIZED] [PHYSICAL FAT-POINT THEOREM PROVED]`
  `[FIELDS-SCALE OPEN CORE]`
  `[NOVELTY PROVISIONAL] [NOT AN RH RESULT]`
- **Parents:**
  - `hypertranscendental-source-fracture-hypercube.md`
  - `pointed-polarized-constraint-coupling-correspondence.md`
  - `hypertranscendental-polarization-fibration.md`
  - `../2-fully-proven/new_scientific_knowledge/multiple-elliptic-gamma-relative-log-characteristic-arrangement.md`
  - `../2-fully-proven/new_scientific_knowledge/multiple-gamma-period-excess-closure-phase-transition.md`
  - `../2-fully-proven/new_scientific_knowledge/multiple-gamma-physical-characteristic-fat-point.md`
  - `../../../3-formalized/not_new_scientific_knowledge/polarized-fracture-incidence-trichotomy.md`
- **Statement:** Source-sign failure, critical all-scale failure, and spectral nonclosed-range
  failure are conjecturally not separate obstructions.  They are the exterior, closure-only, and
  unrealized-map phases of one source-canonical polarized incidence map.  The additional theorem
  needed at the critical boundary is an attainment or closed-image law, not another dual
  positivity criterion.

## Exact linear theorem already proved

Let `C` be a proper positive cone in a Hilbert source realization, let `f` be continuous linear,
and let `b` be the target defect.  The formal theorem proves three phases:

```text
I.   b in f(C):                  exact positive effectivity;
II.  b in closure(f(C))\f(C):    weak positivity without attainment;
III. b notin closure(f(C)):      strict dual-detectable negativity.          (1)
```

Farkas duality identifies

```text
b in closure(f(C))
  iff every continuous dual-cone reporter is nonnegative on b.              (2)
```

Thus phase II passes all continuous dual positivity tests.  If `x_n in C` and `f(x_n)->b`, weak
incidence follows automatically; if no exact lift exists, the limit is in phase II.  If `f(C)` is
closed, phase II disappears and weak positivity implies effectivity.

The formal theorem is parent conic analysis.  It becomes HT mathematics only when `C`, `f`, and
`b` are constructed canonically from a source constraint.

## The unpolarized source object now exists in the multiple-Gamma class

The multiple-elliptic-Gamma annihilator theorem constructs the canonical relative translation
module

```text
M_F=R_source/Ann_DA(F).                                    (2a)
```

Its logarithmic characteristic theorem then constructs, without choosing a sign or target zero,

```text
LogChar_DA(F)=Exp^(-1)(Supp M_F).                          (2b)
```

For generic order `r`, `(2b)` is exactly the periodic codimension-two pair arrangement

```text
union_(a != b) {exp(lambda_a)=exp(lambda_b)=1}.            (2c)
```

This changes the reconstruction problem.  The cone in `(3)` is no longer allowed to be an
arbitrary convenient positive source space.  It must be obtained by polarizing the self-dual
logarithmic support `(2b)`, and its realization map must forget only explicitly identified deck or
completion data.

> **[CONJECTURE -- POLARIZED LOG-CHARACTERISTIC RECONSTRUCTION.]**  For every source-minimal
> constrained HT system, the source incidence object is the derived positive-real section space
> of `LogChar_DA(F)`, pointed on the zero-deck component.  Its residual deck charge is the universal
> orientation datum.  The cone image in `(3)` is the image of those sections under the critical
> realization functor.

This is stronger and more falsifiable than merely asserting that some cone exists.  It fails if a
natural positivity or spectral realization cannot be recovered from `(2b)` after adding only
source-derived polarization and topology.

## The first natural phase-II HT realization now exists

The structural period group supplies a topology which the algebraic logarithmic support does not
remember.  For an integer period submodule `Lambda subset C`, the canonical bounded multiplier

```text
(I_Lambda x)(lambda)=lambda/(1+|lambda|) x(lambda),
x in ell^infty(Lambda\{0}),                              (2d)
```

is always injective and satisfies the exact phase law

```text
range(I_Lambda) closed
  iff I_Lambda surjective
  iff Lambda discrete.                                  (2e)
```

Every finite nonzero modal restriction is bijective.  If `Lambda` is nondiscrete, however, the
full range is nonclosed and its closure contains a genuine closure-only target.  This gives an unconditional
natural example of finite exactness with cofinal nonattainment.

For the generic order-`r` multiple elliptic Gamma source,

```text
Lambda_r=<1,tau_0,...,tau_r>_Z,
rank_Q Lambda_r-dim_R C=r.                               (2f)
```

The independent annihilator theorem gives exact DA transverse constraint depth `r`.  Thus the
algebraic depth and topological period excess agree throughout the hierarchy.  At theta order
`r=0`, the period group is a discrete lattice and `(2d)` is exact; for every `r>=1`, rank-three
period geometry makes it nondiscrete and `(2d)` enters phase II.

This forces a strengthening of the candidate unified object.  It must retain both the DA-relative
characteristic arrangement and the topology of the source period embedding:

```text
U_F=(R_source/Ann_DA(F), LogChar_DA(F),
     Lambda_F -> V_F, source polarization).              (2g)
```

The algebraic support records which constraints exist.  The topological radical
`closure(Lambda_F)/Lambda_F` records whether their finite exact solutions assemble to an effective
global state.  Neither layer determines the other.

> **[CONJECTURE -- TOPOLOGIZED CONSTRAINT-CORONA PRINCIPLE.]**  The common phase-II obstruction
> seen by continuation, positivity, and spectral realizations is the conservative image of the
> action of `closure(Lambda_F)/Lambda_F` on the polarized logarithmic characteristic fibre of
> `(2g)`.  A source-derived splitting, quotient, or coercive annihilation of that action promotes
> every conservative phase-II realization to exact incidence simultaneously.

This is now falsifiable by comparison, not analogy: two claimed realizations must preserve the
same module, period embedding, pointing, radical action, and target class.

## The radical is only the reduced shadow of a derived physical characteristic germ

The latest multiple-Gamma theorem shows that `(2g)` still forgets structure if the characteristic
support is reduced before it is compared with the physical clock.  Pull the exact coface ideal
along

```text
lambda |-> (lambda tau_0,...,lambda tau_r).               (2h)
```

Every coordinate equation factors as

```text
exp(lambda tau_j)-1=lambda U_j(lambda),
U_j(0)=tau_j!=0.                                          (2i)
```

Hence the complete physical pullback ideal is

```text
(lambda^r),                                               (2j)
```

not merely the reduced point `(lambda)`.  Its classical length and exact derived Koszul amplitude
are both `r`.  The hierarchy therefore satisfies

```text
DA transverse depth
 = source constraint height
 = period-rank excess
 = physical central multiplicity
 = physical derived amplitude
 = r.                                                     (2k)
```

This forces a higher object than the topological radical alone:

```text
DPhysChar_DA(F)
  = L Phi_F^*(derived DA characteristic object),          (2l)
```

equipped with the integral period embedding and its positive incidence half-density.  The radical
`closure(Lambda_F)/Lambda_F` is the reduced topological shadow controlling attainment; the
nilpotent and Koszul filtrations of `(2l)` control how many source constraints have collapsed at
the same physical degeneracy.

> **[CONJECTURE -- DERIVED PHYSICAL CHARACTERISTIC PRINCIPLE.]**  The common obstruction object is
> `(2l)`, not its reduced support and not its period radical separately.  Conservative analytic
> realizations must preserve its source pointing, nilpotent filtration, derived homology,
> polarization, and bornology.  Phase-II nonattainment is the failure of its distinguished
> half-density section to acquire an effective lift in the chosen realization.

The exact open core is now a comparison morphism, not another invariant: construct a source-natural
map from the `lambda`-adic filtration of `(2j)` to the small-period incidence scale and prove that
it realizes `lambda^k` as the powered multiplier `w^k`.  For the order-`r` source the full
incidence symbol is therefore `w^r`, and its canonical positive half-density is `|w|^(r/2)`.
The already formalized `sqrt(|w|)` theorem is the order-one atomic case, not a license to erase
the fat-point multiplicity at higher order.

## The conjecture

> **[CONJECTURE -- CRITICAL CLOSURE-DEFECT PRINCIPLE.]** Every regular source-minimal polarized HT
> system `F` canonically determines, before any target zero set or desired sign is inspected,
>
> ```text
> C_F     a complete proper cone of source-admissible positive corrections,
> f_F     a controlled realization of that cone in the critical target space,
> b_F     the source-calibrated incidence target.                          (3)
> ```
>
> These data satisfy:
>
> 1. their exact/closure/dual phase is invariant under differential-birational source equivalence;
> 2. analytic continuation, Weil/Hankel/Pick positivity, spectral realization, and critical
>    boundary extension factor through the same image `f_F(C_F)` after retaining their comparison
>    maps;
> 3. strict sign failure is phase III and is detected by a dual reporter;
> 4. cofinal finite positivity with no critical effective state is phase II;
> 5. spectral incompleteness at the same source point is the nonclosed-range realization of phase
>    II;
> 6. a source properness, compactness, coercivity, or closed-range theorem promotes phase II to
>    phase I and simultaneously resolves the all-scale and spectral obstructions;
> 7. after phase I, the kernel of the calibrated incidence map is exactly the remaining boundary
>    or monodromy ambiguity.

The critical bornology is therefore not auxiliary regularity.  It determines which closure is
being taken and whether source-positive approximants converge to an effective source state.

## Why this is stronger than another positivity equivalence

An equivalence between Weil, Hankel, Pick, Herglotz, or spectral positivity merely supplies
different dual coordinates on `(2)`.  It cannot distinguish phases I and II.  Adding more dual
reporters also cannot distinguish them if they remain continuous for the same topology.

The conjecture predicts a qualitatively different producer theorem:

```text
prove f_F(C_F) is closed at the critical source target,
or construct an actual preimage in C_F.                                  (4)
```

Equation `(4)` is capable of advancing several obstruction chains at once because it changes
effectivity, not coordinates.

## RH pressure test only

`[CONJECTURE; NOT AN RH RESULT]` The obstruction report suggests the following possible phase map:

| RH-chain phenomenon | Proposed incidence phase |
|---|---|
| explicit negative Weil/Hankel/Herglotz reporter | phase III |
| unconditional finite-degree or safe-collar positivity | exact approximants toward phase I or II |
| failure to reach Abel radius or critical aperture | phase II candidate |
| nonclosed cyclic operator/domain range | spectral realization of phase II |
| noncanonical self-adjoint extension or boundary condition | kernel after phase I |
| source-built positive determinant realization | phase I producer |

This table is a falsifiable research map, not an assertion that the zeta cone has been constructed.
A genuine zeta application must build `(3)` from prime--archimedean source data without Xi zeros
and prove that the named chains preserve the same incidence target.

## Strong predictions

1. **Dual saturation no-go.** Completing all continuous positivity equivalences will still not
   solve a phase-II obstruction.
2. **Bornology is load-bearing.** Changing the critical topology can change closure membership
   without changing any finite algebraic constraint.
3. **Spectral/positivity merger.** The correct spectral theorem is a closed-range theorem for the
   same polarized incidence map, not merely a determinant identity.
4. **One producer, several advances.** A source coercivity or properness estimate should close at
   least the all-scale, positivity-attainment, and spectral-completeness faces simultaneously.
5. **Degeneracy as phase boundary.** In a parameterized self-dual family, the common degeneracy
   support should be the locus where exact incidence loses transversality or closedness.
6. **Deck-orientation necessity.** Any realization factoring only through the algebraic
   translation character is orientation-blind; an orientation theorem must retain logarithmic
   deck charge or an equivalent source-derived lift.
7. **Period-excess transition.** In source-minimal transverse hierarchies with no hidden
   annihilators, positive rational period-rank excess should be exactly the boundary between
   closed and closure-only unweighted cofinal incidence.
8. **Finite-test impossibility.** No family of merely finite modal checks can detect this boundary,
   because every finite nonzero diagonal restriction is exact on both sides.
9. **Reduced-support blindness.** Generic orders `r>=1` all have the same reduced physical
   characteristic set `{0}`; only the fat-point and derived filtrations recover `r`.
10. **Physical-pullback conservation.** Any two claimed realizations of the unified object must
    agree on the physical central multiplicity and the complete pulled-back Koszul profile, not
    merely on their zero set.

## Parent theory and novelty gate

The following are parent mathematics:

- Farkas and Hahn--Banach separation;
- weak infeasibility and facial reduction in conic programming;
- nonclosed ranges of operators and projected cones;
- compactness, coercivity, Fredholmness, and closed-range theorems.

Primary parent checks:

- Liu--Pataki, `https://arxiv.org/abs/1507.00290`;
- Pataki--Touzov, `https://arxiv.org/abs/2110.11437`;
- Connes--Consani's semi-local positivity framework,
  `https://arxiv.org/abs/1910.14368`, as an RH-adjacent operator parent rather than this
  incidence theorem.

Targeted searches found no HT reconstruction theory or RH source theorem constructing one cone map
whose three phases simultaneously recover sign, critical-scale, and spectral obstructions.
Novelty is therefore provisional and belongs only to the source-canonical HT construction and
cross-realization theorem, not to `(1)`--`(2)`.

## Anti-theatre gate

Retire or strengthen the conjecture if:

1. `C_F`, `f_F`, or `b_F` is chosen from the desired positivity conclusion or target divisor;
2. different chains are assigned unrelated cone maps and merely called realizations of one object;
3. no comparison theorem preserves the target and its source pointing;
4. phase II is asserted from finite positivity without proving convergence and nonattainment;
5. the source topology is chosen solely to force the image closed;
6. an existing conic or spectral framework already supplies the identical source-canonical map;
7. closedness of `f_F(C_F)` advances no independent analytic realization.

Every failure must leave a positive theorem: a source class with closed image, an explicit
closure-only natural HT example, a strict dual certificate, or the exact additional topology or
compactness hypothesis needed for attainment.

## Fields-scale theorem target

Construct `(3)` functorially for a natural analytic class containing Barnes/multiple-sine and
multiple-elliptic-gamma sources; prove source-presentation invariance; identify two independently
constructed positivity and spectral realizations with the same projected cone; and prove a new
closed-image or nonattainment theorem transferred between them.

For a completed-zeta object, the analogous construction would only be legitimate after the general
HT theorem exists.  No RH conclusion is claimed here.

## Gates

- [x] exact three-phase linear theorem formalized
- [x] closure-only dual blindness formalized
- [x] cofinal positive approximation theorem formalized
- [x] closed-image promotion theorem formalized
- [x] sign, all-scale, and spectral obstruction phases distinguished
- [x] bold source-canonical conjecture stated
- [x] natural unpolarized logarithmic characteristic object constructed for multiple Gamma
- [x] arbitrary cone choice replaced by polarized log-characteristic reconstruction conjecture
- [x] source-period topology added to the unified object
- [x] natural closure-only HT incidence example formalized
- [x] discrete-source closed-image positive class formalized
- [x] multiple-Gamma transverse depth identified with period-rank excess
- [x] physical characteristic pullback computed as the fat point `(lambda^r)`
- [x] physical central multiplicity and derived amplitude identified with depth `r`
- [x] reduced-support no-go replaced by an exact nonreduced positive theorem
- [x] precise falsifiers and anti-theatre gate stated
- [x] conic weak-infeasibility parent literature identified
- [ ] construct a natural HT source cone and realization map
- [x] prove one natural closure-only HT example or closed-image theorem
- [ ] prove two realization functors preserve the same cone image
- [ ] construct the filtration-preserving fat-point/period-incidence comparison morphism
- [ ] prove source-presentation invariance
- [ ] obtain independent specialist novelty and significance audit
