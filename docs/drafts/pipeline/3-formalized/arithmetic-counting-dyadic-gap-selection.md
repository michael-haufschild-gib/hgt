# One dyadic probe selects the untwisted finite-prime source

- **ID:** ACP-DYADIC-GAP-SELECTION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Statement:** Within finite prime flips, the maximal original gap and the untwisted dyadic-response gap jointly select the empty flip set.

## Exact proposed endpoint

Write g0=2 log 2, delta_F for the attained greatest gap, and omega_F for
finite prime parity. Put delta_2=delta_{2}. For every finite set F of primes,

`F=empty iff HasHyperplaneGap(omega_F,g0) and
 HasHyperplaneGap(omega_{2}*omega_F,delta_2)`.

These are two lower bounds, not assumed equalities of complete spectral
measures. The probe is fixed at prime two, independent of the unknown F.

## Dependency-complete proof

The small-prime obstruction and gap attainment give 0<delta_2<g0.
Multiplying omega_F by omega_{2} toggles membership of two in F.
If 2 belongs to F, inclusion gives delta_F<=delta_2<g0, contradicting the
first bound. Otherwise the toggle is insert(2,F). If F is nonempty,
{2} is a proper subset of insert(2,F); inclusion places its gap below g0,
and strict inclusion then gives delta_insert<delta_2, contradicting the
second bound. For empty F the untwisted gap is g0 and the dyadic gap is
attained at delta_2.

All analytic inputs are closed in the exact finite-prime gap and interior-root
leaves. The toggle identity follows from the finite product and the square-one
identity for a single prime sign. No infinite-prime transfer is used.

Precisely, when 2 is absent, the product for insert(2,F) is omega_2 omega_F.
When 2 is present, write F=insert(2,erase(2,F)); multiplication by omega_2
cancels its square, which is one at every integer, including zero.
The strict inclusion step uses the proved equivalence
`delta_G<delta_H iff delta_G<g0` for H properly contained in G.
With H={2} and G=insert(2,F), ordinary inclusion first gives
delta_G<=delta_2<g0, discharging its right-hand side.
If the original maximal gap holds and 2 belongs to F, attainment and
inclusion instead give g0<=delta_F<=delta_2<g0. These two contradictions
cover every nonempty F. In the empty case the density lower bound is g0
and the universal upper bound is g0; dyadic attainment supplies the second
required lower bound. No unproved sign or transfer premise remains.

## Source audit and scope

Corpus search for a dyadic probe selecting finite multiplicative twists found
no existing selector. It found the exact inclusion law and finite sign-gauge
construction used above. This is a new consequence of those local theorems;
no claim of exhaustive literature novelty is made. It adds a concrete source
invariant beyond the nonselective maximal gap.

The claim only concerns the finite-prime flip family. It neither constructs
complete Weil positivity nor selects among arbitrary multiplicative weights.
A positive uniform tolerance for the second reading is not asserted.

## Gates

- [x] Well-posed, arithmetic and non-circular endpoint.
- [x] Dependency-complete paper proof.
- [x] Lean formalization, transitive axiom audit and canonical check.

## Formalization

`OneDyadicProbeSelectsTheFinitePrimeSource.lean` proves
`finiteFlip_dyadicPrimeToggle`, `dyadicFlipGreatestGap_lt_ceiling`, and
`finiteFlip_two_gap_selection`. Scratch 62873 and canonical installed-source
check 1007 exited zero. All three transitive audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. The adjacent audit preserves exact
commands, source hash and actual output. The umbrella imports this leaf.

The lack of any fixed positive tolerance, with an explicit order-1/p
response bound, is formalized in
`arithmetic-counting-gap-stability-and-probe-precision.md`.

External background checked against the primary abstracts: generalized
Liouville signs are studied in [Borwein–Choi–Coons](https://arxiv.org/abs/0809.1691),
and multiplicative Ramanujan expansions and finite Euler factorizations in
[Coppola–Ghidelli](https://arxiv.org/abs/2009.14121). Those constructions are
background, not a claimed novelty here. The scoped contribution concerns
actual constrained prime-matrix gaps and their response to prime toggles.
