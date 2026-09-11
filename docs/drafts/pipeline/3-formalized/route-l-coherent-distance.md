# Route L: uniform L1 separation from joint complete coherence

Status: formalized; scratch Lean, targeted build, all-theorem axiom audit and repository lint passed.
Date: 2026-09-11.
Module: `GaloisForLFunctions.RHTower.XiGammaSixWoldJordanCoherentDistance`.

## Exact source and theorem

Let `r_(a,n)` be the existing normalized fixed-left Big-Witt row at prime `p`,
`K_n=1/(p*M_n)` its original reciprocal raw-mass budget, and `T` the literal
edge transposition. For every profile `b` and finite prime set `S`,

`sum_i |(r_(a,n)-T(r_(a,n))-R(b,S))(i)| >= (1-2*K_n)/3`.

The sum is over the finite support of the displayed difference, before any
prime marginal contraction. Since `K_n->0`, there is one stage after which
this distance is at least `1/6` for **all** profiles and all finite sets.
Consequently, no moving sequence of single complete coherent packets can
approximate the actual transposed repair in full edge `L1`.

The generic source theorem is stronger: replace `T(r_(a,n))` by any finite
packet with nonnegative real coefficients and zero anchor marginal. The same
lower bound holds. No trace, graph-limit or energy assumption is needed for
this finite quantitative statement.

## Dependency-closed paper proof

For a positive-real target `h`, let
`u=(r_(a,n)-h)-R(b,S)`. Then the one-packet repaired row is `h+u`. Every negative
real coefficient of `h+u` has magnitude at most `|u(i)|`, so its total negative
mass is bounded by `V(u)=sum_i |u(i)|`. Because `m_h(p)=0`, its anchor real
marginal is also at most `V(u)`.

The already proved C13 source bound gives
`1-2*K_n-2*delta(h+u)<=Re(m_(h+u)(p))`. Substituting both bounds proves
`1-2*K_n<=3*V(u)`.

The actual transposed row has nonnegative real coefficients and anchor marginal
zero at every finite stage. This discharges the generic target conditions
internally. The original raw mass diverges, so eventually `K_n<1/4`; hence
`V(u)>=1/6` uniformly in `b,S`. A moving complete approximation with distance
tending to zero contradicts this same eventual lower bound.

## Positive survivor and scope

C12's exact nonmembership is robust in the full edge variation topology.
Despite positive target coefficients, trace one, the same singular graph
limit and vanishing reciprocal energy, this actual finite coherent assembly
stays separated from the entire one-complete-packet class. Thus that class
cannot approximate the assembly by errors of vanishing full edge variation.

This does not exclude weaker ambient or graph approximations, identify the
physical completion topology, or establish source-to-fixed-reader agreement.
The class of single complete packets is not asserted to be a vector space or
to equal the physical domain. No optimality claim is made for these constants.
RH remains unproved.

## Corpus and literature mechanism

The perturbation deep/method search reported partial coverage. It retrieved
`Function.locallyFinsuppWithin.negPart_add`; its source proof was read. The
current proof applies the same elementary negative-part comparison directly
to the literal finite complex edge coefficients, then uses the actual source
retention law. Signed-measure variation identities and unrelated sum methods
do not supply the missing physical comparison.

The broad `gluing` search found the August 2026
[Evangelatos–Haiden phase-gap construction](https://arxiv.org/html/2608.21201v1).
Its phase-sector bound is a useful cancellation-control lead, but a sector
condition alone does not retain this source's prime: the positive transposed
row already has aligned phases and escapes. This audit therefore controls
joint complete coherence in a specified norm instead. The paper is not a
Lean dependency or an assumed arithmetic theorem.

## Verification

- `lake env lean /tmp/route_l_coherent_distance.lean` — passed.
- `lake build GaloisForLFunctions.RHTower.XiGammaSixWoldJordanCoherentDistance` — passed, including the final simplification of one unnecessary `simpa`.
- `lake env lean /tmp/route_l_coherent_distance_axioms.lean` — all seven theorem audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
- `scripts/formal_tools.py lint` — passed.
- Umbrella import wired. No full or umbrella build ran; all owned Lean processes completed.
