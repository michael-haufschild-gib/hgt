# Vertical unitary equivalence of completed prime chains

- **ID:** RIAC-unitary-chain-gauge
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [RIAC](renormalized-intersection-arithmetic-counts.md), completed topology
- **Statement:** The canonical diagonal Hilbert completion retains unitary Dirichlet gauge equivalence along every vertical line, in every exterior degree.

## Candidate and significance

Complete the actual prime exterior chains with orthogonal face basis and
squared face weight `(∏_(p∈S)p)^δ`. Multiplication of each prime vertex by
`p^(it)` should extend to a unitary operator in each degree. The algebraic
identity `d_(s+it) G_(it)=G_(it) d_s` should identify the actual finite boundary
graphs and their closures, without presuming that either closure is an operator.

This would show that closed graph relations and their compatible completed
chain structures are unitarily equivalent along each vertical line. The prescribed
diagonal conductor weights cannot themselves distinguish the
imaginary locations of zeros. Additional relative or equivariant structure
must break or supplement this equivalence.

## Proof obligations

Construct the Hilbert embedding from the actual canonical exterior basis,
prove faithfulness and density, construct the unitary diagonal gauge and its
finite-chain comparison, and prove graph and closure transport. Do not
assume bounded differentials, closed domains or a zero-detection comparison.

## Positive survivor and prior work

The survivor is the explicit unitary classification of all finite boundary
graph closures, retaining the original arithmetic differential and every
exterior degree. ESG already supplies algebraic gauges and cutoff compatibility;
RIAC supplies the exact augmentation domain. The analytic norm and graph
comparison remain to be formalized. No theorem or novelty claim is yet made.

## Construction under verification

Use the actual increasing-face exterior basis `b_k`. Embed a chain by the
finite coefficient vector of `G_(δ/2)a` in the canonical face `ℓ²` basis.
The squared norm is exactly the sum of `|b_k.repr(a)(S)|²` times
`∏_(p∈S) p^δ`. The invertible finite gauge and exterior basis give injectivity;
finite coefficient vectors give density.

The existing `HTGeometry.lpPhaseUnitary` constructs the diagonal unitary
with face multiplier `∏_(p∈S) p^(it)`. The finite-chain comparison follows
on basis faces, hence on all chains. Naturality of the actual Koszul
boundary gives the adjacent-degree intertwining identity. The product of
the two unitary homeomorphisms maps each finite boundary graph onto its
vertical translate; homeomorphisms transport closures exactly. This includes
the augmented empty-face degree and does not require closability.

The complete Lean draft is unchecked. Earlier multiplicative phase
invariance in `BiarithmeticGaugeGeometry.PrimeGaugeTorusAndVacuumIntertwiners`
is prior work; the new target is the exact weighted exterior graph closure.
