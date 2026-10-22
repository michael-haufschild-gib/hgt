# Literal deletion mixed-area rank candidate

- **ID:** deletion-mixed-area-rank
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; computationally disfavored, not mathematically falsified
- **Statement:** Test whether a nontrivial zeta zero forces the antisymmetric ordered area of four coprime deletion channels to be decomposable.

## Proposed proof chain and missing links

For an integer label p > 1, use the literal chronological jumps
`x_p(n;s) = (1 - p * [p divides n]) n^(-s)`, for n >= 1. For four
pairwise coprime labels define

`A_pq(N;s) = (1/2) sum_{m<n<=N} (x_p(m;s)x_q(n;s) - x_q(m;s)x_p(n;s))`.

There is no complex conjugation in this definition. The candidate chain is:

1. Construct the infinite joint areas in Re(s) > 0.
2. Prove that a zeta zero forces `A_12 A_34 - A_13 A_24 + A_14 A_23 = 0`.
3. Independently prove that the same Pfaffian cannot vanish at a zero with
   Re(s) > 1/2, without importing an excluded RH-equivalent core.
4. Exclude strict-right zeros and close the remaining RH bridge.

Only the source convergence has existing corpus support. Both decisive arrows
are unproved; no qualifying novel RH architecture or proof is claimed. The
motivation is a possible extra constraint from simultaneous arithmetic deletion
endpoints, not a general theorem about closed paths. Generic closed paths need
not have decomposable area.

## Evidence and falsification gate

`RHTower.DeletionChronologicalLimit.crossPrefix_converges_of_coprime`
proves convergence for coprime channels with both exponent real parts positive.
That implementation conjugates its second jump; substituting the conjugate
exponent yields the holomorphic cross sum above. Check actual kernel definitions
when formalizing this translation; it has not been exported as a new theorem.

Corpus searches `deletion area rank`, `chronological Pfaffian`, and `area
decomposable` were paired with `rg` of the source statements and proof bodies.
The last search found `GaloisForLFunctions.Nieto1810.realOrientation_plucker`, a
determinant identity for real orientations of endpoint period vectors. Its
object is different from the time-ordered area here. Search misses do not
establish novelty. A broader primary-source audit found the relevant existing
general representation; see below. No exact prior zero-rank law was established
by this search, and no absence-from-literature claim follows.

The question whether literal areas at actual zeta zeros satisfy this identity
was not resolved by reasoning. Test approximate zeros on the user-specified
Runpod, with independently checked implementation and increasing cutoffs.
Numerical results are research guidance only: approximate roots and truncations
cannot supply a Lean certificate or an unconditional mathematical no-go.

## Primary literature boundary

Luque–Thibon, [*Pfaffian and hafnian identities in shuffle algebras* (2002),
equation (4)](https://arxiv.org/pdf/math/0204026), already represents an ordered
determinant integral as the Pfaffian of antisymmetric double integrals. Thus
“replace joint areas by a higher alternating iterated integral” is published
general machinery, not a new positive survivor of this experiment.

Kelliher–Masri, [*Analytic continuation of multiple Dirichlet series of Euler-Zagier type*, equation (1.4)
and section 9.2](https://math.ucr.edu/~kelliher/papers/LFunctionsFull.pdf), treats
ordered multiple Dirichlet sums including periodic coefficients. The literal
area is a difference of two depth-two sums of that form in their common
absolute-convergence region. This is an identification of the underlying
objects, not a proof or disproof of the proposed zero-rank condition. Neither
paper is being adopted as an RH proof route.

## Gates

- [x] Literal source and falsifiable conjecture specified.
- [x] Existing coprime cross-completion theorem inspected.
- [x] Remote numerical gate, downloaded artifacts, interpretation report: rank law strongly disfavored.
- [ ] Exact zero-forced rank law, or a rigorous obstruction and positive-survivor audit.
- [ ] Primary literature novelty audit of a surviving mechanism.
- [ ] Independent strict-right exclusion mechanism.
- [ ] Unconditional Lean proof chain to RH.

## No-go closure

Not mathematically retired: no unconditional counterexample is claimed.
At approximate zeta zeros 1, 2, and 5 the Pfaffian has substantial, apparently
stable nonzero values. The largest cutoff is 860,160; independent implementations
agree near floating-point precision. See the [remote computation report](../../../2-fully-proven/computations/deletion-mixed-area-rank/REPORT.md).

The second pass checked these possible repairs:

- Changing the factor 1/2, orientation convention, or nonzero row scales cannot
  turn a nonzero Pfaffian into zero. The endpoint-vector Pluecker theorem acts on
  a different object and supplies no repair.
- Coprime complete-period cancellation concerns unweighted chronological words.
  Multiplying each time by its actual `n^(-s)` weight changes those hypotheses;
  the existing theorem cannot impose the tested rank condition.
- Exact ordered Euler dilation retains four distinct wedge regions and strict
  floor boundaries. Their grouped equality is already proved before imposing
  a zero and contains no new zero-specific rank identity.
- A central commutator in `ConstitutiveCohomologicalPacketFormation` is a single
  decomposable outer-product difference by definition. The whole accumulated
  source area has not been shown to be one such commutator. Introducing that
  representation would assume the missing rank law.
- Replacing the Pfaffian by its alternating iterated-integral representation
  leads to the published Luque–Thibon/de Bruijn identity, not a new arithmetic
  vanishing law. The periodic multiple-L-function description is also published.

**NO POSITIVE SALVAGE FOUND** in this rank-repair second pass. This records no new
mathematical impossibility theorem and does not retire all nonlinear deletion
approaches. Convergence, generic Pluecker algebra, and the existing four-wedge
identity are known facts, not new positive survivors. No production Lean module
was added for a computationally disfavored conjecture.
