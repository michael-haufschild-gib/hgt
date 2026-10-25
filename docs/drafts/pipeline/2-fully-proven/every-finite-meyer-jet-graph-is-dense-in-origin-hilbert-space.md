# Every finite Meyer jet graph is dense in origin Hilbert space

- **ID:** qii-origin-hilbert-full-jet-graph
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/q-ii-source-effectivity-and-linear-degree.md
- **Statement:** The joint map from actual Meyer sources to half-density L2 and any surjective normed cohomological linear reading has dense image in their product. In particular every finite full-Xi-jet graph has full product closure, including critical value coordinates.

## Paper proof [PROVED HERE]

Write iota for the existing half-density source embedding, B for the genuine
Poisson boundary, and q for the actual quotient map. The boundary-density
theorem on `poisson-boundaries-are-dense-in-origin-mass.md` says iota(B(cap))
is dense in H=L2.

Let E:cohomology→Y be a surjective linear reading, with Y a normed complex
space. Given (h,y), choose an actual source g with E(q(g))=y. For every
epsilon>0, choose a genuine boundary Bf with iota(Bf) within epsilon of
h−iota(g). Then

    (iota(g+Bf), E(q(g+Bf))) = (iota(g)+iota(Bf), y)

lies within epsilon of (h,y). Thus the joint graph is dense in H×Y.

The corpus proves surjectivity of every finite complete Xi-jet packet map
`deningerMeyerFiniteXiJetPacketLM_surjective`, with no simplicity or location
condition. Applying the general result gives full product closure of every
such graph. Every closed linear relation containing it is the whole product.
For a nonempty output packet, no single-valued closed relation can contain
the actual source graph: it contains every (0,y).

The same argument applies to the entire faithful convolution representation,
by taking `Y` to be the range of `deningerMeyerConvolutionRepresentationLM`
with its inherited operator norm. The range restriction is surjective by
construction. Its joint graph has full product closure in `H×Y`; every
nonprincipal source therefore gives a nonzero vertical operator in that
closure. No finite-packet reduction or continuity of the source representation
in the origin norm is assumed. The range need not be complete for this argument.

## New distinction

The existing half-density L1 graph closure has a critical/off-line split:
critical zeroth evaluations remain single-valued, while off-line values
become vertical. In origin-mass L2, every finite Xi reading becomes fully
vertical, including critical zeroth values and all higher jets. Strengthening
the positive ambient norm to an L2 Hilbert setting therefore does not preserve
the critical cohomological reading. A closed graph cannot restore that loss.

## Scope and certificate obligations

The theorem concerns the stated origin Hilbert completion and literal full
source graph. It does not rule out stronger source topologies or restricted
domains. Its positive survivor is the exact full-product graph closure.

Corpora searched for dense graph/dense kernel mechanisms and the actual
finite-jet surjection. The source statements were read. Complete unrun draft: `/tmp/QIIMeyerOriginJetGraphDraft.lean`, including
full product closure and the exact empty-packet single-valuedness criterion. The
draft also includes full graph closure for the entire faithful operator range
and its nonzero vertical classes. The
boundary-density prerequisite is fully proved on paper but not yet checked
in Lean. External novelty unverified.

## Dense-image extension

Surjectivity can be weakened to dense image. First choose a class whose reading
is within epsilon of the desired output, lift that class to an actual source,
and then change its origin coordinate by a boundary within epsilon of the
desired Hilbert vector. Both coordinates are within epsilon in the product
maximum norm. Thus the graph is dense also in any normed completion of the
reading image. This strengthens the abstract draft and requires no continuity
of the algebraic cohomological reading. The earlier generic Hilbert graph
annihilator criterion is `HTGeometry/GraphSaturationCore.lean`; here genuine
boundary density supplies the missing arithmetic annihilator rigidity.

Actual candidate: `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/EveryFiniteMeyerJetGraphIsDenseInOriginHilbertSpace.lean`; unverified and unwired. The scratch copy remains until actual-file verification succeeds.
