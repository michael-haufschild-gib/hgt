# Hermitian-reflection audit (logical correction; not an RH proof)

`ReflectionTateParity.lean` correctly proves that RH is equivalent to every
Xi zero being fixed by `ρ ↦ 1-conj ρ`. Its accompanying prose/card makes two
stronger claims that do not follow and are false as stated:

1. A free orbit's permutation module is `ℤ[C₂]≅ℤ²` as an abelian group. It
   has no additive `2`-torsion. An order-two **action** is not an additive
   two-torsion **class**. A separate quotient or cohomology construction is
   needed, and the ordinary Tate cohomology of an induced free-orbit module
   vanishes. This is already formalized for a related signed-reflection
   action in `HTGeometry/ReflectionTateAnomaly.lean`:
   `freeMirrorPair_is_boundary` and the fixed-label parity classification.
2. An even real reader cannot distinguish the two *orientations* `a` and
   `-a`, but can distinguish fixed from free: `F(a)=a²` is even and
   `F(a)=0 ↔ a=0`. The corpus has exact RH-equivalent nonnegativity criteria,
   e.g. `XiWeilPositivityCriterion.lean` theorem
   `riemannHypothesis_iff_xiWeilPolarization_nonneg`. So positivity is not
   information-theoretically blind to RH. The missing step is to **derive**
   the requisite sign or zero-defect identity from the arithmetic source.

The survivor is the correct involution bookkeeping and its fixed-locus
classification. A genus-theoretic producer would need a source-defined map
to an appropriate orbit detector, plus a computation that rules out every
free orbit. Merely attaching `ℤ/2` to the divisor after locating zeros is a
new receiver, not a producer.
