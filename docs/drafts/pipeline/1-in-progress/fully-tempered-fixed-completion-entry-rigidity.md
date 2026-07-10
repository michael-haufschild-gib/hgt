# Fully tempered fixed-completion entry rigidity

- **ID:** fully-tempered-fixed-completion-entry-rigidity
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE; NOVELTY UNVERIFIED]`
- **Source:** `../2-fully-proven/not_new_scientific_knowledge/symmetric-shift-entry-temperedness-boundary.md`

## Target

Fix a degree bound, conductor, archimedean gamma factor, root number, and pole divisor.  Let
`M_temp` be the class of normalized finite-order meromorphic Euler products

```text
L(s)=product_p product_(r=1)^d (1-alpha_(p,r)p^(-s))^(-1)
```

whose unramified local parameters are fully tempered, `|alpha_(p,r)|=1`, and whose fixed completion
satisfies the fixed functional equation about `Re s=1/2`.

`[CONJECTURE]` Every connected subset of `M_temp` in the coefficientwise local-factor topology has
constant nontrivial divisor.  In the primitive fixed-pole class, every connected subset is a
singleton.  Equivalently, a reflected off-line pair cannot enter the critical line along a
coefficientwise-continuous path that remains fully tempered and keeps the complete archimedean data
fixed.

The target is a constraint on the moduli space, not a zero trajectory and not a local jet.

## Why each hypothesis is live

1. Symmetric real shifts `Lambda(s+a)Lambda(s-a)` preserve an Euler product and the functional
   equation and move zeros transversely, but their local slopes are `p^(+/-a)`; they are tempered
   only at the collision parameter.
2. Helson zeta functions keep unimodular Euler factors and can prescribe off-line zeros, but do not
   carry the fixed global functional equation.
3. Gauthier--Xarles perturbations keep the functional equation and move zeros, but do not preserve
   an Euler product.
4. Unitary vertical shifts preserve temperedness, but change the archimedean parameters and move
   ordinates rather than real parts.

Thus no known counterexample remains inside the simultaneous intersection

```text
full temperedness + infinite Euler product + fixed completion + coefficientwise continuity.
```

## Parent-theory boundary

- `[SEARCH]` In standard automorphic subclasses, fixed level/conductor and fixed archimedean type
  give a discrete finite-multiplicity spectrum.  A no-entry statement there is known spectral
  rigidity, not new scientific knowledge.
- `[BRIDGE]` Absolute Euler-discrepancy continuity already forces constancy by the relative-strip
  theorem, but that ultrametric topology is much stronger than coefficientwise continuity.
- `[SEARCH]` Degree-one Selberg-class classification also makes the fixed-completion locus
  discrete.  The first scientifically live case lies beyond currently classified low-degree
  strata.

Scientific novelty would require either a proof in an abstract fully tempered Selberg-type class
not reducible to automorphic finiteness, or a counterexample satisfying all four simultaneous
conditions.

## Candidate constraint mechanism

For two endpoints `F,G` joined inside `M_temp`, the quotient has degree zero, fixed homogeneous
functional equation, and unit-modulus local endpoint data.  The known absolute-convergence argument
controls the quotient only when the endpoint Euler discrepancy is globally small.  The missing
lemma is a replacement that uses the existence of the entire tempered path, rather than an
absolute norm of its endpoint difference:

```text
[OPEN CORE] A coefficientwise-continuous path of unitary local factors whose every global Euler
product has the same finite-order completion cannot acquire a nontrivial quotient divisor.
```

This is a global integrality/continuation constraint: arbitrary paths exist in the product of local
unitary tori, but the conjecture says the fixed-completion meromorphic locus cuts that product into
points (or at least divisor-constant components).

## Falsifiers

1. Fixed gamma data may not be replaced by merely fixed degree; unitary shifts then give paths.
2. Full temperedness may not be weakened to a partial Ramanujan exponent; symmetric real shifts
   then give paths.
3. Coefficientwise continuity may not be silently strengthened to absolute Euler-discrepancy
   continuity; that would reduce the conjecture to the existing bridge theorem.
4. A proof by invoking automorphic discreteness after assuming automorphy is literature, not new
   science.
5. A divisor-discriminant or multiple-zero argument alone is insufficient: it describes the only
   collision stratum but does not prove that the Euler moduli avoid it.

## Gates

- [x] 0 -> 1: exact moduli, conclusion, known counterexamples, parent boundary, and open lemma
  stated.
- [ ] 1 -> 2: prove total disconnectedness/divisor constancy in an unclassified fully tempered
  fixed-completion class, or construct a counterexample inside that class.
- [ ] 2 -> 3: formalize the endpoint/path constraint after the paper theorem exists.
- [ ] 3 -> 4: independent proof and broad novelty audit across Selberg-class, converse-theorem,
  automorphic-finiteness, and Euler-product deformation literature.
