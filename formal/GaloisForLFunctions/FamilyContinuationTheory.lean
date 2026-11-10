import GaloisForLFunctions.FamilyContinuationTheory.TwistedColumnsCorrelateThroughOneResidue
import GaloisForLFunctions.FamilyContinuationTheory.ContinuationFromACommonSignal

/-!
# Family continuation theory

Umbrella for the route "a zero-free half-plane by continuing the reciprocals of a family of
`L`-functions across its rightmost zeros, then from a half-plane to the line".

* **Continuation from a common signal.** A kernel `G` holomorphic on `Re s > 1` with decay on
  vertical strips, whose signal `(1/2π) ∫ G(2+it) Z^{2+it} dt` is `O(Z^b)`, extends to `Re s > b`;
  if `G L = E` with `E` zero-free, `L` has no zero in `Re s > b`. A sum with a direct bound and
  a comparison with the signal gives the half-plane right of the larger exponent.
* **Additive columns of residue characters.** The correlation of two columns of coprime moduli is
  one term; a weighted second moment over the rows is a multiplicative form in the frequency; at
  the frequencies on which the characters are trivial the terms add without cancellation.
-/
