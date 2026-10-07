# Reciprocal symmetrization of the nonperiodic cosine section

- **ID:** cosine-reciprocal-symmetrization
- **Stage:** 5-failed
- **Type:** FALSIFIED candidate; positive coincidence classification formalized
- **Parent:** ../1-in-progress/labeled-lattice-section-periodicity.md, C2-P
- **Candidate:** For the previously certified cosine Mobius section G, set V(w)=G(w)/G(-w). Does this repair reciprocal reflection while preserving the labeled fibers?

## Exact object and hostile verdict

Let T(w)=cos(2*pi*sqrt((w+1/12)/27)), interpreted by even entire descent, and let G=M o T be the fixed Mobius normalization in `LabeledCosineMobius.lean`. Let V=G(w)/G(-w), interpreted meromorphically after removing any cancellations.

Reciprocal reflection V(-w)=1/V(w) and conjugate reciprocity follow from the corresponding conjugate identity for G. These identities do not preserve the old fibers.

**Verdict FALSE.** At w=6*i*sqrt(5), T(w)=T(-w), so V(w)=1 at an off-real point. No claimed C2-P counterexample survives. This construction is elementary classical cosine algebra; significant scientific novelty is not claimed.

## Positive survivor [PROVED HERE, Lean]

The complete reflection coincidence locus has the exact integral parametrization

    T(w)=T(-w) iff exists n in Z,
        4*w^2 = 9*n^2*(1-81*n^2).

Proof. Put u^2=4*pi^2*(w+1/12)/27 and v^2=4*pi^2*(-w+1/12)/27, choosing either square root. Evenness makes their cosines independent of the choice. Cosine equality is equivalent to v=2*pi*n+u or v=2*pi*n-u for an integer n. Either relation implies

    (u^2-v^2)^2 - 8*pi^2*n^2*(u^2+v^2) + 16*pi^4*n^4 = 0.

Substitution and cancellation of the nonzero pi^4 gives the displayed equation. Conversely, for n!=0 satisfying the equation, take

    u=pi*n+2*pi*w/(27*n),   v=-pi*n+2*pi*w/(27*n).

Their squares have the required values, and u-v=2*pi*n. If n=0 the equation forces w=0 and equality is immediate. This proves both directions, with no bound or growth argument.

At w=6*i*sqrt(5), the equation holds with n=1, since w^2=-180. Here -w=conj(w), so conjugation of T and the coincidence identity show T(w) is real. The Mobius numerator and denominator at a real input are conjugate and never simultaneously zero, hence neither vanishes. Therefore the quotient V is holomorphic at this witness and actually takes the value 1; this is not a spurious cross-determinant zero at a cancellation. The witness is nonreal because its imaginary part squares to 180 and so is nonzero.

## No-go closure

- **Killing mechanism:** reciprocal symmetrization adds the reflection coincidence divisor T(w)=T(-w) to the 1-fiber.
- **Positive survivor:** exact complete coincidence locus above, retaining all integer branches and the n=0 case; an actual finite off-real value for the repaired map.
- **New insight:** the missing reflection cannot be repaired by this multiplicative quotient without changing marked fibers. The added divisor is controlled by a quadratic-cover coincidence equation, not the old three labeled divisors.
- **Status:** dependency-closed paper proof and exact Lean proof complete. Full C2-P remains open.

## Audit and next actions

Prior corpus: the existing `LabeledCosineDescent` supplies even descent and full constant fibers; `LabeledCosineMobius` supplies injectivity and conjugate coordinates. Exact follow-up deep query `cosine reflection quotient reciprocal fiber quadratic coincidence` completed with `partial=false`, no errors, incomplete compiler freshness and a slightly older coverage snapshot. All candidate/source statements and the proposed ingredient set were inspected; no exact match appeared. External exact-phrase searches returned no matching theorem; this is not evidence of novelty. The parent cosine identities and even descent are classical. No result from unrelated bound/spectral hits is imported.

## Lean certificate

`HTGeometry/CosineReflectionCoincidence.lean` proves `coincidence_iff`, both symmetry identities, nonvanishing of the actual denominator at `6*i*sqrt(5)`, analyticity there, and `reciprocal_repair_has_off_real_one_fiber`. The latter has no hypotheses. The imaginary part is shown nonzero by its exact square identity; no growth or sign criterion is used.

Direct leaf check clean; `lake build --old +GaloisForLFunctions.HTGeometry.CosineReflectionCoincidence` passed (3400 jobs, leaf 22 seconds). Four scratch axiom audits report only `propext`, `Classical.choice`, `Quot.sound`. The leaf is wired into the HTGeometry umbrella. Global lint still reports exactly five unrelated unreachable aperture/corona modules, as recorded on the discrete-dilation card; no new leaf was flagged. Global lint is not clean.

This closes the specific failed repair and its positive survivor. The next candidate generalizes the obstruction to rational repairs regular on the reflection diagonal; the negative diagonal sign and diagonal basepoints remain explicit escape cases.
