# TG-C8: actual Fourier-paired prime source

- **ID:** TG-C8-20261001-01a0
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `PrimeBurnolFiniteModularSupport`, `PrimeBurnolDepthCompletion`,
  `HalfLineMellinUnitary`, `EvenL2LogUnitary`, `BurnolCoPoissonParityChannels`.
- **Statement:** pairing each literal prime source column with its actual even Fourier image
  removes the finite clock-collision kernel; determine whether that repair survives completion.

## Hard target and provenance

TG still needs joint prime–Gamma cancellation, a bounded cofinal operator, an independently
identified Hardy index, and a source action below one. C6 proved the uncompleted confluent dual
operator escapes. C7 identified both actual mixed Laurent coefficients. Neither identifies a
Gamma counterterm.

The existing co-Poisson parity cross Gram is a genuine noncentral Fourier construction, but its
positivity forces flatness. No new producer follows from that known order theorem. Instead,
test the actual Fourier pairing of the existing half-line source itself. The canonical unitary
from half-line L2 to even real-line L2 is `halfLineExpUnitary.trans logEvenUnitary.symm`; on
representatives it is ordinary even extension divided by sqrt(2). The Fourier operator is the
existing `evenFourierTransform`, not a chosen finite matrix or target-zero interpolation.

This construction has literal Fourier provenance. Its identification with the complete
arithmetic Gamma seam and Xi Hardy index is **not** assumed. Merely transporting both old
sectors by one unitary would preserve the old collision; here only the second sector receives
Fourier transformation.

## Conjecture C8.1 and paper attack

For every finite injectively labelled prime-depth packet, the joint family
`V f_i, Fourier(V f_i)` is linearly independent at clock zero. Consequently its complete Gram
is nonsingular there, retaining all cross terms.

The raw even source is `A_i |x| exp(-lambda_i |x|)`, with distinct positive lambda_i. Its
Fourier transform is
`2 A_i (lambda_i^2-(2 pi x)^2)/(lambda_i^2+(2 pi x)^2)^2`.
The normalization of V multiplies both sides by the same nonzero constant.

Suppose a source/Fourier linear combination vanishes. On the positive real axis it is a sum
of entire exponential-polynomial terms and the displayed rational terms. Multiply by the
product of every squared denominator. The resulting entire function vanishes on a real
interval and therefore everywhere. At `z=i lambda_j/(2 pi)`, all terms vanish except the
j-th rational numerator times the other nonzero denominators. Thus every Fourier coefficient
vanishes; existing literal-source independence kills the remaining coefficients. This is a
finite source statement, not a bound on inverse Gram matrices as depth grows.

## Conjecture C8.2 and cofinal test

Even if C8.1 succeeds, a uniform angle between both completed channels is unlikely: each
single prime's depth span is already dense, and V and Fourier are unitaries. Prove the exact
cofinal channel behavior rather than infer a budget from finite nonsingularity. A failure must
retain the positive finite collision-removal theorem and its precise completion boundary.

## Audit log

- Corpus search `Fourier Gram coherent cross operator` (Burnol filter): complete inventory,
  no partial result or errors; actual parity cross Gram and quotient order checked in source.
- Search `prime Gamma relative operator balanced wall` (RouteP filter): partial, with semantic
  timeout/malformed-JSON report; available hits checked, no absence claim.
- Logarithmic carrier search found both exact unitaries above. Additional searches for
  Fourier/exponential independence and smooth gluing are pending inspection.
- No numerical experiment, added premise, unproved Gamma/Xi identification, or RH claim.
- `PrimeBurnolFourierPair.lean` now passes its production `lake --old env lean -o ...` check
  without warnings. All nine public theorem axiom audits pass with only `propext`,
  `Classical.choice`, and `Quot.sound`; leaf wired to RHTower. This proves the literal
  Fourier integral formula, even-L2 admission, full joint independence, and Gram determinant
  nonvanishing. The raw even extension is unnormalized; no cost-preserving normalization is
  silently inferred.

## C8.2: exact completion mechanism under Lean audit

The source-derived completion is now explicit on paper. The canonical even-extension unitary
V carries every single prime's dense half-line depth span onto a dense span of the raw even
columns, with the exact common factor sqrt(2). Thus the two coordinate depth cores are dense
in H × H, H = actual even L2. Their bounded joint synthesis is

`S(x,y) = x + J y`,  J = actual even Fourier involution.

Its full kernel is the closed graph `x = -J y`. It is onto, with section `h ↦ (h,0)`.
Every coordinate pair has the exact kernel/diagonal decomposition

`(x,y) = ((x+Jy)/2, J(x+Jy)/2) + ((x-Jy)/2, -J(x-Jy)/2)`.

Finite injectivity from C8.1 therefore does not supply a bounded completed inverse. For any
finite bound C, the closed inequality `norm(z) ≤ C norm(S z)` cannot hold on the dense
coordinate depth core: its extension to the whole space fails on every nonzero kernel vector.
This argument asks for no numerical rate or truncation constant.

The original neutral coordinate projection `P(x,y)=(x,0)` also fails to descend through this
kernel: for any nonzero actual source column v, `(-Jv,v)` is killed by S but its P-image is
sent to `-Jv ≠ 0`. The positive survivor is a genuine bounded full Fourier synthesis with
an exactly classified kernel and quotient, together with the new finite nonsingularity theorem.
This only obstructs the ordinary inverse/neutral descent of this particular completion;
signed relative constructions preserving different data remain open. No Hardy-index or RH
conclusion is inferred.

`PrimeBurnolFourierCompletion.lean` now passes its production leaf check without warnings;
all 18 public axiom audits use only the standard three foundations. It also proves the stronger
exact canonical neutral compression `S P T=I/2`, with idempotence defect `-I/4`. Both leaves are
wired and indexed. Shared lint has twelve unrelated wiring errors, recorded on
`../3-formalized/tg-fourier-source-completion-kernel.md`; no new TG error.

C8.1 succeeded. C8.2's bounded-inverse/original-neutral-descent proposal failed, with its strongest
positive survivors fully audited. Continue through
`tg-fourier-radial-jet-completion.md`: retain an actual radial-jet output before completion and
prove the physical maximal-domain Fourier commutator kernel theorem.
