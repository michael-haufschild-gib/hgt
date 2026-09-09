# HB: original physical response equals the complete-source endpoint Green integral

Status: formalized. RH remains unproved.

The original physical Hilbert response is identified with the endpoint
Green integral of its literal complete angular source on
`3/2 < Re(w) < 2`, `Im(w) != 0`. Both endpoint currents, the actual
derivative bounds, and absolute source admission are derived internally.
This closes the overlap identification. The same-copy response now also
has a [continuation to both fundamental QNMs](hb-physical-self-response-continuation.md);
its physical adjoint residue remains open.

## Exact result

For original Xi source and target copies q,r, branch and onset parameter,
write P for the original physical profile, F for
`continuedAngularSourceProjection`, H,N for the original horizon and
normalizable modes at `chi=physicalRadialFrequency(r)`, and c for their
original connection coefficient. The new source-only definition is

```text
G(t) = [N(t) integral(-infinity..t, H F)
       +H(t) integral(t..0, N F)] / c.
```

`physicalCuspProfile_eq_completePhysicalGreenProfile` proves `P(t)=G(t)`
for every t<0. `physicalCuspResponse_ae_completePhysicalGreenProfile`
proves equality with the original Hilbert response almost everywhere
for the original restricted radial measure. F retains its residual term
and all three cutoff commutators, with their original coefficients.
The result assumes no replacement response, endpoint currents, source
integrability, derivative bounds, or outgoing inverse.

## Closed proof

1. Each original principal frequency satisfies `|Im chi_i|<3/2`.
   Consequently, the physical overlap lies in all three original Green
   chambers. The continued principal differences equal the original
   bounded Green corrections there. The reduced forcing is bounded by
   its compact radial profile; the geometric cutoff weight lies in
   [0,1]. Their exact four-channel assembly bounds F uniformly on t<0.
2. The actual classical equation is
   `P''=w^2 P-lambda h P-F`, with `h=sech(t)^2` and
   `lambda=physicalAngularParameter(r)^2-1/4`. The previously proved
   spatial bound for P and the new bound for F give a bound for P''.
   Reflect a backward unit interval and apply the existing complex
   derivative estimate: if `|P|<=C` and `|P''|<=M`, then
   `|P'|<=4C+M` everywhere on t<0, including arbitrarily near zero.
3. The original H and H' tend to zero at the horizon. Bounded P and P'
   imply `J_H=H'P-HP' -> 0` there. The original N tends to zero at the
   outer endpoint. Its compact-radius derivative limit, transported
   through the actual coordinate derivative, gives `N' -> -1`.
   The proved physical Dirichlet trace `P -> 0`, together with bounded
   P', gives `J_N=N'P-NP' -> 0` at that endpoint.
4. The exact dressed horizon mode satisfies
   `|H(t)|<=C_H exp(Re(w)t)` on the entire negative ray. Bounded F
   therefore makes HF absolutely integrable down to the horizon.
   N extends continuously to the outer endpoint with value zero, so
   it is bounded between any fixed interior t and zero. NF is
   absolutely integrable on each such finite interval.
5. Pass the original finite current identities to their respective
   endpoints, using the actual limits and admitted integrals:
   `J_H(t)=integral(-infinity..t,HF)` and
   `J_N(t)=-integral(t..0,NF)`. Substitution into the proved original
   Wronskian identity `c P=N J_H-H J_N`, with c nonzero on the overlap,
   proves P=G. Transfer through the existing representative equality
   gives the original Hilbert response equality.

## Lean surface and audit

One HTGeometry leaf, `NegativeRayBoundedDerivative`, and six RHTower
leaves with prefix `ThetaCuspHawkingBM`:

- `CompleteAngularSourceBounds`
- `PhysicalResponseDerivativeBounds`
- `JointSourceOuterModeLimits`
- `PhysicalResponseEndpointCurrents`
- `PhysicalGreenSourceAdmission`
- `PhysicalResponseGreenIdentification`

These contain 20 public theorems and one definition, in 433 lines.
Each passed a scratch `lake env lean <file>` check and an individual
final `lake build <exact-module>` in the isolated cache-backed audit
project. All seven final builds were warning-free. A scratch-only
axiom audit of these 21 new declarations reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. No added axiom or computational
certificate is used. All 21 installed source/olean/ilean artifacts
matched the audited artifacts by SHA-256. Seven unique umbrella imports
are wired; no umbrella or full build was run.
The index refresh, `scripts/formal_tools.py lint --check-generated`, and
`git diff --check` passed. Static lint reports 141 existing large-file
warnings; the largest new leaf has 95 lines. The frontier map's SHA-256
is unchanged from the read-only snapshot.

## Current continuation and residue scope

The same-copy complete-source G is now continued to both fundamental
resonances by an [exact finite resolvent reduction](hb-physical-self-response-continuation.md).
This uses proved nonvanishing of its actual auxiliary angular gaps.
The cleared reduction also holds for arbitrary source-target pairs;
recovering the response at a cross-copy zero gap remains open.

The integral identity on the positive-frequency overlap does not itself
justify the horizon integral where the decaying mode grows. The subsequent
finite reduction supplies a pointwise meromorphic continuation of the
same observable. Its physical adjoint residue, complete-source pole
survival, spin-two/AIME reconstruction, and independently proved
Hawking-clock extinction remain open. No RH conclusion follows from
these stages alone.
