# PW-B actual reciprocal-kernel endpoint

- **ID:** PW-B-GAMMA-RECIPROCAL-ENDPOINT-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** The complete reciprocal Gamma kernel converges in L1 to its positive integrable right-endpoint kernel. Its integrals have uniform bounds at every inverse polynomial order, with all original difference terms retained.

## Complete kernel and derivative

For a,v,h>0, the existing source kernel is

`K_a(v,h)=exp(-h)*(exp(-a/(v+h))-exp(-a/v))/h`.

The actual derivative of q_a(v)=exp(-a/v) is
`q_a'(v)=(a/v^2)*exp(-a/v)`.
The exponential-series inequality gives, for every natural k,

`0<=q_a'(v)<=((k+2)!/a^(k+1))*v^k`.

Applying the mean-value bound on the positive interval [v,v+h] yields

`0<=K_a(v,h)<=((k+2)!/a^(k+1))*exp(-h)*(v+h)^k`.

The bound controls the complete difference quotient without the former
1/v loss. In particular, k=0 gives the common integrable majorant
`(2!/a)*exp(-h)` for every v>0.

## Actual limit and admission

The right-endpoint kernel is

`L_a(h)=exp(-h-a/h)/h`.

Lean proves exp(-a/v)->0 as v->0+, then K_a(v,h)->L_a(h) for h>0.
The original written formula evaluated at v=0 is different because
Lean totalizes division by zero. No boundary value is inferred from
that evaluation.

The endpoint kernel is strictly positive on h>0 and satisfies

`L_a(h)<=((k+1)!/a^(k+1))*exp(-h)*h^k`.

Its actual positive-ray integral is finite and strictly positive. The
two k=0 bounds dominate |K_a(v,h)-L_a(h)| by
`((2!+1)/a)*exp(-h)`. Filter dominated convergence proves

`integral_0^infinity |K_a(v,h)-L_a(h)| dh ->0`,

and also convergence of the original kernel integrals to the endpoint
integral.

## Uniform bound for the arithmetic tail

The shifted Gamma moment
`J_k=integral_0^infinity exp(-h)*(1+h)^k dh`
is admitted, by bounding (1+h)^k with a sum of two powers and using
the original Gamma integral. For every 0<v<=1,

`integral K_a(v,h) dh <=((k+2)!/a^(k+1))*J_k`,

and `integral L_a(h) dh <=((k+1)!/a^(k+1))*J_k`.
The constants depend on k but not v. For a=n-1 and a coefficient bounded
by n^(N+1), choosing k=N+2 supplies an inverse-square summable tail.
The complete signed source-series passage is being checked separately;
it is not a conclusion of this leaf alone.

## Scope and verification

Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekGammaReciprocalEndpoint.lean`.
All14 public declarations pass the final scratch with only propext,
Classical.choice and Quot.sound. Exact passing proof bodies are promoted
and wired once into RHTower. The targeted leaf build passed in15s,
building only this leaf. Index passed (two changed entries, zero
removals); all14 public source and API declarations occur exactly once
at the correct module, and promoted proof bodies exactly match the
passing scratch. Final repository formal lint passed. No full or
umbrella build, numerical experiment, added axiom, commit or push was
used. The subsequent [complete arithmetic endpoint](pw-b-gamma-arithmetic-reciprocal-endpoint.md)
is separately proved and audited.

The [continuing pairing attack](../1-in-progress/pw-b-gamma-reversible-pairing.md)
retains the full cutoff-adjoint and arithmetic-domain obligations. This
endpoint result does not identify a physical spectral domain, an actual
Xi occurrence or source-forced Ward balance. RH remains unproved.
[Search records](../1-in-progress/pw-b-gamma-reciprocal-flat-endpoint-searches.json)
and the [attack journal](../1-in-progress/pw-b-source-orientation-attack.md)
record partial coverage and checked method applicability.
