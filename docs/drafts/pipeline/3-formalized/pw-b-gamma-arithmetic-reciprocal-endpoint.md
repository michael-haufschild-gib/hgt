# PW-B complete arithmetic reciprocal endpoint

- **ID:** PW-B-GAMMA-ARITHMETIC-RECIPROCAL-ENDPOINT-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** For every complex coefficient parameter z, the original Frullani current of the reflected Gamma/Möbius source, divided by Q(v), has a finite right-endpoint limit. Its limiting signed coefficient series is absolutely summable.

## Original source and retained series

Write Q(v)=sqrt(v)*exp(-v) and let H denote the existing weighted
Frullani generator. The source-fixed inverse-gain reflection is R.
The actual current H(R M_z) is already an admitted integral of the
complete response and equals the sum of its integrated original atoms.
The response atoms at integers0 and1 vanish.

For m>=2 its normalized integrated atom is exactly

`mu(m)*exp(-z*log(m))*sqrt(m)*I_(m-1)(v)`,

where `I_a(v)=integral_0^infinity K_a(v,h) dh` and K_a is the original
complete reciprocal kernel. The new source-identity theorem proves
this equality and retains the entire signed tail:

`H(R M_z)(v)/Q(v)=sum_(m>=2) mu(m)*exp(-z*log(m))*sqrt(m)*I_(m-1)(v)`.

No individual positive kernel or truncated coefficient sum replaces
the original current.

## Uniform tail and actual limit

Choose a natural N with |z|<=N. The exact signed coefficient has norm
at most m^(N+1). The [complete-kernel endpoint](pw-b-gamma-reciprocal-endpoint.md)
gives, for every 0<v<=1,

`I_(m-1)(v)<=((N+4)!/(m-1)^(N+3))*J_(N+2)`,

where `J_k=integral_0^infinity exp(-h)*(1+h)^k dh` is admitted.
Since m<=2*(m-1), the normalized integrated atom is bounded by

`2^(N+1)*(N+4)!*J_(N+2)/(m-1)^2`.

This common bound is summable and independent of v. Each original
kernel integral tends to

`I_a(0+)=integral_0^infinity exp(-h-a/h)/h dh`.

Tannery's theorem now proves the complete original-current limit

`H(R M_z)(v)/Q(v) ->`
`sum_(m>=2) mu(m)*exp(-z*log(m))*sqrt(m)*I_(m-1)(0+)`.

The limiting series is absolutely summable for every complex z. The
bound also holds uniformly for coefficients in each fixed bounded
complex region; no differentiability of the endpoint series is claimed
by this leaf.

## Consequences and limits

This closes the previously unpaid complete arithmetic endpoint. It
can be transported by the actual inverse-gain reflection to test the
backward generator at the opposite end. It supplies no scalar
eigen-equation, physical necessity of a pairing class, or selection of
Xi zeros. The [continuing source attack](../1-in-progress/pw-b-gamma-reversible-pairing.md)
now records the proved logarithmic residual of the corrected skew
candidate on the unchanged source, and its forced unit ground correction. RH and PW-B's source-forced Ward
balance remain unproved.

## Verification

Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusReciprocalEndpoint.lean`.
All11 public declarations pass the final scratch with only propext,
Classical.choice and Quot.sound. Exact bodies are promoted and wired
once into RHTower. The targeted leaf build passed in40s, building only
this leaf. Index passed (two changed entries, zero removals); every
public source and API declaration is unique and each proof body matches
its passing scratch. Final repository formal lint passed. No full or
umbrella build, numerical experiment, added axiom, commit or push was
used. The subsequent [skew-source and forced-correction theorem](pw-b-gamma-skew-source-endpoint.md)
is separately proved and audited.

[Search records](../1-in-progress/pw-b-gamma-reciprocal-flat-endpoint-searches.json)
retain partial coverage and source/compiler freshness metadata. The
[attack journal](../1-in-progress/pw-b-source-orientation-attack.md)
records the actual mean-value, Gamma-majorant, dominated-convergence
and Tannery methods, along with rejected premise substitutions.
