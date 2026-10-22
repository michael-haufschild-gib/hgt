# PW-B admitted logarithmic adjoint-contact pairing

- **ID:** PW-B-GAMMA-ADJOINT-LOG-MOMENT-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** For every positive integer n, the actual Gamma-mode cross-density has an integrable logarithmic moment equal to -log(n)/2 times its positive mass. Pairing the retained 2*log(x) contact against this density gives exactly the complete source-mode adjoint defect.

## Actual source measure and substitution

The [source-test theorem](pw-b-gamma-adjoint-source-test.md) constructs
phi_n=Q(n*x)/Q(x), w=exp(-x-1/x)/x and their finite positive cross-mass
M_n. The complete cross-density has the exact expression

`w(x)*phi_n(x)=sqrt(n)*exp(-n*x-1/x)/x`.

The map j_n(x)=1/(n*x) is a positive-ray involution. Lean proves its
image, injectivity through involution, and actual derivative

`j_n'(x)=-n/(n*x)^2`.

Direct source substitution, retaining the absolute derivative, gives

`|j_n'(x)|*w(j_n(x))*phi_n(j_n(x))=w(x)*phi_n(x)`.

This is the Jacobian used in the actual integral change of variables.

## Admission and exact moment

On x>0, log(x)<=x and -log(x)<=1/x imply
|log(x)|<=x+1/x. The exponential-series inequality bounds
(1/x)^2*exp(-1/x) by2!, hence

`|log(x)|*w(x)<=(1+2!)*exp(-x)`.

Since phi_n<=sqrt(n), an admitted exponential majorant proves actual
integrability of log(x)*w(x)*phi_n(x). Denote this integral by J_n.
The one-dimensional Jacobian theorem, log(j_n(x))=-log(n)-log(x),
and linearity of admitted integrals now give

`J_n=-log(n)*M_n-J_n`,

so J_n=-log(n)*M_n/2. In particular,

`integral_0^infinity 2*log(x)*w(x)*phi_n(x) dx`
`= forwardModePair(n)-backwardGroundPair(n)`.

The right side is the literal source-response defect proved in the
source-test module, not a newly defined surrogate. For n>1 it is
strictly negative and has finite positive mass M_n. The [cutoff theorem](pw-b-gamma-adjoint-cutoff-contact.md)
independently identifies2*log(x) as the retained moving-cutoff contact.
Thus this exact positive survivor accounts for the nonzero defect on
the actual ground-to-mode source tests.

## Remaining mathematical obligations

An integral of the pointwise limiting contact does not by itself
interchange the cutoff limit with the whole source integral. The
original transposition also retains the region where the incoming
interval is empty. The [continuing pairing attack](../1-in-progress/pw-b-gamma-reversible-pairing.md)
records three-region bounds for that passage and a sharper derivative
estimate for the full arithmetic endpoint.

No complete arbitrary-domain adjoint, operator closure, source-forced
pairing requirement, actual Xi occurrence or fixed-grade Ward balance
follows from this mode-level identity. PW-B remains active; RH is
unproved.

## Verification

Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekGammaAdjointLogMoment.lean`.
The final scratch co-imports both finished source/contact leaves and
passes all11 public declarations with only propext, Classical.choice
and Quot.sound. Identical proof bodies are promoted and one RHTower
umbrella import is wired. The targeted leaf build passed in168s,
building only this leaf. Index regeneration passed (four changed entries,
zero removals in the shared tree); all11 public names are unique in
source and API, and proof bodies exactly match the passing scratch.
The first final lint found the concurrently added unrelated Sieve module
MenonHarmonicSieveSwappedReceiver temporarily unreachable. After its
umbrella import appeared in the shared tree, final repository lint
passed. All owned Lean, build, research, index and lint processes are
terminal; a process check found no remaining owned adjoint Lean/lake
process. No full or umbrella build, numerical experiment, added axiom,
commit or push was used.

[Search records](../1-in-progress/pw-b-gamma-adjoint-contact-searches.json)
retain partial corpus coverage and proposed method ingredients. The
[attack journal](../1-in-progress/pw-b-source-orientation-attack.md)
records why reciprocal polynomial substitution and inverse-scaled
atomic moment laws did not apply. The proof instead verifies the
literal continuous source measure and its derivative.
