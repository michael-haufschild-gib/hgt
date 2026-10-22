# PW-B literal reciprocal-cutoff adjoint contact

- **ID:** PW-B-GAMMA-ADJOINT-CUTOFF-CONTACT-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** For every x>0, the literal integral of exp(-h)/h between delta/(x*(x-delta)) and delta tends to 2*log(x) as delta tends to zero from above.

## Proof and retained source term

For 0<delta<x, the transformed cutoff

`a(x,delta)=delta/(x*(x-delta))=(x-delta)^(-1)-x^(-1)`

is strictly positive. Both a(x,delta) and delta tend to zero. For every
positive h, the elementary exponential inequalities give

`|(exp(-h)-1)/h|<=1`.

On any interval with positive endpoints a,b, both exp(-h)/h and 1/h
are actually integrable. Subtraction and the interval norm bound give

`|integral_[a,b] exp(-h)/h-log(b/a)|<=|b-a|`.

With the literal transformed cutoff, delta/a=x*(x-delta). Consequently
the contact differs from log(x*(x-delta)) by at most |delta-a|. The
error tends to zero and the logarithm tends to 2*log(x). The theorem
retains either interval orientation; it assumes no order between a and
delta. No value of the singular integrand at zero is used.

## Scope and next mathematical step

This proves the contact created by the two different displacement
cutoffs. It does not establish integral transposition, a closed operator,
a common arithmetic domain or a physical selection law. In particular,
the predicted identities A*=B+2*log(x) and B*=A-2*log(x) remain to be
proved with their complete paired integrals and domains.

The [source pairing attack](../1-in-progress/pw-b-gamma-reversible-pairing.md)
tests the same contact against actual Gamma source modes. The
[admitted logarithmic-moment theorem](pw-b-gamma-adjoint-log-moment.md)
now identifies its pairing with the entire source-mode defect. Full
original cutoff transposition remains open. Actual Xi occurrence and independently
source-forced fixed-grade balance remain open. RH is unproved.

## Verification and research

Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekGammaAdjointCutoffContact.lean`.
All nine public declarations pass in the final scratch, with only
propext, Classical.choice and Quot.sound in their axiom reports.
Identical proof bodies are promoted and one RHTower import is wired.
The targeted leaf build passed in193s, rebuilding only this leaf.
Index regeneration passed (four changed entries, zero removals in the
shared tree). All nine public names occur exactly once in source and
generated API, and all proof bodies match the passing scratch. Repository
formal lint passed. All cutoff scratch, build, index and lint processes
are terminal. No full or umbrella build, numerical experiment, added
axiom, commit or push was used.

[Deep and method search records](../1-in-progress/pw-b-gamma-adjoint-contact-searches.json)
retain the partial corpus coverage and proposed ingredients. The
[attack journal](../1-in-progress/pw-b-source-orientation-attack.md)
records applicability checks and recent broad arXiv searches. Neither
conditional metric-adjoint results nor unrelated reciprocal polynomial
substitution laws were used to assume the desired source identity.
