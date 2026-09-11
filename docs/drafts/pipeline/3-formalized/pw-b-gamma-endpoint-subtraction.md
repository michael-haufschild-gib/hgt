# PW-B complete endpoint subtraction and retained pole integral

- **ID:** PW-B-GAMMA-ENDPOINT-SUBTRACTION-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** For Re(z)>3/2, the literal correction S_z=M_z-C_z Q has an admitted Mellin integral at s=-1/2, equal to C'_z, where C_z=1/zeta(z-1/2). Its retained value has eventually positive real part as z tends to positive real infinity.

## Complete source proof

Retain Q(x)=sqrt(x)*exp(-x), every coefficient of the original M_z,
and the explicit correction C_z Q. For x>0 define R_z=S_z/(x*sqrt(x)).
The complete series identity is

`R_z(x)=sum_n LSeries.term(mu,z-1/2,n)*(exp(-n*x)-exp(-x))/x`.

The zero atom vanishes. Every positive-index Frullani kernel is integrable,
with integral -log(n) and norm integral log(n). Consequently the full sum
of atom norm integrals equals the absolute logarithmic Möbius L-series,
which is summable for Re(z)>3/2. This proves actual integrability and
interchange, giving

`integral_0^infinity R_z = -LSeries(logMul(mu),z-1/2) = C'_z`.

The actual Mellin integrand of S_z at s=-1/2 equals R_z pointwise on the
positive ray. Thus both admission and value are proved directly at the
former endpoint. No singular Gamma product is evaluated through its
totalized factors.

For Re(z)>5/2 the full first absolute coefficient moment is also summable.
Each difference quotient tends to 1-n and has norm at most n for n>0.
Dominated convergence yields the exact next endpoint coefficient

`R_z(x) -> C_z-C_(z-1)` as x tends to zero from above.

Finally, logMul(mu) vanishes at indices 0 and 1 and equals -log(2) at 2.
The complete L-series leading-coefficient theorem gives

`2^r * integral R_(r+1/2) -> log(2)` as real r tends to infinity.

Its positive limiting real part and the positive real scale imply
eventually positive real integral. Endpoint subtraction therefore retains
a nonzero response throughout an eventual parameter range. It does not
impose universal vanishing.

## Scope and next obstacle

This closes the explicit correction's actual finite pole integral and
first endpoint remainder. It does not prove its entire enlarged Mellin
domain, nonvanishing of C_z-C_(z-1) throughout a real half-line, a critical
estimate at z=0, or identification of coefficient and Xi spectral labels.
The physical pairing and independently source-forced occurrence-level
Ward balance remain open. The [ongoing attack](../1-in-progress/pw-b-source-orientation-attack.md)
now tests a pairing derived from both literal translation kernels and
retains the possible logarithmic correction in their individual adjoints.

The [raw research record](../1-in-progress/pw-b-gamma-endpoint-subtraction-searches.json)
contains four partial deep searches, including full candidate statements,
source arguments, proposed ingredient sets and coverage of723712 declarations.
Their proposed nonvanishing and generic detailed-balance shortcuts were
checked against their actual hypotheses and do not supply the missing law.

## Lean audit

Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusEndpointSubtraction.lean`.
The complete scratch passes; all23 public declarations use only
propext, Classical.choice and Quot.sound. Identical proof bodies are
promoted and the one-copy RHTower umbrella import is wired.
Final targeted leaf build and index audit are pending.

The repository lint run currently reports one unrelated unreachable
HTGeometry module, `ChronologicalTensor.CubicCuspPresentation`; no new
PW-B violation was reported. No full or umbrella build, numerical
experiment, added axiom, commit or push was used. RH remains unproved.
