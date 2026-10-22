# PW-B literal Gamma/Möbius Mellin bridge

- **ID:** PW-B-GAMMA-MELLIN-BRIDGE-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** The actual coefficient-deformed Gamma/Möbius source has Mellin transform Gamma(s+1/2)/zeta(z+s) in its proved absolute region. The complete series of weighted atom norm integrals converges exactly when Re(z+s)>1, provided Re(s)>-1/2.

## Original source and transform

Retain `Q(x)=sqrt(x)*exp(-x)` for positive x and the complete source
`M_z(x)=sum_n mu(n)*exp(-z*log(n))*Q(n*x)`.
The Mellin transform here is the actual integral
`integral_0^infinity x^(s-1)*M_z(x) dx` with Lebesgue measure.
No reflected source, truncated series, changed coefficients or formal
analytic continuation substitutes for this integral.

The source Gamma integral is admitted when Re(s)>-1/2 and equals
Gamma(s+1/2). Positive dilation changes it by the exact factor n^(-s).
Thus the actual weighted arithmetic atom has integral

`Gamma(s+1/2)*LSeries.term(mu,z+s,n)`.

Its norm integral is exactly

`Real.Gamma(Re(s)+1/2)*norm(LSeries.term(mu,z+s,n))`.

Both statements treat the zero atom separately through mu(0)=0 and retain
all positive-index coefficients. The norm formula follows from the
convergent real Gamma integral and exact real-power algebra. Since the
Gamma factor is strictly positive, the corpus's sharp Möbius absolute
L-series boundary gives

`sum_n integral norm(weighted atom_n) < infinity iff Re(z+s)>1`.

## Complete interchange and analytic parameter

Inside that region the weighted atoms are individually integrable and
their complete norm-integral series converges. The full source therefore
is Mellin-convergent, and the series passes through its actual integral.
The full Möbius L-series is the reciprocal of zeta there. Consequently

`Mellin(M_z)(s)=Gamma(s+1/2)/zeta(z+s)`

for Re(s)>-1/2 and Re(z+s)>1. This identifies the combined analytic
parameter z+s from the literal source. It does not identify a Xi
occurrence or prove critical-strip continuation.

Failure of the coefficientwise norm sum at or left of Re(z+s)=1 does
not establish nonintegrability of the complete signed source. Such a
conclusion would require an actual signed endpoint argument. Conversely,
pointwise entireness of the coefficient family and global admission of
its inverse-gain reflection do not extend this Mellin identity's domain.

## Research and next mathematical attack

[Search records](../1-in-progress/pw-b-gamma-mellin-bridge-searches.json)
retain deep source-identification, signed-energy, endpoint and Abel-boundary
searches with their reported partial coverage. The literal Gamma moments,
Mellin dilation, integral interchange and Möbius L-series tools were
verified in the scratch proof. Generic energy estimates retain an
unproved coercivity/accretivity realization; complementary character
halves do not identify the actual arithmetic operators. The existing
Möbius–Laplace critical continuation connector retains a source-decay
premise, and its abstract continuation wall is equivalent to RH.

A broad date-ordered arXiv query used `duality`.
[Boundary control for optimal mixing by two-dimensional second-grade fluids](https://arxiv.org/html/2609.09946v1)
(September 9) derives duality from admitted forward/adjoint tests and
retained terminal/source contributions. Its weak adjoint regularity alone
does not establish a strong boundary operator. No transfer of those
fluid hypotheses to the present arithmetic source has been established;
no external premise enters Lean.

The successor [actual signed-source endpoint audit](pw-b-gamma-source-endpoint.md)
now proves `M_z(x)/sqrt(x) -> 1/zeta(z-1/2)` for Re(z)>3/2, with a nonzero
limit and the sharp actual Mellin domain Re(s)>-1/2. Keeping z+s fixed
while sending z rightward leaves that domain. This closes the proposed
small-coordinate endpoint test; it does not establish signed critical
continuation or carry the large-z spatial-mass law to a fixed Xi argument.

RH remains unproved. PW response -> FE imbalance -> positive Deninger
Ward transmutation is not yet connected to an independently forced
fixed-grade balance at actual Xi occurrences. Signed critical source
control, the physical pairing/domain and occurrence-level Ward balance
remain open.

## Lean audit

Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekGammaMobiusMellinBridge.lean`.
The complete scratch and all nine public declaration axiom audits passed,
using only propext, Classical.choice and Quot.sound. The eight theorems
and one definition were promoted with identical proof bodies; the
umbrella import is wired. The final targeted build passed, rebuilding only the new leaf in 370s;
dependencies were reused. No full or umbrella build ran. Repository-wide formal lint
did not pass: three unrelated active modules lack umbrella reachability,
HTGeometry.WeightedMinimax.Alternation, Coefficient and PolyRoots. The
new PW-B leaf is not flagged. New-source whitespace/conflict checks,
public-name uniqueness, one-copy umbrella wiring and local card links
passed. No critical continuation premise enters these proofs.


Index regeneration passed; all nine public declarations are present in
LEAN_API. All owned Lean/research/audit sessions finished, and the final
process check found no owned Lean/lake process. The three unrelated
repository lint failures above remain unresolved; no full build,
numerical experiment, added axiom, commit or push was used.
