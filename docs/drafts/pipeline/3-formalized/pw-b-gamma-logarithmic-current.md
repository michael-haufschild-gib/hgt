# PW-B actual logarithmic current: global admission and complete mass

- **ID:** PW-B-GAMMA-LOGARITHMIC-CURRENT-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** The literal Gamma/Möbius logarithmic current is globally integrable on the positive ray with integral `Gamma(3/2)`. Its full Euler-current assembly has that same nonzero series/integral defect although every individual term has zero integral. The complete difference of current and original Gamma source is integrable with zero mass.

## Actual source and proof

Use Lebesgue `dx` on `x>0`, the unchanged Gamma source
`Q(x)=sqrt(x)*exp(-x)`, Möbius preimage `M(x)=sum mu(n)*Q(n*x)`,
and actual current `E(x)=sum -mu(n)*log(n)*Q(n*x)`.
The existing complete arithmetic identity is `J M=E`, where
`J M(x)=sum Lambda(n)*M(n*x)`.
The prior [signed endpoint](pw-b-gamma-signed-endpoint.md) proves
`M in L1`, `integral M=0`, and `integral |M|>0`.

Retain `S(n)=sum_(j<=n) mu(j)` and form

`L_n(x)=S(n)*(log(n+1)*Q((n+1)*x)-log(n)*Q(n*x))`.

The zero index vanishes. The exact decomposition is a logarithm times the
previous Gamma difference atom plus a logarithmic increment times an
adjacent Gamma dilation. The existing direct Gamma difference estimate
and `log(n+1)-log(n)<=1/n` give

`integral |L_n| <= (Gamma(3/2)+Gamma(5/2))*|S(n)|*log(n)/n^2 + Gamma(3/2)*|S(n)|/n^2`.

The current corpus's unconditional four-log Mertens estimate
`|S(n)|<=B*n/log(n)^4` eventually proves summability of the extra
logarithmically weighted inverse-square term by comparison with
`B/(n*log(n)^3)`. No square-root cancellation premise is introduced.
Thus all Abel atoms are integrable and their norm integrals are summable.
The original series and regrouped series are also proved summable at each
positive `x`.

The exact finite identity is

`sum_(n<N) L_n(x) = sum_(n<=N) -mu(n)*log(n)*Q(n*x) + S(N)*log(N)*Q(N*x)`.

The scalar terminal `S(N)*log(N)/N` tends to zero by the four-log saving.
The inverse-square Gamma estimate then also kills the pointwise Gamma
terminal. Both limits are explicit, and identify the full Abel sum with
`E`. Admitted Bochner interchange establishes global integrability.

Each atom has exact integral

`Gamma(3/2)*S(n)*(log(n+1)/(n+1)-log(n)/n)`.

The finite scalar Abel identity equals
`Gamma(3/2)*(moebiusLogHarmonicPartial(N)+S(N)*log(N)/N)`.
The corpus theorem `Sieve.tendsto_moebiusLogHarmonicPartial_one` supplies
the first limit, and the second terminal tends to zero. Consequently

`integral E = Gamma(3/2)`.

## Complete arithmetic contribution

Every term `Lambda(n)*M(n*x)` is integrable with zero integral, including
index zero, whose arithmetic coefficient vanishes. The actual full
current `J M=E` is integrable and has mass `Gamma(3/2)>0`. Hence

`integral J M - sum_n integral Lambda(n)*M(n*x) = Gamma(3/2)`.

The sum of these term norm integrals cannot be summable: otherwise
Bochner interchange contradicts the positive defect. This is a complete
source contribution, not a missing convergence hypothesis silently
assumed in a formal cancellation. The positive survivor is the exact
admitted identity

`integral (E-Q)=0`.

Neither this one tested zero mass nor the equality of total masses
identifies the functions, a spectral generator, or the Ward charge.

## Route boundary and next mathematical attack

The chain remains literal PW response -> FE partner imbalance -> positive
Deninger Ward transmutation -> independently source-forced fixed-grade
balance -> RH. This module closes global admission of the actual current
and identifies its full nonzero mass. RH remains unproved; PW-B stays active.

The next attack must derive the connection between this complete source
contribution, the actual differential forcing, the physical measure and
the spectral parameter. Global differentiation through the coefficient
family at zero and any extension toward negative parameter values are
separate obligations. A generic zero-mass subtraction supplies neither. The successor
[forcing/measure classification](pw-b-gamma-forcing-measure-classification.md)
now evaluates both actual differential forcings, proves their separate
log-domain nonintegrability, and retains the admitted complete derivative.
The arithmetic current differs from that complete response in ray mass
by exactly `2*Gamma(3/2)`; the independent physical identification remains open.

## Methods, literature and novelty

Three deep searches, including retrieved methods and premise groups, are
saved in [search artifact](../1-in-progress/pw-b-gamma-log-current-searches.json).
All reported partial coverage. The useful ingredients were the four-log
Mertens saving, finite Abel summation, Gamma dilation moments and the
logarithmic Möbius normalization. Generic dilation symmetries, abstract
adjoints and unrelated source-manifold results did not supply Ward balance.
The theorem is a literal-source extension of these current corpus methods,
not a new general Abel theorem or an independent proof of PNT.

Broad searches read the primary abstracts for
[wetting reconstruction, July15](https://arxiv.org/abs/2607.13606) and
[precursor films, September1](https://arxiv.org/abs/2609.01444).
They describe fluid numerical methods; no arithmetic transfer was found.
The [September6 coherence fluctuation paper](https://arxiv.org/html/2609.06632v1)
retains a complex correction in its integral fluctuation identity.
The [August31 reciprocity paper](https://arxiv.org/abs/2608.30778)
distinguishes conservation constraints from the adjoint matching needed
for its response classification. These suggest retaining complete defect
and matching data; neither supplies the missing arithmetic or spectral
identification. No external paper is a Lean premise.

## Lean audit

Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusLogarithmicCurrent.lean`.
Scratch and direct `lake env lean` checks passed. The targeted
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusLogarithmicCurrent`
passed. All 23 public theorems were audited with `#print axioms` in a
scratch file: only `propext`, `Classical.choice`, and `Quot.sound` occur.
The leaf has one definition and 405 lines. Its premise-free capstone is
`pwGammaMobiusLogarithmicCurrent_closed`. Formal lint and index regeneration
passed; all 24 public names are indexed. Umbrella import is wired.
No full/umbrella build or numerical experiment ran. All owned Lean and
research processes finished.
