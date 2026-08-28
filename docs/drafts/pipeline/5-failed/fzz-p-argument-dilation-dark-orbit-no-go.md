# FZZ-P argument-dilation dark-orbit no-go

- **ID:** FZZ-P-HC39
- **Stage:** 5-failed
- **Type:** PROVEN NO-GO / exact all-scale survivor formalized
- **Sources:** `FZZCigarParityDelaySourceContinuation` +
  `FZZCigarParityDeningerInformationWardTransmutation` + mathlib Mellin scaling
- **Frontier map:** read-only; no edit permitted

## Candidate producer under test

Could literal positive argument dilation of the parity-delay source force HC38's shared FZZ/Deninger
Ward charge to vanish on every divisor mode?

For `r>0`, define the actually dilated source response

`M_r(s) = Mellin[t -> fzzCigarParityDelay(r t)](s)`.

The strongest plausible source-covariance proposal says all-scale darkness or scale stationarity of
a divisor mode should select `Re(s)=1/2` and hence annihilate the shared Ward charge.

## Frozen no-go conjecture

1. `M_r(s)=r^(-s) M_1(s)` exactly for every `r>0`;
2. a mode is dark at one positive dilation iff it is dark at every positive dilation;
3. every actual Xi divisor copy is therefore an all-positive-scale literal FZZ dark orbit,
   unconditionally;
4. all-scale darkness has no implication for HC38 Ward cancellation beyond RH itself: imposing
   cancellation on all such orbits is equivalent to RH.

## Paper proof

Positive change of variables in the Mellin integral gives the nonzero character multiplier
`r^(-s)`. Multiplication by a nonzero scalar preserves and reflects zero. HC38 proves every Xi
divisor-flow eigenvalue is a literal FZZ mode, hence every copy has the full dilation orbit. HC38
also proves Ward charge vanishes exactly on the critical line, so adding charge cancellation over
these already-universal dark orbits is precisely the remaining RH condition.

## Positive survivor

The exact all-scale source law is stronger than a negative statement: each divisor mode determines
a positive-dilation dark orbit with explicit character `r^(-s)`. Any viable dynamical producer must
break pure Mellin argument covariance—e.g. through a boundary, interaction, recoil, or another
channel not multiplicative in the original Mellin response.

## Corpus audit

Mandatory searches on 2026-08-28 included:

- `scripts/formal_tools.py research "FZZ parity delay source dilation covariance Mellin zero Ward charge derivative"`
- `scripts/formal_tools.py research "FZZ cigar source scale derivative Mellin transform zero mode stationary"`
- `scripts/formal_tools.py research "Mellin zero scale covariance Euler operator eigenvalue boundary term source"`
- `scripts/formal_tools.py research "FZZ parity source dilation generator commutator reflection charge"`
- `scripts/formal_tools.py research "salemFermiMellin dilation covariance scale Mellin transform"`
- `scripts/formal_tools.py research "FZZ parity Mellin all scale zero mode dark dilation"`

Corpus has the literal FZZ Mellin mode, general Mellin dilation identities, and various two-scale
Krein reporters, but no theorem classifying the actual argument-dilated FZZ source zero orbit or
connecting its blindness to HC38's shared charge.

## Literature boundary

Primary sources checked on 2026-08-28:

- Hikida--Schomerus, *The FZZ-Duality Conjecture -- A Proof*, arXiv:0805.3931;
- Creutzig--Hikida--Rønne, *The FZZ duality with boundary*, arXiv:1012.4731;
- Patkowski, *On Salem's Integral Equation and related criteria*, arXiv:2003.00581;
- González--Negrín, *A new equivalence to the Riemann Hypothesis by means of the Salem integral
  equation*, arXiv:2604.15396;
- Yakubovich, *Integral and series transformations via Ramanujan's identities and Salem's type
  equivalences to the Riemann hypothesis*, arXiv:1206.1166.

Search found no FZZ-specific theorem packaging complete positive-dilation darkness together with
the surviving Ward charge. Mellin dilation covariance itself is standard. Novelty claim is bounded
to source-specific classification and proof-burden exclusion.

## Formal theorem

Module:
`GaloisForLFunctions.RHTower.FZZCigarParityArgumentDilationDarkOrbitNoGo`

The formalization proves unconditionally:

1. literal argument-dilated response is exactly `r^(-s)` times original FZZ Mellin response;
2. dilation character is nonzero for every positive scale;
3. darkness at any positive scale is equivalent to original FZZ mode status;
4. darkness at all positive scales is likewise equivalent to one FZZ mode equation;
5. every actual Xi divisor copy has such an all-scale literal FZZ dark orbit;
6. requiring HC38 Ward cancellation on all these already-dark orbits is equivalent to RH.

## No-go verdict

**RETIRED:** pure positive argument dilation, including any condition depending only on persistence
of zero response along that orbit, cannot be shared Ward-charge producer. Its action is an
everywhere-nonzero Mellin character and preserves every divisor zero regardless of horizontal
position.

## Formalized positive survivor

Exact all-scale dark-orbit classification survives and is wired into corpus. It sharpens viable
producer boundary: FZZ/GFZZ dynamics must introduce a nonmultiplicative channel (boundary,
interaction, recoil, or cross-response) rather than pure source rescaling. This survivor is stronger
than merely saying dilation fails.

## Verification

- direct check:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarParityArgumentDilationDarkOrbitNoGo.lean`;
- targeted build:
  `lake build GaloisForLFunctions.RHTower.FZZCigarParityArgumentDilationDarkOrbitNoGo`
  passed (`8824` jobs);
- `#print axioms` on all seven public theorems reported only `propext`, `Classical.choice`, and
  `Quot.sound`;
- formal lint reported no HC39 finding; repository-wide lint still reports unrelated pre-existing
  unreachable modules;
- module is wired into `GaloisForLFunctions.RHTower`; full umbrella build intentionally not run;
- frontier map remained read-only and untouched.

## Status

- [x] corpus-led candidate and no-go conjecture frozen
- [x] dependency-closed paper proof
- [x] Lean formalization and exact no-go
- [x] direct check, targeted build, axiom/lint audit, umbrella wiring
- [x] bounded literature audit
- [x] move to `5-failed` with positive survivor formalized
