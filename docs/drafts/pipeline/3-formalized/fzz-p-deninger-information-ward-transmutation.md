# FZZ-P/Deninger information--Ward transmutation

- **ID:** FZZ-P-HC38
- **Stage:** 3-formalized
- **Type:** THEOREM / cross-route exact identity and shared equilibrium law
- **Sources:** `FZZCigarParityReflectedFermiInformationGradientFlow` +
  `DeningerDivisorGaugeWardIdentity` + `CentralReciprocalMoments`
- **Frontier map:** read-only; no edit permitted

## Frozen conjecture

For `0<sigma<1`, define the nonlinear Ward multiplier

`C(sigma) = 1` at `sigma=1/2`, and

`C(sigma) = F(sigma)/(2 sigma-1)` otherwise,

where `F` is HC37's reflected Fermi information force. For every Xi divisor copy `q`, let `D(q)`
be the cup trace of the Deninger reflect-gauge commutator on the basis vector `delta_q`.

Conjecture:

1. `C(sigma)>0` throughout the open critical strip;
2. `F(sigma)=(2 sigma-1)C(sigma)` exactly;
3. `D(q)=1-2 Re(q)` exactly;
4. after identifying every divisor copy with its literal FZZ parity-Mellin mode,
   `F(Re(q)) = -C(Re(q))D(q)`;
5. FZZ information equilibrium at a divisor copy is equivalent to vanishing Deninger reflect-gauge
   commutator there;
6. universal cancellation of this one shared charge is equivalent to RH.

This is not a proof that the shared charge vanishes. It tests whether two independently developed
routes carry exactly the same oriented open core, including a strictly positive conversion factor.

## Paper proof

HC37 gives strict sign of `F` matching the sign of `2 sigma-1`, so their quotient is positive away
from center; the center branch is positive by definition. Algebra gives the factorization. The
unconditional Deninger Ward identity, evaluated at the reflect gauge whose cup diagonal is `1`,
gives `D(q)=lambda_Rq-conj(lambda_q)`. Functional-equation reflection gives
`lambda_q+lambda_Rq=1`, hence `D(q)=1-lambda_q-conj(lambda_q)=1-2 Re(q)`. The transmutation follows.
Every Xi divisor copy lies in the open strip and is a zero of Xi, hence its eigenvalue is a literal
FZZ parity-Mellin mode by the source-continuation theorem. Positivity of `C` makes the two vanishing
laws equivalent. Universal vanishing forces all divisor real parts to `1/2`, and conversely RH
does so.

## Corpus audit

Mandatory searches on 2026-08-28 included:

- `scripts/formal_tools.py research "FZZ parity Mellin zero phase derivative Ward identity stationary reflected information force"`
- `scripts/formal_tools.py research "Fermi Mellin zero derivative log moment reflection functional equation Wronskian"`
- `scripts/formal_tools.py research "FZZ winding condensate Ward identity dilaton gradient equilibrium divisor mode"`
- `scripts/formal_tools.py research "Deninger divisor Ward charge 1 - 2 rho real part diagonal reflection"`
- `scripts/formal_tools.py research "FZZ Deninger bridge parity Mellin source divisor gauge Ward"`
- `scripts/formal_tools.py research "positive multiplier equivalence Ward defect information force critical line"`

Corpus contains both component detectors but no exact positive-multiplier FZZ-information/Deninger
Ward transmutation theorem.

## Literature boundary

Primary sources checked on 2026-08-28:

- Hikida--Schomerus, *The FZZ-Duality Conjecture -- A Proof*, arXiv:0805.3931;
- Creutzig--Hikida, *Higher rank FZZ-dualities*, arXiv:2010.14681;
- Deninger, *A dynamical systems analogue of Lichtenbaum's conjectures on special values of
  Hasse--Weil zeta functions*, arXiv:math/0605724;
- Raskutti--Mukherjee, *The Information Geometry of Mirror Descent*, arXiv:1310.7780;
- Patkowski, *On some Mellin transforms for the Riemann zeta function in the critical strip*,
  arXiv:1705.02256.

Search found no source combining literal Fermi--Mellin information force with a Deninger divisor
commutator. This is a bounded corpus-and-primary-source audit, not exhaustive-literature proof.

## Formal theorem

Module:
`GaloisForLFunctions.RHTower.FZZCigarParityDeningerInformationWardTransmutation`

The formalization proves unconditionally:

1. the piecewise Ward multiplier is strictly positive everywhere in the open strip;
2. HC37's force factors exactly as `(2 sigma-1)C(sigma)`;
3. the cup-traced Deninger reflect-gauge commutator is exactly the complexification of
   `1-2 Re(q)`;
4. each Xi divisor-flow eigenvalue is a literal source-first FZZ parity-Mellin mode;
5. on each divisor copy, FZZ force equals `-C` times Deninger Ward charge;
6. local FZZ equilibrium is equivalent to local reflect-gauge equivariance;
7. universal shared equilibrium is equivalent to RH.

## New route knowledge and remaining burden

HC38 proves FZZ-P nonlinear source mechanics and Deninger divisor-gauge mechanics do not present
independent RH gates. They are the same oriented charge on every actual divisor copy, related by a
strictly positive scalar. Thus any source law annihilating one annihilates the other, and no sign or
zero information is lost in translation.

This still does **not** prove charge cancellation. Remaining RH-strength core is one shared
producer: derive vanishing of the reflect-gauge commutator / Fermi information force from
source-native FZZ/GFZZ or arithmetic dynamics. The exact identity prevents further progress by
merely switching between these detector languages.

## Verification

- direct check:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarParityDeningerInformationWardTransmutation.lean`;
- targeted build:
  `lake build GaloisForLFunctions.RHTower.FZZCigarParityDeningerInformationWardTransmutation`
  passed (`8823` jobs);
- `#print axioms` on all 11 public theorems reported only `propext`, `Classical.choice`, and
  `Quot.sound`;
- formal lint reported no HC38 finding; repository-wide lint still reports unrelated pre-existing
  unreachable modules;
- module is wired into `GaloisForLFunctions.RHTower`; full umbrella build intentionally not run;
- frontier map remained read-only and untouched.

## Status

- [x] corpus-led conjecture frozen
- [x] dependency-closed paper proof
- [x] Lean formalization
- [x] direct check, targeted build, axiom/lint audit, umbrella wiring
- [x] bounded literature novelty audit
- [x] move to `3-formalized`
