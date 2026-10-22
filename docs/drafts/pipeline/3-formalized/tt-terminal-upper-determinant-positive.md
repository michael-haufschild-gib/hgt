# Complete terminal upper determinant and actual-source positive tail

- **ID:** tt-terminal-upper-determinant-positive (C105–C111)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md, Route TT
- **Statement:** At load 10^13, the complete terminal upper-center determinant is strictly positive for every K>=5/4. It has degree34 and positive leading real coefficient. The complete actual-source upper determinant, divided by k^34, tends to that leading coefficient and is eventually strictly positive.

## Goal
Close the terminal-line and actual-tail determinant signs in the complete
source-quadratic route. Global actual last-entry positivity, the compact
actual upper determinant, compact gap propagation, controlled joining,
integrated/all-rank positivity, and RH remain open. Finite terminal-line
points are not asserted to be points of the actual source orbit.

## Gates
- [x] 0 → 1: exact complete source and a corpus-derived terminal specialization.
- [x] 1 → 2: exact polynomial certificate and asymptotic transfer below.
- [x] 2 → 3: seven direct leaf audits and all75 imported declaration axiom checks; no umbrella build.
- [ ] 3 → 4: standalone publication audit.

## Proof mechanism
Specialize the existing squared-drift polynomial chart at U=9,J=1/3,K=X.
The specialization is a ring homomorphism and carries the complete source
Lie derivative to (36X+12)d/dX. Weighted jets satisfy

    F_0=6X-1,
    F_(n+1)=(36X+12)F_n'+9(1-12X)F_n.

Retain every term of the reflected binomial moments through order14, then
form the full head, constant, border, and last native cofactors. Exact
specialization commutes with these constructions and with the weighted
sixth slope. Thus the resulting one-variable determinant is exactly the
upper-center determinant on this terminal line; no source moment or border
term is discarded.

The complete polynomial identity is certified by terminalUpperDeterminantNorm.
For c=10^13, translating X=5/4+y produces a positive constant plus
nonnegative monomials for y>=0; the kernel checks the exact normalization
and positivity. It also verifies degree34 and strictly positive real part
of the leading coefficient. No sampled sign or external coefficient
arithmetic enters either proof.

For the actual source, the established all-order-flat polynomial transfer
says actual evaluation minus terminal evaluation tends to zero. Since
k tends to infinity, multiplying this difference by k^(-34) still tends
to zero. The corpus polynomial asymptotic theorem gives the terminal
polynomial divided by k^34 tending to its leading coefficient. Adding
these limits proves the actual normalized limit. Its real part has a
strictly positive limit; k^34 is positive eventually, so the original
actual determinant is eventually strictly positive.

## Exact Lean capstones
Namespace HTGeometry.ThetaRatioWeightedSquare, module
GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalUpperDeterminantSigns:

- terminalUpperDeterminant_shift_pos
- terminalUpperDeterminant_boundary_pos
- terminalUpperDeterminant_degree
- terminalUpperDeterminant_leading_re_pos
- actualUpperDeterminant_normalized_tendsto
- actualUpperDeterminant_eventually_pos

The other six production modules retain the exact flow, specialization,
jet, moment, cofactor, and full-entry identities. They are wired into
RHTower.lean. No new axiom, placeholder, source-sign premise, numerical
experiment, or raised proof limit is used.

## Failed conjecture and positive survivor
The attempted strict negative value at K=5/4 reduced to False. Its failed
Lean declaration was rejected. The audited positive survivor is stronger
than the opposite endpoint sign: strict positivity on the whole terminal
ray, plus the actual-source positive tail above. This rejects that proposed
terminal obstruction; it does not prove actual compact positivity or RH.

## Audit record
- Direct commands: lake --old env lean -o <module.olean> <module.lean>, one at a time.
- Imported final audit: lake --old env lean /tmp/TTC110TerminalProductionAudit.lean.
- Logs: /tmp/tt_c110_terminal_production_audits/.
- All75 public declarations checked for axioms; only standard Lean axioms allowed.
- Scoped git diff --check passed.
- Repository lint30722 failed:27 unrelated umbrella omissions and one unrelated
  proof-debt declaration in ZetaOffLineWeightedDensity.lean. No new terminal
  module error; full repository lint remains non-green.
