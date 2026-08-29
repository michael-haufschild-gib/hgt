# LI completed-Abel finite critical-prefix oscillation no-go

- **ID:** LI-CAB7.NG
- **Stage:** 3-formalized
- **Type:** `[FALSIFIED] [LEAN-PROVED]` route no-go
- **Source:** LI-CAB4--LI-CAB6 completed-Abel current; Hardy critical-locus reserve; finite simultaneous phase recurrence
- **Statement:** Every nonempty finite packet of critical-line Xi copies has completed-Abel adjacent-current sums of both strict signs cofinally in the Li mode.

## Goal

Kill the finite-prefix producer for LI-CAB5:

`termwise or finite-prefix all-mode current nonnegativity`
`=>` nonnegative full current by monotone/dominated passage
`=>` LI-CAB5
`=>` LI-CAB3 completed endpoint positivity
`=>` RH.

The theorem does not kill LI itself. It proves that any viable LI orientation theorem must be an
essentially infinite cancellation law; no nonempty critical-line truncation can carry the sign.

## Corpus frontier

- `[CORPUS]` `liEvenCrossUnitFluxQuotient_eq_oddChebyshev` gives the exact flux polynomial
  `-(n+1)(1-X)U_(2n+1)(2X-1)`.
- `[CORPUS]` `liEvenCrossSquareMassAdjacentFlux_eq_unitFluxQuotient` identifies each actual Xi atom.
- `[CORPUS]` `xiShiftedReciprocalSquare_pos_real_of_copy_re_eq_half` makes every critical-line atom a positive real shifted node.
- `[CORPUS]` `nonempty_xiCriticalLineResolventCopy_of_hardy` supplies such an atom unconditionally.
- `[CORPUS]` `exists_fin_simultaneous_two_pi_phase_approximation_delayed_quantitative` gives one delayed recurrence clock for every finite phase packet.
- `[CORPUS]` `XiShiftedAtomwisePositivityNoGo` kills universal affine-square positivity off the critical line, but does not treat the actual LI adjacent-current polynomial on the critical line.

## Literature frontier

Bombieri--Lagarias and Lagarias express Li coefficients as zero sums/Weil functionals. Voros's
Keiper--Li analyses explicitly emphasize oscillatory individual-zero contributions and global
cancellation. No audited source states the squared-mass completed-Abel derivative theorem here:
cofinal sign oscillation for every finite multiplicity-exact critical-line packet. The underlying
Chebyshev identity and simultaneous recurrence are classical. Priority claim is limited to the
corpus-specific LI route classification and remains `[NOVELTY UNVERIFIED]` pending expert review.

Primary sources checked:

- E. Bombieri and J. C. Lagarias, *Complements to Li's Criterion for the Riemann Hypothesis*, JNT 77 (1999), 274--287.
- J. C. Lagarias, *Li coefficients for automorphic L-functions*, Ann. Inst. Fourier 57 (2007), 1689--1740.
- A. Voros, *Discretized Keiper/Li approach to the Riemann Hypothesis*, Exp. Math. 29 (2020), 307--321.
- A. Voros, *From asymptotic to closed forms for the Keiper/Li approach to the Riemann Hypothesis*, 2022.

## Conjecture and paper proof

Fix `0<v<=1/4`, `d>0`, and a packet `q : Fin d -> XiCriticalLineResolventCopy`. For mode
`m=n+1`, write the shifted reciprocal atom as `x_i>0`, put `y_i=v*x_i`, and define

`theta_i = arccos(2y_i-1)`, `omega_i = 2*pi-2*theta_i`.

The unconditional Xi height gap gives `0<y_i<1/2`, hence `0<omega_i<pi`. The Chebyshev sine law
then gives the exact normalized packet current

`Phi_packet(n)/(n+1) = F(n+1) = sum_i a_i sin((n+1)omega_i)`,

where `a_i=x_i(1-y_i)/sin(theta_i)>0`. Thus `F(1)>0`.

Let `delta=F(1)` and `A=sum_i a_i`. Choose phase resolution with
`2*pi*A/(Q+1)<delta/2`. Delayed simultaneous recurrence supplies arbitrarily late `k` and integers
`r_i` with `|k*omega_i-2*pi*r_i|<=2*pi/(Q+1)`. Periodicity and the unit Lipschitz bound for sine give

`|F(k+1)-F(1)| < delta/2`,

`|F(k-1)+F(1)| < delta/2`.

Taking the delay at least two yields cofinally late positive mode `k+1` and negative mode `k-1`.
Every dependency is supplied by the cited corpus; no zero ordinate or numerical computation enters.

## Hostile conjecturing loop

1. `[CONJECTURE]` One critical atom changes sign in the mode.
2. `[REDISCOVERED]` This is the elementary Chebyshev oscillation already implicit in classical Li zero-sum formulas; it does not classify finite truncation.
3. Stronger `[CONJECTURE]` Every nonempty finite critical packet has both signs cofinally.
4. The one-atom objection no longer kills it: simultaneous recurrence synchronizes the complete finite packet near its positive mode and its odd reflection, regardless of rational relations or repeated atoms.
5. Hostile verdict: `[LEAN-PROVED]`; the production theorem closes the exact route-kill statement.

## No-go closure

- **Exact killing theorem/mechanism:** delayed simultaneous phase recurrence returns every finite packet near its mode-one configuration and near its odd reflection, forcing both signs.
- **Strongest positive survivor:** normalized finite critical-prefix current is an explicit positive-amplitude sine pencil with recurrent sign oscillation.
- **New insight:** any LI-CAB5 proof must extract orientation from the complete infinite divisor through nonuniform tail cancellation. Termwise positivity, fixed finite packets, eventual finite-prefix positivity, and positive dominated passage are impossible.
- **Status:** `[LEAN-PROVED]`; finite-prefix and termwise positivity producer retired.

## Main Lean theorems

- `liEvenCrossSquareMassAdjacentFlux_criticalAtom_sine`
- `cofinal_both_signs_finitePositiveSinePacket`
- `cofinal_both_signs_liEvenCrossCriticalPacketCurrent`
- `exists_hardyCritical_liEvenCrossAdjacentFlux_neg`
- `not_all_hardyCritical_liEvenCrossAdjacentFlux_nonnegative`
- `not_all_nonempty_finiteCriticalPacket_currents_nonnegative`

Lean module:
`GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelFiniteCriticalPrefixOscillationNoGo`.

## Formal audit

- Production-file check with `lake env lean`: passed.
- Targeted module build: passed in 46 seconds, 12,989 jobs.
- Axiom audit of the Chebyshev identity, atom normal form, recurrence theorem, packet theorem, and
  both closed capstones: `propext`, `Classical.choice`, `Quot.sound` only.
- Formal lint reports only pre-existing unrelated umbrella-reachability failures; this module is
  wired into `GaloisForLFunctions.RHTower` and is not among them.
- No numerical computation or zero table enters the proof.

## Gates

- [x] 0 -> 1 in-progress: corpus origin, external audit, hostile loop, and RH chain fixed
- [x] 1 -> 2 fully-proven: dependency-closed paper proof above
- [x] 2 -> 3 formalized: exact Lean theorem, production check, targeted build, axiom audit, umbrella wiring
- [ ] 3 -> 4 publication-ready

## Log

- 2026-08-29 — One-atom conjecture rejected as rediscovered; finite-packet cofinal oscillation survives and is paper-proved by delayed simultaneous recurrence.
- 2026-08-29 — Formalized exact positive-amplitude sine normal form and cofinal two-sign recurrence. Closed Hardy capstones refute atomwise and universal nonempty finite-prefix all-mode positivity.
