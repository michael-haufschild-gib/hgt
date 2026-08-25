# Route P cubic genuine two-sheet contact-seven wall

- **ID:** `CUBIC-GENUINE-TWO-SHEET-CONTACT-SEVEN`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** completed-Xi cubic irregular-microlocal Riemann--Hilbert route
- **Statement:** A genuinely equivariant two-sheet, one-Stokes-orbit sphere landing has highest-difference numerator at least `7`; an explicit cyclic Puiseux spectrum with numerator exactly `7` lands, so the genuine wall is sharp.

## Goal

Replace abstract orbit grouping by actual cyclic Puiseux continuation and prove first negative
completed-Xi landing chamber is inhabited.  Determine exact smallest integral contact allowed by
both the cubic landing sign and two-sheet monodromy.

## Gates

- [x] 0 -> 1 in-progress: exact claim, corpus audit, genuine-orbit correction, hostile attack
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: exact Lean theorem, targeted check, new-declaration axiom audit
- [ ] 3 -> 4 publication-ready: standalone paper and independent priority review

## Exact theorem `[PROVED HERE]`

Let `f` be a two-sheet coefficient spectrum on cover degree `N=2`, with genuine cyclic
equivariance, primitive root `zeta`, and monodromy interchanging sheets `0` and `1`.  Let `d(f)` be
the coefficient-generated one-orbit local datum at the unique marked point of the sphere, and put

`k(f) = contactNumerator_f(0,1)`.

Then:

1. every completed-Xi cubic unit landing for `d(f)` forces `7 <= k(f)`;
2. there is an explicit equivariant spectrum `f_7` with only top exponent `7/2`, monodromy
   swapping the two branches, primitive root `-1`, and coefficients `+1,-1` at numerator `7`;
3. `k(f_7)=7`, and the completed-Xi cubic unit landing fibre for `d(f_7)` is nonempty.

Thus `7/2` is the exact minimal normalized contact in the genuine two-sheet cyclic sector.  The
abstract real wall is `5/2`; cyclic continuation removes the integral candidate `3=6/2`, because
even contact would be monodromy-invariant rather than sheet-swapping.

## Internal frontier

- `[CORPUS]` abstract two-branch classification gives landing iff `5N<2k`; at `N=2` this only gives
  `k>=6` and does not impose genuine analytic continuation.
- `[CORPUS]` `EquivariantFinitePuiseuxFamily` records actual cyclic coefficient equivariance, and
  `toPuiseuxOrbitCoareaDatum` quotients by genuine continuation orbits.
- `[CORPUS]` no theorem combines two-sheet equivariance with the cubic landing wall, excludes
  numerator `6`, constructs the numerator-`7` formal type, or proves a genuine landing fibre
  inhabited.
- Naive `N=1` multibranch witnesses were rejected: unramified continuation fixes each branch and
  cannot justify one genuine orbit.

## External frontier

- Arinkin's irregular rigidity theory and the irregular Deligne--Simpson literature treat
  existence/rigidity for prescribed formal types, not this completed-Xi scalar target.
- Ramified toral and isoclinic classifications allow genuine cyclic formal data in restricted
  settings but do not state the `7/2` completed-Xi landing wall.
- The parity/continuation mechanism is standard formal-type algebra `[BRIDGE]`; the sharp
  completed-Xi consequence and explicit landing are `[NOVELTY UNVERIFIED]`.

## Hostile attack

- **Fake orbit risk:** excluded by starting from `EquivariantFinitePuiseuxFamily` and requiring the
  monodromy permutation to exchange the two sheets.
- **Contact exponent validity:** coefficient injectivity gives distinct sheets, and the existing
  contact-attainment theorem supplies actual coefficient inequality at numerator `k`.
- **Root ambiguity:** only `zeta^2=1` is needed for necessity; no classification of primitive
  square roots is used.
- **Boundary `k=6`:** equivariance at the highest differing coefficient would multiply it by
  `(zeta^-1)^6=1`, so swapped sheet coefficients would agree, contradiction.
- **Sufficiency:** explicit `f_7` has coefficient vectors differing only at numerator `7`; its
  swap equivariance is literal and the abstract sharp iff gives landing because `10<14`.
- **Circularity:** no Xi-zero location or RH statement enters, only unconditional cubic residual
  negativity already used by the landing classification.
- **Remaining realism gap:** this constructs genuine cyclic formal Puiseux data and an abstract
  microlocal charge, not a global meromorphic connection or arithmetic source-to-charge map.

**Preliminary verdict:** `SURVIVES PRELIMINARY ATTACK`; novelty remains unverified.

## Dependency-closed proof `[PAPER-PROVED]`

Write `k=k(f)`.  Any landing for `d(f)` satisfies the already proved integral two-branch wall

`5*2 < 2k`.

Hence `6<=k`.  Let `e` be the coefficient coordinate with numerator `k`.  Because the branches are
distinct, their coefficients at `e` differ.  Equivariance and the sheet swap give

`coeff_1(e) = (zeta^-1)^k coeff_0(e)`.                                `(1)`

Assume `k=6`.  Primitivity of `zeta` of order two gives `zeta^2=1`, hence
`(zeta^-1)^6=((zeta^-1)^2)^3=1`.  Equation `(1)` then says
`coeff_1(e)=coeff_0(e)`, contradicting contact attainment.  Therefore `k!=6`, and `6<=k` implies
`7<=k`.

For sharpness, take cover degree `2`, exponent window `0,...,7`, primitive root `zeta=-1`, and
monodromy swapping the two sheets.  Set every coefficient below numerator `7` to zero and the top
coefficients to `+1` and `-1`.  Constant terms vanish, coefficient vectors are injective,
`monodromy^2=1`, and at exponent `e` the factor `(-1)^e` makes the family equivariant; in
particular the odd top coefficient is exchanged.  The two vectors differ at numerator `7` and
nowhere higher, so `k=7`.  The integral landing criterion becomes `10<14`, giving an explicit
nonempty completed-Xi cubic landing fibre.  No paper-proof dependency remains.

## Lean formalization `[LEAN-PROVED]`

File:
`formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetContactSeven.lean`

- `routePPrimitiveGammaJuliaStokesGenuineTwoSheetSingleOrbitDatum` retains coefficients from a
  genuinely equivariant two-sheet spectrum in the one-orbit landing model.
- `routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetUnitLanding_contactNumerator_seven_le`
  combines the abstract landing wall with order-two coefficient equivariance to exclude numerator
  `6` and prove `7<=k`.
- `routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily` constructs the cyclic spectrum
  from the canonical primitive square root and its exponent-seven orbit.
- Its monodromy theorem proves sheet exchange, and its contact theorem proves numerator exactly
  `7`.
- `nonempty_routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenUnitLandingFiber` proves the
  explicit genuine negative chamber is inhabited.

Direct targeted module elaboration passed.  A `/tmp` `#print axioms` audit of exactly these six
public declarations returned `[propext, Classical.choice, Quot.sound]` for each.  Area umbrella
import was added without building the umbrella.  No repository-wide lint or full build was run.

## No-go closure / positive survivor

- **Killed candidate:** normalized contact `3=6/2`; it cannot exchange two sheets under order-two
  continuation.
- **Positive survivor:** genuine numerator-`7` cyclic formal type with a constructed landing.
- **New insight:** abstract contact wall `5/2` discretizes to sharp genuine wall `7/2`, not `3`.
- **Open core left:** actual meromorphic-connection realization and fixed arithmetic source
  landing.

## Log

- 2026-08-25 -- naive unramified witness rejected; genuine two-sheet contact-seven theorem
  isolated, hostile-tested, dependency-closed, and promoted to Stage 2; exact necessity and sharp
  equivariant witness formalized; targeted elaboration and six-declaration axiom audit passed;
  promoted to Stage 3.
