# HB source-FE cocycle hyperbolic modulus orientation

- **ID:** HC78
- **Stage:** 3-formalized
- **Type:** THEOREM / EXACT SOURCE-WARD CLASSIFIER
- **Source:** read-only `rh-current-frontier-map.md` · shared HB/FZZ-P/PW-B/RBH source-Ward core

## Goal

Extract an unconditional positive orientation law from the literal nonlinear Birmingham--Mokhtari
source functional-equation cocycle.  Existing corpus proves this cocycle is involutive, never zero,
and real exactly on the critical line, but does not classify its modulus.  The frozen claim is the
exact trichotomy

`normSq(cocycle(q)) > 1  iff  Re(q) < 1/2`,

`normSq(cocycle(q)) = 1  iff  Re(q) = 1/2`,

`normSq(cocycle(q)) < 1  iff  Re(q) > 1/2`.

This is not a numerical estimate.  It is a source-faithful gain/loss orientation of every actual
Xi divisor copy and its FE reflection orbit.

## Gates

- [x] 0 → 1 in-progress: corpus and bounded primary-literature audit; exact statement frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready: independent mathematical review and broader novelty search

## Corpus audit

- `[CORPUS]` `ThetaCuspHawkingBMSourceFECocycleFixedPairingRigidity.lean` defines the literal
  unit-source FE cocycle, proves source transport and anti-linear involutivity, and classifies fixed
  bilinear-pairing preservation as an RH receiver.
- `[CORPUS]` `ThetaCuspHawkingBMSourceFERealCocycleReflectionOrbitExtinction.lean` proves cocycle
  reality exactly on the critical wall and exposes the carrier polynomial
  `P(s)=(1+s/2)(s/2)^2`.
- `[CORPUS]` `ThetaCuspHawkingBMGlobalLeftCoordinatePeierlsIncidence.lean` constructs exact global
  Peierls incidence; the remaining physical issue is source-fixed FE--Schwarz covariance.
- `[CORPUS]` `ThetaCuspHawkingSharedWardEnergySquare.lean` transports the common Ward zero locus to
  HB optical darkness, FZZ-P force balance, PW-B recoil balance, and RBH multiplicity balance.
- `[CORPUS NEGATIVE]` exact searches for source-FE cocycle norm, `normSq`, absolute value, unit-circle
  locus, and modulus orientation returned no theorem classifying this trichotomy.

## Bounded primary-literature audit

- Birmingham--Mokhtari, arXiv:hep-th/0609028, derives exact hypergeometric gravitational QNM
  frequencies for massless topological AdS black holes, but not the corpus nonlinear Xi-source FE
  cocycle or its modulus wall law.
- Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935, constructs conserved QNM bilinear
  forms and excitation projections for Kerr, but not this topological-AdS nonlinear source cocycle.
- Spiers--Pound--Moxon, arXiv:2305.19332, derives a nonlinear second-order Kerr Teukolsky source,
  not the present Xi-reflected carrier quotient.
- Sberna--Bosch--East--Green--Lehner, arXiv:2112.11168, studies third-order absorption-induced mode
  excitation, not an exact FE source-gain classifier.

This bounded audit found no published statement matching the frozen theorem as of 2026-08-28.  It
is not an exhaustive claim over all literature.

## Conjecture HC78-A: reflected carrier norm trichotomy

For every `s` in the open critical strip, let

`P(s)=(1+s/2)(s/2)^2 = s^2(s+2)/8`.

Then

`normSq(P(1-s)) > normSq(P(s)) iff Re(s)<1/2`,

with equality exactly at `Re(s)=1/2`, and the reverse strict inequality exactly at
`Re(s)>1/2`.

Paper mechanism: write `s=x+iy`.  Reflection changes the two positive factors by

`|(1-s)|^2-|s|^2 = 1-2x`,

`|3-s|^2-|s+2|^2 = 5(1-2x)`.

Both factors therefore move strictly in the same direction.  Since `0<x<1`, all factors are
strictly positive, so their product has the same strict trichotomy.  Equality cannot arise from a
cross-factor cancellation.

## Conjecture HC78-B: literal cocycle hyperbolic orientation

Off the critical wall the source is nonzero and exact source transport gives

`kappa(q) = source(reflect q) / conj(source(q))`.

The reflection-invariant helicity mixing coefficient cancels in squared modulus, while the
quadratic Einstein carrier is exactly `P`.  Hence

`normSq(kappa(q)) = normSq(P(1-q))/normSq(P(q))`.

The denominator is positive throughout the open strip.  HC78-A therefore gives the frozen
trichotomy.  On the wall the source vanishes and the corpus definition fixes `kappa=1`, closing the
equality case without division by zero.

## Hostile checks

- Do not infer modulus orientation merely from cocycle involutivity; arbitrary involutive
  anti-linear cocycles need not orient one half-strip.
- Do not divide at the critical wall, where the literal source vanishes by construction.
- Preserve the exact nonlinear carrier `P`; dropping `(s+2)` would erase one independently aligned
  positive factor.
- Prove both strict directions and the equality case.  A one-sided estimate is insufficient.
- No RH premise, numerical zero verification, positivity continuation, fitted kernel, or new axiom.

## Expected survivor and route impact

If proved, the cocycle itself supplies a source-native positive hyperbolic gain: FE reflection
inverts it, the unit circle is exactly the critical wall, and its expanding/contracting direction
recovers horizontal Xi orientation.  This strengthens the current phase/reality receiver and gives
the shared HB/FZZ-P/PW-B/RBH descent a literal positive source coordinate.  It does not by itself
prove the global Ward identity; next burden is to show the fixed physical Peierls/Einstein action
uses this gain rather than the unconditionally transported pairing.

## Closure

Status: `[NEW] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY-AUDIT-PASSED-BOUNDED]`.

Formal module:
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFECocycleHyperbolicModulusOrientation`.
It is imported by `GaloisForLFunctions.RHTower`.

The carrier trichotomy is proved by
`normSq_hbXiPeierlsUnitSourceCarrierPolynomial_lt_reflect_iff`,
`normSq_hbXiPeierlsUnitSourceCarrierPolynomial_reflect_lt_iff`, and
`normSq_hbXiPeierlsUnitSourceCarrierPolynomial_reflect_eq_iff`. The literal source-cocycle lift is
proved by `one_lt_normSq_hbXiPeierlsUnitSourceFECocycle_iff`,
`normSq_hbXiPeierlsUnitSourceFECocycle_lt_one_iff`, and
`normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff`. Reflection reciprocity is exact in
`normSq_hbXiPeierlsUnitSourceFECocycle_reflect_mul`; universal unit gain is equivalent to RH in
`forall_normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_rh`. The same pointwise unit-gain locus is
transported unconditionally to HB optical power, Deninger Ward charge, FZZ-P information force,
every PW-B balance, and canonical-copy RBH balance.

Verification on 2026-08-28:

- `lake env lean` on module: pass.
- Target-only `lake build` on module: pass, 12,017/12,017 jobs.
- `#print axioms` on carrier orientation, pointwise/unit-universal cocycle laws, FZZ-P receiver, and
  RBH receiver: only `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint: no HC78 finding; repository-wide gate remains red only for unrelated pre-existing
  unreachable modules in RHTower and HTGeometry.
