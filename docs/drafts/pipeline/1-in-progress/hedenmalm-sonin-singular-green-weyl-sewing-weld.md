# Hedenmalm--Sonin singular Green/Weyl sewing weld

- **Label:** `P-G135`
- **Route:** P
- **Parents:** `P-G134`, `RiemannSingularGreenHodgeAdmissionLaw`, `DeningerCalderonWittSingularGammaTransgression`
- **Status:** theorem proved in Lean; umbrella integration complete

## Conjecture tested

P-G134 isolates reciprocal scalarization as missing producer.  The singular Calderón--Witt Green
source already has exact reciprocal reflection sewing.  Test whether its two source sewing legs
provide a genuinely new mechanism, or whether Weyl selection of the decaying leg recreates the
same Sonin cusp and reciprocity defect.

## Scientific decision gate

- **Success:** derive the lower sewing cost from literal prime-clock Gamma transport and identify
  it coefficient-exactly with Sonin cancellation, including Riemann boundary fracture.
- **Failure:** an abstract reciprocal pair or a restatement of P-G134 without actual source sewing
  coefficients is theatre.
- If welded, retire singular Green sewing as an independent escape; only an oriented source law
  forcing both non-amplification and reciprocity can remain.

## Prior-research audit

- 2026-08-13 — `RiemannSingularGreenHodgeAdmissionLaw` proves the two oriented Calderón--Witt
  sewing costs multiply to one and global Hodge admission is RH-equivalent.
- 2026-08-13 — P-G134 proves a reflection-even exact cancellation scalar cannot also be reciprocal
  off the critical wall.
- 2026-08-13 — No prior theorem computes Weyl lower envelope of actual singular sewing or welds it
  to Hedenmalm--Sonin aperture escape.

## Conjecturing log

- 2026-08-13 — C1 proved in scratch: lower of two actual reciprocal sewing costs is
  `exp(-2 |a| (log p+log q)(n+1))`.
- 2026-08-13 — C2 proved in scratch: this is exactly `soninEscapeCancellingGaugeModulus` with
  source coefficient `2(log p+log q)(n+1)`.
- 2026-08-13 — C3 proved in scratch: lower cost is reflection-even and its reflected product is
  `exp(-4 |a| (log p+log q)(n+1))`, unit exactly at `a=0`.
- 2026-08-13 — C4 proved in scratch: at Riemann boundary fracture, lower sewing is Sonin modulus
  with coefficient `4(log p+log q)(n+1)` in horizontal distance `Re(rho)-1/2`.
- 2026-08-13 — C5 proved in scratch: unit Weyl reciprocity defect at all actual Xi support points
  is equivalent to RH for every fixed prime pair and valuation depth.

## Verification log

- 2026-08-13 — Direct foreground check passed:
  `lake env lean GaloisForLFunctions/RHTower/HedenmalmSoninSingularGreenWeylSewingWeld.lean`.
- 2026-08-13 — Imported by `GaloisForLFunctions/RHTower.lean`.
- 2026-08-13 — Exact module build passed:
  `lake build GaloisForLFunctions.RHTower.HedenmalmSoninSingularGreenWeylSewingWeld`
  (`12963/12963`).
- 2026-08-13 — Axiom audit passed for every new theorem; dependencies are exactly `propext`,
  `Classical.choice`, and `Quot.sound`.

## Result and pivot

- Singular Green sewing and Sonin aperture escape are two realizations of one determinant-one
  Cartan/Weyl mechanism.  They cannot be combined as independent constraints.
- Actual source geometry supplies reciprocity only before scalarization.  Selecting the decaying
  orientation on both reflected fibres supplies exact cancellation but creates strict product
  loss off wall.
- Remaining producer must force an oriented no-amplification law on the raw reciprocal pair, or a
  source-canonical scalarization retaining orientation.  Ordinary Hodge admission merely restates
  this as an RH-equivalent condition; its unconditional construction remains open.
