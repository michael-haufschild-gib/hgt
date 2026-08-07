# Suzuki rectangular Ward-defect semiboundedness — formalization certificate

- **Stage:** 3-formalized
- **Paper proof:**
  `./suzuki-rectangular-ward-defect-semiboundedness.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiRectangularWardDefectBoundedness.lean`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC BRIDGE]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Formalized theorem

For fixed `L>0`, arbitrary source energy `E(n)>=0`, and

```text
Delta_L(n)=Re xiScrewWindowCurvature(L,log n)-E(n),
```

Lean proves:

```text
Delta_L eventually bounded below on admissible logarithmic nodes -> RH.
```

It specializes automatically to `E(n)=||R(n)||^2` in any seminormed additive group.  Lean also
proves hostile converse:

```text
not RH -> for every E(n)>=0, Delta_L is cofinally unbounded below.
```

Key declarations:

```text
suzukiRectangularWardDefect
riemannHypothesis_of_suzukiRectangularWardDefect_eventually_bddBelow
riemannHypothesis_of_suzukiRectangularHilbertWardDefect_eventually_bddBelow
not_riemannHypothesis_implies_suzukiRectangularWardDefect_cofinally_unbounded_below
not_riemannHypothesis_implies_suzukiRectangularHilbertWardDefect_cofinally_unbounded_below
```

This changes unresolved source theorem from exact Gram equality to uniform lower semiboundedness
of explicit mixed prime--Gamma Ward defect.  Bound itself remains conjectural; RH is not yet
proved.

## Integration and verification

- imported by `GaloisForLFunctions.RHTower` umbrella;
- imported and summarized in `RiemannHypothesisSOTA2026`;
- direct source check:
  `lake env lean GaloisForLFunctions/RHTower/SuzukiRectangularWardDefectBoundedness.lean`;
- targeted SOTA build: `9451/9451` jobs;
- axiom audit: `propext`, `Classical.choice`, `Quot.sound` only;
- forbidden declaration scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.

