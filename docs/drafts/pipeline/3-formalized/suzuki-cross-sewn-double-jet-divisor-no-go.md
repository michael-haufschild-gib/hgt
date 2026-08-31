# Suzuki cross-sewn double-jet divisor no-go

- **ID:** C-SUZ-DJ2
- **Stage:** 3-formalized
- **Type:** PROVED / ROUTE-CLASS NO-GO
- **Source:** `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`; surviving distinct-channel producer
- **Statement:** At every Xi zero, analyticity of a division-free opposite-shift cross-sewn
  exterior is equivalent to second-order vanishing of its sewn characteristic, hence to one of
  three explicit source-divisor incidences.

## Goal and exact RH chain

Kill divisor-blind holomorphic distinct-channel regularization as a producer for the shared
Suzuki/HB/FZZ-P/PW-B/RBH Ward endpoint:

```text
Xi-independent distinct-channel source sewing
  -X-> holomorphic cross-sewn exterior at every nonreal point
  -> Suzuki FE-reflected wall Ward assembly
  -> shared HB/FZZ-P/PW-B/RBH Ward cancellation
  -> RH.
```

The first arrow is impossible unless the sources already encode each Xi zero through values or
first jets. Thus divisor-blind cross-sewing does not reduce the RH proof burden; it relocates the
Xi-divisor problem into the source channels.

## Gates

- [x] 0 -> 1: corpus-derived conjecture and exact RH chain frozen
- [x] 1 -> 2: dependency-closed paper proof and hostile audit
- [x] 2 -> 3: closed Lean certificate, umbrella wiring, targeted build, axiom and lint audits
- [ ] 3 -> 4: publication-ready exposition and independent priority review

## Internal frontier

Corpus search supplied the exact parent chain:

- `SuzukiOppositeShiftCrossSewnExterior` proves cross-sewing reduces arbitrary opposite channels
  to the zero-shift exterior with characteristic `P = 2 WPlus WMinus`.
- `SuzukiShiftedXiTargetFlatPencil` proves the target's meromorphic normal form has simple order at
  every Xi zero and gives trailing coefficient `z² / ord_z(XiC)`.
- `SuzukiExteriorPoleTomography` proves a nonvanishing analytic source leaves an exact simple pole.
- `Bottcher.analyticAt_simple_factor` factors any analytic zero as `(w-z) U(w)` with
  `U(z)=W'(z)`.

Targeted corpus searches found no theorem proving actual totalized target analyticity for arbitrary
Xi multiplicity, no wrong-center-value obstruction, no zero-characteristic first-jet
classification, and no cross-channel double-jet incidence law.

## External frontier

Suzuki's screw-function and canonical-system papers develop Weil-form, screw-function,
de Branges, and canonical-system RH equivalences, including
[arXiv:2606.09096](https://arxiv.org/abs/2606.09096),
[arXiv:2206.03682](https://arxiv.org/abs/2206.03682),
[arXiv:1204.1827](https://arxiv.org/abs/1204.1827), and
[arXiv:2301.00421](https://arxiv.org/abs/2301.00421). Removable-singularity and product-jet algebra
are classical. Targeted primary-source search through 2026-08-31 found no totalized
opposite-channel Suzuki theorem with the exact double-jet classifier below. Novelty is claimed for
this route-specific totalization obstruction and source-incidence classification, pending
independent priority review.

## C-SUZ-DJ2 — proved

For any `z` with `XiC z = 0`, arbitrary shift `eta`, and source functions analytic at `z`, put

```text
P = 2 * WPlus * WMinus,
J = WMinus * intervalPlus + WPlus * intervalMinus.
```

Then

```text
AnalyticAt
  (suzukiCrossSewnExterior eta WPlus WMinus intervalPlus intervalMinus) z
iff
P(z) = 0 and P'(z) = 0.
```

Equivalently, exactly one of the following possibly overlapping incidences holds:

```text
WPlus(z)=WMinus(z)=0,
WPlus(z)=WPlus'(z)=0,
WMinus(z)=WMinus'(z)=0.
```

The closed proposition `SuzukiCrossSewnDivisorBlindHolomorphicRegularization` existentially
quantifies every shift, Xi zero, and four analytic source functions while demanding failure of all
three incidences. Lean proves its negation with no premises.

## Complete paper proof

Let `T = suzukiShiftedXiTarget eta`. Its canonical meromorphic normal form `F` agrees with `T` on a
punctured neighborhood and has order one at `z`. Nonnegative order makes `F` analytic, and order
one forces `F(z)=0`. Since totalized `T(z)=0`, punctured equality upgrades to neighborhood equality;
hence the actual target `T`, not merely its normal form, is analytic at `z` with exact analytic
order one.

The existing trailing coefficient law then becomes an actual first-jet identity:

```text
T'(z) = z² / ord_z(XiC) != 0.
```

Factor `T(w)=(w-z)Q(w)` with `Q(z)=T'(z) != 0`. If analytic `W` vanishes at `z`, factor
`W(w)=(w-z)U(w)` with `U(z)=W'(z)`. On the punctured germ,

```text
T(w)^(-1) W(w) = U(w)/Q(w).
```

The right side tends to `W'(z)/T'(z)`, while the actual totalized left side has center value zero.
Both can be analytic at the center exactly when `W'(z)=0`. If `W(z) != 0`, existing pole
tomography already forbids analyticity. An analytic interval correction does not change this
criterion.

Cross-sewing identifies the exterior with the zero-shift remainder having characteristic `P` and
interval term `J`; therefore analyticity is exactly `P(z)=P'(z)=0`. The product rule and a complete
zero/nonzero case split yield the three channel incidences.

## No-go closure

- **Exact killing theorem:**
  `not_suzukiCrossSewnDivisorBlindHolomorphicRegularization`.
- **Exact local classifier:**
  `analyticAt_suzukiCrossSewnExterior_iff_channelIncidence`.
- **New target infrastructure:** actual target analyticity, exact analytic order one, and arbitrary-
  multiplicity jet `T'(z)=z²/ord_z(XiC)`.
- **Strongest positive survivor:** successful holomorphic sewing must split one Xi zero across both
  channel values or put a double zero into one channel.
- **Consequence:** surviving producer must derive divisor incidence, or leave the holomorphic local
  source class through singular/nonlocal data. Divisor-blind holomorphic cross-sewing is killed.
- **Status:** `[LEAN-PROVED]`.

## Lean formalization and audit

Module:
`GaloisForLFunctions.RHTower.SuzukiCrossSewnDoubleJetDivisorNoGo`.

Main declarations:

- `analyticAt_suzukiShiftedXiTarget_of_XiC_zero`
- `analyticOrderAt_suzukiShiftedXiTarget_eq_one_of_XiC_zero`
- `deriv_suzukiShiftedXiTarget_of_XiC_zero`
- `analyticAt_suzukiExteriorRemainder_iff_doubleJet`
- `analyticAt_suzukiCrossSewnExterior_iff_doubleJet`
- `analyticAt_suzukiCrossSewnExterior_iff_channelIncidence`
- `not_suzukiCrossSewnDivisorBlindHolomorphicRegularization`

Audit on 2026-08-31: direct `lake env lean` passed; targeted module build passed; umbrella import
wired; formal lint passed. `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound` for all main results, with no project axiom, `sorry`, `admit`, `opaque`, or `unsafe`
declaration.

## Log

- 2026-08-31 — C-SUZ-DJ2 frozen from corpus-derived cross-sewing and target-order laws.
- 2026-08-31 — arbitrary-multiplicity target regularity and exact first jet proved.
- 2026-08-31 — divisor-blind holomorphic distinct-channel producer killed; exact channel-incidence
  survivor formalized, wired, built, and audited.

