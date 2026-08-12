# Source-horizontal adaptive chirality–Wold cubic bridge

- **ID:** SH-ACWC-C12
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean); one source annihilation law unresolved
- **Source:** Frankenstein seam joining adaptive observer chirality, Gamma-Bockstein/Wold neutral
  jets, Route-T prime-clock residual, and Xi multiplicity-labelled reflection

## Conjecture attacked

Adaptive KL orientation and Route-T cubic horizon might be unrelated receiver packages. If so,
combining them adds no leverage.

## Verdict

**FAILED EXACTLY; POSITIVE SURVIVOR FORMALIZED.** They are one signed coefficient class. For every
prime `p`, Lean proves

```text
A_p := ∂³_t sourceHorizontalPrimeAdaptiveKLChirality_p(0)
W_p := ∂³_t sourceHorizontalWoldPrimeDeformation_p(0)
A_p = G_p W_p
G_p = 8p^5/((p-1)^2(p+1)^3)
1 ≤ G_p ≤ 32.
```

Hence `A_p=0 ↔ W_p=0`, with quantitative comparison `W_p ≤ A_p ≤ 32W_p`. Gauge keeps prime labels
and neither erases nor compactly smooths coefficients.

## Aggregate theorem

Define finite adaptive-information moment

```text
I_N = sum_{n≤N} G_{p_n}^{-1} A_{p_n}.
```

Then unconditionally

```text
I_N = sourceHorizontalWoldNaturalCubicMoment(p_N).
```

After subtracting terminal holonomy `(log p_N)^3`, adaptive residual coefficient equals Route-T
residual coefficient term-for-term and

```text
(I_N-(log p_N)^3)/(log p_N)^3 → -2/3.
```

For each `XiZeroCopy q`, multiplying by its centered rate cubed produces exactly existing Wold
prime-clock response. Line conjugation negates response; limit vanishes exactly when copy lies on
critical line. Divisor multiplicity and both orientations survive.

## Higher universal principle

Metric routes measured distance, information route measured orientation, Route T measured cofinal
arithmetic residual. Cubic bridge shows these are not three obstacles. Frozen/adaptive Fisher
curvature is even metric shell; directed KL cubic is its odd local current; Wold prime-clock
`-2/3` remnant is same current after ordered all-prime transport and terminal-holonomy subtraction.

Earlier stuck points were shadows of one principle: reflection pairing kills odd current only after
it has already erased which orientation failed to land. Producer must equate terminal holonomy and
adaptive information current on one oriented source carrier before reflection pairing.

## Exact remaining producer

Prove from completed arithmetic source—not Xi-zero assumption—that one-orientation terminal
holonomy current equals inverse-gauged adaptive information current at cofinal horizon. This forces
adaptive residual limit to zero. Formal `-2/3` law then forces every retained centered rate to zero.

Rejected substitutes:

- reflected-pair cancellation: automatic for every odd response;
- same-source observer conditional invariance: already equivalent to neutrality;
- bounded label-blind scalarization: cannot distinguish signed carrier;
- local primewise vanishing: false; each cubic coefficient is positive.

## Formal module

`formal/GaloisForLFunctions/RHTower/SourceHorizontalAdaptiveFisherChiralityWoldCubicBridge.lean`

Key capstones:

- `sourceHorizontalAdaptiveChiralityWoldCubicGauge_mul_woldCubic`
- `sourceHorizontalAdaptiveChiralityWoldCubicGauge_bounds`
- `sourceHorizontalAdaptiveChiralityCubic_eq_zero_iff_woldCubic_eq_zero`
- `sourceHorizontalAdaptiveChiralityNaturalCubicMoment_eq_wold`
- `sourceHorizontalAdaptiveChiralityResidualCubicCoefficient_eq_wold`
- `tendsto_sourceHorizontalAdaptiveChiralityResidualCubicCoefficient_normalized`
- `sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse_eq_wold`
- `sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse_reflection`
- `sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicLimit_eq_zero_iff`

## Gates

- [x] conjecture attacked rather than assumed
- [x] dependency-closed paper algebra
- [x] unconditional direct Lean check
- [x] targeted module build
- [x] capstone axiom audit
- [ ] external novelty audit
- [ ] pre-zero arithmetic source annihilation theorem
- [ ] RH

## Log

- 2026-08-12 — Third adaptive chirality jet calculated exactly.
- 2026-08-12 — Explicit gauge and `[1,32]` coefficient-faithful bounds proved.
- 2026-08-12 — Finite moment, cofinal `-2/3`, Xi reflection, and critical-line endpoint transported.
- 2026-08-12 — Targeted module build passed; capstones depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
