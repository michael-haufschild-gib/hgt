# Observer-clock transmutation groupoid, neutral-charge anomaly, and properness law

- **ID:** ULF-TAFM-19
- **Stage:** 3-formalized
- **Type:** THEOREM / CLOCK GROUPOID / GLOBAL PROPERNESS CLASSIFICATION
- **Source:** ULF-TAFM-15 through ULF-TAFM-18; completed harmonic and Riesz source laws
- **Status:** `[PAPER PROOF COMPLETE] [LEAN FORMALIZED] [HOSTILE AUDIT PASSED] [NOT RH]`

## Statement

One source density forms different currents under different observer clocks. Nondegenerate clock
changes compose as a multiplicative groupoid, and every target response splits exactly into
boundary storage plus clock-acceleration work. Relative rate is uniformly bounded exactly when all
neutral unit dipoles remain uniformly bounded. Every unbounded rate amplifies neutral charges of
fixed `l1` mass without limit.

Literal completed prime--polar--Gamma source closes at zero in harmonic clock and becomes completed
Riesz moment in square-root clock. Harmonic-to-square-root relative rate grows at least linearly.
Thus RH is not generic clock-operator boundedness; it is exceptional arithmetic-source regularity
inside an unbounded transmutation domain.

## Gates

- [x] dependency-closed paper proof and hostile audit
- [x] generic clock groupoid and properness classification
- [x] literal harmonic/Riesz landing and clock-rate escape
- [x] scratch test, direct checks, narrow-import optimization, leaf builds, axiom audit, wiring
- [ ] source-specific exceptional-domain cancellation law
- [ ] RH selection consequence

## Formalization

See `observer-clock-transmutation-groupoid-neutral-charge-anomaly-and-properness-law-formalized.md`
and Lean modules `GaloisForLFunctions.HTGeometry.FormationClockTransmutation` and
`GaloisForLFunctions.RHTower.SuzukiHarmonicRieszClockTransmutation`.
