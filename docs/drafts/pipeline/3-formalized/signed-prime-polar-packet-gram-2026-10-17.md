# Signed prime–polar packet Gram transport

- **ID:** signed-prime-polar-packet-gram
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `1-in-progress/signed-prime-polar-transport-2026-10-17.md`
- **Contribution count:** one package; cumulative program count 2/100.
- **Paper:** `docs/reports/BiScaleUncertainty/SignedPrimePolarPacketGram.md`
- **Ledger:** `docs/reports/BiScaleUncertainty/SignedPrimePolarTransport-FACTS.md`

## Exact result

For every actual compact continuous real source, the finite-window prime–polar
packet P_L is compact continuous, with Q_L=∫P_L² equal to the full signed Gram
form, including both mixed terms. It satisfies Q_L≤M_L²h(0) and
|D_L(h(·+y)−h)|²≤2Q_L(h(0)−h(y)) for all real y. Annular averaging therefore
couples the original signed pairing directly to the exact Chebyshev work with
cost at most ηJ_annulus+Q_L/(2ηd²)∫annulus exp(−y/2)sinh y dy.
No grid blindness or extra analytic premise enters the main theorem.

## Analytic dependency closure

The polar packet's support lies in a bounded interval derived from source support.
The mixed product q(u)p(t)f(u+t) has compact support in ℝ², supplying actual Fubini.
Source translation chords and Cauchy–Schwarz produce the signed increment estimate.
Compact-rectangle Fubini and the existing scalar Young inequality give the annular
bound. The exact signed Gram representation proves the unsigned-budget comparison.
These are components of one substantial cancellation-sensitive transport package.

## Lean evidence

- `SignedPrimePolarPacket.lean`: actual packet, mixed representation, Gram identity,
  source-chord bound, and unsigned-mass comparison.
- `SignedPrimePolarGramTransport.lean`: exact annular interchange, comparison of
  costs, and direct signed Chebyshev coupling with reciprocal-weight penalty.
- Main endpoint: `SignedPrimePolar.abs_pairing_sub_chebyshevWork_le_packet_levy`.
- Both direct `lake --old env lean` leaf checks exit 0 with no diagnostics.
- Seven endpoint axiom reports contain only propext, Classical.choice, Quot.sound.
- Main signatures have only source and numerical parameters; imports are wired.
- Indexes refreshed; lint flags only two unrelated concurrent unwired modules:
  `CoprimeTentHilbertFrame` and `InfiniteCoprimeTraceProjection`.

## Boundaries

This is finite-window transport. Scalar support stabilization does not establish
stabilization of Q_L. No full-half-line packet, uniform arithmetic estimate,
external priority claim, or publication-ready status is asserted.

## Gates

- [x] Source-pure problem and corpus search.
- [x] Dependency-closed paper proof.
- [x] Direct Lean leaf verification, axiom reports, and umbrella wiring.
- [ ] Publication-ready external novelty and exposition audit.
