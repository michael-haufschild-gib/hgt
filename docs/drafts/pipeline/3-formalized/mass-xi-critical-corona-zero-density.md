# Mass-Xi critical corona zero-density law

- **Stage:** 3 — formalised in Lean 4
- **Date opened:** 2026-08-05
- **Date formalised:** 2026-08-05
- **Parent:** `mass-xi-critical-oblique-diagonal-corona`
- **Target:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3

## Frozen conjecture C21

Let `S` be any finite packet of Xi zero copies supported in the closed disc
`closedBall 2 r`.  Then multiplicity copies can be grouped fiberwise over the
Xi divisor support, and their number is bounded by the exact divisor mass:

\[
 |S|\le \operatorname{xiBallOrderSum}(2,r).
\]

For the critical diagonal corona at mass `a >= 2`, every supporting Xi zero
lies in the explicit disc of radius

\[
 r=2(a-1/2)+2.
\]

Consequently the corpus zero-count theorem gives

\[
 |\mathcal C_a|\le C_\Xi(1+r)\log(2+r),
\]

and the literal von-Mangoldt source on `4 sigma v = 1` is bounded by this
`O(r log r)` envelope plus fixed spectral and Gamma constants.

## Result

Conjecture proved unconditionally.  The proof does not forget zero
multiplicity: it identifies each `XiZeroCopy` fiber cardinality with the
analytic order, embeds packet support into the finite divisor support of the
disc, and compares the resulting nonnegative divisor sums exactly.

This sharpens the independently formalised quadratic capacity estimate.  It
also changes the open core: growth of the complete critical source is no
longer mysterious.  At this stage, cancellation inside one moving finite
chirp packet was the only apparent survivor.  Successor card
`mass-xi-critical-zero-free-edge-extinction` proves a stronger fact: corpus
zero-free width extinguishes that packet termwise, so no critical
cancellation resource remains for Xi.

## Lean artifacts

- `formal/GaloisForLFunctions/RHTower/XiMassCriticalDiagonalPrimeCoronaGrowth.lean`
- `formal/GaloisForLFunctions/RHTower/XiMassCriticalDiagonalPrimeCoronaZeroDensity.lean`

Principal declarations:

- `xiMassCriticalDiagonalCorona_card_le_quadratic`
- `card_le_xiBallOrderSum_of_support_mem`
- `xiMassCriticalDiagonalCorona_support_mem_closedBall`
- `xiMassCriticalDiagonalCorona_card_le_zeroCountEnvelope`
- `norm_xiMassBottomPrimeIntegral_critical_le_zeroCountEnvelope`

## Verification

- Direct `lake env lean` passes.
- Targeted module build passes: `9422/9422`.
- `#print axioms` for packet counting and source capstone reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Global formal lint reaches corpus audit and reports no forbidden declaration
  in these modules; current exit is caused by two unrelated concurrently added
  modules missing from their area umbrellas.
