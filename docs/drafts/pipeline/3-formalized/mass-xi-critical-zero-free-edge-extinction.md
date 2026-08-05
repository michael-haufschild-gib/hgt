# Mass-Xi critical zero-free edge extinction

- **Stage:** 3 — formalised in Lean 4
- **Date opened:** 2026-08-05
- **Parent:** `mass-xi-critical-corona-zero-density`
- **Target:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3

## Frozen conjecture C22

Put `A=a-1/2`, and assume the exact critical wall

\[
 a\ge2,\quad \sigma>0,\quad v>0,\quad v|u|\le A,
 \quad4\sigma v=1.
\]

For a Xi zero copy of Poisson height `R` in the critical corona
`A/2 <= R <= 2A`, let

\[
 d(R)=\operatorname{xiWardZeroFreeMargin}(R)
 =\frac{C_\Xi}{\log(R+9)^9}.
\]

Then the zero-free strip margin strengthens the critical phase defect by

\[
 M(-\sigma M+uK)
 \le-\sigma((A-R)^2+A)-4\sigma ARd(R).
\]

Using `M <= A+R+1/2` on the corona gives the uniform term bound

\[
 \|e^{-(\sigma+iu)m_a(p)}\|
 \le \exp\!\left(-\frac{3\sigma}{5}A,d(2A)\right).
\]

Therefore the complete critical Xi corona has envelope

\[
 C_\Xi'(1+r)\log(2+r)
 \exp\!\left(-\frac{3\sigma}{5}A,d(2A)\right),
 \qquad r=2A+2,
\]

and tends to zero as `A -> infinity`.  The literal von-Mangoldt source on
the exact wall also tends to zero after adding the already proved spectral
and Gamma tails.

## Higher-principle interpretation

Universal mass geometry exposes a finite diagonal corona at `4 sigma v=1`,
but actual Xi balance additionally requires zeros to approach the strip edge
at scale `O(1/A)`.  Corpus zero-free width is much larger than that scale.
Thus the universal critical survivor is arithmetically empty in the
co-moving limit: fixed-slope transition remains a geometric wall, while the
Xi information wall is a shrinking boundary layer below it.

## Hostile checks

- Use the full Xi divisor with exact multiplicities.
- No RH, cancellation, unproved zero-density, or finite verification.
- Do not infer extinction merely from packet finiteness; combine explicit
  packet count with explicit termwise zero-free decay.
- Preserve exact critical constants and literal Euler/Gamma transfer.

## Status

Fully proved unconditionally and formalised in Lean 4.

Lean module:

- `formal/GaloisForLFunctions/RHTower/XiMassCriticalZeroFreeEdgeExtinction.lean`

Principal declarations:

- `xiMass_critical_phase_defect_zeroFree`
- `norm_xiMassFamily_term_le_critical_zeroFree`
- `norm_xiMassCriticalDiagonalCoronaTraceC_le_zeroCount_mul_zeroFree`
- `tendsto_xiCriticalZeroFreeScale`
- `tendsto_xiMassCriticalZeroFreeEnvelope_zero`
- `norm_xiMassBottomPrimeIntegral_critical_le_zeroFreeEnvelope_add_tails`
- `tendsto_norm_xiMassBottomPrimeIntegral_critical_zero`

Verification:

- direct `lake env lean` passes;
- targeted module build passes: `9496/9496`;
- capstone `#print axioms` reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
