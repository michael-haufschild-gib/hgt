# Mass-Xi zero-free subcritical boundary layer

- **Stage:** 3 — formalized in Lean 4
- **Date opened:** 2026-08-05
- **Date formalized:** 2026-08-05
- **Parent:** `mass-xi-critical-zero-free-edge-extinction`
- **Target:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3

## Frozen conjecture C23

Put `A=a-1/2`, `d_A=xiWardZeroFreeMargin(2A)`, and assume

\[
 a\ge2,\qquad \sigma>0,\qquad
 2\sigma A\le |u|,
 \qquad |u|(1/2-d_A/2)\le2\sigma A.
\]

For each Xi corona point `A/2<=R<=2A`, zero-free width gives

\[
 M(-\sigma M+uK)
 \le-\sigma((A-R)^2+A)-\frac{|u|R d_A}{2}.
\]

The residual half-margin, `R/M>=3/20`, and `|u|>=2 sigma A` give termwise decay

\[
 \|e^{-(\sigma+iu)m_a(p)}\|
 \le \exp\!\left(-\frac{3\sigma}{20}A d_A\right).
\]

Outside the corona, the layer hypothesis and `d_A<=1/8` imply `7|u|<=32 sigma A`.
The exact quadratic comparison

\[
 (A+R)^2\le21\left(A^2+R^2-\frac{16}{7}AR\right)
\]

then gives a uniform `sigma/28` exponential tail.

## Explicit genuinely subcritical schedule

Define

\[
 u_*(A)=\frac{2\sigma A}{1/2-d_A/2}.
\]

Lean proves simultaneously:

- `u_*(A)>0` and `u_*(A)->+infinity`;
- `|u_*(A)|(1/2-d_A/2)=2 sigma A`;
- `2 sigma A<=|u_*(A)|`;
- `4 sigma A<|u_*(A)|`, so the schedule lies strictly below the universal geometric wall;
- the complete literal Euler/Gamma source tends to zero along `a=A+1/2`, `u=u_*(A)`.

Thus geometric and arithmetic walls differ.  Half the available zero-free width pays wall deficit;
half remains as decay and absorbs the exact `O(A log A)` corona multiplicity.

## Lean artifacts

Source:

- `formal/GaloisForLFunctions/RHTower/XiMassZeroFreeSubcriticalBoundary.lean`

Key declarations:

- `RHTower.xiMass_subcriticalBoundary_phase_defect`
- `RHTower.norm_xiMassFamily_term_le_subcriticalBoundary`
- `RHTower.xiMass_subcriticalBoundary_phase_le_outside_corona`
- `RHTower.norm_xiMassTraceC_sub_criticalDiagonalCoronaTraceC_le_subcriticalBoundary`
- `RHTower.norm_xiMassBottomPrimeIntegral_le_subcriticalBoundaryEnvelope`
- `RHTower.xiMassZeroFreeBoundaryFrequency_strictly_subcritical`
- `RHTower.tendsto_xiMassZeroFreeBoundaryFrequency_atTop`
- `RHTower.tendsto_norm_xiMassBottomPrimeIntegral_zeroFreeBoundary_zero`

Umbrella:

- `formal/GaloisForLFunctions/RHTower.lean`

## Verification

- `lake env lean GaloisForLFunctions/RHTower/XiMassZeroFreeSubcriticalBoundary.lean`: pass.
- `lake build GaloisForLFunctions.RHTower.XiMassZeroFreeSubcriticalBoundary`: pass, `[9497/9497]`.
- Axiom audit of defect, complete envelope, strict subcriticality, and extinction capstone:
  only `propext`, `Classical.choice`, and `Quot.sound`.
- No RH hypothesis, project-local axiom, `sorry`, `admit`, `opaque`, `unsafe`, or computation proof.

## Novel survivor

The critical wall is only a universal geometric wall.  Xi arithmetic shifts the extinction region
strictly below it by a quantified zero-free boundary layer.  The controlling invariant is a
margin budget: wall deficit consumes zero-free width, residual width creates decay.

## Successor conjecture

Half-margin split is not intrinsic.  For every fixed budget fraction `0<theta<1`, spending
`theta*d_A` on wall crossing should leave `(1-theta)*d_A` decay, still enough to absorb
`O(A log A)`.  The true boundary should be governed by residual margin mass
`A(1-theta(A))d_A` versus logarithmic corona entropy.

