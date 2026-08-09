# Mass-shifted squared-factorial root-threshold no-go (2026-08-09)

Context: attack on `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 after `mem:research/mass_shifted_krein_volterra_global_budget_2026_08_09`.

## Exact positive survivor

For finite carrier weights/nodes and squared-factorial moments
`s_k = (Σ_i w_i t_i^k)/(k!)²`,
`Σ_j c_j s_(r+j) = Σ_i w_i t_i^r Psharp_(r,c)(t_i)`,
where `Psharp_(r,c)(t)=Σ_j c_j t^j/((r+j)!)²`.
Thus first crossing is literal weighted mass balance across endogenous roots of actual null flag.

For exponential mixture density
`rho(t)=Σ_i w_i a_i⁻¹ exp(-t/a_i)`,
Lean proves
`∫_(0,∞) t^k rho(t)dt=k!Σ_iw_i a_i^k`
and exact adaptive integral identity. This is an actual Lebesgue integral theorem using corpus Gamma primitives.

## Conjecture 29 FAIL: root geometry

Atomic carriers:
- positive: weights (48/49,1/49), nodes (3/4,13)
- negative: weights (12/13,1/13), nodes (1/2,7)

Both have s0=s1=s2=1, same positive semidefinite singular size-2 face and nonzero kernel (-1,1). Same `Psharp_2=(t-9)/36`, unique simple positive root. Crossings: +37/144 and -19/72. Negative support below root; positive support straddles root.

## Conjecture 30 FAIL: full support

Earlier factorial carriers are squared-factorial moments of strictly positive full-support exponential-mixture densities:
- (16/17,1/17; 3/4,5) gives +7/24
- (4/5,1/5; 1/2,3) gives -1/12
Same Psharp root 9.

Higher principle: total positivity, multiplier sequences, interlacing, carrier positivity, smooth/full support, and variation count do not choose source occupation across adaptive roots. Missing theorem must be completed Euler–Gamma source-specific strict mass imbalance on combined Lebesgue-minus-Chebyshev discrepancy.

## Files

- Lean: `formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryFactorialRootThresholdNoGo.lean`
- umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- card: `docs/drafts/pipeline/3-formalized/mass-shifted-squared-factorial-root-threshold-orientation-no-go.md`
- route updated at equations (9.3.274)–(9.3.280)
- aggregate card updated: `mass-shifted-hankel-boundary-hilbert-charge-flow.md`

## Audit

Direct `lake env lean` and targeted module build passed. Axiom audit: only propext, Classical.choice, Quot.sound. Target forbidden scan and diff hygiene clean. Corpus lint red only on seven unrelated unreachable HTGeometry modules during concurrent refactor. Scratch files deleted.