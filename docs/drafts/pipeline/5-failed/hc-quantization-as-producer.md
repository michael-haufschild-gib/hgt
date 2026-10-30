# Quantized horizontal-collision carriers as an RH producer

- **ID:** hc-carrier-source-computability
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** docs/reports/review-3010/opus.md §3, §7
- **Statement:** Some reflection-faithful carrier is both computable from arithmetic and keeps a
  finite collision quantum, so that an arithmetic bound below the quantum would prove RH.

## Test 1: classification of the carriers (Lean definitions)

| Carrier | Zero-side summand | Source formula | Source-side quantum |
|---|---|---|---|
| Collision charge (`XiHorizontalCollisionChargeEndpoint`) | `m_ρ(H_ρ − m_ρ)`, fibre multiplicities | none | endpoint only |
| Two-prime Cesàro (`…TwoPrimeCesaroCarrier`) | `m_ρ (2^a 3^b)^{2i Im ρ}`: `χ_p(ρ)χ_p(1−ρ̄) = p^{ρ−ρ̄}`, holomorphic × antiholomorphic | none ("remaining producer is an explicit source estimate") | no |
| Prime–Cayley (`…PrimeCayleyInformationLoss`) | adds `realCayley(2 Re ρ − 1)` | none | no |
| Ward–Green (`…WardGreenCayleyQuantum`) | weight `(Re ρ − ½)^{−2}` (`thetaXiWardTransverseGreenWeight_eq`), built from per-zero Ward mass and energy | none | no |
| Exterior (`…WardGreenExteriorSourceCarrier`) | coefficients divided by the transverse coordinate `Im z` | prime–Gamma formula for the critical-feature Weil matrix only | no: the quantum appears after per-zero normalization |
| Gauss–Hodge (`…GaussHodgePrimeCurrent`) | `(½ − Re ρ) log 2` times a Bockstein coefficient of `2 Re ρ − 1`: a function of `Re ρ` | none (sum over zero copies) | no |
| Ordered prime cross curvature | source-side signed observable | n/a | no landing in a carrier |
| Holomorphic pencil (`XiHolomorphicTwoPrimePencilGrowthDichotomy`) | `m_ρ Y^{ρ−½}`, holomorphic | explicit formula | excess unbounded with an off-line zero |

No carrier is both source-computable and quantized.

## Test 2: the no-go

Proved and formalized: [holomorphic-carrier-rigidity](../3-formalized/holomorphic-carriers-cannot-be-quantized.md).
Linear and sesquilinear holomorphic carriers that vanish on critical configurations vanish on all
admissible ones; the off-line signal at depth `δ` is at most `2ε^{1−δ/Δ}M^{δ/Δ}`. A ζ-specific weight
vanishing at the real zeros but not at an off-line pair is the theta annihilator, which exists iff RH
fails (`exists_offLine_annihilator`).

## Test 3: finite height

Take a smooth window `w(γ/T)` and `Y = 4^a 9^b`. By the explicit formula,
`Σ_ρ w(γ_ρ/T) Y^{ρ−½}` equals the smoothed prime count in a multiplicative window of width `≍ 1/T`
around `Y`, minus its expectation, divided by `√Y`, up to bounded archimedean terms.

- Under RH the sum is `O_T(1)`. An off-line zero forces growth `Y^δ` (growth dichotomy).
- So the absolute source statement is square-root precision for prime counts in windows of relative
  width `1/T`. That is RH-equivalent and in the precision class of `negIndex_zetaKernel_eq_zero_iff_count`.
- For `Y ≤ T^θ`, the mean square of the holomorphic sum is Montgomery's unconditional pair form
  (`MontgomeryFormLogScaleMeanSquare`). Its leading order is proved for `0 < α < 1`
  (`MontgomeryPairCorrelationLeadingOrder`). A census bound needs its constant-accuracy part, i.e. pair
  correlation, which census Route II needs beyond `α = 1`.

Reduces to Π (absolute) and to pair correlation (normalized).

## Test 4: selection

The carriers are defined for any zero set closed under `s ↦ 1 − s̄`. The corpus has the following
models with zeros off the line:

- an entire completed function with the exact Riemann functional equation and a nonnegative
  generalized von Mangoldt measure (`EntireFunctionalEquationOffLine`,
  `LambdaPositiveFunctionalEquationOffLine`);
- Beurling systems (`BeurlingRegularIntegersOffLineZeros`).

A source law using only the functional equation, `Λ ≥ 0` and an entire completion holds for these
models, so it cannot bound the charge below 2. What singles out ζ is discreteness of the prime
measure (`BeurlingRiemannFunctionalEquationRigidity`). This is the selection wall Γ.

## Test 5: 𝔽_q calibration

For a curve, the holomorphic clock is `Σ (α_i/√q)^n = −(N_n − qⁿ − 1)/q^{n/2}`. It is bounded in `n`
iff RH holds for the curve, and its input is exactly `|N_n − qⁿ − 1| ≤ C q^{n/2}`.

- The same-point clock `Σ (α_i/|α_i|)^n` has no point-count expression.
- Exponent `½ + ε` in the count gives only `|α_i| ≤ q^{½+ε}`.

The mechanism is count precision: Π.

## Test 6: census salvage

In the holomorphic mean square, an off-line pair at depth `δ` contributes `Y^{2δ} + Y^{−2δ} + 2`,
against `4` for a double critical zero. The excess is `4 sinh²(δ log Y) ≈ 4(δ log Y)²`.

- At `Y ≤ T^θ`, zeros at depth `δ ≪ 1/(θ log T)` are invisible. This is the coalescence blind spot, and
  the same quadratic collapse as the Cayley gap.
- The 70 % near-line core may sit at such depths.

No gain over near-line zero density.

## No-go closure

- **Exact killing theorem/mechanism:** holomorphic carrier rigidity (exact and three-lines), the
  growth dichotomy, and the off-line models with the Riemann functional equation and `Λ ≥ 0`.
- **Strongest positive survivor:** `linearCarrier_eq_zero`, `sesquilinearCarrier_eq_zero`,
  `norm_quartet_le_interp`, `exists_depth_without_quantum`. The census bridge
  `xiStripWindowTotalOrder_sub_collisionCharge_le_lineOrder` (`N₀ ≥ N − O(T)`) remains.
- **New insight:** the HC quantum lives on weights non-holomorphic in the zero (functions of `Re ρ` or
  `Im ρ` alone, or `(Re ρ − ½)^{−2}`). Every source-computable carrier only sees data determined on the
  critical line, with off-line signal bounded by three lines. Quantization reduces to Π (absolute source
  side), pair correlation (normalized source side), zero density or spectral realization (zero side),
  or theta completeness (ζ-specific weights). A producer must also use discreteness of the prime
  measure.
- **Status:** Lean `RHTower/HolomorphicCarriersCannotBeQuantized.lean` checked with standard axioms.
  Tests 3–6 are paper reductions, not Lean theorems.
