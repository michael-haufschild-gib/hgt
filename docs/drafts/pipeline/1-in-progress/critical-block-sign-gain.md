# Signed gain beyond the absolute assembly threshold

- **Stage:** 1-in-progress
- **Target:** B7: eventual full-space positivity beyond the size-only optimum.
- **Status:** Sharp aliasing floor formalized. Negative-vector compactness, signed source transfer,
  and certification of A4's absolute-assembly optimum remain open.

## Threshold and limiting form

For an absolute two-block comparison
`A(R)=J−αR`, `D(R)=g−βR`, `B(R)=γR`, with positive constants,
the admissible interval ends at `A(R)D(R)=B(R)²`, while both diagonal
entries remain positive. Replacing `A(R)` by `J+ηR`, `η>0`, gives a strict
gain at that endpoint and hence beyond it.

The actual growing low conductor packet has the checked positive polar
correction `aφ(2+γ_E−log(4π))R`. Applying the comparison requires retaining
all constants and free allocations in A4's far reserve, residual and Schur
payments, and certifying their joint optimum. Existing existential
small-multiple witnesses do not certify it.

For `R=c⁸/log N`, the optimized fixed-window limit is

`Q_R(h)=aφ W(H)+(7J₁/R)∫e⁻⁸ʸH²
        −generalTerminalPolarSource(A,h)²/criticalPoleWindowCost(R)`,

where `H=halfWeight h`. Its negative polar Schur term is essential.
The transfer conjecture is that uniform positivity of this form in the
exponential norm forces eventual full-space positivity. Positive limits
on fixed periodic or trigonometric sectors do not control moving sectors.

Corpus anchors: `TheTopCollarHasADyadicSeventhPowerReserve`,
`LogarithmFreeCriticalConductorResiduals`,
`TheCriticalSchurPairingRetainsTheCollarWeight`,
`TheCriticalLowPacketRetainsItsSignedPolarPart`.

## Formalized aliasing floor

Write `φ=tiltedUnitSpline`, `m=∫φ`, `Mφ=∫φ²`, `aφ=m²/Mφ`,
`U_N=(√N/c) centredAtomicTest(φ,x_N,c,N)`, and `Cφ=7MφJ₁`.
On every critical schedule `c⁸/log N→R>0`, with `c≥1`,
`∫U_N²≤1`, integrable `F`, and strong physical `L¹` convergence `U_N→F`:

- `m c⁸ B_high(U_N,U_{h,N};Ne⁻ᴬ)→Cφ∫F H e⁻⁸ʸ`.
- `c⁸ E_high(U_{h,N};Ne⁻ᴬ)→Cφ∫H²e⁻⁸ʸ`.
- For every `A>0` and `b<Cφ∫_{(-A,0)}F²e⁻⁸ʸ`, eventually
  `b<m²c⁸ E_high(U_N;Ne⁻ᴬ)`.

These are `tendsto_criticalCurve_highFourierPair_horizon`,
`tendsto_criticalCurve_highFourierMass_horizon`, and
`eventually_criticalCurve_highFourierMass_gt_weighted_floor` in
`ArithmeticHodgeTheoryOfDegenerations/TheHighAliasingHasItsPhysicalDualFloor.lean`.
Fatou derives `F∈L²`; no separate square-integrability input is needed.
The actual-path audit passed with only standard axioms.

The supporting results below are also formalized and audited with only
standard axioms. Module names are under `ArithmeticHodgeTheoryOfDegenerations`
unless marked `CriticalArithmeticCorrelationTheory`.

| Module | Mathematical input |
|---|---|
| `TheAliasingMeanIsStableUnderL1Convergence` | For integrable `G` supported in `[δ,∞)`, `∫G(x)c⁸ aliasDensity(φ,cx)→(7/2)MφJ₁∫G(x)x⁻⁸`; stable under strong `L¹` convergence. |
| `AtomicSynthesisRecoversLipschitzTests` | Adjoint synthesis error at most `(c/N)Lip(f)‖φ‖₁‖x‖₂`. |
| `TheAliasingPairsWithStrongPhysicalLimits` | The exact discrete pairing tends to `(7/2)MφJ₁∫Fg e⁻⁸ʸ` for bounded terminal Lipschitz `g` and polynomial coefficient growth. The scaled multiplier has Lipschitz constant `O(c⁹)`. |
| `AtomicSynthesisRetainsItsMixedMass` | `∫U_N²≥growingMassConstant·Mφ c⁻⁸‖x_N‖₂²`; unit physical mass gives `‖x_N‖₂=O(c⁴)`. The mixed-row error is `O(c/N)‖x_N‖₂`, yielding `m c⁸(∫U_NU_{h,N}−m∫U_NH)→Cφ∫FHe⁻⁸ʸ`. |
| `TheSynthesizedProfileIsRecoveredBelowTheGrid` | Below-grid Fourier error at most `C(c²r³/N²+1/r)` for `1≤r≤Ne⁻ᴬ`. Choosing `r=c^(j+1)` makes `c^j` times the error vanish. |
| `CriticalArithmeticCorrelationTheory/TheHighFourierMassHasADualLowerBound` | `2m B_high(f,g)−E_high(g)≤m²E_high(f)`; the squared mixed error is bounded by `‖f‖₂²/(2π)` times the below-grid recovery error. |
| `CriticalArithmeticCorrelationTheory/SmoothTerminalTestsRecoverWeightedMass` | Smooth tests supported in `[-A,0]` recover every strict lower bound below `∫_{(-A,0)}F²e⁻⁸ʸ` through `2∫FHe⁻⁸ʸ−∫H²e⁻⁸ʸ`. |

The pairing limits also hold along cofinal filters. The weighted floor holds
along every nontrivial countably generated cofinal filter, through
`eventually_criticalCurve_highFourierMass_gt_weighted_floor_along_filter`.
The full dependency chain passed actual-path audits with standard axioms.
Strong convergence for possible negative vectors remains open.

## Confinement

Let `L=linearDefectCutoff c`, `M=N/L`,
`P=Σ_{n≤M}x_n²`, and `S₇=Σ_{M<n≤N}(N/n)⁷x_n²`.

Split the top archimedean form into one quarter of the
dyadic aliasing bound, one half of the high-frequency bound, and one
unpaid quarter. The existing cross payment spends one eighth of the
aliasing bound. This leaves one eighth of that reserve and one quarter
of the original archimedean form.
For every fixed `R,κ>0` and `B∈ℕ`, eventually in `N`, all
`1≤c≤(log N)^(9/64)` with `c⁸≤R log N` and `w⊥V₁` satisfy

`Q_N(w)≥(7/8)D_M(w)+(g/8c⁷)(log N)S₇−(C_S+C_*R)cS₇
          −κ(log N)/(1+log log N)^B P+archForm(top)/(4G)`,

where `G=(c/N)Mφ`, `g=dyadicTopMassConstant`, and
`C_*=128(1+2e)e² splineWindowConstant/g`. Parameter choices use
`9/64<1/7` and `13/7<2`; no smallness condition on `R` is needed.

The raw and fixed-ratio reserves are formalized in
`CriticalArithmeticCorrelationTheory/TheFarReserveRetainsArchimedeanEnergy.lean`:
`exists_prefix_top_window_reserve_retaining_archForm` and
`exists_fixed_ratio_far_reserve_retaining_archForm`. Their actual-path audits
passed with only standard axioms.

The remaining absorption step requires a growing conductor packet. With
`q=N^(1/(1+log log N)^5)` and controlled terminal leakage, its prefix floor
would give `P=O(c(log log N)^5/log N)S₇` for negative far vectors. This is
unproved. It would absorb the free prefix tolerance `κ>0` and bound the
archimedean energy when `S₇=1`; the logarithmic Gamma floor would then
control Fourier tails. The signed limit still needs the sharp source.

The spatial estimates are:

1. For `1≤c` and `L≤N`,
   `∫e⁻⁸ʸU_tail²≤(256e²+4+2e)Mφ S₇`.
   The Gram row at `n` has at most `1+2n(e^{c/N}−1)` overlaps.
   Exponential conjugation gives `(N/n)⁸/c`; on the collar,
   `N/n<L≤(256e²+4)c`, while `e^{c/N}−1≤ec/N`.
2. Physical `L¹` tails are `O(√(P/c))` for the prefix and
   `O(e⁻⁴ᴬ√S₇)` for the collar below `−A`. Weighted Cauchy–Schwarz gives
   `(∫_{y≤−A}|H|)²≤e⁻⁸ᴬW₈(H)/8`; apply the first estimate.

The first bound is formalized as `normalized_tail_exponential_mass_le` in
`CriticalArithmeticCorrelationTheory/ThePhysicalCollarHasBoundedExponentialMass.lean`.
Its actual-path audit passed with standard axioms. The L¹ tail bound and the
stronger truncated Laplace estimate are formalized in
`CriticalArithmeticCorrelationTheory/ExponentialMassControlsLaplaceTails.lean`:
for `p+2q>0`,
`(∫_{y≤b}|H|e^{qy})²≤W_p(H)e^{(p+2q)b}/(p+2q)`.
Both actual-path endpoint audits passed with standard axioms.

The prefix estimate is formalized in
`CriticalArithmeticCorrelationTheory/ThePhysicalPrefixHasSmallL1Mass.lean`:
`normalized_prefix_integral_abs_sq_le` gives
`‖U_prefix‖₁²≤(M/N)‖φ‖₁²P`, and `linear_prefix_integral_abs_sq_le` sharpens
this to `‖φ‖₁²P/(4c)`. Both actual-path audits passed with standard axioms.

`CriticalArithmeticCorrelationTheory/PhysicalAndFourierTailsGiveCompactness.lean`
formalizes total boundedness, and compactness of the closure, for bounded L²
families with uniform physical and Fourier tails. Both endpoints passed their
actual-path standard-axiom audits. Establishing these premises for negative
vectors still requires the growing-packet prefix absorption estimate.

## Prime form and polar source

For `H` supported in `(-∞,0]`, put `W₈(H)=∫e⁻⁸ʸH²`.
The existing global bound in
`ArithmeticCastelnuovoSeveri/ExponentialSourceMassControlsTheFullPrimeSum.lean`
applied to `|H|` gives
`|primeSum H|≤2(ΣΛ(k)k⁻³ᐟ²)∫e⁻²ʸH²`.
Since `Ct≤εt⁴+B_ε`, this implies
`|primeSum H|≤εW₈(H)+B_ε‖H‖₂²`, uniformly over terminal apertures.
Both bounds are formalized in
`CriticalArithmeticCorrelationTheory/PrimeShiftsAreInfinitesimalInTheExponentialWeight.lean`:
`abs_primeSum_le_two_threeHalvesMass_mul_exponentialSourceMass` and
`exists_abs_primeSum_le_exponential_mass`. The actual-path audit passed with
only standard axioms.

The polar source has the candidate global functional

`S(H)=aφ[∫He⁻ʸᐟ²−log(2π)∫Heʸᐟ²−½∫Heʸᐟ²log(1−e²ʸ)
          −Σ_{k≥1}Λ(k)∫_{y≤−log k}Heʸᐟ²]`,

with the first three integrals over `y<0`. Substitution `x=eʸ` gives
`S(halfWeight h)=generalTerminalPolarSource(A,h)` on compact windows.
Weighted Cauchy–Schwarz gives
`|∫_{y≤−log k}Heʸᐟ²|≤k⁻⁹ᐟ²√W₈(H)/3`.
The convergent series `ΣΛ(k)k⁻⁹ᐟ²` therefore bounds the prime functional.
These moment estimates and the full prime functional's absolute summability
and bound are formalized in `ExponentialMassControlsLaplaceTails.lean`, through
`polar_laplace_moments_sq_le_eighth_exponential_mass`,
`abs_prime_laplace_tail_le_eighth_exponential_mass`, and
`prime_polar_functional_summable_and_bound`. Actual-path audits passed with
standard axioms.
The other three dual weights have weighted squared masses `1/7`, `1/9`,
and at most `1`. The last uses `x=e²ʸ` and `∫₀¹log²(1−x)dx=2`.
Its integrability and bound are formalized as
`polar_logarithmic_dual_weight_integrable_and_le_one` in
`CriticalArithmeticCorrelationTheory/ThePolarLogarithmHasFiniteExponentialDualMass.lean`.
The actual-path audit passed with standard axioms.

Strong local `L²` convergence with bounded `W₈` would preserve this source
by tail truncation. Equivalently its kernel is
`s(y)=e⁻ʸᐟ²[1−eʸψ(e⁻ʸ)−eʸ(log(2π)+½log(1−e²ʸ))]`, `y<0`.
Lean status: identity, continuity, and discrete moving-source transfer pending.
