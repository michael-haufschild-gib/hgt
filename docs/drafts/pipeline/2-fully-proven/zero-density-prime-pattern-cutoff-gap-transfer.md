# Finite-cutoff upper bounds at zero Euler density

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean verification pending)
- **Obstacles:** Γ12; route-obstacles B24.
- **Statement:** For every prime set `P` and cutoff `Q`,
  `primeSetGreatestGap P ≤ finiteFlipGreatestGap (primeSetCutoff P Q)`.

## Consequence

The existing strict finite-flip comparison would extend the atomic Hodge
index or its two-adic probe to every nontrivial prime-set flip, without a
density or harmonic cancellation assumption.

## Argument under investigation

1. For fixed `d`, `S(N/d) = S(N) + O_d(1)` by bounded sign coefficients.
2. Fixed Ramanujan correlations are `S(N)` times the finite Euler conductor
   coefficient, with bounded error.
3. A positive gap forces `S(N)² ≥ c log N` along a cofinal subsequence
   (`frequently_harmonicSum_sq_ge_of_hasHyperplaneGap`).
4. On that subsequence, bounded correlation errors vanish relative to
   `S(N)`. Fixed conductor quasimodes then transfer a finite-cutoff witness
   with exact hyperplane correction.

## Paper proof — dependency closed

Write `H_N = Σ_{n≤N}1/n`, `S_N = Σ_{n≤N}ω_P(n)/n`,
`β_m = (Σ_{d|m} μ(m/d)ω_P(d))/√φ(m)`, and
`E_m = ramanujanAdjunctionEnergy m`. The exact incidence formula gives
`Σ_{n≤N}ω_P(n)c_m(n)/n = Σ_{d|m}μ(m/d)ω_P(d)S_{⌊N/d⌋}`.
Since `|S_N−S_{⌊N/d⌋}|≤1+log d`, its difference from `√φ(m)β_m S_N`
is bounded for fixed `m`, uniformly in `N` and `P`.

Suppose the actual prime pattern has a positive gap `g`. The existing ceiling
witness forces `S_N²≥c log N` cofinally for some `c>0`. Choose a cofinal
sequence on which `|S_N|→∞`. For every finite packet `Σ b_m v_{m,N}` with
`Σ b_m β_m=0` and conductor one included, subtract
`R_N v_{1,N}`, where
`R_N=(Σ b_m Σ_{n≤N}ω_P(n)c_m(n)/(n√φ(m)))/S_N`.
This enforces exact orthogonality to the prime-pattern constraint, and
`R_N→0`. Harmonic Gram convergence and the prime quasimode residual give
the packet's limiting shifted energy
`Σ b_m²(E_m−γ−s)≥0` for every `0<s<g`.

For any finite set `S` of conductors at least two, put
`T=Σ_{m∈S}β_m²/(E_m−γ−s)`, `b_1=−T`, and
`b_m=β_m/(E_m−γ−s)` on `S`. The constraint is exact because `β_1=1`.
The energy inequality reads `T−sT²≥0`, hence `T≤1/s`.
Finite-cutoff spectral weights are bounded by the corresponding full-pattern
weights. Their summable reciprocal series therefore has secular sign at
most zero throughout `0<s<g`. The finite-prime secular classification gives
the claimed upper bound. Nonpositive gaps follow directly from the same
classification's vacuous interval.

## Lean status

Proof sources: `ArithmeticCountingPositivity/RelativePrimePatternCoordinates`
and `EveryPrimePatternInheritsFiniteCutoffUpperBounds`. Initial compilation
pending; no theorem counted before complete direct checks and axiom audits.
