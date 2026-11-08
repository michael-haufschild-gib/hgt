# Review-0811 §2.2 open obstacles: contribution loop

- **ID:** review-0811-open-obstacles-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop)
- **Source:** docs/reports/review-0811/obstacles-summary.md §2.2
- **Statement:** Conjecture, prove and formalize contributions that move problems of §2.2 (Σ, Π, Γ); target 250.

## Contributions (formalized)

| # | Problem | Result | Lean |
|---|---|---|---|
| 1 | B115, B88 | The archimedean Frobenius kernel `min/(1−(min/max)²)` is `2π√(mn)·G_{1/2}(d)`, `G_s(d)=e^{−(s−1)d}/(4π sinh d)` the Green function of `Δ−s(2−s)` on `ℍ³`, `d=|log(n/m)|` the distance of `z_m=(0,0,m)`, `z_n`; radial equation; Newtonian pole `4πd·G_s→1` (the diagonal is a Coulomb self-energy); `Δ=½` propagator = `Δ=3/2` propagator + complementary-series `1/(2cosh(d/2))`; damped kernels `√(mn)e^{−d/2}/(1−r²e^{−2d})` PSD (Ornstein–Uhlenbeck), lossless off the diagonal, diagonal `n/(1−r²)→∞`; Weil's archimedean-plus-pole weight `= 4πG_{1/2}(u)−4cosh(u/2)` | `SurfaceOfSpecZ/TheArchimedeanFrobeniusIsAHyperbolicGreenFunction` |
| 2 | B115, B17, B88 | Every square block of `archKernel` on rows below columns is a scaled Cauchy matrix, hence nonsingular; on pairwise coprime orders the archimedean Frobenius agrees with no kernel of finite rank (no finite-dimensional fibre carries the jets). `√(mn)C_∞(m,n)=(n³−nm²−m³)/(n²−m²)`: the compensation is negative iff `n/m` is below the plastic number `ρ³=ρ+1`, positive above, never zero (`ρ` irrational) — the `log ρ` aperture is where the archimedean compensation changes sign | `SurfaceOfSpecZ/TheArchimedeanFrobeniusHasInfiniteRank` |
| 3 | B87, B95 (F15 C15.1) | The Krein squares of the integer probes are not all integers, unconditionally; no `ℤ`-valued count and no integral trace form `Tr(T_mT_nᵗ)` equals `Q` on integer probes. Proof: integer squares at `e_i`, `e_i+e_j` put `2Re F(log(m/n))∈ℤ` for the spline series `F`; density + continuity make `Re F` constant; bounded orbit ⇒ RH; under RH `Re F(0)−Re F(π/γ₁)≥2m|B̂(γ₁)|²>0` at a zero the spline sees | `CountingHolography/TheIntegerProbesAreNotIntegerValued` |
| 4 | B17 | Weil's atomic off-diagonal kernel `W(m,n)` is negative iff `max/min` is below the plastic number `ρ³=ρ+1`, positive above, never zero; the primes never flip the sign (`Λ(x)/√x < C_∞` at integral ratios). The first Beurling–Deny criterion `Q(|x|)≤Q(x)` (every diagonal) holds on a finite atom set iff all its pairs lie within the plastic ratio: the atomic form of the Markov/Perron threshold `log ρ` | `SurfaceOfSpecZ/TheSignOfWeilsAtomicKernelIsPlastic` |
| 5 | B88, B118 | The damped `ℍ³` profile `K_r(x)=e^{−|x|/2}/(1−r²e^{−2|x|})` has self-energy `Z(r)=∫K_r=Σr^{2k}·2/(2k+½)` with `log(1/(1−r²))+4−π²/24 ≤ Z(r) ≤ log(1/(1−r²))+4`; `∫K_r g = g(0)Z(r) − ∫K_r(g(0)−g)`, and for `g ≤ g(0)` (every autocorrelation) `∫K_r g − g(0)Z(r) → −∫ω(g(0)−g)`, `ω` the archimedean Lévy density. The archimedean place needs exactly one counterterm, universal and logarithmic; the remainder is minus the Lévy jump energy | `SurfaceOfSpecZ/TheArchimedeanSelfEnergyIsLogarithmic` |
| 6 | B84, B103 | Quantiles of `V(x)=W(x)−W(x/2)/2+W(min(x,u₀)/2)/2` (strictly increasing: `w(u)>w(u/2)/4` beyond `u₀`) give positive discrete primes with `|N−(W−W(·/2)/2)|≤M`; their Euler product equals `ζ_c(s)exp(−L(4s)/4+sΛ(s)+sΛ(2s)+R₃(s))`, holomorphic on `Re s>1/3`, `s≠1`, zeros there exactly `(1−μ)±iγ`; holomorphic and zero-free on all of `Re s=½`, finite at `½` (the uncorrected one-off diverges). Remaining for an FE defect: growth of `sΛ(s)` on the line (trivially `O(|s|)`) | `ArithmeticPositiveDuality/ADiscreteOneOffCrossesTheCriticalLine` |
| 7 | B103, B84, B98 | Rounding the corrected primes up to `q_k=⌈e^{t_k}⌉` gives, at every height `γ`, natural generators `q_k≥2` and natural coefficients `a_n` with `Π(1−q_k^{-s})^{-1}=Σa_n n^{-s}=F(s)` on `Re s>1`, `Σ_{n<N}a_n∼AN` (`A>0`, Wiener–Ikehara), `F` holomorphic on `Re s>1/3`, `s≠1`, zeros there exactly `3/5±iγ`, `F≠0` on `Re s=½`. Generic: natural generators with `Euler product = H(s)/(s−1)`, `H` holomorphic past `Re s=1`, `H(1)≠0` ⇒ linear counting. Of B103's hypotheses only the FE can exclude a finite layer | `ArithmeticPositiveDuality/AnIntegerNormOneOffCrossesTheCriticalLine` |
| 8 | B26 | On the real axis `ξ_τ(σ)=∫Φ(x)e^{−τx²}e^{(σ−½)x}dx`, and `ξ_τ/ξ` is the mean of `e^{−τx²}` under the tilted law `∝Φ(x)e^{(σ−½)x}`, which escapes to `+∞` below `log(2σ+5)` (envelope `Φ≤C₀e^{9x/2}e^{−πe^{2x}}`): for `τ>0` the ratio `→0` yet `≥½e^{−τlog(2σ+5)²}`; for `τ<0` it `→∞`. An absolutely convergent Dirichlet series tends to `a₁` at rate `2^{σ₁−σ}`. Hence `ξ_τ = ½s(s−1)Γ_ℝ(s)D(s)` on a real half-line with `D` a Dirichlet series iff `τ=0`: the Dirichlet structure alone (no Euler product, no FE) selects `Φ` among `Φe^{−τx²}`, read at `σ→∞` on the scale `log σ` | `ZeroConfigurationGeometry/OnlyTheUndeformedKernelHasADirichletSeries` |
| 9 | B84, B103 | For a positive spectrum (`λ₀=1`, masses `≥1`) with an integrable FE defect and pole coefficient `β`, the Abel means `C_τ` obey the Gram inequality `2rΣ_{m∈S}C_{λ_m} ≤ r²C_0+Σ_{m,m'∈S}C_{λ_m−λ_{m'}}`; with `C_0→β/π`, `C_{λ_m}→a_m/2π` and `C_τ→0` at separated non-frequencies (every positive non-frequency is separated), a set `S` of frequencies whose differences are no frequencies has `Σ_S a_m ≤ 2β√|S|`, so `|S|≤4β²`. A spectrum with difference-free sets of every size has no integrable defect at any residue: an integrable defect forces the generalized integers to be additively saturated (independence number of the difference graph `≤` squared residue) | `ArithmeticPositiveDuality/IntegrableDefectsForceAdditiveSaturation` |

## Conjecture log
- C1 (proved, #1): the jets carrier is hyperbolic three-space with dilations as translations along a geodesic.
- C2 (proved, #2): every carrier of the jets on coprime orders is infinite-dimensional; the sign of `C_∞` is the plastic cubic.
- C3 (proved, #3): C15.1 — integer probes are not integer-valued; integrality would force RH and then a constant Bohr series.
- C4 (proved, #4): the atomic Weil kernel's sign is the plastic law; Markov holds exactly on plastic windows.
- C5 (proved, #5): the archimedean counterterm of the damped `ℍ³` propagator is `g(0)·log(1/(1−r²)) + O(1)`, universal; the renormalized limit is the Lévy jump energy.
- C9 (proved, #9): integrable FE defects force additive saturation of the frequency set at every residue.
- C8 (proved, #8): the time-0 selector of the heat family is already the Dirichlet structure, visible at real infinity.
- C7 (proved, #7): integrality, linear counting and continuation across the line together still allow a finite layer.
- C6 (proved, #6): a discrete one-off continues across `Re s=½` once the count carries the prime-square term; the obstruction to an FE defect is the type of `sΛ(s)` on the line, not discreteness.

## Log
- 2026-11-08 — created; #1–#9 formalized and wired; loop paused by user after #9.
