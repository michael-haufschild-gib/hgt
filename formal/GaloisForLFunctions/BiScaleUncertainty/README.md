# Bi-Scale Uncertainty (BSU)

Umbrella `BiScaleUncertainty.lean` (~670 modules, flat folder). Root namespace
`GaloisForLFunctions.BiScaleUncertainty`; sub-namespaces `ChebyshevGauge` (explicit formula, packets,
zero width), `FiniteHorizon` (integer windows), `SobolevShear`/`PathCongestion` (physical L²),
`EnergyCycle`/`SharpCycle`/`L2Cycle` (closed-cycle observation), `SieveMoments` (+ `TwoLagSieve`,
`AffineSieve`, `ArithmeticEdges`, `CoprimeOverlap`, `TopAnchor`, `ParityNeighborhood`,
`LinearVisibility`, `PrimeAnchor`).

## 1. Motivation

For a real test `f` with autocorrelation `h = h_f`, the Weil form is exactly

`Re W_Λ(f * f̃) = Ω(0)·h(0) + J(f) − 2·⟨h, ν⟩`,

`J` = archimedean (Lévy) energy, `ν = Σ Λ(n) n^{−1/2} δ_{log n} − 2cosh(x/2) dx` = prime minus polar
measure. RH ⇔ this is `≥ 0`. On tests blind at every prime power (`h(log n) = 0`) with zero pole mass
the prime term vanishes and RH becomes an uncertainty inequality between two scales:
`|Ω(0)|·h(0) ≤ J(f)` (`|Ω(0)| = γ + π/2 + log 8π ≈ 5.37`). Additive scale: positions `log n`.
Multiplicative scale: dilations, the singular weight `ω` at the origin.

BSU asks:
1. What does blindness on (parts of) the log grid cost in archimedean energy? Sharp constants,
   asymptotics, which node sets matter.
2. What is the prime–polar pairing `⟨h,ν⟩` when blindness is dropped? (Answer: a Chebyshev gauge
   transform of `ψ(x) − x`; its size is the RH question.)
3. Which observations of a correlation (log-grid samples, closed cycles, polar moment, sieve moments)
   are stable, compact, recoverable?

## 2. Objects

Archimedean side.
- `h(x) = ∫ f(u) f(u+x) du`; normalized `H = h/h(0)`.
- `ω(x) = archLevySinhWeight x = e^{x/2}/sinh x = 2/(e^{x/2} − e^{−3x/2})`; strictly antitone;
  `ω(x) ≥ e^{−1/2}/x` on `(0,1]`; `ω(log n) = 2n^{3/2}/(n²−1) ≈ 2/√n`.
  `ω = sech(x/2) + ω*`, `ω* = e^{−x/2}/sinh x` (functional-equation dual).
- `J(f) = biScaleLevyEnergy f = ∫_0^∞ (h(0) − h(x)) ω(x) dx`; normalized `J/h(0)`.
- Symbol `γ(r)` (`gammaBracket`); `γ(ω) − γ(0) = ∫(1 − cos ωx) ω(x) dx` (`archFrequencyCost`);
  `γ(ω) ≤ log ω + O(1)`; `Ω(0) = γ(0) < 0`.
- Polar moment `2∫_0^∞ h cosh(x/2) = (∫f e^{u/2})(∫f e^{−u/2})`; Re pole term
  `= 2((∫f cosh(u/2))² − (∫f sinh(u/2))²)`.
- Test classes: `RealWeilTestFn` (real `C²_c`), `RealEvenPolarTestFn` (even, polar integral 0),
  `RealOddTestFn`, `RealOddPolarTestFn` (odd, sinh-moment 0), `RealHyperplaneGenerator`.
- `LevyEnergySource E`: `C²_c`, positive mass, `J/h(0) ≤ E`; `InfiniteGridEnergySource K`
  adds `h(log n) = 0` for all `n ≥ 2`.

Arithmetic side.
- Gauge error `Ẽ(t) = e^{−t/2}(ψ(e^t) − e^t)`; gauge derivatives `D₋f = f' − f/2`, `D₊f = f' + f/2`;
  `weilPoleOperator = D₊D₋ = f'' − f/4` (kills `e^{±t/2}`).
- Cutoff `L = log(N+2)`; `ν_N`, `pairing_N`, `fullPairing` (stabilizes beyond support scale).
- Signed packet `S_f(u) = Σ Λ(n)n^{−1/2} f(u + log n) − ∫_0^L 2cosh(t/2) f(u+t) dt`;
  `packetEnergy = ‖S_f‖²`.
- Laplace response `R_N = K ⋆ ν_N`, `K = e^{−x/2}1_{x≥0}`; `laplaceEnergy = ∫R_N² =
  ∬ e^{−|s−t|/2} dν_N dν_N = ∫ S_N`, `S_N(ξ) = |ν̂_N(ξ)|²/(¼ + 4π²ξ²)`,
  `ν̂_N` = pole-subtracted truncated `−ζ'/ζ` on the critical line.
- Stationary packet `P_f(τ)` = pairing of a translate of `f` with `ν`; zero series
  `Σ_ρ m_ρ f̂(γ_ρ) e^{iγ_ρ τ}`; critical energy `E(f) = Σ m²|f̂(γ)|²`, Weil energy `W(f) = Σ m|f̂(γ)|²`.
- `splineProbe U(u) = e^u B(u)`, `B = (½·1_{[−1,1]})^{⋆4}` (support `[−4,4]`), `B̂ = (sin z/z)⁴`
  (real-rooted, so every boost `|t| ≥ ½` sees all zeros).
- CCM deficit `D(T) = ∫_0^T (e^t − ψ(e^t)) dt`; incoming `in(T)` (`ccmPrimeDeficitIncoming`, normalized
  deficit flux), critical energy `E = in²`, signed work `W`, coprime cross work;
  `Φ_lag(L) = Re Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))` (`weilLagFunctionReal`); `zetaZeroWidth = sup|Re ρ − ½|`.
- Combination cone: nonnegative combinations `c` of tests; `A(c)` = arch-only value, `W(c)` = Weil
  value, node value `L_n(c)`, pole mass; `𝒩`-blind = node values vanish on `𝒩`.
- `blindSymbolValue 𝒩` = inf of `A/mass` over `𝒩`-blind combinations (zero-pole version too);
  window ceiling `c(L)` / floor = sup/inf of `(A − W)/‖c‖²` over tests in windows of length `L`.
- Deletion price `w(m) = Λ(m)/√m`; folded symbol `F(z) = γ(‖z‖/ℓ)` on the circle, `ℓ = log q`,
  period mean `m_q`.

Factorial producers.
- Factorial lift `F_K(x) = Σ_{j≤K} e^{x/2}1_{[0, log(K/j)]}`, `F_K(log n) = √n ⌊K/n⌋`;
  bi-null `B_N = (F_{4N} − 4F_{2N} + 4F_N)/√N`; continuous/causal versions `C_N`;
  `chebyshevBiNullProducer N = log C(4N,2N) − 2log C(2N,N)`; balanced sources `P = sL + R/s`,
  `M = sL − R/s` (`s = N^{1/4}`, `L` reflected ramp, `R` narrow exponential tent),
  `(h_P − h_M)/2 = C_N` on `x ≥ 0`.
- Müntz seed / completion / tail (corrected by `c_N e^{x/2}1_{x≤0}`, `c_N = 1/(2√N)`).

Collar geometry. Collars `(log k − r, log k + r)`; physical partitions (measurable shares);
partition coefficient `c(ρ)`; kernels: independent `ω + mass − √(ω² + blockNorm²)`, paired, capped,
dyadic Schur, signed Gram `h(0)(W + Σa) − √h(0)·‖packet‖`; optima `c_N`, limits `c_∞`.

Discrete and physical.
- `additiveStepEnergy`, `multiplicativeScaleEnergy K`, `biScaleJointEnergy K N`,
  `WindowCoercivityBound`; dyadic mantissa tent `τ(n)`.
- `Velocity = L²(ℝ)`, primitive, translation `T_b`, dilation `(D_a q)(t) = a q(at)`, box average
  `A_s`, affine commutator `[D_a, T_b]`; tent frames, divisor grids, cell currents.
- Sieve: `sieveSeq N c`, Selberg coordinates `Y(e) = Σ_{d≤N, e|d} c_d/d`, `Q_Sel = Σ φ(e)Y(e)²`,
  Ramanujan lag weight `c_e(h) = Σ_{d|e, d|h} d μ(e/d)`.
- CHMD `SourceGraph`: `sourceEnergy`, prime clock atoms, stationary resolvent.
- Nyquist cells `[log n, log(n+1))`, order-`m` Taylor residual of `cosh(βx)`.

## 3. Language

- Grid-blind / `𝒩`-blind: `h(log n) = 0` for `n ∈ 𝒩` (finite `N`, full grid, prime powers).
- Polar / polar-balanced: half-line polar integral zero.
- Collar: neighbourhood of a node; origin collar `(0, a)` is where `ω` is singular.
- Clique: node set with all pairwise differences being zeros of `h` (orthogonal translates).
- Leverage: transfer of a singular origin weight onto node collars via a sphere inequality.
- Producer: explicit test certifying a bound; consumer: test paired against it.
- Packet: prime–polar measure convolved with a source; band: frequency window `|ξ| ≤ √x`.
- Zero width `β`: all zeros in `|Re ρ − ½| ≤ β`; rate `β`: growth `e^{βT}`.
- Deletion price: change of the zero-pole symbol value when one node leaves `𝒩`.
- Closed cycle: lag list with sum `0`; value = product of normalized correlations.
- Fibre: set of sources/weights with identical observations.

## 4. Mechanisms

M1. Sphere leverage. Orthogonal translates (clique) give Bessel `Σ h(y − t_i)² ≤ h(0)²`. With the
origin as extra coordinate of weight `W₀` the support function `√(W₀² + Σw²)` gives
`(Σw − Σw²/(2W₀))h(0) ≤ W₀(h(0) − h(y)) + Σ w_i(h(0) − h(t_i − y))`. Since `ω ~ 1/y` at the origin,
`W₀ → ∞` and the full collar weight transfers to Lévy energy. Shared origin across cosets costs
`√(W² + (Σ block norms)²)` once; optimal proportional allocation is unique.

M2. Divisibility chains. Odd fibres `{m 2^k}` are comparable under divisibility, so blindness at
`log n` makes each dyadic coset a clique. Products `h(log a + log b) = 0` for `a, b ≤ √N` make
opposite-sign cosets orthogonal (paired sphere).

M3. Hilbert attainment of collar optima. Shares as `L²` sections with closed convex fibres;
dual prices give affine supports; weak compactness ⇒ optimal partitions exist; complementary
slackness certifies optimality; Frank–Wolfe on a regularized Gram gives produced certificates.

M4. Krein increment and linear smoothing. `(h(x) − h(y))² ≤ 2h(0)(h(0) − h(x−y))`; progression
smoothing `|h − Sh| ≤ h(0) − Sh(0)` is linear (no square root) and yields a linear log modulus.

M5. Spectral flatness. Zeros at `mδ` (`m ≤ M`) make the Dirichlet-kernel energy of `|f̂|²` flat in
phase; arc covering gives logarithmic window laws; quarter-shifted cosine atoms attain them.

M6. Distant copies. `f − a f(· − T)` leaves local correlations unchanged, changes energy by
`O(e^{−T/2})`, and cancels any exponential moment with `a = e^{−βT}`. Constraints on finitely many
moments (polar balance) cost nothing; separated packets carry parity charges invisible to short
closed cycles.

M7. Hyperbolic multipliers. `C_α f = cosh(αu)f`, `S_α f = sinh(αu)f` form an `SO⁺(1,1)` doublet;
Casimir `h_{C f} − h_{S f} = cosh(αx) h_f`. Odd `f` ⇒ `S_α f` even (moves odd tests to the even
sector). Folding the sinh multiplier along `log 2` gives the coherent moment price.

M8. Node criticality by duality. Two-sided Farkas on node values + pole coordinate ⇒ a positive
`𝒩`-supported Weil certificate; pole-weight rigidity and Weil-cone uniqueness force it to be `Λ`.
Narrow pair tests `h ± h(· − log m)` read a single node; trains at positions `log m_A` read Euler
products (unique factorization selects lags).

M9. Phase measure. For a nonnegative combination `G_c(r) = Σ c|f̂(r)|²`; blindness at powers of `q`
kills Fourier coefficients of the folded phase law on `ℝ/2πℤ`; the symbol only sees its fold.
Blind slack on any set of powers of one integer = moment problem for the folded symbol.

M10. Polar Schur bound. On windows of length `L` the prime operator is a weighted adjacency on
`u ~ u ± log n`; with the polar weight `e^{−t/2} + e^{−(L−t)/2}` the Schur test gives
`c(L) ≤ K e^{L/2} + …` from `ψ(x) ≤ Kx + B`; prime mass at distance `log n` pays polar weight at the
far end. Kronecker modulation turns `n^{iξ}` into any unimodular completely multiplicative twist.

M11. Chebyshev gauge. Stieltjes against `ψ`: `P_f(u) = [f(u) − ∫ e^{−t/2}f(u+t)] + Ẽ(L)f(u+L)
− ∫ Ẽ(t)(f' − f/2)(u+t) dt`. All arithmetic content of every packet is the single response `R_N`;
`packetEnergy = ⟨autocorr(D₋f), autocorr R_N⟩ ≤ ‖D₋f‖₁²·laplaceEnergy`.

M12. Band reduction. Montgomery–Vaughan bounds the critical-line Dirichlet polynomial above
frequency `√x` by `O(log x)`; the remaining band `|ξ| ≤ √x` is the whole question.

M13. Residue/Landau. A one-sided exponential bound on a nonnegative density continues its Laplace
transform (Landau) to the right of the bound; zeros of `ζ` appear as residues of a resolvent, so
continuation forces their coefficients to vanish. Gives: packet growth ⇔ blindness to deep zeros;
band rate ⇔ zero width; deficit one-sided bounds ⇔ zero width.

M14. Abel–Bessel. Linear mean-square bounds give Abel energies; Abel coefficients at distinct
ordinates are orthonormal, so `Σ |coeff|² ≤ slope` (zero energies, multiplicities).

M15. Factorial cancellation. `Σ_{d≤K} ψ(K/d) = log K!`; stencils `(1, −4, 4)` on `(K, 2K, 4K)` (and
coprime `(2,3)` stencils) kill linear drift, Euler constant and the double pole: `O(log K)`
unconditional. Small pairing does not mean small norm; narrow supports force `log N` Lévy cost.

M16. Selberg/Ramanujan diagonalization. Over a factorial period every lag covariance of a divisor
sieve is `Σ_e c_e(h) Y(e)²`; DFT coefficients of the residue signal are Selberg coordinates;
`m`-th translated moments are products of `Y` over zero-sum frequency tuples.

M17. Arithmetic Friedrichs angles. Tent projections for coprime spacings have a single nonzero
angle `cos²θ ∈ {1/4, 1/2}`, read equally by the longest active run of the union grid.

M18. Beurling–Deny / Markov positivity. Graph forms decompose under modulus and clamp; resolvents
preserve positivity; nodal cross terms are controlled by lobe energies.

M19. Taylor producers on Nyquist cells. Weight `cosh(βx)` minus its order-`m` jet at cell nodes
leaves a residual summable iff `β < m + 1`; at `β = m+1` a finite part `B_m` survives.

## 5. Pillar theorems

A. Archimedean cost of blindness (unconditional).
1. Collar law: every `C_c` source blind on `log 2..log N` has `c_N h(0) ≤ ∫_0^{log N}(h(0) − h)ω`,
   `c_N > 0` explicit; optimal partitions exist; `c_N ↑ c_∞` with `√N(c_∞ − c_N) → 4`; paired cosets
   strictly improve (`c_∞^{indep} + g ≤ c_∞^{paired}`, explicit `g`); product-coupled hierarchy
   `N^{1/4}(c_∞^{pair} − c_N) → 4`. No regularity beyond `C_c`.
2. Signed Gram (no blindness): `h(0)(W+Σa) − √(h(0)·Gram) ≤ Σa_i(h(0) − h(t_i))`; optimum monotone,
   inverse-sqrt saturation, constructive Frank–Wolfe certificate. Anchored Gram minimum on dyadic
   nodes is exactly `1/(m+1)`: anchor cancellation degenerates logarithmically.
3. Turán windows: zeros at `mδ`, `m ≤ M` ⇒ `|∫_0^{(M+1)δ} h| ≤ 12δ(4 + log(M+1))h(0)`; attained up to
   constants (`≥ (δ/4π)log(M+2)h(0)`).
4. Linear log modulus: `log(1/|x−y|)·|h(x) − h(y)| ≤ 32√e J + 2h(0)`; rate and linear energy
   dependence both sharp (modulated bumps). Full integer-log blindness ⇒ `|T|·|h(T)| ≤ 32√e J + 2h(0)`;
   prime-power blindness ⇒ `(29/100)T|h(T)| ≤ C` (Hoheisel `θ = 71/100`).
5. Infinite grid: polar sources blind on the whole log grid exist; cost `≍ −log(distance of copy
   centre to the grid)`, linear `≍ log N` for a copy between `log N` and `log(N+1)`. Finite trains:
   blind ⇔ every active lag off-grid; one uniform constant for all patterns.
6. Equivalences of infima: polar vs nonpolar, even polar vs even, odd sinh-neutral vs odd, finite
   exponential-moment constraints, vector vs scalar sources — all have the same best log-grid
   energy constants. Broad sources approach every feasible spectral design from above.
7. Bi-scale uncertainty inequality on the polar hyperplane: `weilArchRe = Ω(0)h(0) + J`;
   `weilArchRe ≥ 0 ⇔ |Ω(0)|h(0) ≤ J`. Folded collar: log-2-blind even polar tests satisfy
   `weilArchRe ≥ (Ω(0) + C_fold)h(0)`.

B. Exact Weil identities.
8. Universal pole absorption: for every real `C²_c` `f` (any parity), and every compact continuous `f`
   with finite jump energy, `Re W_Λ(f*f̃) = Ω(0)h(0) + J(f) − 2·fullPairing(h_f)`. Odd sector:
   `weilArchRe + 2(∫f sinh(u/2))² = Ω(0)h(0) + J`. RH ⇔ positivity on `RealOddPolarTestFn` (sinh-neutral
   odd tests lose nothing); `β > 1` odd positivity fails for every weight.
9. Signed all-scale coercivity (unconditional): `C_all(N)h(0) ≤ J + Σ δ_n ϖ_n h(log n)` and von
   Mangoldt version — grid sum enters with positive coefficients (rearrangement, not positivity).

C. Node criticality and window spectrum.
10. `ZeroPoleBlindPositiveOn 𝒩 ⇔ RH ∧ (all prime powers ∈ 𝒩)`. Deleting a prime power falsifies
    unconditionally; deleting a composite changes nothing. `0 ≤ zeroPoleBlindSymbolValue 𝒩 ⇔ RH ∧
    prime powers ⊆ 𝒩`; RH ⇔ every deleted value lies in `[−Λ(m)/√m, 0)`.
11. Deletion prices: one node `±Λ(m)/√m` exactly (narrow pairs are the only extremals, periodization
    defect); coprime nodes add (Euler multiplicativity), also on the full integer grid; within a tower
    sub/super-additive (`(√(1+8m) ± 1)/(2m)` laws); whole towers read the local Euler factor
    `2Re(−ζ_p'/ζ_p)(½+it)` (open interval, not attained); blindness at `pq` is free for single nodes,
    costs `≥ 9/10` for whole towers {2,3}.
12. Attainment thresholds: Euler price attained on windows iff `L > log Π m_p`; {2,3} decoupling
    length `log 6` (price jumps there), {2,4} attained already past `log 4`.
13. Density: blindness on gapped or sub-square-root-density node sets never suffices (pole mass free,
    zero-pole positivity fails); powers of one integer, `S`-smooth integers fail. Square-root node
    density is critical; incidence (prime powers), not density, decides.
14. Single integer: blind slack on powers of `q` is `−m_q`; removing `q^d` costs `|φ_d|`; orbit law
    `−min F_d`; general set of exponents = circle moment problem `V_q(J)`; without blindness
    `A = m_q·mass + Σ φ_j √(q^j) v(q^j) + fold defect`. Two towers enclosed in
    `[−T(q₁,q₂), −m_{q₁} − η]` (exact value open).
15. Window spectrum: `c(L)/e^{L/2} → 1`, `floor/e^{L/2} → −1`; dlVP and VK remainders
    `e^{L/2 − κL^{ex}}` (any `ex < 3/5`); RH ⇔ `c(L) ≤ e^{L/2} + O(L)`; width `θ` ⇔ excess
    `O(e^{θL})` up to `width ≤ θ* ≤ width/2 + ¼`. Liouville mirror `|c + floor| ≤ 4L + O(1)`;
    every unimodular completely multiplicative twist has the same window extremes.
16. Graded pole compression: CCM `2×2` cross entry `|cross(a)| ≤ Ce^{(1+2α)a}` ⇔ zeros in
    `Re ρ ≤ ½ + α` (size, not sign).

D. Chebyshev gauge and packets.
17. `∫_0^L Ẽ² = ∫_1^{N+2}(ψ − x)²/x²` = Nyquist-cell sum `Σ(ψ(n) − m_n)²/(n(n+1)) + O(1)`;
    `packetEnergy ≤ 3(10 + Ẽ(L)²)h(0) + 3‖D₋f‖₁²∫Ẽ²` and converse; `laplaceEnergy ≍ ∫Ẽ² + O(1)`.
    Every unconditional lower bound for `Re W_Λ` in the programme has this mean square as remainder.
18. Band theorem: `laplaceEnergy ≤ ∫_{|ξ|≤√(N+2)} S_N + O(L)`. Band rate laws: zero width `≤ α` ⇔
    every `β > α` rate for mean square / Laplace / band energy. RH ⇔ linear band ⇔ any
    subexponential band (self-improvement). Linear band ⇒ `Σ n²/|ρ|² ≤ slope`; never sublinear
    (Hardy). Off-line zero at `½+β` forces the exponential band floor.
19. Packet laws (unconditional): `P_f = O(e^{στ})` ⇔ `f̂` vanishes at all zeros of depth `> σ`;
    one-sided bounds suffice. Universal probes (all but countably many boosts of any bump; explicit
    `splineProbe`): RH ⇔ `Σ Λ(n)√n B(log n − τ) ≤ ∫ 2cosh(x/2)e^x B(x−τ) + Ke^τ` for `τ > 4`;
    width `β` ⇔ same with `e^{(1+β)τ}`. Persistence: every nonzero packet exceeds `±c` infinitely
    often; amplitude `≥ m_ρ|f̂(γ_ρ)|` per zero; dilates `√(t log(1/t))`.
20. Packet energy vs Weil: if `P_f` bounded above, `(1/L)∫P_f² → E(f)`, `Weil(h_f) = W(f) ∈ [0, E(f)]`;
    `E/W → m_ρ` on tuned probes (multiplicity spectroscopy); `E − W = Σ m(m−1)|f̂|²` (multiplicity
    defect, finite-prime version); RH ∧ simple zeros ⇔ bounded universal packet ∧ defect `→ 0`.
    Pairing recurrence: `limsup −⟨h(·−τ), ν⟩ = W(f)`; one-sided bound on the packet of `h_f` gives
    Weil positivity for `f`. Under RH: sign change in every multiplicative interval.
21. Weil-lag deficit: `weilPoleOperator` annihilates polar modes; `P_f = ∫Φ_lag·weilPole f + O(e^{−τ/2})`.
    Hardy inequality `2E(T) + ∫_0^T E ≤ 4∫_0^T Ẽ²`. Explicit formula `|in(T) − Re Σ e^{T(ρ−½)}/ρ²| ≤
    C(1+T)e^{−T/2}`. Slack-free endpoint laws: width `≤ σ` ⇔ `|in| ≤ Be^{σT}` ⇔ one-sided
    `D(T) ≤ Be^{(½+σ)T}` ⇔ `E ≤ Ce^{2σT}` ⇔ cross-work lower rate ⇔ one-sided `Φ_lag ≤ Me^{σL}` (also on
    the dense lags `k log p + l log q`); rate sets are `[zetaZeroWidth, ∞)`. RH ⇔ `E` bounded ⇔ cross
    work bounded below.
22. Zero density filter (unconditional): Ingham/Guth–Maynard give `N(σ,T) ≪ T^{1−(4/3−δ)(σ−½)}`;
    cosine-filtered incoming deficit on windows `A ≤ α log Γ` (`α < 2/3`) has frequency average
    `≤ CΓ^{−1/2}N(ψ)`; zeros with `|γ| ≥ x^{1/(2α)}` carry `O(1)` ⇒ `in(T)` = finite low-zero sum
    `+ O(1)` (same for `E`, cross work, `Φ_lag`).
23. Under RH (consequences, not progress): Cramér limit `(1/M)∫_0^M Ẽ² → Σ m²/|ρ|²`; finite-cutoff
    packet energy `/L → E(F)` iff boundary term vanishes; `(1/T)∫E → Σ m²/|ρ|⁴`.

E. Factorial producers.
24. `|fullPairing(B_N)| ≤ (10 log(4N+1) + 3)/√N` with `1 ≤ ∫B_N² ≤ 16`; realized as a difference of two
    autocorrelations of balanced sources, `‖P‖² ∈ [6√N, 46√N]`, normalized Lévy energy `≳ log N`;
    complete Weil value `≥ γ(0) + c log N − C → ∞` (unconditional coercivity).
25. Ramp diagonal: the pole lowers it, `N·polarLoss/log N → ¼`; mixed Gram error `= o(polarLoss)`
    (polar absorption shortcut closed); sign of the pure ramp diagonal open.
26. Müntz completion: zero-annihilated completion of the ramp; corrected readout `c_N/ρ` at every zero;
    zero side `= c_N² Σ 1/(ρ(1−ρ))`, real part `> 0` for every zero in the open strip (no RH); tails
    have Fourier mass `O(N^{−3/2})` at low frequency and Weil energy `≥ (½log N − C)·mass`.

F. Observation, compactness, recovery.
27. Bounded-energy grid-blind correlations are relatively compact in sup norm; limits keep positive
    definiteness, grid zeros, energy `≤ K` (Fatou); energy defect concentrates at the origin; strict
    energy loss occurs. Signed version: compact ⇔ signed log-traces vanish uniformly.
28. Polar moment is discontinuous: attenuated copies are polar-balanced with non-polar limit;
    diffuse ternary trains converge in correlation and energy with polar moment `→ ∞`.
29. Closed cycles: all closed products determine the signed correlation; no finite order does (for
    every `m`, full-grid-blind sources in one energy class agree through order `m`); exact detection
    order `⌊T⌋ + 1` for copies at distance `T`; Gram determinants same threshold. Quantitative: energy
    ceiling + accuracy fix radius, mesh, order, noise threshold (conditioning `2^{n+1}(n+2)`,
    `n ~ R/r(E)`); Dirichlet energy gives linear conditioning; everything holds for `L²` sources.

G. Finite horizon and physical Sobolev geometry.
30. Window coercivity `Var_N(f) ≤ C·biScaleJointEnergy`: best `C = Θ(N)` (upper `6N`, tent and resonant
    cosines lower); no `N`-uniform constant for any fixed dilation horizon (Dirichlet-recurrent
    log-oscillations). Doubling energy alone gives none (tent is a nonconstant null vector). Exact
    doubling incidence is destroyed by arbitrarily small perturbations (constant jumps to
    `N(N+1)/12`); soft weights `max(0, 1 − 2|x_j − 2x_i|)` are stable for displacement `< 1/6`.
31. Coprime tents: `P_d P_e` commute ⇔ `gcd(d+2, e+2) ≥ 2`; `‖P_dP_e − P_lcm‖² = cos²θ ∈ {0, ¼, ½}`;
    `(P_dP_e)^{k+1} − P_lcm = c^k T`; Riesz constants `2 ∓ 2cos(π/(L+1))`, `L` = longest active run
    (sharp). Divisor families: positive coercivity ⇔ closed range ⇔ bounded runs; projection error =
    negative half-line + noncellular + component charges.
32. `‖[D_a, T_b]‖ = 2√|a|` (if `b(a−1) ≠ 0`), never attained (no antiperiodic `L²`); box averaging
    gives `2√|a| min(1, |b(a−1)|e^{−s})`; compensated logarithmic producers are dense in the form
    sense with explicit tails.

H. Sieve moments.
33. `periodCovariance(N,c,h) = Σ_e c_e(h) Y(e)²` for all lags; lag-(0,1,2) moments fill an explicit
    five-facet cone. Affine data ⇔ comparable products `Y(q)Y(d)`; triple data ⇔ triangle products;
    fifth + sixth translated moments determine all translated moments and the source up to the
    half-period companion (absolute iff depth 0 or anchored). Degree 6 sharp; parity weights defeat
    affine + odd data.
34. Stability: Hölder `1/6` (sharp), cube root on top-mode stratum (sharp); parity neighbourhood
    exponents `1, 1/3, 1/5, 1/6` by cutoff (`N = 2, < 12, < 20, ≥ 20`); Lipschitz ⇔ every missing
    mode visible (`ω(q) ≤ 5` for prime-power sources). Squarefree arithmetic rows (Möbius tapers,
    Barban–Vehov) have cubic ceiling `α ≤ 1/3` unconditionally (`N ≥ 9`).
35. Prime families: sixth readout `(a_p a_q)³` recovers up to sign; fewer than `#modes` observations
    never suffice; adaptive protocol `≤ 128M − 64`.

I. Nyman–Beurling / Fermi and Route PM.
36. Fermi–Nyman generators are dyadic bricks of the gauge; RH ⇔ every witness has top-octave energy
    `≤` lower-half energy; witness cell transfer moves bulk cell integrals into the origin tail.
    Selberg lossless identity `Σ_{k≤M} s² = M·Q_Sel − R`; complete-fibre collapse for Möbius;
    Barban–Vehov pinch `Q_Sel ∈ [1/Σ, O(1/log X)]`. Power-damped Fermi source admitted for `ε ≥ ½`;
    uniform sawtooth budgets for `ε < ½` imply RH (open).

J. CHMD source graph.
37. Markov positivity of the stationary resolvent; Pythagorean prime-shift bound
    `⟨T u,u⟩² + ⟨Drift u,u⟩² ≤ ⟨primeDiag u,u⟩²`; weight rigidity (no summable `w ≥ Λ/√n` with strict
    inequality); `sourceEnergy` concentrates on distinct-prime off-diagonal clock sums; their
    eventual nonnegativity ⇔ `μ ≤ ½` (criterion, sign open); bounded-amplitude clock packets compact,
    unbounded escape.

K. Nyquist residuals.
38. Residual of `cosh(βx)` after order-`m` cell jets: integrable ⇔ `β < m+1`; tail `~ C/(N+1)^{m+1−β}`;
    critical finite part `B_m` (prefix `= c_m log N + B_m + O(1/N)`); critical residual of a stretched
    source converges iff `∫f = 0` while its Lévy energy `→ 0`; supercritical residuals are unbounded
    under every energy ceiling.

## 6. Tools

Developed (reusable):
- Sphere/support-function calculus: capped disks, paired spheres, two-column Schur support
  (sum of singular values), allocation equality cases, Lagrange identities.
- Hilbert attainment for measurable-share optimization; dual prices; Frank–Wolfe with explicit
  iteration counts.
- `ω` toolkit: antitone, origin/tail splits, `∫_a^∞ ω ≤ log(6/a) + π`, endpoint tail `4/√N + O(1/N)`,
  compression `J(f(L·)) ≤ J + 2log L`, dilation `J(f(δ·)) ≤ δK`.
- Krein increment, linear progression smoothing, log modulus; local correlation energy stability
  `|J_f − J_g| ≤ 2∫_a^∞ ω` when correlations agree on `[0,a]`.
- Exact Weil identity on all real test classes; spectral identification for finite jump energy.
- Chebyshev gauge: Stieltjes/Abel formulas, Nyquist cell quadrature (exact cell energies), Laplace
  response, renewal chain, rectangle law `pairing(e^{t/2}1_{[0,a]}) = ψ(e^a) − e^a + 1 − a`, divisor-
  averaged Chebyshev law `Σ_{j≤K}(ψ(K/j) − K/j) = log K! − K H_K`.
- Landau/residue continuation engine for packets, bands, deficits; Abel–Bessel inequality;
  almost-periodic Parseval and window means; universal probe construction (countable bad boosts,
  real-rooted transforms).
- Polar Schur test on windows; Kronecker twist realization; Euler trains, staircase and slab trains;
  lag-selection lemmas by `p`-adic valuations; two-antiperiod rigidity on dense subgroups.
- Circle cosine designs (quadrature, exactification), product designs.
- Factorial stencils (`O(log N)` with explicit constants), central binomial ratio bounds,
  clamped lattice sums, Bernoulli primitives, exponential tent sources.
- Sieve Fourier dictionary (DFT = Selberg coordinates), Ramanujan inversion realizing any coordinate
  profile, threshold rounding, cubed-Gram stability, resonance counting.
- Tent frames, masked successors (nilpotent sine bound), divisor-grid completion, cell analysis.
- Physical `L²` toolkit: translation/dilation/box, Sobolev traces, modulus and clamp, path
  congestion with archimedean singularity cancelled by path resistance.
- Closed-cycle recovery templates (finite nets, measured arrays, `L²` sources).

To build:
- A mechanism forcing `|Ω(0)|h(0) ≤ J` on the prime-power-blind zero-pole cone (RH itself); all
  collar constants found so far are too weak or require extra structure.
- An unconditional bound on the band energy `∫_{|ξ|≤√x} S_x` better than `O(x)` with a usable
  exponent (anything subexponential is RH).
- A sign argument for distinct-prime off-diagonal clock sums (CHMD).
- Exact two-tower blind slack; sharp identification of `c_∞`.
- Effective control of the pure ramp Weil diagonal.

## 7. Open questions

- Exact blind slack for two multiplicatively independent towers (between `T(q₁,q₂)` and
  `m_q + η`); for finitely many towers.
- Sharp value of the grid-blind collar constant `c_∞` and of the Schur-capped limit; are capped/Schur
  hierarchies strictly better than paired in the limit?
- Is there a node set strictly between prime powers and the full grid on which some quantitative
  (non-RH) positivity holds with explicit loss?
- Sign of `W(1,0)` for the pure factorial ramp; can the Müntz tail growth be made uniform in `N`?
- Route PM: uniform centered sawtooth variance for `0 < ε < ½` (RH-strength).
- Off-diagonal prime-clock sign; theta cusp bounded-action remainder; inverse-overlap Sonin comparison
  for the squarefree source.
- Multiplicity: bounded critical multiplicities ⇔ uniform `E ≤ KW`; any unconditional `K`?
- Window remainder beyond VK; any statement between dlVP precision and `O(L)`.
- Optimal closed-cycle recovery order as a function of energy (only `O(n^{−1/2})` ambiguity decay known
  on fixed signed-grid fibres).
- Sieve moments for arithmetic (squarefree) rows beyond the cubic ceiling.

## 8. Traps

- Rearrangement circularity: every unconditional lower bound for `Re W_Λ` (signed coercivity,
  Chebyshev–packet, gauge, Laplace, band, cell, shear producers) has the mean-square Chebyshev error
  (or its band) as remainder; that remainder is RH-equivalent. Signed coercivity bounds have the grid
  sum on the right with positive weights; they are not positivity.
- Prime-free producers (Chebyshev slope `ψ(x) ≤ (log 4 + 4)x`) are `O(N)`: the trivial bound.
- Factorial producers: small pairing is bought with `log N` archimedean energy; their Weil positivity
  (zero side `c²Σ1/(ρ(1−ρ)) > 0`) holds for off-line zeros too and is not evidence for RH.
- Pole-free / rank-one-readout combinations carry no zero information.
- Gapped, sub-square-root or single-integer node sets never give zero-pole positivity; primes alone
  fail (node 4 needed); composites are free for single deletions but not for whole towers.
- Window extremes see `Λ` only through sizes (Liouville/character twists identical); they cannot
  separate `ζ` from twisted `L`-functions.
- dlVP/VK window remainders do not move the RH gap (`O(L)` needed).
- Polar balance is not closed under correlation+energy convergence; compactness arguments cannot
  produce polar positivity. Energy convergence needs origin control.
- Finite closed-cycle order never determines correlations within an energy class; recovery is only
  finite-accuracy.
- Exact multiplicative incidence is fragile under perturbation; use soft weights.
- Source zeros do not make sinh-multiplier correlations vanish (parity); multiplier leakage is
  unbounded relative to source energy. The plastic crossover is not `≥ 0` on odd sources (infimum
  `−2M²`, approached by escaping sources).
- Conditional theorems (`hRH : RiemannHypothesis` hypothesis: Cramér limit/tail, finite-cutoff packet
  asymptotics, probe Parseval/resolution, fourth-power limit) are consequences of RH.
- `ZeroDensityFilteredCriticalDeficitLaw` labels `2(1−σ)` on `[5/6,1]` "Density Hypothesis"; the proofs
  use the uniform Guth–Maynard bound there (no DH assumption).
- Wrapper modules with no new mathematics: `FundamentalTheoremsOfBiScaleUncertainty`,
  `HurwitzAnchorContactAndPrimeLogRajchmanClocks`, `TypeIPrimeAmplifier…`, `RamareGeometricLadder…`,
  `UniformConstantDischarges`; several "Pillar" numbers are duplicated.
- Misfiled modules: `RHTower.ThetaCuspDefect`, `RHTower.SquarefreeDiscrepancy`, Mertens and Robin
  modules live in this folder under `RHTower` namespaces.
- `ExplicitApertureSplineInputs` ends with `#print axioms` commands in source.

## 9. Place in the research

BSU is the corpus's dictionary between the explicit formula and archimedean energy on real tests.
- Imports: `RHTower` (explicit formula, `weilFullFunctional`, CCM deficit and Landau engine, Zeta23
  zero configuration, Hardy, sieve engines: Hoheisel, VK, Ingham/Huxley/Guth–Maynard, MV, Halász),
  `HTGeometry` (Kronecker density, circle Fourier uniqueness, Farkas duality, compactness, `L²`
  translate independence), `BezoutValuationIncidence` (`sieveSeq`), `TransHorizonIncidenceMechanics`,
  `ArithmeticCastelnuovoSeveri`, `SquareRootThreshold`, `arithmetic-positivity-theory`,
  `ArithmeticCriticalityTheory`, `Hurwitz`, `U0`.
- Consumers: `RHTower`, `BezoutValuationIncidence`, `arithmetic-positivity-theory` (Lévy symbol,
  signed prime–polar pairing, deletion prices, Müntz producers), `TransHorizonIncidenceMechanics`,
  `RenormalizedArithmeticPotentialTheory`, `SquareRootThreshold`, `ArithmeticOrientationTheory`,
  `CriticalArithmeticCorrelationTheory`, `ArithmeticCastelnuovoSeveri`, and single imports from
  `ArithmeticCriticalityTheory`, `ArithmeticIncidencePositivity`, `ArithmeticCorrespondencePositivity`,
  `ArithmeticIntersectionTheory`, `ArithmeticIndexDescent`, `BiarithmeticGeometry`,
  `CompletedArithmeticForms`, `ScaleSignedIncidenceCriticality`, `SpacingScaleHarmonicAnalysis`,
  `twin-prime`, `MainTheorems`.
- Shared language: the exact Weil identity, `ω`, `J`, `Ẽ`, packets, zero width, node criticality and
  deletion prices are used across these programmes; APT's critical families and BSU's factorial
  producers are the same objects seen from source and pairing side.

## 10. Big picture

RH is an uncertainty principle between the additive log grid and the multiplicative origin: a
correlation that vanishes at every prime power and carries no pole mass must pay archimedean energy
at least `|Ω(0)|` times its mass. BSU proves every shape of this principle unconditionally — collar
constants, logarithmic windows, linear log modulus, inverse-linear tails, blind polar sources costing
`log N` — but never with the constant `|Ω(0)|`. The constant is the theorem.

Which nodes matter is decided exactly: prime powers, each with price `Λ(m)/√m`, adding over primes
like an Euler product and coupling within a tower through the local Euler factor. Density is
irrelevant above the square-root threshold; incidence is everything. Composite nodes matter only
through lags of joint tests. So positivity is a statement about `Λ`, not about how many constraints
are imposed.

When blindness is dropped, the prime side collapses to one object: the Chebyshev error `ψ(x) − x` seen
in the gauge `e^{−t/2}`, i.e. the critical-line band `|t| ≤ √x` of `ζ'/ζ`. Every packet, every
producer, every window bound reads this band, and every growth rate of it is a zero-width rate. RH is
"linear band", "bounded packet", "window ceiling `e^{L/2} + O(L)`", "bounded critical deficit" — the
same statement in different coordinates. The programme's unconditional results reach exactly the
classical PNT strength (dlVP, VK, zero density) and stop at the square-root barrier.

The observation side says that the RH-relevant quantities are unstable: polar balance is not closed,
finite-order cycle data never suffice, exact incidence breaks under perturbation, sieve phases need
degree six. Positivity cannot be obtained by limits, compactness or finite observation; it has to come
from an exact arithmetic identity at the square-root scale.
