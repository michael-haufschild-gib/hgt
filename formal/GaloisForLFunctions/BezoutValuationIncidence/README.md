# Bézout–Valuation Incidence (BVI)

Umbrella `BezoutValuationIncidence.lean` (~370 modules, flat folder). Namespace
`GaloisForLFunctions.BezoutValuationIncidence`. Inputs: `RHTower` (ζ bounds, VK/dlVP zero-free
regions, Littlewood, Mertens rates, sieve and Weil/Kloosterman, `receiverDampings`), `HTGeometry`
(digamma, Mellin–Plancherel), `BiScaleUncertainty`, `TransHorizonIncidenceMechanics`, `PNTPlus`, plus
bridge imports from `RenormalizedBiarithmeticGeometry`, `SelectivePositivityAndThresholdLaws`,
`ArithmeticElectrostatics`, `SquareRootThreshold`.

## 1. Motivation

Every truncated-divisor route to RH works with a finite row `c(1..N)` and its response
`s_{N,c}(k) = Σ_{d|k, d≤N} c(d)` on windows `M ≤ N^A`, while the period `lcm(1..N) = e^{ψ(N)}` is
unreachable. Three integer structures act there and nowhere in an abstract multiplicative system:

- **Bézout**: `gcd(k, k+1) = 1`; least seeds of `pa − qb = h`.
- **Valuation**: lag `h` sees Ramanujan mode `q` iff `q/rad q | h`.
- **Incidence**: the matrix `1_{d|n}`, its sawtooth `{n/d}` and floor geometry.

BVI builds the finite calculus of these rows: which data determine a row, which quadratic forms are
blind, how prefix discrepancies become pronic energies with a von Mangoldt readout, and how the RH
receiver (Route PM)

`E_T(ε) = Σ_{n≤T} A_ε(n)²/(n(n+1))`, `A_ε(n) = Σ_{d≤n} μ(d)d^{−ε}⌊n/d⌋ − n/ζ(1+ε)`

decomposes into signed pieces. It then separates what is unconditional (identities, observability,
cross-scale dispersion below the diagonal, VK bands) from what is exactly a zero-free strip or RH.

## 2. Objects

Rows and coordinates.
- `sieveSeq N c k = s_{N,c}(k)`; harmonic mean `H = Σ c(d)/d`; prefix discrepancy
  `L_N(M,c) = Σ_{k≤M} s − MH = −Σ_d c(d)(M mod d)/d = Σ_{e≥2} Re R_e(M)Y(e)` (`R_e` Ramanujan
  primitive).
- Selberg coordinates `Y_{N,c}(q) = Σ_{q|d≤N} c(d)/d`; inversion `c(d) = d Σ_{m≤N/d} μ(m)Y(dm)` realises
  any `Y`. Spectral form `s(k) = Σ_{ζ∈T_N} Y(ord ζ)ζ^k` (`T_N` = roots of order `≤ N`).
- Witt ghost coordinates (`wittSieveReceiver`): `Y(q) = ghost_q`; Frobenius 2 consumes cutoff `2N`.
- Visibility clock `clock(q) = q/rad q`; lag coefficient `c_q(h) = Σ_{d|q}μ(q/d)d·1_{d|h}`.
- Möbius bands: `s_{N,μ} = 1_{k=1}` on `[1,N]`, `−μ(k)` on `(N,2N]`, complementary quotients
  `−Σ_{q≤B, q|k, qN<k} μ(k/q)` on `k ≤ (B+1)N`.

Period quadratic forms (diagonal in `Y`, weight at `e ≥ 2`).
- variance `V` (`φ`), successor covariance (`μ`), reserve `R = Q_Sel − Q_Bez` (`φ − μ`), phase loss
  (`φ − μ²/φ`), primitive energy `12E_prim` (`J₂`), lag covariance `Cov(h)` (`c_e(h)`), tuple variance
  (`S_q(H) = Σ_{ζ prim q}|Σ_{h∈H}ζ^h|²`).

Pronic objects.
- Pronic weight `w(M) = 1/(M(M+1))`; `Σ_M R_e(M)w(M) = −Λ(e)`; readout `ℛ(c) = Σ_e Λ(e)Y(e) =
  Σ_d c(d)log d/d`.
- Pronic Gram `𝒢 = ΛΛᵀ + 𝒢^ec`; mean-centred `𝒢^mc = 𝒢^ec + κκᵀ`, `κ(q) = φ(q)/2 − Λ(q)`.
- Vasyunin sums `V(h,k) = Σ_{a<k} cot(πa/k)((ha/k))`; Báez–Duarte residual
  `Σ_M (1 + L_N(M,c))² w(M) = (1 − ℛ)² + Q^ec(c)`.

Sawtooth and Route PM.
- `B̃₁(d,n) = {n/d} − (d−1)/(2d)`; `W = −Σ c(d)B̃₁(d,·)`, `ΔW = s − H`. At step `n → n+1` moduli
  split into `d|n` (post-jump peak), `d|n+1` (pre-jump trough), **Bézout interior** (neither).
- `τ_ε(n) = Π_{p|n}(1 − p^{−ε})` (radical-invariant, GCD–LCM modular), `α_ε = ρ_ε = 1/ζ(1+ε)`,
  interior prefix `I_ε`, active pair `S_ε ∈ [0, ½]`.
- `receiverDampings` (bounded `E_T`), `receiverDampingRate` (inf); parity twin `c'_ε` (same `|Y|`,
  flipped signs).

Damping chain.
- Cesàro kernel `K_η(n,k)` (stochastic, semigroup `K_sK_t = K_{s+t}`); entrance law
  `π_η(k) = ρ_η k(k^{−1−η} − (k+1)^{−1−η})`; centred `C_η = K_η − π_η`; residue modes
  `v_d(n) = ⌊(n+1)/d⌋/(n+1) − 1/d`; size-bias `h`-transform `h(k) = 1/(k+1)`.

Cross-scale objects.
- Rows `c` (small moduli `~P`) and `c'` (large scale `~Q`); `θ = 2log P/log Q`.
- `B(c,c') = Σ_M V_c V_{c'} w`; row mean `m`, Dirichlet constant `β`, readouts `R, H`.
- Potentials `Φ_d(M) = (d²/2)B₂(ρ/d) − 1/12 = Σ_{η∈T_d} η^M/|η−1|²` (PD on `ℤ/d`),
  `Ψ_d` (cubic); kernels `𝔅(d,n) = Σ_j Φ_d(jn)/j²`, `𝔅₃(d,n)`; residue mean `m_d`.
- Kernel statistic `Λ_d(c') = Σ (c'/n²)(𝔅(d,n) − m_d) + Σ (c'/n³)𝔅₃(d,n)`; dual norm `Σ_{d∈S}|Λ_d|/d`.
- Actual rows: Möbius block `μ1_{(Q,2Q]}`, centred prime block `(Λ − 1)1_{(Q,2Q]}`.

Vaughan objects.
- Five pieces at cutoffs `U, V` (two small legs, small×small convolution, both-large, pole); centred
  Gram `G_{ij}(T)`; smooth signs `s = (0,0,−1,1,0)`; smooth coefficient `c_ε`; harmonic partials
  `μ̃_U = Σ_{d≤U} μ(d)/d`; amplitude set `A = {μ̃_U²μ̃_V²}`; admitted coefficient submodule of `ℝ⁵`.

Cofinal Möbius.
- Profile `P(B) = lim E_N((B+1)N)/N`; band slope `γ_t`; slope `κ = lim P(B)/B`; period mean square
  `C(N) = Σ_{d,e≤N} μ(d)μ(e)/[d,e]`; `w = μ/σ`, coprime profiles `g_δ(v) = T_δ(⌊e^v⌋)`.

Reciprocity kernel.
- `W_K(p,n) = 𝔅(p,n) + π²(p²−1)/(72p)` on `p∤n`; coefficients
  `C_m(p) = (π²p/2)Σ_k β_p(k)β_p(m k̄ mod p)`, `β_p(k) = B₂(k/p) + 1/(6p)`.

## 3. Language

- **Row**: finite `c` on `[1,N]`. **Response / signal**: `s_{N,c}`. **Mode** `q`: Selberg coordinate
  `Y(q)`. **Active order**: `Y(q) ≠ 0`. **Recurrence complexity**: `Σ_{Y(q)≠0} φ(q)`.
- **Layer** (at `p^a`): orders with `p^a ‖`-top valuation. **Layer admissible**: no layer count `= 1`
  (and even at `p = 2`). **Companion**: half-period reflection flipping the top dyadic layer.
- **Common return**: `M` divisible by every `d ≤ N`. **Arbitrary phase**: any window start.
- **Pronic / energy-centred / mean-centred**: the three Grams. **Readout**: `ℛ`.
- **Paid / admitted**: bounded pronic norm. **Extra rank**: receiver direction admitted.
- **Coherent window**: `n₀` near `0 mod d` for most small moduli; **anti-coherent**: near `d/2`.
- **Below / on the diagonal**: `θ < 2` / `θ = 2` (`d ≍ Q`). **Minor arcs**: roots of large order.
- **Omitted class**: residue `0 mod p` missed by primes.
- **Sign-blind**: depends only on `(Y(q)²)` or `|s|`.
- **Strip statement**: equivalent to `Θ < 1`; **RH statement**: to `Θ = ½`.

## 4. Mechanisms

1. **Bézout splitting.** Divisor pairs of `(k, k+1)` ↔ divisors of `k(k+1)`; coprime `d₁,d₂ ≥ 2` give no
   prime power: `Λ(k(k+1)) = 0`; `F(k)F(k+1) = F(k(k+1))` for every GCD–LCM modular `F`;
   `τ_ε(k)τ_ε(k+1) ≤ 1 − 2^{−ε}` (2-adic ceiling), three-step `≤ τ_ε(6)`. The input fails in Beurling
   systems.
2. **Simultaneous diagonalization.** All complete-period quadratic forms are diagonal in `Y`;
   modal inequalities `2μ ≤ φ` (equality `e = 6`), `4μ ≤ φ` off 6, `(q+1)φ ≤ J₂`, `J₂ ≤ n²φ` give exact
   joint moment regions, sharp frontiers, finite-generated lag-covariance cones (`G_h` from `(h!)²`).
3. **Polarization.** `2R_N(M) = −Σ(Δs)² + s(M+1)² − s(1)²`; CRT sawtooth `Σs(k)s(k+1) = MQ_Bez + O(‖c‖₁²)`;
   renormalization is forced (raw Möbius defect is linear).
4. **Observability.** Monic cyclotomic recurrence `Π_{q≤N}Φ_q` (degree `Φ(N) = Σφ(q)`) kills every
   response; `Φ(N)` consecutive values at any phase determine the row; minimal recurrence = support
   totient mass. Superlinear CRT grids kill responses on `mN` points: **no linear horizon at
   arbitrary phase** (2N − 3 holds only at common returns). Window sandwich constant exact order
   `N²`; degree-`m` translated moments transfer at exact order `N^m`.
5. **Moment visibility.** Sign pattern `ε` visible at degree `m` ⇔ some layer-admissible active
   `m`-tuple has `Πε ≠ 1` (complete classification). Odd modes at degree 3; `{2p, 2r}` exactly at
   degree 6; degrees 5–6 determine a row up to the companion; quantitative `|ΔY|⁵ ≤ 16·relation energy`.
6. **Pronic Gram calculus.** Pronic character series `1 + Q(z)`, `Q(z) = (1−z)log(1−z)/z` ⇒
   `𝒢^mc(p,q)` = cotangent–sawtooth = Vasyunin sums; Möbius–Vasyunin: `𝒢` is the double Möbius
   transform of Nyman–Beurling residue second moments; Vasyunin reciprocity = residue-difference
   pronic energy (exact order `h(1 + log⁺(p/h))`); `𝒢^ec` strictly PD.
7. **Báez–Duarte in rows.** Residual `(1 − ℛ)² + Q^ec`; Rayleigh minimum `Q^ec/Q`; unconditional floor
   `κ/log N` ⇒ uncertainty `κℛ² ≤ (log N − κ)Q^ec`.
8. **Sawtooth martingale calculus.** `E_T = active-deleted diagonal + 2·predecessor peak +
   2·interior martingale`; first two have explicit drifts with `O(1)` compensated remainders; the
   interior equals `½E_T − counterterm·H^comp + O(1)` with coefficient one. Summation by parts is a
   conservation law, never a contraction.
9. **Vaughan calibration.** Five pieces sum to the interior prefix; `E^int = ΣG_{ij}`; diagonal linear
   (pole mass), `mixed/diagonal → −1` unconditionally; normal form: packet = linear drift +
   smooth power `n^{1−ε}` (coefficient `c_ε μ̃_U μ̃_V(w₃ − w₂)`) + receiver direction `w₃` + bounded.
   Admission rank: 4 (`ε > ½`), 3 (`ε = ½`), 3 or 2 below (3 ⇔ interior bounded).
10. **Uniform logarithmic laws.** Divisor-square bounded families with uniform log partial-sum rates
    keep every log rate through the damped floor transform; centred Vaughan Gram =
    `(c_ε μ̃_U μ̃_V)² ssᵀ T^{1−2ε}/(1−2ε) + O(T^{1−2ε}/log^q T)` uniformly.
11. **Damping chain = vertical shift.** Residue-mode coordinates diagonalize `C_η` (eigenvalue `e^{−η}`):
    the chain is `F(s) ↦ F(s+η)` on Dirichlet series; reciprocal orbit coefficients `μ(e)e^{−η}` = 1/ζ.
    Pronic dual norm of the entrance law finite ⇔ `η > ½`; `h`-transform makes it bounded at every `η`.
12. **Cross-scale rank-two law.** `B + mR' + βH' = Σ c'(n)(c(d)/d)(𝔅(d,n)/n² + 𝔅₃(d,n)/n³) + …` to every
    order (potential chain); the cross-scale form sees only residue masses `n mod d` plus two readouts
    (parity-blind); exact loss = `ℓ¹` residue discrepancy at rate `π²/72`; reduction to the single-modulus
    dual norm `Σ|Λ_d|/d`.
13. **Barrier and ladder.** Coherent near-multiples ⇒ Type-II barrier `Q ≍ P^{5/3}` (sharp, survives both
    rank-two side conditions); sharp-cutoff Type I stops at `4/3`; smooth order `K` reaches
    `θ = 2K/(K+1)`; block equidistribution / twisted short-interval square-root cancellation is the exact
    replacement hypothesis.
14. **Minor arcs vs archimedean place.** Vinogradov/Vaughan decomposition at exact denominator `p`
    (only additive structure of ℕ, not Weil): actual rows have power saving at every modulus
    `Q^δ ≤ d ≤ Q^{1−δ}`; on the diagonal the low harmonics are slowly varying weights and the statistic
    is a functional of long-window partial sums only (Mertens / `ψ(x) − x`).
15. **Möbius inversion of the kernel.** `μ⋆1 = δ` collapses both kernels: full-row statistic is explicit
    `(d−1)(d−3)/4 − (6/π²)m_d`; all arithmetic of Möbius window statistics sits in the window cutoffs.
16. **Zero-free bands.** Rate hyperbola transfers Mertens rates to the receiver on horizon-dependent
    bands (dlVP width `1/(80√log T)`, VK width `κσ(T)/(480 log T)`); Littlewood gives `ε > Θ/2`.
17. **Cofinal Möbius laws.** Finite alphabet of cofinal values, explicit value law, clock support;
    slope `κ` = period variance = signed coprime-energy sum = one-line energy of `1/ζ` on `Re s = 1`.

## 5. Pillar theorems

Observability and moments.
- `not_exists_linear_observability_horizon`; `windowSandwichConstant_exact_quadratic_order`;
  `sameRelationSpectrum_five_six_iff` (degrees 5–6 classify up to companion).
- `periodCovariance_eq_iff_exists_scaledSelbergRow` (complete-period data = sign orbit);
  `primePairWeights_transHorizon_separated` (`δ₂ ± δ₃`: same period data, separated trans-horizon).
- Log-free large sieves: `largeSieve_set_properFarey_logFree`, `largeSieve_expSum_fareySet_logFree`,
  `arithmetic_largeSieve_montgomeryVaughanConstant` (`N + Q² − 1`).

Pronic Gram and Báez–Duarte.
- `pmRamanujanMeanCenteredGram_eq_cotangent_sawtooth`; `vasyunin_reciprocity_exact`,
  `vasyunin_reciprocity_exact_order`.
- `riemannHypothesis_iff_pronic_prefix_energy`; `exists_readout_energy_uncertainty`.

Reciprocity kernel.
- `bernoulliKernel_sub_primeKernelMean_eq_ramanujan_add_kloosterman` (Ramanujan sum + Kloosterman wave);
  `exists_abs_reciprocityKloostermanCoeff_ge` (Weil bound `|C_m(p)| ≤ (π²/24)p^{3/2}` order-sharp);
  `abs_pmRamanujanEnergyCenteredGram_sub_rankThree_kloosterman_le` (prime Gram = rank three +
  `W_K(p,q)/q` ± `¾p³/q²`).

Receiver structure.
- `exists_pmBezoutInterior_compensated_energy_bound`, `pmInterior_strict_contraction_iff_bounded_energy`
  (interior martingale is energy in disguise).
- `exists_receiver_le_on_vinogradovKorobovBand`, `exists_receiver_le_on_vinogradovKorobovBand_of_pos`;
  `receiverDampingRate_sandwich` (`Θ − ½ ≤ rate ≤ Θ/2`), `receiverDampingRate_lt_half_iff`.
- `mem_receiverDampings_iff_hTransformed_hilbertSchmidt`;
  `bounded_naturalDilationHeadEnergy_iff_mem_receiverDampings` (natural cutoff = receiver);
  `tendsto_hypercubeDilationDirichletForm_primeBlockProd` (prime-support truncation diverges `< ½`).

Vaughan.
- `pmPronicVaughanRankDampings_eq_receiverDampings`, `riemannHypothesis_iff_accPt_zero_vaughan_rank`,
  `finrank_pmPronicVaughanAdmittedSubmodule_of_half_lt`, `rank_pmPronicVaughanLimitGram` (rank 2, `ε ≥ ½`).
- `zetaZeroAbscissa_lt_one_iff_uniform_pmUndampedVaughan_power`.
- `pmPronicVaughanCentredGram_limit_set_eq`, `pmPronicVaughanCentredGram_converges_iff_escape_or_fixed_amplitude`,
  `accPt_pmVaughanSmoothAmplitudeSet_iff` (limit set compact, countable, infinite, accumulation only at 0),
  `exists_horizon_vaughan_zero_and_relative_rank_one_limits`.

Cross-scale.
- `abs_rowBilinear_add_mean_add_beta_le_smoothnessNorm` (every-order smooth law);
  `abs_rowBilinear_add_mean_add_beta_sub_smooth_all_le` (all moduli); `exists_readout_free_barrier`.
- `norm_sum_moebius_mul_pow_le` (minor-arc Möbius at prime roots);
  `abs_kernelStatistic_moebiusWindowRow_le_rpow`; `crossScale_dichotomy_moebius_and_centredPrime`;
  `crossScale_allModuli_moebius_and_centredPrime_le_rpow`;
  `exists_kernelStatisticAll_moebius_and_centredPrime_le_everyModulus`.
- `exists_abs_rowBilinear_centredPrimeRow_le` (prime row passes the coherent-block obstruction, Huxley).
- `hasSum_moebius_mul_kernelTerm` (Möbius inverts the kernel).

Strip equivalences (all `⇔ Θ < 1`).
- `balancedStatisticPowerSaving_iff`, `centredPrimeBandPowerSaving_iff`, `moebiusPowerWindowSaving_iff`,
  `primePowerWindowSaving_iff`, `quasiRH_crossRoute_seven_way_tfae`.
- `escapedMoebius_receiver_abscissa_tfae`, `escapedMoebius_rbg_seven_way_tfae` (pointwise at `θ`).

Cofinal Möbius.
- `tendsto_sieveL2PrefixEnergy_div` (energy transfers at every superlinear horizon to `κ`);
  `tendsto_twelve_mul_sievePrimitiveEnergy_moebius_div` (`12E_prim/N → c ≈ 0.3311`: diffusive).
- `cofinalMobiusSlope_eq_tsum_coprimeEnergy`, `cofinalMobiusSlope_eq_integral_one_line`,
  `cofinalMobiusSlope_eq_integral_eulerProduct`.

Unconditional ceilings.
- `exists_abs_escapedPairing_moebiusSource_le_vk_rate`; `exists_reading_logHorizon_vk_ceiling`,
  `tendsto_reading_logHorizon_div_sq_zero` (VK sub-trivial theta-prefix ceiling).
- `not_eventually_moebiusCombinedPrefixDefect_le_rpow` (raw defect not sublinear).

## 6. Tools developed and tools still to build

Developed.
- Selberg / spectral / ghost coordinates with Ramanujan inversion; exact joint moment regions and
  finite cone certificates for lag inequalities.
- Cyclotomic recurrence observability; zero-product relation classification; relation-spectrum Parseval.
- Log-free large sieve (window-sandwich and Montgomery–Vaughan constants), multiplicative and arithmetic
  forms; discrete Gallagher inequality; dilated large sieve (factor `j`).
- Pronic calculus: character series, cotangent–sawtooth Gram, Vasyunin formulas, Báez–Duarte residual,
  pronic tails at the quadratic horizon, higher pronic weights `u_k`.
- Sawtooth/Bézout layer calculus (active, predecessor peak, interior, arbitrary-depth shells).
- Cross-scale law of every order; Bernoulli/cubic kernels in Fourier, reciprocity and Kloosterman form;
  residue-discrepancy, block, smoothness and dual-norm reductions.
- Minor-arc laws at prime and composite roots (Vinogradov/Vaughan, no Weil); archimedean diagonal law.
- Vaughan pronic Gram toolkit (normal form, admission rank, uniform log laws, limit sets).
- Damping chain: semigroup, entrance law, compact centred operator, spectrum, residue-mode
  diagonalization, `h`-transform, paired Markov work FTC.
- Cofinal Möbius machinery: dilation means, coprime cancellation, harmonic fibres, alphabet and value law.
- VK/dlVP rate hyperbola; Littlewood transfer; escaped-pairing VK bound.

Still to build.
- A **signed interior contraction** `2M^int + 2·counterterm ≤ (1−δ)E_T + C` at one fixed `ε < ½`
  (must use mixed Vaughan entries / Bézout structure; diagonal data are blind).
- A balanced (`θ = 2`) dispersion gain beyond zero-free-region quality.
- Twisted short-interval square-root cancellation at length `P²/(aX)` for actual prime packets
  (replacement hypothesis of the Type-II barrier at fixed exponent).
- Dual rows with `ℛ²/Q^ec → ∞` (equivalent to RH) or energy-variance vanishing along small-ε paths.
- Forward `ℓ²` chain bound below `½` reading Möbius signs.
- Sharp arbitrary-phase observability horizon `H(N)` (between `≫ N` and `Φ(N)`).

## 7. Open questions and research topics

1. **Receiver at one fixed `ε < ½`** (equivalently: bounded interior energy, strict contraction, first
   chain column in `ℓ²`, extra Vaughan admission rank, bounded dual residual). Strip-strength.
2. Can mixed Vaughan entries `G_{ij}`, `i ≠ j`, carry a Bézout-selective identity that the diagonal cannot?
3. Is there a gain at the diagonal from averaging over moduli or the CRT block of `(p, q)` beyond
   single-modulus statistics (Kloosterman reciprocity is order-sharp at one prime)?
4. Cross-depth cancellation: a hypercube or natural-cutoff dilation form uniform in the cutoff for
   `0 < ε ≤ ½` that keeps μ signs.
5. A finite, cutoff-quantitative statistic separating the parity pair below the VK band.
6. Exact growth of `H(N)/N`; exact optimal sandwich constant `/N²` (`∈ [3/π², 1]`).
7. Positivity and value of `κ` (one-line energy of `1/ζ` with Euler factors in `(0,1)`); rate of
   `C(N) → κ` beyond `(log N)^{−3}`.
8. Whether Witt structure (Frobenius / Verschiebung) yields an estimate Selberg coordinates do not.

## 8. Traps

| Trap | Correct statement |
|---|---|
| Multiplicative identities can close the gap | Beurling systems satisfy them all; need `gcd(n,n+1)=1`, `pa−qb=h`, omitted classes |
| Complete-period quadratic data decide the row | They are exactly sign-blind (`(ℤ/2)^{N−1}` orbits); trans-horizon / linear data separate |
| Observation needs the period `lcm(1..N)` | `Φ(N) ≤ N(N+1)/2` values suffice at any phase |
| A linear observation horizon exists | Only at common returns; at arbitrary phase it is superlinear |
| Degree-`m` statistics transfer at `N²` | Exact order `N^m`; no moment argument reaches a linear horizon |
| Compressed lags form a semigroup | Prime-power revival defect `−1/(p−1)` |
| Raw Möbius defect is small | Linear in `N` (terminal primes); only the renormalized defect is controlled |
| Summation by parts is an estimate | It returns `E_T` with coefficient one |
| Relative Vaughan cancellation is progress | `mixed/diagonal → −1` unconditionally; need `|1 + mixed/diag| = O(1/T)` |
| A uniform Vaughan / tail / window power gain is new | Each is exactly a fixed strip `Θ < 1` |
| Factorial log-rate order 3 → 1 is technical | Order one is exactly a strip |
| Prime-support truncation organises cancellation | Hypercube form diverges below `½` (sign-blind threshold) |
| Far scales decouple for arbitrary coefficients | Only `Q ≥ P^{5/3}` (coherent near-multiples, side conditions don't help) |
| The cross-scale form can see parity | Only residue masses + two readouts |
| Flat/smooth rows model primes | Sharp cutoffs stop at `4/3`; actual rows are not smooth |
| Sub-Weil saving for `C_m(p)` at one prime | Weil bound is order-sharp (`p ≥ 67`) |
| Constant centring removes the prime anomaly | Omitted class `0 mod p` survives (`QΛ_p → −π²(p²−1)²/(144p²(p−1))`) |
| A diagonal power saving is weaker than a strip | `balancedStatisticPowerSaving_iff`: it is a strip |
| A Mertens rate bounds the receiver at fixed `ε < ½` | Only on a horizon-dependent band |
| Pointwise prefix bounds suffice | Lose half the width (`Θ/2` vs `Θ − ½`); estimate in mean square |
| Total variation of the chain controls the receiver | Entrance tail non-square-summable for `η ≤ ½` |
| Another quasi-RH or RH equivalence is progress | Dozens are unified (rank, tail index, escaped boundary, Carathéodory, theta prefixes); none is a bound |
| Endpoint rates are attainable with `o` | `M(x) = Ω±(√x)` forbids it; attained endpoint rates force RH and simple zeros |
| First pronic moment carries the exponent | The leading coefficient is the cutoff mean value |
| Matomäki–Radziwiłł / Huxley give power savings | Only `o(1)`; a power saving is `Θ < 1` |

## 9. Place in the programme

- **Upstream**: RHTower (all analytic inputs and the receiver definitions), BiScaleUncertainty (full-period
  moment recovery; BVI supplies window lengths), TransHorizonIncidenceMechanics (horizon rows, rate
  transfer, two-way: THIM imports ~46 BVI modules, BVI ~39 THIM modules), HTGeometry, PNTPlus.
- **Downstream**: THIM (window laws, parity pairs, receiver symmetries), BiScaleUncertainty,
  ArithmeticContinuationAndCriticalEnergy (signed damping work), SignedSuccessorArithmetic (successor
  defects recover signs), ArithmeticDefectRigidity, ArithmeticCompensationTheory, CriticalArithmeticCorrelationTheory,
  ArithmeticGaugeTheory, RenormalizedArithmeticPotentialTheory, ArithmeticCorrelationGeometry,
  ArithmeticIndexDescent, ArithmeticCountingPositivity, CompletedArithmeticForms, ArithmeticOrientation*,
  TransThresholdPairCorrelation, SelectivePositivityAndThresholdLaws, goldbach, twin-prime, MainTheorems.
- **Role**: the finite arithmetic and pronic Gram engine of the corpus. It owns divisor rows, Selberg
  coordinates, the pronic (Nyman–Beurling) calculus, the Route PM receiver decomposition, and the
  cross-scale (Type I/II) dispersion theory; other programmes read its identities and its exact
  equivalences.

## 10. Big picture

BVI shows where the RH difficulty is, and that it does not move under reformulation. Everything finite
and structural is in hand: rows are determined by polynomially many values at any phase, the
Nyman–Beurling Gram is an explicit cotangent sum, the Báez–Duarte residual splits into a readout and a
centred energy, the receiver splits into pieces whose drifts are computed, and cross-scale correlations
are dispersed unconditionally at every exponent below the diagonal using only the additive structure
of the integers.

Every remaining gap collapses to one place: the diagonal `d ≍ Q`, the Bézout interior martingale, the
receiver below half damping. There the statistic is a functional of long-window Möbius partial sums and
nothing else, so its quality is exactly the zero-free region: power savings there are `Θ < 1`, endpoint
rates are RH. Quadratic, period and diagonal data are provably sign-blind, so no positivity argument
built from them can see the zeros. A proof must inject a new signed input at the diagonal — a
cancellation of Möbius on long windows stronger than the zero-free region provides — and BVI's value is
that it has reduced every finite route to that single, sharply identified statement.
