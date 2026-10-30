# Trans-Horizon Incidence Mechanics (THIM)

Umbrella `TransHorizonIncidenceMechanics.lean` (~240 modules, flat folder). Namespace
`GaloisForLFunctions.TransHorizonIncidenceMechanics`. Inputs: `RHTower` (ζ/L bounds, zero-free
regions, VK, CHMD odd sector, `receiverDampings`), `BezoutValuationIncidence` (sieve rows, Selberg
coordinates, complete-period forms), `BiScaleUncertainty`, `HTGeometry`,
`ArithmeticCriticalityTheory`, `ArithmeticIncidencePositivity`, `HilbertMetric`.

## 1. Motivation

Every truncated-Möbius route to RH (Nyman–Beurling/Báez-Duarte, Selberg mollifiers, Route PM
cofactor rows) runs through a finite divisor observer of horizon `N`:

`s_{N,c}(k) = Σ_{d|k, d≤N} c(d)`.

For `k ≤ N` it is the full divisor sum; for `k ≫ N` it omits divisors. The RH-relevant quantity is a
horizon-uniform statement about the omitted part, the receiver energy

`E_T(c) = Σ_{n≤T} A_c(n)²/(n(n+1))`, `A_c(n) = Σ_{d≤n} c(d)⌊n/d⌋ − n·Σ_d c(d)/d`.

RH ⇔ `E_T(μ(d)d^{−ε})` is bounded in `T` for every `ε > 0`
(`riemannHypothesis_iff_forall_pos_receiverBounded_moebius`). THIM asks:
1. What does the finite observer conserve, dissipate and recover beyond its horizon under
   `k ↦ k+1`, `N ↦ N+1`, `k ↦ pk`?
2. Which sign statements (renormalized defect `≤ 0`) and energy statements survive `N → ∞`?
3. Which data decide whether a weight is *paid* (`sup_T E_T < ∞`), and which data are provably blind?

## 2. Objects

Observer.
- `sieveSeq N c k = s_{N,c}(k)`; horizon row `horizonRow c N = c·1_{d≤N}`; dyadic rows `c·1_{d≤2^J}`.
- `L_N = lcm(1..N)`; observation state `σ_N(k) = gcd(k, L_N)`; radical state `R_N(k) = gcd(k, N#)`;
  phase `k mod L_N`. Trans-horizon rough `r`: all prime factors `> N` (⇔ `R_N(r) = 1`).
- Valuation clock `d/rad d` (`lagVisibilityClock`): Ramanujan mode `q` visible at lag `h` iff
  clock`(q) | h`.
- Band normal form, `BN < k ≤ (B+1)N`: `s_N(k) = Σ_{d|k}c(d) − Σ_{q≤B, q|k} c(k/q)`.

Weights.
- `μ`; damped Möbius `c_ε = μ(d)d^{−ε}`, `τ_ε(k) = Σ_{d|k}c_ε(d) = Π_{p|k}(1 − p^{−ε}) ∈ [0,1]`;
  Liouville `λ`; real characters `χ`, `χ₄`; smooth power `d^{−ε}`; Selberg row `μ(d)log(N/d)`;
  Route PM cofactor row `c_Q` (its horizon-`Q` response is the truncated Ramanujan expansion of `τ_ε`).
- Completely multiplicative patterns `f(d)d^{−ε}`: `z^{Ω(d)}`; residue flips `f_{q,S}`
  (`f(p) = −1 ⇔ p mod q ∈ S`); subgroup flips; oscillating `a cos(t₀ log p + φ)`; finite spectra
  `c₀ + Σ_k Re(B_k p^{it_k})`; amplitude defects `(1 − d(p))cos(t₀ log p)`.
- Parity twins: same Ramanujan amplitudes, flipped signs (`c'_ε`; `χ₄`-twin `∝ 1_odd d^{−ε}`;
  Liouville twin `κd^{−ε}`; even flip `c^♭`).

Spectral coordinates and period forms.
- Selberg coordinates `Y_{N,c}(e) = Σ_{e|d≤N} c(d)/d`, `Y(1) = H_N(c)`. For `c_ε`, `Y → w_ε(e) =
  ρ_ε μ(e)/D_ε(e)`, `ρ_ε = 1/ζ(1+ε)`, `D_ε(e) = Π_{p|e}(p^{1+ε} − 1)`.
- `Q_Sel = Σφ(e)Y²`; `Q_Bez` (coprime part); successor reserve `R_N = Q_Sel − Q_Bez =
  Σ_{e≥2}(φ−μ)(e)Y²`; covariance `Cov_N(h) = Σ_{e≥2} c_e(h)Y(e)²`; primitive energy
  `12E_prim = Σ J₂(q)Y(q)²`.
- Ramanujan coefficients of a weight `W_c(e) = Σ_k c(ek)/(ek)`.

Defects and horizon steps.
- Prefix energy `E_N(M) = Σ_{k≤M} s_N(k)²`; renormalized defect `D_N(M)` with Dirichlet polarization
  `2D_N(M) = −Σ_{k≤M}(s(k+1) − s(k))² + s(M+1)² − s(1)²`.
- Step `Δ(m,B) = E_m(M) − E_{m−1}(M)`, `B = ⌊M/m⌋`; Buchstab slope
  `λ(m) = 1 + 2μ(m)Σ_{d<m}μ(d)gcd(d,m)/d`; band mean `A(B)`; profile `P(B) = lim E_N((B+1)N)/N`.

Fermi observer.
- Cell response `F(n) = Σ c(d)(2⌊n/2d⌋ − ⌊n/d⌋)`, boundary jumps `J(n)`, dyadic rays `n = 2^k b`
  (`b` odd). Schedules = observed 2-adic levels: selected (odd + `4|n`), all-boundary, one-gap at level
  `g`; p-adic cells `p⌊n/pd⌋ − ⌊n/d⌋`. Inverse constant `K_N = sup(sieve energy / trace energy)`
  in pronic weights `1/(n(n+1))`.

Receiver.
- `ReceiverBounded c` (paid). Damped class `𝒞(K,ε) = {|c(d)| ≤ Kd^{−ε}}` (`DampedClass`).
- Critical Wiener algebra `Σ_j |k(j)| j^{−1/2} < ∞` (`CriticalWiener`); pole value
  `K(1−ε) = Σ k(j)j^{−(1−ε)}`; partial pole sums `S_k(n) = Σ_{j≤n} k(j)j^{−(1−ε)}`.
- Mellin pairing `Φ(s) = Σ_n A(n)(n^{−s} − (n+1)^{−s}) = ζ(s)(C(s) − m)`, `C(s) = Σ c(d)d^{−s}`,
  `m = C(1)`; line energy `∫|Φ(σ+it)/(σ+it)|² dt`.
- Probes `d^{−ε}cos(t log d)(log d)^k`; `receiverDampings`, `signBlindDampings`;
  `Θ = zetaZeroAbscissa = sup Re ρ`.
- First pronic moment `M(c) = Σ_n A_c(n)/(n(n+1))`; log moments `M(c·log^k)`; higher von Mangoldt
  `Λ_{k+1} = Λ_k·log + Λ_k ⋆ Λ`.

Odd sector (CHMD).
- Theta kernel `Θ`; odd profile `m_a(x) = (Θ(x−a) − Θ(x+a))/(2sinh(a/2))`; polar function `Ψ_a`;
  `sourceEnergy`, `sourcePair`, `weilForm`; odd resolvent eigenvectors (eigenvalue `μ`), lobes `q^±`,
  nodal defect; pole moment `⟨q, tanhL⟩`; collar/direct/across jumps; Lévy density
  `ω(s) = e^{−s/2}/(1 − e^{−2s})`.

## 3. Language

| Term | Meaning |
|---|---|
| sub-/trans-horizon | `k ≤ N` (complete divisor sum) / `k > N` (divisors `d > N` omitted) |
| radical ratio | `R_N(k)/(N+1)`; controls the Möbius envelope |
| iso-state window | endpoint states agree; polarization boundary term vanishes |
| paid / unpaid | receiver energy bounded / unbounded in `T` |
| sign-blind | depends only on `|W_c|`, `|c|`, `Y²` or other `(ℤ/2)^N`-invariant data |
| complete-period | quadratic statistic over a full period `L_N` (diagonal in Selberg coordinates) |
| parity pair | identical sign-blind data, one paid, one unpaid |
| even flip `c^♭` | negate coordinates at even moduli = Fermi transform of the even part |
| pole law | payment of `k ⋆ q` decided by `K` at the abscissa `1−ε` |
| quarter law | half-damped pattern paid ⇔ local Euler exponent `< 1/2` at each height |
| Dini law | at divergent defect mass: paid ⇔ `∫₀¹ e^{−cΛ(ρ)}dρ/ρ < ∞` or a critical zero |
| selectivity I/II/III | Beurling-universal / sign-blind / Bézout-selective (`gcd(n,n+1) = 1`) |
| Route PM / Route MC | cofactor-row receiver / long-sawtooth–tail anti-alignment receiver |
| tangent | `ε`-derivative of a damped identity (Selberg row = tangent of Möbius) |
| Θ-parametrized | statement for `ε > Θ − 1/2` or `ε > Θ/2`; unconditional content only for `ε > 1/2` |

## 4. Mechanisms

Finite-observer algebra.
1. Rough absorption: `s_N(qr) = s_N(q)` for rough `r`; primes `> N` reset the row to `s(1)`. At rough
   checkpoints the boundary squares cancel ⇒ `D_N(r−1) ≤ 0` for every weight. Roughness is also
   necessary (two-atom witness `δ₁ + tδ_p`).
2. Horizon filtration: omitted divisors are complementary quotients `k/q`, `q ≤ B`, on band `B`.
3. State compression: `σ_N` is a complete invariant for all weights, `R_N` for squarefree weights;
   squarefree rows are constant on `k ↦ dk` (`d|k`) and `k ↦ k^m`. The canonical representative
   maximizes the defect in its class, so all-`M` sign questions reduce to tests at `r | N#`.
4. Successor non-descent: `+1` descends to states iff `N ≤ 2`; the phase `k mod L_N` carries it.
   `W ≥ φ(p^a)` consecutive `gcd` observations recover `k mod p^a`; with `e` errors and `s` erasures
   the sharp clock is `C_q(e,s) = (e + ⌊s/2⌋)q + (s even ? φ(q) : q)`.
5. Exact recovery: active-sawtooth samples at powers recover `c` by Möbius inversion, amplification
   `(2d/(d−1))(τ(d) − 1)` (sharp).

Polarization and envelopes.
6. Every sign statement is polarization: dissipation `−Σ(Δs)²` vs endpoint squares. Integer Möbius
   paths give margins via `|z| ≤ z²`. Spike cancellation: `s(M)s(M+1) ≤ 0 ⇒ D(M) ≤ 0`.
7. Envelope ladder (Möbius, radical ratio `r/(N+1)`): `|s| ≤ 1` below 5 (first failure `k = 30p`,
   `N = 6p−1`, response 2), `≤ 2` below 11, `≤ 3` below 13; prime shells give `|s| ≈ π(Q) − π(√Q)`,
   so envelopes grow almost linearly in the ratio. Endpoint-square arguments die at polylog ratios.
8. Rough-prime dissipation: each prime `p ∈ (N,2N)` gives a jump `≥ 4^{−ε}` beside a 4-divisible
   point; the PNT count beats the divisor-square boundary up to `M ≤ N⁶`.
9. Long-window law: Montgomery–Vaughan on step differences over response roots ⇒
   `2D_N(M) ≤ 4H² − (M − 10N²)V` (window constant exact order `N²`); Bertrand terminal prime ⇒
   `V ≥ 1/(2N)`.

Period (Haar) dynamics.
10. `L_N`-periodicity: `D(M + qL) = D(M) − qL·R_N`; on a return period `Σs² = L·Q_Sel`,
    `Σs(k)s(k+1) = L·Q_Bez`, `Σ(Δs)² = 2L·R_N`. Torus Poincaré constant 1 (not `L²/4π²`) because
    `gcd(k,k+1) = 1` kills non-coprime correlations in one step.
11. Möbius is white: `Q_Bez(N;μ) → 0`, `Cov_N(h;μ) → 0` (`h ≥ 1`), variance `→ κ ≥ 1/288`, carried
    by moduli comparable to `N` (spectral escape). Damped is tight: `V(ε) = Σ_{e≥2}φ(e)w_ε(e)²
    = ε/2 − ε² + o(ε²)`, `R(ε) = ε/2 + o(ε²)`; damped defect dissipates linearly at rate `R(ε)`.
12. Non-commuting limits: variance, dissipation and band profiles of `c_ε` do not converge to
    Möbius values as `ε → 0` (the horizon effect lives in trans-horizon divisors). Pronic energy
    `Σ s_N(n)²/(n(n+1))` does commute.
13. Primitive energy: bounded iff `ε > 1/2`, `≍ N^{1−2ε}` below, linear for Möbius.
14. Selberg row: `Cov_N(h) → 𝔖(h) − 1` (Hardy–Littlewood); equals the second-order `ε`-tangent
    `A_ε(h)/ε²` of the damped row.

Buchstab horizon calculus.
15. `Δ(m,B) = μ(m)²B + 2μ(m)Σ_{d<m}μ(d)⌊B·gcd(d,m)/d⌋`, `|Δ − Bλ(m)| ≤ 2(m−1)`; `λ(m)/m` is the
    horizon derivative of `Q_Sel`.
16. Smooth-core law: `Δ(m,B)` depends only on `gcd(m, B#)`; large primes invisible
    (`λ(aq) → λ(a)`). Möbius prime horizons inject (`λ(p) → 1`); `λ(2q) → −1`.
17. `A(B) < 0` for `B ≤ 9`, `A(10) = (1/9)(6/π²) > 0`; profile non-concave infinitely often.
18. Damped crossover: slope sign = sign of `p^{−ε} − 2ρ_ε`; `Λ(ε) = log(1/(2ε))/ε + γ + o(1)`,
    additive window `±ε`; no damping-uniform dissipation threshold.

Fermi observability.
19. Normalized ray responses form a chain pinned by saturation above level `⌊log₂N⌋`; a schedule is a
    boundary condition. Injective ⇔ at most one of `⌊log_p N⌋ + 2` slots missed.
20. Conditioning = inverse lowest chain eigenvalue: selected `K_N ~ (4/π²)(log₂N)²`, all-boundary
    `~ (1/π²)(log₂N)²`, one gap at relative depth `α`: `4max(α,1−α)²/π²`. Sharpness by quarter-wave
    and cosine packets.
21. Prime capacity: uniform observability on dyadic antichains ⇔ `Σ_{p∈Π}1/p < ∞`; over all primes it
    fails even for nonnegative packets (nearly parallel parity packets of prime banks).
22. Tightness: subpower `|A_row(n)| ≤ Bn^γ`, `γ < 1/2` ⇒ uniform bulk and origin-tail tightness.

Receiver calculus.
23. Split `A_c(n) = Σ_{d≤n}c(d)(⌊n/d⌋ − n/d) − nΣ_{d>n}c(d)/d` (sawtooth + tail drift). On `𝒞(K,ε)`:
    `|A_c(n)| ≤ KC_ε n^{1−ε}` ⇒ all paid for `ε > 1/2`. Nonnegative weights: paid ⇔
    `Σ_k M_k²/2^k < ∞` (dyadic masses; Hardy inequalities). Bounded-sign patterns pay at every `ε > 0`.
24. Convolution `A_{g⋆c}(n) = Σ_q g(q)A_c(⌊n/q⌋) + m_c A_g(n)`; dilation contracts the pronic norm by
    `q^{−1/2}`; critical Wiener kernels preserve payment. Local factors `δ₁ − aδ_p` preserve the growth
    class iff `|a| < √p`.
25. Pole law: drift `nΣ_{(n,2n]}q(d)/d ≥ κn^{1−ε}` gives `Φ_q(1−ε+δ) ≲ −1/δ`, so paid `k ⋆ q` forces
    `K(1−ε) = 0`; log drift forces `K = K' = 0`. Sufficiency: pole-free dilations
    `δ_j − j^{−(1−ε)}δ₁` have energy `O(1/j)`.
26. Moments: `M(c·log^k) = −Σ_e Λ_{k+1}(e)W_c(e)` = derivatives of `C(s)` at `s = 1`; `Λ_{k+1}` reads
    moduli with `≤ k+1` prime factors; all log moments form a complete receiver invariant.

Mellin reading.
27. Paid ⇒ `ζ(C − m)` continues to `Re s > 1/2` and `|C(σ) − m| ≲ √E(2σ−1)^{−1/2}`.
28. Boundary energy (Mellin–Plancherel of the step source):
    `Σ A(n)²(n^{−2σ} − (n+1)^{−2σ}) = (σ/π)∫|ζ(C − m)/s|²`; on `𝒞(K,1/2)` paid ⇔ line energies
    bounded as `σ ↓ 1/2`.
29. Euler-log pinching: `|log|F(w)| − Re Σ_p f(p)p^{−w}| ≤ Σp^{−2}` for completely multiplicative
    `|f| ≤ 1`; prime sums become `log|ζ|`, `log|L(·,χ)|`, `arg ζ` at shifted heights. A singularity
    `|C(s)|² ≍ |s − s₀|^{−e}` is line-integrable iff `e < 1`; a zero of `ζ` at `s₀` cancels it.
30. Below half damping, analyticity of `C·ζ` at `1−ε+it₀` makes local Euler exponents integers;
    `|cos x| ≤ 3/4 + (1/4)cos 2x` makes them 0 off the real axis.
31. Probe asymptotic `Σ_{d≤n}d^{ρ−1}⌊n/d⌋ = ζ(2−ρ)n + ζ(ρ)n^ρ/ρ + O(n^{Re ρ/2})`: the prefix main
    term is `Re(ζ(ρ)n^ρ/ρ)`, so receiver energy calibrates `|ζ|²`.

Odd sector.
32. Odd eigenvector identities: `sourceEnergy(|q|) − 4·sourcePair(q⁺,q⁻) = ((1−2μ)/μ)‖q‖²`; RH ⇔ a
    cross-lobe inequality for odd eigenvectors with `μ > 1/2`.
33. Collar transport: unconditional Schur ratio `m_a(x) ≤ 4e^{4t}(m_a(t+x) − m_a(t−x))`
    (`a`-independent); support radius `R` ⇒ primes with `log d ≥ 2R` cost nothing. Light-cone
    variation (`κ(s) − κ(s+2y) ≥ 4sinh(y/2)sinh((y+s)/2)`) pays all `log d ≤ a − R` with an
    `ε`-fraction of light-cone energy for large shift `a`.
34. Absorption boundary: cosh tail price `P(L) = πe^{2L − (5/4)log 2} > 1` for `L ≥ log 2`; no fixed
    coefficient absorbs cosh mass; the minimal pointwise correction is `max(ρ_θ, 0)`.

## 5. Pillar theorems

Finite observer.
- Uniform global defect sign: eventually in `N`, `D_N(M; c_ε) ≤ 0` for every `M` and every
  `ε ∈ [0,1]` (`eventually_pmPowerDamped_renormalizedDefect_nonpos_uniform`).
- Sharp unit envelope through `5(N+1)`; Möbius defect `≤ 0` below radical ratio 11.
- PM cofactor row: global nonpositive defect at large cutoff (it sees the complete `τ_ε ≤ τ_ε(1)`);
  linear dissipation at the Haar rate `R(ε)`.
- White Möbius observer (`tendsto_periodCorrelation_moebius`, `one_div_288_le_cofinalMobiusSlope`).
- Fermi position law `4max(α,1−α)²/π²`; schedule injectivity (`pAdicFermiScheduleInjective_iff`);
  prime-capacity classification.

Receiver thresholds.
- Parity barrier: on `𝒞(K,ε)`, payment is a function of Ramanujan amplitudes ⇔ `ε > 1/2`
  (`receiverBounded_amplitudeInvariant_iff`, `parity_barrier`); same line for magnitudes and
  unsigned majorants; `signBlindDampings = (1/2, ∞)`.
- Parity pairs at every `0 < ε ≤ 1/2`: `χ₄` and all real characters (`chiFour_parityPair`,
  `char_parityRows`); Fermi even flip, invisible to all additive moments (`fermi_evenFlip_parityPair`,
  `fermi_parityRows`); Liouville vs `κd^{−1/2}` (`liouville_parityPair_at_half_damping`).
- Cubic moments pin squarefree rows up to the even flip (`pmCofactor_twist_eq_or_evenFlip`); log
  moments are a complete receiver invariant (`exists_logMoment_ne`).
- Horizon-limit commutation on `𝒞(1,ε)` ⇔ `ε ≥ 1/2` (`horizonLimit_commutes_with_receiver_iff`).
- Hyperplane law: `CriticalWiener k`, `0 < ε < 1/2`: `k ⋆ d^{−ε}` paid ⇔ `K(1−ε) = 0`
  (`receiverBounded_dirichletConv_unit_iff_critical`), rows included
  (`rows_bounded_iff_dirichletConv_unit_poleValue_eq_zero`); fails exactly at `1/2`
  (`criticalWiener_hyperplaneLaw_iff_lt_half`), where the threshold weight is `√log`
  (`halfDamped_hyperplaneLaw_logarithmic_threshold`) and payment ⇔ `Σ S_k(n)²/(n+1) < ∞`
  (`receiverBounded_dirichletConv_unit_half_iff_summable_partialPoleSum`). Double pole needs double
  zero (`receiverBounded_dirichletConv_logWeight_unit_iff`). Weights pretending to 1 are paid ⇔ some
  local factor vanishes at the pole (`receiverBounded_iff_exists_poleLocalFactor_eq_zero`).

Analytic reading.
- Boundary energy (`receiverBounded_iff_exists_lineEnergy_le`).
- Zero spectroscopy: `d^{−ε}cos(t log d)(log d)^k` paid ⇔ `ζ` vanishes to order `> k` at `1−ε+it`
  (`receiverBounded_oscillatingSmoothPower_iff`, `receiverBounded_logPowerCosine_iff_all`);
  `2|1/2+it|²E_T/log T → |ζ(1/2+it)|²` (`norm_sq_riemannZeta_half_eq_limit`).
- Damping = zero width (`sInf_derivedSet_liouville_dampings_eq_zetaZeroAbscissa_sub_half`).
- Half-damped phase diagrams, unconditional: `z^{Ω}` paid ⇔ `z < 1/2` on `[−1,1]`, Liouville paid
  (`receiverBounded_constantSign_iff_full`); residue flips ⇔ `φ(q) < 4#(S∩units)`
  (`receiverBounded_residueFlip_half_iff_general`); subgroup flips ⇔ `ε ≥ 1/2`
  (`receiverBounded_subgroupFlip_iff`); phase law `a cos φ < 1 ∨ ζ(1/2+it₀) = 0`
  (`receiverBounded_phaseWeight_iff`); finite spectra (`receiverBounded_spectralWeight_iff`); Dini law
  for monotone defects (`receiverBounded_monotoneDefectPattern_iff`; harmonic threshold `c = 1`).
- Below half damping: integer local exponents (`exists_int_localExponent_of_receiverBounded_damped`),
  quantized prime means (`not_receiverBounded_of_primeMean`), full `z^{Ω}` diagram
  (`receiverBounded_constantSign_damped_iff`).
- Real-axis prime data do not decide payment (`exists_paid_unpaid_with_same_prime_signs_and_mean`).

Odd sector.
- Sub-unit collar domination at large shift (`exists_shift_subunit_collar_domination`).
- Nine-moduli law: atom − polar + arch excess positive on `(0, log d)` ⇔
  `d ∈ {2,3,4,5,7,8,9,11,13}`.

## 6. Tools

Developed.
- Dirichlet polarization, defect normal form, state compression (`σ_N`, `R_N`).
- Selberg/Ramanujan diagonalization of period statistics; Parseval for `τ_ε`; Cesàro transfer from
  periodic rows to `τ_ε`.
- Buchstab step formula; dilation identity `Σ_{j≤B}s_N(c,mj) = Σ_d c(d)⌊B·gcd(d,m)/d⌋`; smooth-core
  reduction.
- MV window inequality on response roots (constant `N(N−1)`).
- Chain spectral certificates (Dirichlet, mixed, soft prefix, Robin ramp); quarter-wave, cosine and
  rising-sine packets; GCD/Boolean Gram bounds `Π(p∓1)/(p±1)`.
- Pronic toolkit: Minkowski, dilation contraction `q^{−1/2}`, sawtooth norm `√(2/q)`, pronic Abel
  identity, readout–variance decomposition `E_∞ = M² + Var`.
- Hyperbola transfers: bounded partial sums; `|S(x)| ≤ Lx`; subpower `O(x^β)` ⇒ paid for `ε > β/2`;
  log-weighted version for `μ ⋆ Λ`; VK band `ε ≥ 1/2 − 1/(80√log T)`.
- Pole-free dilation decomposition with assembly lemma; drift ⇒ pole lower bounds (simple, double).
- Complex Mellin pairing, step-source Plancherel, line-energy payment criteria (majorants off countable
  sets, multi-singularity collapse, Dini majorants), local obstruction `|C|² ≥ κ/|s − s₀|`.
- Euler-log pinching; character expansion of residue flips; `1/|ζ| ≪ |t|^{1/4}` and polylog bounds on
  `1 < Re w ≤ 2`.
- Floor-sum asymptotics with Cauchy control of derivatives in `ρ`; multi-frequency window energy.
- Schur ratio and collar bridges for the odd sector.

To build.
- A signed bound for `Σ_{e≤N}(μ ⋆ Λ)(e) = O(N^β)`, `β < 1`, or for the long-sawtooth–tail
  anti-alignment, at one `ε < 1/2`.
- A quantitative Class III (successor-selective) law controlling off-diagonal Vaughan Gram entries.
- Dini law for non-monotone defects; multi-frequency patterns without amplitude budget.
- Uniform horizon-row payment on `Θ − 1/2 < ε ≤ Θ/2`.
- Asymptotics of `Q_Sel(N;μ)` (weights `φ(f)/f²` not summable).
- Integrability of the 2D absorbed integrand in the all-scale Obstacle-B comparison; odd cross-lobe
  bound.

## 7. Open questions

1. Möbius receiver at one fixed `ε < 1/2` with an unconditional input. Sign-blind inputs are excluded by
   the parity barrier; the input must read signs of `μ` on composite moduli.
2. A separating Class III statistic with an exponent: cubic, first and log moments separate parity pairs
   only qualitatively.
3. Sign pattern of `A(B)` for `B > 10`; a damped deformation commuting with the cofinal limit.
4. Möbius all-prefix sign is proved for `N ≤ 12` (`moebius_defect_nonpos_of_le_twelve`) and
   eventually; the intermediate horizons are uncovered.
5. Horizon-row gap `Θ − 1/2 < ε ≤ Θ/2`; weak limits of bounded Nyman rows; origin-tail tightness below
   `Θ/2` without zero-free input.
6. Odd sector: the cross-lobe bound, or the low-prime/inner-end residual after light-cone transport;
   the growth of the budget in `R`.
7. Möbius discrepancy energy: it lies between `N` and `N log N`; exact order.

## 8. Traps

| Trap | Fact |
|---|---|
| Sign-blind data can see RH | Amplitudes, magnitudes, `Y²`, complete-period forms, diagonal Vaughan entries, two-point moments are all decided at `ε = 1/2`; parity pairs exist for every `ε ≤ 1/2` |
| More sign-blind observables narrow the gap | Blindness is closed under post-processing; the floor stays `1/2` |
| Higher additive moments see parity | The even flip is invisible to every translated moment of every degree |
| A separating observable is an estimate | Separation is qualitative |
| First-octave defect `ab − a² ≤ 0` is Möbius-specific | It holds for every `f` with `f² = |f|` (`μ²`, `1`) |
| Eventual defect `≤ 0` encodes cancellation | It coexists with reserve `≥ 1/576` and an unbounded linear budget |
| Small-horizon sign extends | `N ≤ 12` is a finite check; envelopes `2^{ω−2}` and prime shells grow |
| Ratio 5 is a sign boundary | Unit envelope fails at `30p`; the Möbius sign holds to ratio 11 |
| Möbius = `ε → 0` limit of damped | Variance, dissipation and band profiles do not commute with the limit |
| Prime horizons dissipate | Möbius large prime horizons inject; damped ones dissipate only beyond `Λ(ε)` |
| Complete-period averages bound discrepancy below `1/2` | Primitive energy `≍ N^{1−2ε}`; pronic weights are essential |
| Full period is `N!` | Least period is `lcm(1..N)` |
| Observability ⇒ source estimate | Recovery is linear algebra with `(log N)²` conditioning |
| Probe/pattern payment is progress | `d^{−ε}cos(t log d)` paid ⇔ `ζ(1−ε+it) = 0`; anti-alignment gap, `θ_long < 1`, oscillating patterns are exact RH reformulations |
| Real-axis tests detect oscillating probes | The pole sits at `1−ε ± it`; real-axis series stay Lipschitz; prime signs + prime mean do not decide |
| Collars and finiteness of admitted sets exclude zeros | A planted Euler kernel keeps both and is paid at a planted point |
| Local Euler factors are harmless | `(1 − 2^{1−w})` cancels the boundary singularity and erases zero detection |
| Defect mass decides payment | At divergent mass the Dini integral decides |
| Θ-parametrized results are unconditional | Only for `ε > 1/2` (`Θ ≤ 1`) |
| Odd-sector criteria are results | Rayleigh `≤ 1/2` and cross-lobe premises are unproved; `θ ≤ 1` absorption is infeasible |
| Model-wave coercivity concerns zeros | Off-line hyperbolic excess is a statement about explicit test waves |
| `CriticalWiener` is necessary | `μ(j)j^{−ε}` is not in it, yet `μd^{−ε} ⋆ d^{−ε} = δ₁` is paid |
| Budgeted multi-frequency patterns test zeros | Two active frequencies under `Σ|a_k| ≤ 1` are always paid |
| `Λ(d) = log(d/clock(d))` always | Only for prime powers; `Λ(6) = 0` |

## 9. Place in the research

THIM is the receiver theory of the finite divisor observer.

- Imports: `RHTower` (98 import lines), `BezoutValuationIncidence` (73), `BiScaleUncertainty` (9),
  `HTGeometry` (7), `ArithmeticCriticalityTheory` (4, light-cone variation), `ArithmeticIncidencePositivity`
  (2), `HilbertMetric` (2).
- Imported by: `BezoutValuationIncidence` (29 modules; the two programmes depend on each other at
  module level), `ArithmeticOrientationTheory` (15; even flip as orientation at 2),
  `ArithmeticDefectRigidity` (5; same receiver via cofactor energy), `ArithmeticContinuationAndCriticalEnergy`
  (5; transports the receiver in damping/cutoff), `BiScaleUncertainty` (4), `BiarithmeticGeometry`,
  `ArithmeticCountingPositivity` (2 each), and single imports from `ScaleSignedIncidenceCriticality`,
  `ArithmeticCompensationTheory`, `CriticalArithmeticCorrelationTheory`, `ArithmeticCorrelationGeometry`,
  `RenormalizedArithmeticPotentialTheory`, `SmoothBernoulliPoleCalibration`, `twin-prime`, `RHTower`,
  `MainTheorems`.
- Roles: locates the sign-blind boundary used downstream as a resolution limit
  (`ScaleSignedIncidenceCriticality`, `ArithmeticOrientationTheory`); calibrates Route PM rows and
  receiver equivalences; supplies the unconditional `|ζ|` spectroscope for multiplicative patterns.

## 10. Big picture

The finite divisor observer is rich. It has complete invariants, exact recovery, white-noise
statistics, and sharp sign theorems far beyond its horizon. None of this pays the RH receiver. That
information is either sign-blind or linear-algebraic, and both kinds stop at damping `1/2`.

`ε = 1/2` is one line seen from many sides: absolute convergence of the class, sign-blindness,
horizon-limit commutation, the critical Wiener hyperplane law, primitive-energy boundedness, and the
unconditional Möbius receiver. The quarter law locates the same line inside one Euler factor: a local
exponent of `1/2` at each height. This is the square-root barrier, stated as an observation theorem.

Above the line the receiver is ζ itself. Its energy is the boundary energy of `ζ(s)(C(s) − m)/s`.
Every paid/unpaid dichotomy for structured weights reads the zero divisor of ζ, a local Euler exponent,
or a singularity's integrability. Payment can therefore only be proved from an input as strong as zero
location. The available unconditional inputs (`ζ ≠ 0` on `Re s = 1`, zero-free regions, VK) settle
half damping and nothing below it.

For the RH programme: truncated-Möbius, Nyman and mollifier energies are exact instruments, not
estimation devices. Finite-horizon combinatorics supplies conservation laws and calibrations, but no
cancellation. Progress needs a new signed input that reads `μ` on composite moduli through successor
or Bézout structure (Class III) and carries an exponent. The odd sector gives the same picture: every
unconditional estimate pays local, low-prime pieces, and what remains is a global cross-lobe statement.
