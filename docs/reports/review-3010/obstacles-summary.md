# Research frontier: work, open problems and next questions

Status: 30 October 2026, corpus `12ba3d87c6` plus working tree. **RH is open.**

Companions: [route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md) · [working log](../../../logs/review-3010-rev5-facts-2026-10-30.md).

- Evidence labels [L]/[K]/[S]/[P] follow the frontier map. [S] on a recent module means statement and proof were read in source.
- (inference) marks this review's interpretation; (external) marks literature outside the corpus.
- The original review ran no builds; A6's subsequent formalization passed its Lean and axiom audit.

## The corpus in one paragraph

**Classical layer, formalized unconditionally.** Guth–Maynard large values, Vinogradov–Korobov, ≥ 0.6725 of zeros simple and critical, 0 ≤ Λ_dBN < 1/8, and "≥ 3/4 critical or a positive proportion of simple off-line zeros near the line".

**Weil positivity beyond the literature.**

- Below a fixed fraction of the atom spacing, for ζ and every sign twin, on every C² test supported near the logarithms.
- On the complete prime/Gamma/polar atomic matrix at every fixed overlap c, where it rejects the Liouville twin and every cofinite flip.
- On fixed conductor packets up to overlap (log N)^{1/19}.
- On every coefficient vector for `1≤c≤(log log N)^α`, every `0<α<1/16`,
  with an all-vector logarithmic defect reserve. [Proof and Lean audits](../../drafts/pipeline/3-formalized/logarithmic-defect-reserve-at-iterated-logarithmic-overlap.md).

At fixed c the complete matrix is a solved operator: its low spectrum is spanned by Ramanujan conductor modes with energies E_m(c), explicit nonnegative Fourier tails.

**The decisive invariants are exact.**

- Index of the Weil kernel = 2·#sector zeros.
- Finite index ⟺ bounded heat counts ⟺ all zeros above some height critical.
- The de Bruijn–Newman flow counts depth: its t-uniform high counts are the depth-counting function of Ξ, and deep zeros are bounded by C log X·N(t).
- The Hecke state on Aff(ℚ) is PD exactly from s = 1/2, the Kakutani threshold of the prime Poisson measure.
- Every line-calibrated explicit formula computes Weil's reflection-paired form W and never the same-point form S. S is read from integer theta prefixes, and RH is S = W.

**The diagnosis.**

- A crossing input must be critical, square-root precise and selective at once, and no input in the corpus is all three.
- Every quantitative obstruction inside the complete matrix sits at a cutoff edge (horizon, top band, Euler head).
- All coupling between primes, and between addition and multiplication, passes through the archimedean place.

## 2.1 Work that is "just work"

Each item has a working mechanism in the corpus and a proved smaller instance. None promises a sign beyond its stated range.

**Complete Weil matrix (HF, SRT, AIP, ACS, SC, CHMD).**

- **A1. Top-band joint cancellation (SSH) — formalized.** `exists_abs_jointWitnessCoefficient_le_uniform_overlap` gives `Kφ G(c + 1 + log N)` uniformly for `1 ≤ c ≤ N/4`, hence `Oφ(G(1 + log N))` for `c ≤ log N`. The pole-row lattice estimate and Laplace factorization discharge the cancellation. Direct Lean and axiom audits passed. [Uniform bound](../../drafts/pipeline/3-formalized/joint-top-band-payment-uniform-in-overlap.md).
- **A2. Growing Euler heads (AID) — formalized.** `eventually_eulerHead_negative_family` gives every prescribed negative dimension once the head and horizon are large enough. The log-power-head corollary gives unbounded index along every positive log-power schedule. Direct Lean and transitive axiom audits passed. [Proof](../../drafts/pipeline/3-formalized/growing-euler-heads-have-unbounded-negative-index.md).
- **A3. Explicit conductor confinement — formalized.** `exists_sieveProfile_ramanujan_approximation_explicit` gives closed horizon and conductor cutoffs for prescribed relative squared error in actual harmonic class mass, uniformly over profile coefficients. [Finite-sieve proof](../../drafts/pipeline/3-formalized/finite-sieve-profiles-have-explicit-conductor-cutoffs.md). Every nonpositive unit complete Weil packet at `N≥Hc^8` also has conductor cutoff `R≤exp(D(Cc^16+1))`, uniformly in horizon and coefficients. [Complete-packet proof](../../drafts/pipeline/3-formalized/negative-weil-packets-have-exponential-conductor-cutoffs.md). Both passed direct Lean and transitive axiom audits.
- **A4. Explicit positivity horizons are formalized for every fixed `c>0`:** proved conductor cutoffs and residual constants give finite horizon inequalities for the actual complete matrix, with direct Lean and transitive axiom audits. [Certificate for `c≥1`](../../drafts/pipeline/3-formalized/complete-weil-positivity-above-an-explicit-logarithmic-horizon.md); [one uniform certificate for `0<c≤1`](../../drafts/pipeline/3-formalized/one-explicit-horizon-makes-every-touching-ratio-positive.md). [Finite-family index certificates](../../drafts/pipeline/3-formalized/every-finite-weil-family-has-an-explicit-index-horizon-test.md) also passed: actual Euler–Maclaurin entry budgets retain the entire negative index when the explicit compressed inequalities hold. [Exact Steklov schedule certificates](../../drafts/pipeline/3-formalized/steklov-index-certificates-cover-every-integer-horizon.md) also passed direct Lean and axiom audits, including every integer horizon. **Full-index Steklov exhaustion is formalized:** `steklovDCProfile_atomicGram_reaches_index` gives convergence to the entire Weil index at width `(log log N)(log log log N)^β/N` for every `β>2`, with direct Lean and axiom audits. [Proof](../../drafts/pipeline/3-formalized/the-steklov-schedule-reaches-the-whole-index.md).
- **A5. Full-source fixed-coarse index bound — formalized.** A universal detail head `A` bounds the negative dimension of the literal full Weil form by `R+A` at coarse cutoff `R`, uniformly in detail coefficients and upper horizon. All primes, Gamma and polar interactions are included; direct Lean and transitive axiom audits passed. [Proof](../../drafts/pipeline/3-formalized/fixed-coarse-cells-control-the-entire-haar-weil-index.md). Joint finite first-prime mixing also retains any Gamma fraction below one and both exact polar moments; its negative dimension is at most `A+1`. [Joint payment and Lean audit](../../drafts/pipeline/3-formalized/finite-first-prime-mixing-shares-the-full-polar-reserve.md).
- **A6. The matched class Hodge index on a finite sieve — formalized.** `eventually_sieveHodgeGram_one_positive_direction` proves exactly one positive direction for `P_N − (log N − γ − η)I`, for `0 < η < 2 log 2`, on every full finite-sieve partition. One horizon works for every sieve, including growing sieves. The existing all-vector prime gap supplies the shared polar hyperplane. [Proof and Lean audit](../../drafts/pipeline/3-formalized/matched-prime-form-hodge-index-uniform-in-the-sieve.md). Transfer to the complete Weil form remains open (§2.5 O2).

**Theta and heat.**

- **A7.** Theta Hankel ranks nine, ten, … by seam-split piece certificates, each stated as flux domination through the square-plus-flux identity. Rank-N PSD reduces to positivity of the native tail.
- **A8. The graded heat ladder — formalized.** Inverse-logarithmic persistence gives `#F≤C log X·N(cd²/log X)`, uniformly in depth. Thus `N(t)≤exp(A t^{−α})` gives subpower deep-zero density for `α<1`, and polynomial growth gives polylogarithmic exponent `a+1`. These improve the earlier `α<1/4` and `4a+1` transfers. [Proof and Lean declarations](../../drafts/pipeline/3-formalized/the-heat-count-ladder-at-inverse-logarithmic-heat.md).
- **A9. Every fixed Jensen degree is eventually real-rooted — formalized.** `eventually_splits_xiJensenPoly` transports separated Hermite sign changes through the proved actual coefficient limit. Direct Lean and transitive axiom audits passed. [Proof](../../drafts/pipeline/3-formalized/every-fixed-xi-jensen-degree-is-eventually-real-rooted.md). Further finite degrees on the log2/log3 grids remain.

**Fixed-aperture positivity.**

- **A10. Effective collar shifts and aperture improvement — formalized.** Closed shift thresholds cover every integer atom outside `{2,3,4,5,7}` and every finite family of such atoms. [Proof](../../drafts/pipeline/3-formalized/shifted-collars-have-explicit-payment-thresholds.md). [Odd witnesses](../../drafts/pipeline/3-formalized/odd-liouville-witnesses-fit-every-radius-above-twenty-seven-fiftieths.md) fit every radius `r>27/50`, retaining zeta margin `1/25` and Liouville margin `−3/10`. An [explicit aperture strictly above `181/500`](../../drafts/pipeline/3-formalized/a-fixed-weil-floor-survives-an-explicit-aperture-enlargement.md) retains full Weil floor `1/8000` for every real or complex C² test. All passed direct Lean and transitive axiom audits.

**Selection and index bookkeeping.**

- **A11. Finite flip thresholds — formalized.** `tiltedUnitSpline_finiteFlip_resolutionThreshold_spec` specializes the existing all-finite-set theorem to the explicit tilted spline, with no profile conditions left to prove. Every nonempty finite prime set has a positive finite threshold, eventual positivity below it and a unit negative packet above it. Direct Lean and axiom audits passed. [Proof](../../drafts/pipeline/3-formalized/every-finite-prime-flip-has-a-tilted-spline-threshold.md).
- **A12. Native source-data action — formalized.** The action is defined directly on raw source functions and event kernels; responses are constructed by integration. Exact theta-data pullback, absolute admission, cutoff contact and exhaustion limit passed direct Lean and transitive axiom audits. [Proof](../../drafts/pipeline/3-formalized/native-two-response-action-on-source-data.md). An independent realization remains B7.

**Foundations and programmes.**

- **A13. Actual elliptic product formula, analytic Euler product and additive quotient — formalized.** Every nonzero function on `y²=x³−x` over `𝔽₃` has finite place support and total normalized magnitude one in the [actual adelic completions](../../drafts/pipeline/3-formalized/elliptic-product-formula-uses-the-actual-adelic-completions.md). Actual closed-point counts identify the formal Euler product with the zeta series; the [unordered analytic product equals the nonzero zeta function on `|u|<1/3`](../../drafts/pipeline/3-formalized/elliptic-closed-places-give-the-analytic-euler-product.md). The [additive quotient has Haar probability and covolume one](../../drafts/pipeline/3-formalized/elliptic-adeles-have-a-volume-one-simple-pole-domain.md). All passed direct Lean and transitive axiom audits. [Actual idele spectral characters](../../drafts/pipeline/3-formalized/actual-elliptic-ideles-have-continuous-spectral-characters.md) are continuous and trivial on diagonal field units, with the same audits. [Actual loop Iwasawa sections](../../drafts/pipeline/3-formalized/actual-elliptic-loops-have-iwasawa-spectral-sections.md), their transformation laws and arithmetic-Borel triviality passed the same audits. The [literal unipotent arithmetic quotient](../../drafts/pipeline/3-formalized/actual-elliptic-unipotent-quotient-has-invariant-probability.md) has an invariant probability and a product-domain homeomorphism, with direct Lean and axiom audits. The [actual adelic radial kernel is absolutely integrable and has integral equal to the global zeta ratio for `Re(s)>1`](../../drafts/pipeline/3-formalized/elliptic-radial-kernels-integrate-to-the-global-zeta-ratio.md), with the same audits. Eisenstein unfolding remains.
- **A14. Full Ξ-divisor depth identity — formalized for `σ>1`.** `sub_mul_xiSamePointResolvent_sub_logDeriv` proves `(σ−1/2)S−Re(ξ′/ξ)=D`, with absolute convergence of both series and `D≥0`. The Euler and archimedean terms are also opened exactly. [Proof and Lean audit](../../drafts/pipeline/3-formalized/the-full-xi-resolvent-depth-identity.md).
- **A15.** MC growing-modulus shell transfer is formalized: uniformly for `q≤(log Y)^A`, every logarithmic error rate `Cφ c/(log Y)^k` holds once `X≥2cY`; direct Lean and axiom audits passed. [Proof](../../drafts/pipeline/3-formalized/growing-conductor-reciprocal-shell-transfer.md). WL: support-size scalar-jet recovery is formalized for arbitrary prime families and arbitrary complex coefficients, at every complex base point. [Proof and Lean audit](../../drafts/pipeline/3-formalized/arbitrary-prime-support-is-detected-by-finitely-many-scalar-jets.md). CTF completion is formalized with horizon `Tₙ=(n+1)(Mₙ+1)²`, error at most `1/(n+1)` and the signed terminal correction retained. [Proof and Lean audit](../../drafts/pipeline/3-formalized/euler-completion-along-growing-source-cutoffs.md). All-order Euler/jet identities and multiplicity-to-jet vanishing are formalized. [Proof and Lean audit](../../drafts/pipeline/3-formalized/general-prime-logarithmic-higher-jet-transfer.md). Same-order mixed-jet recovery for three or more primes remains separate.

## 2.2 Open mathematical problems

Nobody knows how to produce these. Strength tags:

| Tag | Strength |
|---|---|
| [RH] | Equivalent to RH |
| [FS] | Finitely many off-line zeros; implies LH |
| [LH] / [QRH] | Lindelöf; zero-free strip |
| [C%] | Critical-line proportion |
| [Siegel] | Exceptional Dirichlet zeros |
| [sub] | Implies no classical conjecture by itself |

**Family Σ — the critical sign.**

| # | Problem | Strength | Corpus form |
|---|---|---|---|
| **B1** | Complete Weil positivity at RH-complete overlap | [RH] | Positivity eventually in N for c⁴/log N → ∞, or at every Kc*_N, c*_N ≍ L(log L)². Margin = synthesis error there. |
| **B2** | Signed joint edge payment at a controlled horizon | [sub] | W ≥ ac⁻⁷(D − C log(2c)‖x‖²) is formalized, eventually in N, uniformly over all vectors and `1≤c≤(log log N)^α`, every `0<α<1/16`. The agreement-shell decomposition and RH-complete overlap remain open. |
| **B3** | Positive supersolution of the full arithmetic generator | [RH] | The odd Markov form is never subcritical; every obstruction is prime. |
| **B4** | Rank-uniform theta / heat positivity | [RH] | Flux domination uniformly in rank; Λ_dBN = 0; all-degree Jensen. |
| **B5** | A source law for the same-point side | [RH] | Force the two reconstructed orientations of the Ξ resolvent to agree, equivalently S = W, the Hecke defect = 0 or D(s) = 0. Explicit formulas compute only W. |
| **B6** | A source bound on the collision quantum | [RH], [C%] | O ∈ 2ℕ; RH ⟺ O < 2 on every window; O ≤ cN with c < 1/4 gives 75%. |
| **B7** | A realization without zero indexing | [RH], [QRH] | CCM anticommutator sign; an unbounded Deninger generator; a Hölder mixing realization (strip). |
| **B8** | Local-to-global signature | [sub] → [RH] | Assemble the matched local Hodge indices over all primes through the archimedean glue. Local towers alone give index 0 or ∞. |

**Family Π — square-root precision.**

| # | Problem | Strength | Corpus form |
|---|---|---|---|
| **B9** | Finite Krein index | [FS] | κ < ∞ ⟺ t-uniform heat count ⟺ eventual criticality. |
| **B10** | Growth of the heat count N(t) as t ↓ 0 | [sub] | Known exp((2/3+ε)/t). Polynomial growth gives polylog deep density; exp(Ct^{−α}), α < 1, gives X^{o(1)}. Depth counting alone cannot bound it (polynomial no-go). |
| **B11** | A square-root producer over ℤ | [RH] | Parity-selective integer auxiliaries of controlled height. Adams costs 2^{qr}; factorial ratios cost 2 log 2. |
| **B12** | Quadratic effectivity / Rosati heights | [RH] | Subquadratic h⁰ on degree-zero classes of the scaling surface; infinite genus blocks a constant. |
| **B13** | A non-envelope amplifier seed | [RH] | Any subexponential bound on the scaling orbit correlation of one generic cycle. Orthogonal families cancel their gain. |
| **B14** | Dispersion / parity | [QRH]+ | Any fixed zero-free strip; the 3/4 strip ⟺ near-band cyclotomic energy O(N^{3/2+ε}). No eventual single-height power saving exists. |
| **B15** | Classical conjectures and census | [LH], [Siegel], [C%] | Lindelöf; density hypothesis below 5/6; exceptional zeros; signed coalescent prime pairs past bandwidth 1 for 70%/75%. |

**Family Γ — selection.**

| # | Problem | Strength | Corpus form |
|---|---|---|---|
| **B16** | The exponent at the trivial gauge point | [RH] | θ_μ(0) = 1/2; 0 is never better than typical; gauge-invariant data stop at 3/4. |
| **B17** | Uniform selection at growing resolution | [RH] | Single prime flips need c₀(p) ≍ p^{1/7}; selection and criticality must hold on one schedule. |
| **B18** | Hecke invariance of the collided polarization | [RH] | W = collided; the scaling defect is a Hecke similitude. |
| **B19** | A successor-carrying positive carrier | strength unknown | On Aff(ℚ) none exists with Weil's dilation part; an adelic or indefinite one is not excluded. |

(inference)

- At the endpoint the three families are one statement (route-unification ledger §2).
- B2 is the only open item of unknown strength that controls an entire route family.
- B6 is the only formulation in which RH has an integer margin.
- B10 is the only formulation with a known quantitative rung, exp(C/t), to improve.

## 2.3 The three questions to answer next

**Q1. Can the complete Weil form be paid jointly at its cutoff edges?**

Concretely:

- Is there, eventually in N and for every coefficient vector, a reserve W ≥ ac⁻⁷(D − C log(2c)‖x‖²)?
- **Answer: yes, including prescribed growing overlap, formalized.**
  `exists_completeWeil_logarithmic_defect_reserve_iteratedLog` gives absolute
  `a,C>0` and, for every `0<α<1/16`, one eventual horizon for all vectors and
  all `1≤c≤(log log N)^α`. The complete matrix is also positive definite
  throughout this range. [Reserve](../../drafts/pipeline/3-formalized/logarithmic-defect-reserve-at-iterated-logarithmic-overlap.md)
  and [positivity](../../drafts/pipeline/3-formalized/complete-weil-positivity-at-growing-iterated-log-overlap.md)
  passed direct Lean and transitive axiom audits. RH-complete overlap remains open.
- Equivalently: is the complete matrix at overlap c a defect-relative perturbation of its conductor Hamiltonian Σ_m E_m(c)\|⟨x, u_m⟩\|², with O(log c) loss, once shells, Euler heads and pole are paid together?

Why this question:

- **It is the bottleneck of the most developed route family.** The confinement exponent 16 = 2 + 2·7 is the cost of paying shells and pole separately. Every open estimate of HF/SRT/AIP/ACS/CHMD becomes polynomial bookkeeping once the defect bound is logarithmic.
- **The corpus has located the obstruction at the edges.**
  - The zeros meet the pole mode only through the horizon boundary B_N(ρ)B_N(1 − ρ) [S].
  - The quasimode residual on each conductor mode is the upward prime defect [S].
  - The separate-payment witness lives on the top band [L].
  - The Euler-head obstruction lives at the head edge m = Y [S].
- **A "yes" must use the sign.**
  - Separate payment is capped [L].
  - Coherence: on nonnegative data the trivial point is extremal, so repayment can only happen on signed nonpolar directions [S].
  - On conductor modes the sign is known: Möbius collapse and the integrality of h turn the shell symbol into a nonnegative Fourier tail.
- **It carries the selection.** A twin's defect is exactly its successor-disagreement shells [S]. A joint payment that works on agreement shells is selective by construction.
- **A "no" is just as informative.** A family of signed nonpolar vectors on which shells and heads beat the pole at every log-power loss would be a structural obstruction to the whole complete-matrix family.

Subquestions:

- **A1, nonpolar Ramanujan top-band cancellation — yes, formalized.** On
  `u_m+ηu_m1_T`, `m≥2`, the actual joint coefficient is bounded by
  `Kφ mφ(m)G(1+log N)`, uniformly for `N≥8` and `1≤c≤N/4`.
  The exact quadratic identity retains both pole cross terms and the quadratic
  pole term. More generally, any bounded base and independent mean-zero periodic
  top-band perturbation satisfy the same overlap-uniform logarithmic bound.
  [Proof and Lean audit](../../drafts/pipeline/3-formalized/nonpolar-ramanujan-top-band-cancellation.md).
- **A2, joint head–pole–tail cancellation — yes, formalized.** On the actual
  detail–far-window witnesses, the literal all-prime mixed source minus both
  polar terms is `o(√Y)`. The prime tail and both pole moments are retained
  exactly. Cancellation is uniform over bounded coefficients on every fixed
  finite family; growing detail or window indices are outside this statement.
  [Proof and Lean audit](../../drafts/pipeline/3-formalized/the-full-prime-window-cancels-the-growing-head-pole.md).
- A Ramanujan–Plancherel decomposition of the shell block (§2.5 O1) remains open.
  **Two-conductor top-band step — formalized:** on `a=α+βc_m/√φ(m)`, `m≥2`,
  `J(a,a)−α²J(1,1)` is bounded by `Kφ,m,α,β G(1+log N)`, uniformly for
  `N≥8`, `1≤c≤N/4`, with explicit conductor and coefficient dependence.
  Both mixed orientations are retained.
  [Proof and Lean audit](../../drafts/pipeline/3-formalized/two-conductor-top-band-polar-channel.md).
  The downward divisor jet has an exact positive divisor-edge completion and
  finite adjunction spectrum: for `F=Σ_(k|M)f(k)c_k`,
  `E_M(f)=M⁻¹Σ_(d|M)φ(d)[log d+tameDifferent(d)]F(M/d)²`.
  Reciprocal Ramanujan modes give its complete eigenbasis, retaining every
  valuation boundary.
  [Proof and Lean audit](../../drafts/pipeline/3-formalized/finite-divisor-jet-adjunction-spectrum.md).
  Finite signed-source smoothing preserves an exact positive edge-square
  completion and gives a positive adjunction lag kernel.
  [Proof and Lean audit](../../drafts/pipeline/3-formalized/autocorrelation-divisor-jet-square-completion.md).
  The lag charge remains positive with compact source profiles at arbitrary
  real shifts, including exact logarithmic positions.
  [Proof and Lean audit](../../drafts/pipeline/3-formalized/profiled-adjunction-lag-kernel.md).
  The harmonic Gram finite part is exactly
  `B_ml=γ·1_(m=l)−I(m,l)/√(φ(m)φ(l))`. For every coefficient vector through
  `Q≥2`, its correction to `H_N∑a_m²` is the negative torsion pairing,
  with absolute remainder at most `min{Q(Q−1)/(N+1),6log Q+log4+5}∑a_m²`.
  [Finite part](../../drafts/pipeline/3-formalized/ramanujan-harmonic-gram-finite-parts-are-prime-local.md)
  and [uniform remainder with logarithmic plateau](../../drafts/pipeline/3-formalized/harmonic-gram-remainders-have-a-logarithmic-plateau.md)
  passed direct Lean and standard-axiom audits.
  Complete-period affine correlations also have an exact conductor rule:
  `∑_(n<M)c_m(n)c_l(kn+h)=1_(m=l/gcd(l,k)) M c_l(h)`, with every mixed
  packet entry retained. [Proof and Lean audit](../../drafts/pipeline/3-formalized/affine-shell-correlations-select-conductor-quotients.md).
  For `v_m,N=c_m/√(φ(m)n log N)`, the literal full prime pairing has finite
  part `−I(m,l)/√(φ(m)φ(l))−1_(m=l)[log m+tameDifferent(m)]` after removing
  `1_(m=l)log N`; in particular its diagonal is `−2log m`.
  [Exact packet limit and Lean audit](../../drafts/pipeline/3-formalized/prime-conductor-finite-parts-retain-the-torsion-boundary.md).
  The centered fixed-prime head has the opposite torsion sign; the
  complementary boundary has ordered limit `−2I(m,l)/√(φ(m)φ(l))`.
  [Exact cutoff identity and Lean audit](../../drafts/pipeline/3-formalized/prime-conductor-heads-and-tails-have-opposite-torsion-limits.md).
  At cutoff `floor(N^theta)`, `0<theta≤1`, the leading term is `theta(2−theta)delta_ml log N`
  and the finite part is
  `(1−2theta)I/√(φ(m)φ(l))−delta_ml[log m+tau(m)+2(1−theta)gamma]`.
  The square-root head is diagonal; scalar-identity centering still retains
  `(1−theta²)B_ml`. [Power and band formulas, final Lean audit](../../drafts/pipeline/3-formalized/square-root-prime-heads-diagonalize-conductor-finite-parts.md).
  Pointwise dilation `phi(q)c_l(kn)=phi(l)c_q(n)`, `q=l/gcd(l,k)`, gives an
  exact finite-head decomposition into reduced-conductor harmonic Grams.
  Centered period heads have packet norm at most `6log Q+log4+4`, uniformly
  in cutoff. [Identities and norm bound, final Lean audit](../../drafts/pipeline/3-formalized/centered-prime-heads-have-logarithmic-packet-norms.md).
  The full undilated component `U_N=2sum_(k≤N)Lambda(k)G(floor(N/k))/(k log N)`
  has `|U_N−log N·sum a_m²+2T_Q(a)|≤C(1+log Q)² sum a_m²/log N`,
  with one absolute `C` for all `Q,N≥2` and every packet.
  [Exact scalar and finite part, final Lean audit](../../drafts/pipeline/3-formalized/undilated-prime-heads-have-a-uniform-torsion-finite-part.md).
  Packet mass on rows `N/n<T` costs only `[1+log(2T)+2L_Q]sum a_m²`,
  where `L_Q=6log Q+log4+5`.
  [Quotient-tail proof and final Lean audit](../../drafts/pipeline/3-formalized/conductor-packet-quotient-tails-cost-only-logarithms.md).
  The actual scalar prime-row residual has squared norm at most
  `C(1+log Q)sum a_m²/log N`, with one absolute constant for all `Q,N≥2`.
  [Uniform norm proof and final Lean audit](../../drafts/pipeline/3-formalized/scalar-prime-residuals-have-logarithmic-packet-cost.md).
  The conductor-changing correction remains separate.
  The full Weil agreement-shell identity remains open.

**Q2. Is there a source law that makes the two orientations of the Ξ resolvent agree?**

- **The receiver.** On the Ξ divisor, RH ⟺ the resolvent vector equals its line reflection ⟺ the two source polarizations agree (`riemannHypothesis_iff_xiResolvent_sourcePolarizations_eq`) [S].
- **The setting.** Both orientations lie in one closed continued-Cauchy source carrier and admit separated finite-source reconstruction. The question asks for the law that identifies them.

Why this question:

- **Explicit formulas read one side only.** HEF proves that they compute only the reflection-paired W. Every route that builds positivity from the explicit formula reads one side of the identity whose two sides RH equates.
- **Both readings exist.** The same-point side is the limit of integer theta-prefix readings (CDG); W is the prime explicit formula. Q2 asks for a comparison theorem between two existing readings, not for an estimate.
- **Quantization supplies a margin.** The collision charge is an even integer, RH ⟺ charge < 2 on every window [S], and O ≤ N/4 gives 75%. This is the one place where the zero margin of Σ becomes an integer gap.
- **Its source must be additive.** Strip-holomorphic carriers vanishing on critical configurations vanish on all reflection-invariant ones [L], and the de la Vallée Poussin scalar coupling has no budget below the first quantum at distance 1/2 [S].

Subquestions:

- **Theta–prime expression — formalized at `s=4`.** `xiResolventDefect_four_eq_thetaPrime`
  expresses the defect using two convergent limits of finite integer theta-prefix
  readings, the Gamma factor, and `ΣΛ(n)n⁻⁴`. The source definition contains no zero
  locations. [Proof and Lean audit](../../drafts/pipeline/3-formalized/theta-prime-expression-for-the-resolvent-depth.md).
- **Theta-prefix collision reading — formalized.** `finiteThetaCollisionReading_error`
  gives the exact window charge an error bound valid from a defined separation
  threshold. The reading and prefix schedule use no zero locations; the error's
  separation parameters use the finite divisor. Convergence and eventual exact
  integer rounding are proved. A bound below the first collision quantum remains
  open. [Proof and Lean audit](../../drafts/pipeline/3-formalized/theta-prefix-reading-of-horizontal-collision-charge.md).
- **Integer calibration — formalized.** `tsum_explicit_eq_xiWeilPolarization` identifies
  every entire line-calibrated explicit statistic with Weil's polarization;
  `norm_sq_sub_explicit_eq_half_reflectionDefect` gives its exact Hilbertian defect.
  Both transitive axiom audits contain only the standard three axioms.

**Q3. How fast can the de Bruijn–Newman nonreal count N(t) grow as t ↓ 0?**

Rungs, using the uniform inverse-logarithmic persistence law (A8):

| Growth of N(t) | Consequence |
|---|---|
| bounded | finite off-line support, hence LH [FS] |
| ≤ At^{−a} | O((log X)^{a+1}) zeros of fixed depth ≥ δ in [X, 2X] [sub] |
| ≤ exp(Ct^{−α}), α < 1 | X^{o(1)} such zeros [L] [sub] |
| ≤ C R log R, R = 2π exp((2/3+ε)/t) | known [L] |

Why this question:

- **It is the graded form of finite index**, the weakest structural target that implies a first-rank conjecture.
- **It asks about an integer-valued, antitone quantity**, not a margin.
- **It is selective by itself.** Finite ζ index forces infinite index for every single-prime flip [L].
- **The corpus has three attack surfaces:**
  - localized dissipation through collisions and t = 0 [K];
  - persistence of deep zeros for `t log X≤cδ²`, with constants uniform in
    depth and height; `#F≤C log X·N(t)` on each dyadic window. Direct Lean and
    transitive axiom audits passed. [Proof](../../drafts/pipeline/3-formalized/wd-shrinking-window-heat-persistence.md);
  - the two-sided high-count law [S].
- **It has a sharp warning.** On real polynomials the heat flow has no depth budget: a deep pair holds a shallow pair off the axis [S]. A bound on N(t) must therefore use Ξ-specific input, such as the zero density (log T)/2π or prime structure, not depth alone.

Subquestions:

- Which rung does the localized dissipation inequality give once its outer flux C log X·∫E_outer is summed over heights?
- An arithmetic ceiling for one nonblind prime tower.
- **Global functional — formalized.** The full multiplicity-weighted squared-depth
  energy is continuous and nonincreasing for positive times, satisfies
  `E(b)+2∫_a^b N(t)dt≤E(a)`, and vanishes exactly when all heat zeros are real.
  No finite initial energy or improved growth rung follows yet.
  [Proof and Lean audit](../../drafts/pipeline/3-formalized/the-global-heat-depth-energy-dissipates.md).

## 2.4 A wildly different route

**Assessment: no route is visible that avoids all three walls.** The corpus proves closure theorems for every mechanism class that a new route would most naturally use:

| Mechanism class | Closure theorem | Wall it lands on |
|---|---|---|
| Linear/holomorphic identities on the explicit formula | Every line-calibrated statistic is W; holomorphic carriers cannot be quantized [L] | Σ7 |
| Positivity at bounded scale | Archimedean domination makes every bounded-aperture test positive at large height, off-line zeros or not [S] | Σ |
| Multiplicative (gauge-invariant) information | Bounds ≥ 3/4 at the trivial point; pointwise-closed statements are twin-blind [L/S] | Γ |
| Size statements | Coherent at both the trivial point and the Liouville antipode [S] | Γ6 |
| Poisson / crystalline rigidity of the zero divisor | Comb rigidity needs zero-side positivity, which is RH; one-sided gaps give only local mass bounds [S] | Σ (via Γ8) |
| Positive states on Aff(ℚ) | Weil's correlation carries no successor; integer successor ⟂ archimedean; Mautner rigidity [S] | Γ7 |
| Dynamical realizations | Finite even/virtual realizations impossible; additive ⇒ commutative; Hölder ⇒ strip only [L] | Σ6 |
| Heat flow by depth | No depth budget on polynomials [S] | Σ5 |
| Integer producers | Chebyshev precision; twist towers collapse [L] | Π3 |

In particular, the route "the zeros as the crystalline partner of log ℕ" lands on Σ. Its rigidity step needs positivity of the zero-side measure, and by `positive_duality_of_the_explicit_formula` that positivity is RH [S]. Positivity and the prime-free gap sit together on the prime side of the Weil pair.

**One region lies outside the closure theorems** (inference). It is a region, not a route.

**The finite-height arithmetic of the prime phases.** It rests on two facts:

- **Twin-blindness has a scope.** It is proved for pointwise-closed classes that contain all vertical shifts (`PointwiseClosedStatementsAreTwinBlind`) [L]. A statement anchored at height 0, whose prime range grows with the height T, is not shift-invariant, and that theorem does not reach it.
- **The phases have not equidistributed.** Prime phases align syndetically at every fixed number of primes [S]. But at height T the flow t ↦ (t log p mod 2π)_{p ≤ (log T)^C} runs on a torus of dimension far above log T, well before its Dirichlet recurrence time. This is the pre-ergodic regime.

The shape of a counterexample is constrained:

- An abstract periodic off-line pattern that hides above (P − 1)ℓ/2 at unboundedly many scales is a uniform crystal (`uniform_crystal_of_hiding`) [S].
- Bounded-aperture positivity at height T reads only primes up to about (log T)^{O(1)}.

**What a route here needs:**

1. **A forced-shape theorem for actual ζ.** An off-line pair of depth δ at height T that hides from every test of aperture ≤ log log T/(2δ) forces a specific coherence of (p^{iT})_{p ≤ (log T)^{1/δ}} on a set of heights in [T, 2T].
2. **A pointwise non-coherence theorem for growing prime ranges below recurrence time.** This is quantitative linear independence of the logarithms of d ≍ (log T)^C primes. The corpus has the friable Vandermonde bound with forms ≥ P_S^{−D} and no Baker input [S].
3. **The link between 1 and 2,** at least for a range of δ. Success in any range is a zero-free statement. Failure, recorded with its exponent, says how much quantitative transcendence RH needs.

**Why its walls differ** (inference):

- **Σ.** The positivity it uses is archimedean domination, with margin ≍ log T at bounded aperture.
- **Π.** Nothing is counted at √x.
- **Γ.** Its anchoring at height 0 escapes the closure theorem behind twin-blindness.

**Risks.**

- Averaging over heights turns step 2 into mean-value and large-value statements for short Dirichlet polynomials. Those bound counts, not locations: the census and Guth–Maynard layer.
- The forced-shape theorem is proved only for abstract periodic patterns, not for ζ's configuration.

**First question.** At height T, for which depths δ does every off-line configuration that hides up to aperture log log T/(2δ) force (p^{it})_{p ≤ (log T)^{1/δ}} into a fixed neighbourhood of a rank-one (crystalline) subtorus on a positive proportion of t ∈ [T, 2T]?

## 2.5 Breakthrough opportunities on Weil positivity

Each item is a mechanism that would create positivity or precision from structure. None is a receiver, a constant or a lower bound.

**O1. A sum-of-squares identity on the successor shells.**

- **The pieces exist in the corpus:**
  - The completed conductor energies E_m(c) are nonnegative Fourier tails produced by Möbius collapse and Poisson summation [K]. Harmonic sieve order further gives `E_m(c) ≥ E_1(c/m)` and a uniform lower bound `log(m/c)` plus a fixed profile constant. [Lean proof and audit](../../drafts/pipeline/3-formalized/the-completed-conductor-energy-dominates-its-rescaled-pole.md).
  - The divisor collapse Λ∗1 = log is maximal exactly at the trivial gauge point [S].
  - A twin's prime-form defect is exactly the sum of its successor-disagreement shells, weighted by 1 − σ_h(km) ∈ {0, 2} [S].
  - On the top band the shells and the pole move by the same lattice-free quantity [S].
  - The harmonic Gram component has an exact torsion finite part and an all-vector
    remainder `Q(Q−1)/(N+1)` through conductor `Q`.
    [Lean proof and audit](../../drafts/pipeline/3-formalized/harmonic-ramanujan-gram-has-a-logarithmic-operator-bound.md).
- **The opportunity:** an exact identity

  W(x) = Σ_m E_m(c)\|⟨x, u_m⟩\|² + (sum of squares carried by agreement shells) − (edge remainder),

  with the edge remainder paid by the pole through PNT.
- **What it would give:**
  - B2 by identity, hence polynomial confinement and a direct attack on B1.
  - Selectivity built in: for a twin the disagreement shells enter with the opposite sign.
- **First test:** the joint witness coefficient (A1) and the joint top-band coefficient
  on two-conductor packets are now controlled uniformly in overlap. Only the
  polar–polar entry remains outside the logarithmic bound. The complete-form
  sum-of-squares identity on these packets remains open.

**O2. A Hasse principle for the Krein index.**

- **The corpus has the local and the obstruction pieces:**
  - At each prime, matched against log M − γ, the prime form on the p-adic class pole vectors has a Hodge index with gap → p log p/(p − 1) [S].
  - Positive local assemblies on ℤ^S have index 0 or ∞ [S]: the towers alone cannot produce a finite index.
  - The only off-tower constituent is archimedean, and a rank-one partner pays exactly one direction [S].
- **The opportunity:** a signature formula of Atiyah–Bott or Hirzebruch type:

  κ(global) = Σ_p (local defect at p) − (archimedean gluing),

  with every term an integer computed locally. All local Hodge indices share one positive direction, the pole, which is the archimedean matching. A finite index would follow from finiteness of the local defects, i.e. B8 ⇒ B9.
- **Why it differs from the routes:** it converts the critical sign into a local–global integer computation, the form in which Hasse principles succeed. It also uses the structure (one positive direction shared through the archimedean place) that makes ℤ differ from 𝔽_q.
- **First test:** A6 (finite sieve) is formalized, uniformly in the sieve. The complete Weil form and infinite assembly are not covered.

**O3. A Lyapunov functional for the de Bruijn–Newman zero dynamics.**

- **The setting:**
  - The zeros of H_t move by the reciprocal field of the other zeros.
  - The corpus has localized energies with a dissipation inequality through collisions [K], and a lower bound for N(t) by deep zeros [S].
  - The full squared-depth energy now satisfies `E(b)+2∫_a^b N≤E(a)` for
    `0<a≤b`, with no exterior flux. It is continuous through collisions and
    vanishes exactly when every heat zero is real.
    [Proof and Lean audit](../../drafts/pipeline/3-formalized/the-global-heat-depth-energy-dissipates.md).
  - The polynomial obstruction concerns individual depths and count thresholds;
    it does not contradict monotonicity of total squared depth.
- **Remaining opportunity:** control `E(t)` as `t↓0`, or construct a finite
  renormalized initial energy that retains the dissipation law.
- **What remains needed:** positive-time dissipation alone supplies no growth
  rung. An initial-energy bound would control the integrated nonreal count;
  a strict energy quantum per nonreal zero would additionally constrain support.

**O4. Integrality as margin through the additive reading.**

- **Three places where integrality creates a margin at criticality:**
  - the shell shift h ≥ 1 repays log(2πc) exactly, while continuum shells give only the pole charge [L];
  - the collision charge is an even integer, with endpoint 2 on Ξ [S];
  - the Krein index is an integer [L].
- **The opportunity:** arguments whose only analytic input is an approximate statement with error below the integer gap, and whose exact conclusion comes from integrality. This is the characteristic-zero analogue of "eventual Hasse–Weil is Hasse–Weil".
- **The source** must be the additive (theta-prefix) reading. The multiplicative scalar coupling has no budget below the first quantum at distance 1/2 [S].
- **Concrete targets:**
  - O(T) < 2 from O(T) ≤ 2 − η on windows;
  - a ceiling on κ from an approximate count;
  - repayment of log c on non-conductor vectors from the unit gap of the shift lattice.

**O5. A second bridge between the primes.**

- **The situation:** all inter-prime coupling passes through the archimedean place (route-unification ledger §3, Reading 3).
- **What the corpus rules out:**
  - On Aff(ℚ) the integer successor cannot carry Weil's correlation positively: they are spectrally singular, and a ℤ-periodic successor with continuous dilation part is constant [S].
  - Every Hermitian kernel on `Aff(ℚ)` with a nonzero integer-Haar multiple and dilation reading continuous at one has infinite negative index. The zero-axis polynomial correction removes any integer-period defect before the cyclic Gram-limit argument. Extension by zero gives the same obstruction on `Aff⁺(ℚ)`. [Lean theorems and verification boundary](../../drafts/pipeline/1-in-progress/cyclic-haar-averages-force-infinite-index-at-continuous-dilations.md).
  - The Bost–Connes states are PD for β > 1 with Hecke exponent β/2 [S], and at s = 1/2 the Hecke state is the Haar state [L].
- **Adelic obstruction:** on `ℚ⁺ ⋉ (ℝ × 𝔸_f)`, with rational scalars acting on both components, the actual nonzero finite-adelic Haar overlap coefficient and pure Weil dilation reading cannot coexist at finite index. The Haar integral and rational-affine restriction are formalized in `AdelicKreinGeometry/Haar/FiniteAdelicReading.lean` and `AdelicObstruction.lean`.
- **Remaining positive survivor:** the canonical positive Haar, slope, and zero-axis polynomial decomposition, with its exact residual index, remains to be formalized.

## 2.6 Does crossing the walls need a new field?

(inference, ideation constrained by the corpus)

**Yes.** Every problem in 2.2 asks to pay an infinite-rank arithmetic debt through a single rank-one channel, the archimedean place, at zero margin, at the exponent 1/2. Existing fields each supply two of the needed features:

| Field | Supplies | Lacks |
|---|---|---|
| Hodge theory | An index theorem at zero margin | Finite rank; a conformal Frobenius |
| Harmonic analysis on groups | Plancherel positivity | Treats + (Fourier on ℝ, ℤ̂) and × (Mellin on ℚ^×) separately; on Aff(ℚ) the two are spectrally singular |
| Krein / Pontryagin space theory | Exact negative indices, finite-rank perturbations | Arithmetic producers of the index |
| Probability on the gauge torus | Kakutani dichotomies, typicality, zero–one laws | Speaks about almost every gauge, not the trivial point |
| Analytic number theory | Precision | Through estimates that spend a margin |

The corpus pins down what the missing field must contain:

- **Indefinite structures**, because positive states on Aff(ℚ) are excluded (Γ7).
- **A local-to-global signature theory** with the archimedean place as the unique glue (Σ9).
- **A conformal symmetry.** Hecke dilations are isometric boosts; power maps and the successor are not conformal (ALG).
- **Same-point access**, because holomorphic carriers fail (Σ7).
- **Renormalization at edges** with a counterterm of nontrivial null cone (survival law).

A working name: **arithmetic signature theory** (adelic Krein geometry).

**What the field would be about.** Hermitian forms and states of finite negative index on the adelic dilation–translation system ℚ^×_{>0} ⋉ 𝔸 ⊃ Aff(ℚ). It would study their local decomposition into prime towers glued by the archimedean place, and the comparison of their additive (theta, Poisson, successor) and multiplicative (Euler, Mellin, dilation) spectral readings.

**What it would be like.**

- **Like Hodge theory:** its central theorem is an index theorem that holds at the boundary of the positive cone.
- **Like the Atiyah–Bott and Hirzebruch signature formulas:** global index = sum of local contributions, here one per prime plus an archimedean term.
- **Like Arakelov theory:** the archimedean place is a full participant with its own Green function, here the Gamma/Lévy kernel.
- **Like L²-invariants:**
  - infinite-dimensional spaces with a group action carry finite dimensions per unit volume;
  - the zero density (log T)/2π plays that role;
  - the Krein index is the integer that should vanish;
  - the Kakutani threshold s = 1/2 is a change of type of a measure on the gauge torus.

**Criteria for the field to be real rather than a reformulation.**

1. **Intrinsic objects** defined from ℤ without reference to zeros: the dilation lattice, the gauge torus, prime towers, the archimedean Lévy kernel, theta prefixes, conductor modes, successor shells.
2. **A local signature theorem** at each prime (matched Hodge index) and a **global gluing theorem** that computes the global index from local data.
3. **An additive–multiplicative comparison theorem** (S = W, Hecke invariance, agreement of the two resolvent orientations) proved as an identity.
4. **A conformal symmetry** with factor ≠ 1, or a proof that none exists together with a substitute that plays Frobenius's role.
5. **Calibration:** over 𝔽_q[T] it reduces to Rosati positivity and Weil's theorem, with one tower and conformal Frobenius.
6. **Selectivity:** it fails for twins (disagreement shells), Beurling systems, continuous Λ-measures and higher-order poles.
7. **Edge control:** its renormalized limits keep a nontrivial null cone, so positivity survives the passage N → ∞.

**Questions it would answer.**

- Is there a signature formula expressing κ(K_ζ) as a sum of local prime defects minus an archimedean gluing term?
- Do the matched local Hodge indices share one positive direction for every finite sieve, and what obstructs the infinite assembly?
- Is there a Pontryagin (finite negative index) state on the adelic system whose dilation part is Weil's correlation and whose successor is the Haar state at the critical temperature? Is its index κ(K_ζ)?
- What replaces conformal Frobenius over ℤ? A correspondence on an adelic carrier, not on the atoms?
- Is there an integer invariant computable on the additive side that equals the number of off-line zeros? Candidates: the collision charge read from theta prefixes, or a Fredholm index of a Toeplitz operator on H²(𝕋^∞).
- Is there an exact sum-of-squares decomposition of the complete Weil form whose squares are indexed by successor-agreement shells?

**Tools to develop.**

- Pontryagin-space index theory on groups (Krein–Langer on ⊕_p ℤ with continuous logarithmic structure).
- Local–global signature calculus: matched counterterms, survival cones, coupled survival.
- Kakutani–Hellinger dichotomies and zero–one laws on the gauge torus.
- Mautner/Howe–Moore phenomena for adelic ax+b systems.
- Bost–Connes / KMS states at the critical temperature.
- Ramanujan sums as a Plancherel basis on ℤ̂; the conductor Hamiltonian.
- Successor-shell calculus with the divisor collapse.
- Lyapunov methods for the de Bruijn–Newman zero flow.
- Quantitative linear independence of many logarithms (for §2.4).

**Objects.**

- The dilation lattice ⊕_p ℤ and its prime towers; the gauge torus, its trivial point and Liouville antipode.
- The archimedean Lévy kernel and its successor collar.
- Conductor modes, successor shells, Euler heads and their edges.
- Theta prefixes, the collided form, the Ξ resolvent and its two orientations.
- The collision charge, the Krein index, the matched local Hodge indices.

**Language.**

- Local defect; archimedean gluing; matched counterterm; survival cone.
- Edge payment; agreement and disagreement shells; coherent excess (the pole).
- Orientation (of the resolvent); quantum (least excess on off-line configurations).
- Rate = depth; Kakutani threshold; pre-ergodic regime.

**Mechanisms it would provide.**

- **Positivity by identity:** Fourier tails and sums of squares on agreement shells, instead of coercivity.
- **Index by localization:** local signatures glued at the archimedean place, instead of global estimates.
- **Same-point access:** an orientation law comparing the additive and multiplicative readings, instead of explicit formulas.
- **Margin from integrality:** quantized invariants, instead of margins.
- **Selection by structure:** the divisor collapse and the boundary sign of the pole in the definitions, instead of in the test data.
