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
- **A3. Explicit finite-sieve conductor confinement — formalized.** `exists_sieveProfile_ramanujan_approximation_explicit` gives closed horizon and conductor cutoffs for every prescribed relative squared error in actual harmonic class mass, uniformly over profile coefficients. Direct Lean and axiom audits passed. [Proof](../../drafts/pipeline/3-formalized/finite-sieve-profiles-have-explicit-conductor-cutoffs.md). Complete negative-packet confinement is being checked separately.
- **A4. Effective horizons** for fixed-c positivity and the explicit full-index schedules remain. **Full-index Steklov exhaustion is formalized:** `steklovDCProfile_atomicGram_reaches_index` gives convergence to the entire Weil index at width `(log log N)(log log log N)^β/N` for every `β>2`, with direct Lean and axiom audits. [Proof](../../drafts/pipeline/3-formalized/the-steklov-schedule-reaches-the-whole-index.md).
- **A5. Haar branch:** first-prime, coarse, polar and head payments on fixed finite cells and finite sources.
- **A6. The matched class Hodge index on a finite sieve — formalized.** `eventually_sieveHodgeGram_one_positive_direction` proves exactly one positive direction for `P_N − (log N − γ − η)I`, for `0 < η < 2 log 2`, on every full finite-sieve partition. One horizon works for every sieve, including growing sieves. The existing all-vector prime gap supplies the shared polar hyperplane. [Proof and Lean audit](../../drafts/pipeline/3-formalized/matched-prime-form-hodge-index-uniform-in-the-sieve.md). Transfer to the complete Weil form remains open (§2.5 O2).

**Theta and heat.**

- **A7.** Theta Hankel ranks nine, ten, … by seam-split piece certificates, each stated as flux domination through the square-plus-flux identity. Rank-N PSD reduces to positivity of the native tail.
- **A8. The graded heat ladder — formalized.** `stretchedExponential_deep_density_of_nonrealZeroCount` gives `C log X exp(K(log X)^{4α})`; `subpower_deep_density_of_subcritical_nonrealZeroCount` gives `X^ε` eventually for every `ε>0` when `α<1/4`. The existing polynomial rung has exponent `4a+1`. Direct Lean and axiom audits passed. [Proof](../../drafts/pipeline/3-formalized/heat-count-stretched-exponential-density-ladder.md).
- **A9.** HCF/LA: further finite degrees on the log2/log3 grids and Jensen degrees.

**Fixed-aperture positivity.**

- **A10.** RW, EWU, OWU, ACT: further fixed-radius floors and odd witnesses; effective shift thresholds for fixed-support collars.

**Selection and index bookkeeping.**

- **A11. Finite flip thresholds — formalized.** `tiltedUnitSpline_finiteFlip_resolutionThreshold_spec` specializes the existing all-finite-set theorem to the explicit tilted spline, with no profile conditions left to prove. Every nonempty finite prime set has a positive finite threshold, eventual positivity below it and a unit negative packet above it. Direct Lean and axiom audits passed. [Proof](../../drafts/pipeline/3-formalized/every-finite-prime-flip-has-a-tilted-spline-threshold.md).
- **A12.** PW-B: restate the native two-response action on source data, removing `XiZeroCopy` indexing.

**Foundations and programmes.**

- **A13.** ACS 𝔽₃ elliptic base: product formula, quotient measures, Iwasawa characters, Eisenstein unfolding.
- **A14. Full Ξ-divisor depth identity — formalized for `σ>1`.** `sub_mul_xiSamePointResolvent_sub_logDeriv` proves `(σ−1/2)S−Re(ξ′/ξ)=D`, with absolute convergence of both series and `D≥0`. The Euler and archimedean terms are also opened exactly. [Proof and Lean audit](../../drafts/pipeline/3-formalized/the-full-xi-resolvent-depth-identity.md).
- **A15.** MC growing-modulus shell transfer is formalized: uniformly for `q≤(log Y)^A`, every logarithmic error rate `Cφ c/(log Y)^k` holds once `X≥2cY`; direct Lean and axiom audits passed. [Proof](../../drafts/pipeline/3-formalized/growing-conductor-reciprocal-shell-transfer.md). WL: higher-order scalar-jet transfer for general prime families. CTF: terminal and Euler-completion bookkeeping.

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
| **B2** | Signed joint edge payment | [sub] | W ≥ ac⁻⁷(D − C log(2c)‖x‖²) for all vectors: shells, Euler heads and pole paid together at the cutoff edges. Separate shell payment is capped at A²/(2ε), absolute head payment ends at (log A)², defect-only capture is exponential. |
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
| **B10** | Growth of the heat count N(t) as t ↓ 0 | [sub] | Known exp((2/3+ε)/t). Polynomial growth gives polylog deep density; exp(Ct^{−α}), α < 1/4, gives X^{o(1)}. Depth counting alone cannot bound it (polynomial no-go). |
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
- **Fixed-overlap answer: yes, formalized.** `exists_completeWeil_logarithmic_defect_reserve`
  gives absolute `a,C>0` and `∀c≥1, eventually N, ∀x`. The horizon depends on `c`
  and is ineffective; a prescribed growing-overlap schedule remains separate.
  [Proof and Lean audit](../../drafts/pipeline/3-formalized/logarithmic-reserve-by-shifting-the-prime-energy.md).
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

- A1 (top-band cancellation). Then the same joint coefficient on the next witness family: Ramanujan modes perturbed on the top band.
- A2 (growing heads), followed by the joint head–pole–tail version: does PNT on windows cancel the √Y coupling?
- A Ramanujan–Plancherel decomposition of the shell block (§2.5 O1).

**Q2. Is there a source law that makes the two orientations of the Ξ resolvent agree?**

- **The receiver.** On the Ξ divisor, RH ⟺ the resolvent vector equals its line reflection ⟺ the two source polarizations agree (`riemannHypothesis_iff_xiResolvent_sourcePolarizations_eq`) [S].
- **The setting.** Both orientations lie in one closed continued-Cauchy source carrier and admit separated finite-source reconstruction. The question asks for the law that identifies them.

Why this question:

- **Explicit formulas read one side only.** HEF proves that they compute only the reflection-paired W. Every route that builds positivity from the explicit formula reads one side of the identity whose two sides RH equates.
- **Both readings exist.** The same-point side is the limit of integer theta-prefix readings (CDG); W is the prime explicit formula. Q2 asks for a comparison theorem between two existing readings, not for an estimate.
- **Quantization supplies a margin.** The collision charge is an even integer, RH ⟺ charge < 2 on every window [S], and O ≤ N/4 gives 75%. This is the one place where the zero margin of Σ becomes an integer gap.
- **Its source must be additive.** Strip-holomorphic carriers vanishing on critical configurations vanish on all reflection-invariant ones [L], and the de la Vallée Poussin scalar coupling has no budget below the first quantum at distance 1/2 [S].

Subquestions:

- (σ − 1/2)S(s) − Re ξ′/ξ(s) at one σ > 1 as a theta–prime expression.
- A theta-prefix reading of the collision charge on a window, with an explicit error.
- The ℤ-analogue of "every circle-calibrated explicit formula is the Rosati pairing" over 𝔽_q.

**Q3. How fast can the de Bruijn–Newman nonreal count N(t) grow as t ↓ 0?**

Rungs, all exact consequences of `exists_card_deep_le_mul_nonrealZeroCount` and the depth law (A8):

| Growth of N(t) | Consequence |
|---|---|
| bounded | finite off-line support, hence LH [FS] |
| ≤ At^{−a} | O((log X)^{4a+1}) zeros of depth ≥ δ in [X, 2X] [sub] |
| ≤ exp(Ct^{−α}), α < 1/4 | X^{o(1)} such zeros [L] [sub] |
| ≤ C R log R, R = 2π exp((2/3+ε)/t) | known [L] |

Why this question:

- **It is the graded form of finite index**, the weakest structural target that implies a first-rank conjecture.
- **It asks about an integer-valued, antitone quantity**, not a margin.
- **It is selective by itself.** Finite ζ index forces infinite index for every single-prime flip [L].
- **The corpus has three attack surfaces:**
  - localized dissipation through collisions and t = 0 [K];
  - persistence of deep zeros for t ≲ δ²/log⁴X [S];
  - the two-sided high-count law [S].
- **It has a sharp warning.** On real polynomials the heat flow has no depth budget: a deep pair holds a shallow pair off the axis [S]. A bound on N(t) must therefore use Ξ-specific input, such as the zero density (log T)/2π or prime structure, not depth alone.

Subquestions:

- Which rung does the localized dissipation inequality give once its outer flux C log X·∫E_outer is summed over heights?
- An arithmetic ceiling for one nonblind prime tower.
- A global monotone functional for the zero dynamics (§2.5 O3).

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
- **The opportunity:** an exact identity

  W(x) = Σ_m E_m(c)\|⟨x, u_m⟩\|² + (sum of squares carried by agreement shells) − (edge remainder),

  with the edge remainder paid by the pole through PNT.
- **What it would give:**
  - B2 by identity, hence polynomial confinement and a direct attack on B1.
  - Selectivity built in: for a twin the disagreement shells enter with the opposite sign.
- **First test:** the joint witness coefficient (A1), then the same identity on two-conductor packets at growing c.

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
  - It has no global functional, and the polynomial no-go shows that depth alone is not monotone [S].
- **The opportunity:** a global functional F(t) of the zero configuration with dF/dt ≤ −c·N(t) + (controlled flux), for example a renormalized transverse energy 𝓔 (AES, where RH ⟺ 𝓔 < 1).
- **What it would give:** an integral bound ∫N(t)dt, hence a rung of the heat ladder (Q3), hence a density statement beyond the density hypothesis. A strict quantum in 𝓔 per off-line zero would turn it into finite support.

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
  - The Bost–Connes states are PD for β > 1 with Hecke exponent β/2 [S], and at s = 1/2 the Hecke state is the Haar state [L].
- **The opportunity:** an indefinite (Pontryagin) or adelic state whose archimedean dilation part is Weil's correlation and whose finite-adelic part is the Haar state at the critical temperature. A finite negative index would replace positivity. Such an object would be the "second bridge" between the towers, and it is not excluded by any corpus theorem.

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
