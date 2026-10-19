# Fresh review of the RH programme (Fable, 19 October 2026)

Scope. I read the route ledger (`docs/reports/rh-current-frontier-map.md`, all 677 lines), the corrected
obstacle summary (`docs/reports/hard-obstacles-summary-1810.md`), the four programme READMEs, and the Lean
declarations named below. I searched the Lean corpus with `scripts/formal_tools.py research` for the
classical tools that the diagnosis depends on. I did not read any other markdown. Evidence is listed in
Section 6.

Headline. The four programmes contain 808 Lean modules and about 204,000 lines. They contain 25 theorems
whose conclusion is `RiemannHypothesis`. They contain no theorem that is at the same time
weight-specific, RH-selective and cofinal. That is not an accident of effort. It is forced by three
barriers that every tool in the four programmes respects. Section 1 states the barriers and checks each
programme against them. Section 2 answers which tools are missing. Section 3 says what each programme
should do next and what it should stop doing. Section 4 recommends exactly one new programme, with a
falsifiable first theorem, and explains why the obvious alternatives should not be started.

---

## 1. Diagnosis: what the 204,000 lines actually prove

### 1.1 The three properties an RH-closing theorem must have

A theorem closes a route only if it is simultaneously:

- **Weight-specific.** It must fail when the literal weights `μ`, `Λ`, or `Λ(n)/√n` are replaced by
  weights with the same sieve data but different sign pattern (for instance `λ(n)|c(n)|` with `λ` the
  Liouville function). Otherwise it is a statement about divisibility, not about primes.
- **Selective.** It must fail for `ζ(s−a)ζ(s+a)` and for Beurling systems with off-line zeros. The
  ledger records both countermodels (`R:NonTemperedShiftedZetaPairCountermodel`, `BeurlingSystem`,
  `Zeta23`). Anything that survives them cannot distinguish truth from falsity of RH.
- **Cofinal.** It must hold uniformly as the scale parameter (aperture `R`, horizon ratio `M/N`,
  damping `ε`, cutoff `T`) goes to its limit.

### 1.2 Classification of the existing output

Every theorem in the four programmes falls into one of three bins. Each bin lacks at least one of the
three properties.

| Bin | What it is | Typical examples (from the ledger and the Lean statements) | Property missing |
|---|---|---|---|
| A. Exact identities for every weight | Polarisation, Selberg-coordinate diagonalisation, Bézout splitting, pronic Abel laws, Ramanujan lag covariance, iso-state classification | BVI `Q_Sel−Q_Bez` laws; THIM short-window defect `≤ 0 ⟺ equal endpoint states`; `selberg_sub_harmonic_sq_le_two_mul_sieveSuccessorReserve` ("for every weight `c`") | Weight-specific |
| B. Nonselective positivity | Positivity of a form on a restricted family that stays positive when RH is false | APT `FactorialTailSpanWeilCoercivity` (`Re W ≥ (c log M − C)Σ|b|²`); BiScale `FactorialMuntzTailWeilGrowth`; BiScale all-scale `wΛ` lower bounds; THIM inserted-wave excess (`OffLineHyperbolicPrimeChainExcess`) | Selective |
| C. Finite-horizon sign laws | Signs that hold up to an explicit multiple of the horizon and provably break after it | `|s_{N,μ}(k)| ≤ 1` through `k ≤ 5N+4`, failing at `30p`; renormalised defect `≤ −1` for `M+1 < 6(N+1)`; damping radii `1/(96N(N+1)log N)` | Cofinal |

The 25 receivers named `riemannHypothesis_*` inside the four folders are not a fourth bin. They are
reformulations: each premise is of the form "for every `δ > 0` there is `ε < δ` and a bound `B` with
energy `≤ B` for all `T`" (nine BVI receivers, two BiScale receivers, one THIM receiver), or "every
putative odd eigenvector with `μ ∈ (1/2, 1)` satisfies an inequality" (five THIM receivers). None of
them lowers the difficulty of the premise below RH itself. The ledger says this correctly route by route;
I am only pointing out that the pattern is universal across all four programmes.

### 1.3 Why the pattern is forced: three barriers

**Barrier 1 (parity).** Weil positivity on a test whose autocorrelation `h` is nonnegative at every
`log n` reads

    Σ_n Λ(n) n^{−1/2} h(log n)  ≤  ∫ 2cosh(x/2) h(x) dx  +  Ω(0) h(0)  +  Lévy increment integral.

The right side is the prime-number-theorem main term plus an archimedean term that is lower order for
wide tests. So the inequality is an upper bound on a prime sum with constant `1 + o(1)`. Information of
sieve type, meaning divisibility by moduli `d ≤ D`, gives constant `2` and no better: this is Selberg's
parity phenomenon. The Selberg coordinates `Y_{N,c}(q)`, Ramanujan modes, pronic Gram matrices and
Bézout interior sums that BVI and THIM work with are exactly sieve-type information, and their theorems
are stated for every weight `c`. They cannot certify constant `1`. They are parity-blind by
construction, and the README of BVI says as much when it insists that its identities hold on arbitrary
Beurling systems.

**Barrier 2 (power saving only through zeros).** The Möbius cancellation receivers (MC, CTF, PM, BVI)
need `M(x) = O(x^{1/2+δ})` or an equivalent. A bound `M(x) = O(x^{θ+ε})` is equivalent to a zero-free
half-plane `Re s > θ`. No method in mathematics gives a power saving for `M(x)`, or for `ψ(x) − x`,
except through zeros; elementary methods stop at `x·exp(−c(log x)^{θ})`. The BVI/PM receiver at a fixed
damping `ε` is, by the corpus's own bridge
(`V:RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence`), Mellin analyticity on `Re s > 1/2`, that is
the zero-free half-plane `Re s > 1/2 + ε`. The programme is therefore aiming the elementary toolkit at the
one target where elementary tools are known to give nothing.

**Barrier 3 (universality of the identity layer).** Multiplicative identities and the explicit formula
hold for Beurling systems and for `ζ(s−a)ζ(s+a)`. The additive structure of `ℤ` enters classical
analytic number theory through additive characters: Poisson summation, the circle method, Kloosterman
sums and the Kuznetsov formula. The only additive input the four programmes use is `gcd(n, n+1) = 1`
and the Ramanujan sums, which are the periodic part of additive analysis and are known not to carry
power savings. The corpus already owns the additive-character tools (`HeathBrownIdentity`,
`VinogradovUpperHalfSaving`, `KloostermanBilinear`, Matomäki–Teräväinen type I/II modules), but none of
the four programmes consumes them.

### 1.4 Consequence

The obstacle summary lists six families. Mathematically they are two problems plus one conditioning
problem:

1. **Sign of an indefinite form** (families 3.2, 3.3, 3.6; receivers RW, OWU, EWU, CHMD, HF, TH, HCF).
   Positivity theorems in mathematics come from a second structure not visible in the trace formula:
   an intersection pairing with a Hodge index theorem (Weil's proof for curves), a unitary
   representation, a stable polynomial or Lee–Yang interaction, or a positive ground state of a
   Schrödinger-type operator. The four programmes have none of these; they have identities and
   nonnegativity of pieces.
2. **Power-saving cancellation** (families 3.1, 3.4; receivers MC, CTF, PM, FU, RP, LI, PBM). Known to
   be equivalent to zero-free regions. No elementary engine exists.
3. **Conditioned tails** (family 3.5, BAG). A genuine probabilistic question, not addressed by any of
   the four programmes.

The positivity problem is the only one of the three where a new mathematical mechanism could plausibly
be built. Section 4 is about that.

---

## 2. Question 1: what tools are we, or mathematics, missing

### 2.1 Tools that exist in mathematics but are absent from the corpus or unused by the programmes

1. **Criticality theory for nonlocal Dirichlet forms (Allegretto–Piepenbrink, ground-state
   representation, Agmon ground states).** The odd-sector criterion
   `riemannHypothesis_iff_odd_primeChain_poincare` is literally a Hardy inequality:

       ∫ Θ(x) cosh(x/2) v(x)² dx  ≤  E_arch(v) + E_prime(v)      for all odd v ∈ C²_c,

   with `E_arch(v) = ∫_{t>0} ω(t) ∫ Θ(x)Θ(x+t)(v(x) − v(x+t))² dx dt`, `ω(t) = e^{−t/2}/(1 − e^{−2t})`,
   and `E_prime(v) = Σ_n Λ(n) n^{−1/2} ∫ Θ(x)Θ(x+log n)(v(x) − v(x+log n))² dx` (plus the chain
   variances). Criticality theory says that such an inequality holds if and only if a positive
   supersolution exists on the half-line. THIM's `m_a`-Doob gauge is exactly a supersolution attempt,
   and its residual `θ · sourcePair` is exactly the supersolution defect. The corpus has no
   Allegretto–Piepenbrink theorem, no ground-state representation and no Harnack inequality for the
   arithmetic jump kernel (search returned nothing relevant). This is the one missing tool that matches
   an existing RH-equivalent receiver term for term.

2. **Type I / Type II decomposition inside the trans-horizon energy.** The corpus owns Heath-Brown and
   Vaughan identities and Montgomery–Vaughan mean values. BVI never applies them to its interior
   bracket. Doing so would identify which part of the trans-horizon energy is a bilinear form, and hence
   where Barrier 2 bites.

3. **Positive calibration over function fields.** The corpus has negative calibration (Beurling,
   `Zeta23`, shifted zeta) but no positive one. Over `F_q[T]` the analogues of every receiver are
   theorems. A method that cannot reproduce the `F_q[T]` theorem cannot prove RH. The corpus has
   Frobenius and finite-field infrastructure in `HTGeometry/ABHN` but no function-field zeta receiver.

4. **A quantitative unit of selectivity.** `HodgeIndexAtLevel Z a` (Weil positivity on
   `C²_c` tests supported in `[−a, a]` with both polar moments zero) is already in the corpus with the
   Nyquist horizon theorem `zeta_hodge_index_nyquist_horizon`: a zero of depth `δ` and height `γ ≥ 102`
   forces failure at every level `a ≥ 2000 A₀ log(|γ|+3) log(10⁶/δ)`. So positivity at level `a` is
   worth a zero-free region of depth `δ` up to height `exp(a/(2000 A₀ log(10⁶/δ))) − 3`. No programme
   measures its results in this unit. APT's span positivity, for example, does not imply
   `HodgeIndexAtLevel` at any level.

5. **The off-line pair defect as an explicit selective quantity.** With
   `W(f,g) = Σ_ρ m_ρ F_f(ρ) conj F_g(1−ρ̄)` (the APT convention) and `Z(f) = Σ_ρ m_ρ |F(ρ)|²`, pairing `ρ`
   with `ρ' = 1 − ρ̄` gives the identity

       Z(f) − W(f,f) = Σ_{off-line pairs {ρ, 1−ρ̄}} m_ρ |F(ρ) − F(1−ρ̄)|²  ≥ 0,

   with equality for all `f` if and only if RH. APT already uses `Z` as an unconditional majorant
   (`weil_mixed_norm_le_sqrt_square_mass`), but it does not use the defect `Z − W` as the object to be
   bounded. Everything APT proves about `Z` alone is nonselective; the selective content is in the
   defect. (Check the corpus before claiming novelty; `zetaZeroSquareSummand_reflectPerm` is adjacent.)

### 2.2 Tools that mathematics as a whole does not have

1. **A positivity engine for the Weil form over `ℚ`.** Over function fields the Weil form is an
   intersection number on the surface `C × C` and positivity is the Hodge index theorem (equivalently
   Castelnuovo–Severi). Over `ℚ` the analogous surface would be `Spec ℤ ×_{F₁} Spec ℤ`; the corpus's
   Deninger and Arakelov modules show how far that object is from existing. Nothing else in mathematics
   produces positivity of an indefinite arithmetic form.
2. **Any power saving for `Σ_{n≤x} μ(n)` not routed through zeros.** See Barrier 2.
3. **Chowla or Elliott correlations with power savings or uniformity in the shift.** Needed by the
   "complete signed successor law" of obstacle 3.1; the September 2026 preprint cited in the obstacle
   summary gives qualitative cancellation only.
4. **A self-adjoint arithmetic operator whose self-adjointness is proved from arithmetic.** The corpus
   proves self-adjointness equivalences (`riemannHypothesis_of_xiReciprocalOperator_isSelfAdjoint`),
   which are receivers.
5. **Criticality theory for arithmetic nonlocal operators** as a developed subject. Item 2.1.1 is its
   seed; the Harnack and ground-state asymptotics for a jump kernel with prime-indexed jump lengths do
   not exist anywhere.

---

## 3. Question 2: what to research next in each programme

Each list is ordered. The first item is the one I would start on today. "Stop" items are lines whose
further output is predictable from Section 1.

### 3.1 Arithmetic Positivity Theory (50 modules, 15,731 lines)

Frontier. High-scale corrected-factorial span positivity (`FactorialTailSpanWeilCoercivity`,
`FactorialRampFullWeilSmoothingLimit`), critical-envelope prime-channel limits
(`FactorialCriticalPrimeLimit`, `FactorialCriticalPrimeCumulativeCharge`), relative Krein stability,
Schur margins. All in Bin B.

Stop. Any further estimate on factorial, ramp, tent or Müntz families (about 30 of the 50 modules).
Their positivity is proved and nonselective; more precision does not change that.

Next.

1. **Selectivity gate as a lemma.** For every test family `F` studied, prove or refute: "positivity of
   `W` on `span(F ∩ tests supported in [−a, a])` implies `HodgeIndexAtLevel zetaZeroConfig a`". For the
   factorial families the answer is no (the ledger says positivity is nonselective). Make this lemma
   mandatory before any new estimate on a family. Cheap in Lean; most of the ingredients exist.
2. **Windowed off-line waves as the test family.** `WeilCompactOrbitInertia` already shows that every
   negative direction at large aperture is spanned by compactly supported approximations of
   `e^{βx} cos(γx)`. Take the family `w_R(x) e^{βx} cos(γx)` directly. The Weil Gram matrix on finitely
   many `(β_j, γ_j)` has entries that are Dirichlet polynomials
   `Σ_{n ≤ e^R} Λ(n) n^{−1/2 ∓ β − iγ} w(log n / R)`. Prove the reduction: `HodgeIndexAtLevel a` holds if
   and only if these finite Gram matrices are positive semidefinite for all frequency sets. This turns
   APT into a consumer of the corpus's mean-value and large-values theorems
   (`dirichlet_meanValue_sharp`, `huxley_local_large_values`, `largeValues_dirPoly`), which are the only
   place arithmetic cancellation currently lives. It also makes precise what APT can and cannot prove:
   diagonal dominance for well-separated frequencies is a mean-value theorem; the off-diagonal control
   for close frequencies is the zero-density problem.
3. **The defect `Z − W`.** Formalise the pair identity of 2.1.5 and restate every APT result as a bound
   on the defect. Then look for an arithmetic expression of `Z(f)` through the second explicit formula
   (the corpus has `tendsto_montgomeryForm_div_leadingOrder`); `Z` is Montgomery's form sampled at the
   test's frequencies. Any arithmetic upper bound on `Z` of the form `Z ≤ W + (controlled)` is a
   selective statement.
4. **Odd-mode sinh capacity (APT topic 5).** Hand this to the new programme of Section 4; it is the
   same inequality as the THIM odd criterion.

### 3.2 Bi-Scale Uncertainty (536 modules, 116,265 lines)

Frontier. Five fundamental theorems (Ramanujan diagonalisation, Lorentz boost, origin allocation,
polar enforcement, Nyquist finite part), the infinite-grid origin-concentration obstruction
(`exists_smooth_infiniteGrid_positive_origin_defect`), signed Gram/collar hierarchies, and the newest
sieve-visibility line (`SieveLocalVisibilityClassification`, `SieveLinearVisibility`,
`SieveVisibilityPerturbations`, `SieveVisibilityPhaseSeparation`, `SieveVisibilityRadialEstimates`).

Stop. All-scale lower bounds that pay only archimedean or Lévy energy; receiver reformulations; finite
observation/moment-recovery laws. The ledger lists well over a hundred BiScale modules under RW, EWU and
PBAP, each ending "none gives a sign". The README's own rule 1 ("unconditional producers first") has
been applied to objects that are not selective.

Next.

1. **Repair the sieve-visibility anchor.** The classification assumes `Y_{N,c}(2^{⌊log₂ N⌋}) ≠ 0`,
   which vanishes for every squarefree-supported row (obstacle 1.7), hence for `μ` and Barban–Vehov.
   Replace the anchor by the largest prime `p ≤ N`: for `μ`, `Y_{N,μ}(p) = Σ_{p | d ≤ N} μ(d)/d = μ(p)/p
   = −1/p ≠ 0` because `N/p < 2` by Bertrand. Prove the lower-support classification with this anchor
   and explicit constants. This is a small, falsifiable fix that makes the newest line apply to the
   actual sources.
2. **Profile decomposition for bounded Lévy energy.** The corpus has the escape channels as separate
   counterexamples: origin bubble (`InfiniteGridOriginConcentration`), distant copies
   (`DistantCopySharpness`), narrow-support midpoint escape (Trap 8). Prove a concentration-compactness
   theorem: every sequence with bounded archimedean energy splits into finitely many profiles (origin
   bubble, translates to large `x`, oscillatory waves at fixed frequency) plus a remainder with
   vanishing Weil energy, and the Weil form is asymptotically additive over profiles. The payoff is a
   reduction theorem: Weil positivity on all tests follows from positivity on origin bubbles
   (archimedean, provable), on pure translates (prime-blind, provable) and on single-frequency
   oscillatory profiles (the RH content, identical to APT item 2). That would tell the programme exactly
   where the RH content sits and close the "naive limit passage" obstacle by classification instead of
   by example.
3. **The Weil Sobolev norm.** The obstacle summary says the approximation loss must be measured "in the
   norm required by the form". Define it: the completion of `C²_c` in `E_arch + E_prime + ∫ Θ cosh v²`.
   Prove the moment and phase recovery theorems of the programme in that norm, with the sharp embedding
   constant from it to grid samples. Everything currently stated in `L²` is in the wrong norm.
4. **Audit the PM/FZZ-P admission premises.** For `0 < ε < 1/2` the source admission assumes a uniform
   centred-sawtooth variance bound; the ledger notes this. List which BiScale Fermi/Nyman statements are
   unconditional and which rest on that premise, and retire the latter from the "established" column.

### 3.3 Trans-Horizon Incidence Mechanics (95 modules, 30,237 lines)

Frontier. The odd-sector prime-chain criterion (`riemannHypothesis_iff_odd_primeChain_poincare`), the
sinh-absorption identity (`convex_doob_chain_sinh_absorption_le_one`), the valuation-clock bridge
(`vonMangoldt_eq_log_div_lagVisibilityClock`), the fourth-band envelope and its sharp failure, iso-state
window classification.

Stop. Further bands of the Buchstab envelope (Bin C), further iso-state or checkpoint sign laws (Bin A),
and observability thresholds. These are finished as positive survivors; record them and move on.

Next.

1. **Convert Pillar 4 into criticality theory.** State and prove in Lean the Allegretto–Piepenbrink
   equivalence for the odd criterion: the Hardy inequality of 2.1.1 holds if and only if there is a
   positive function `ω` on `(0, ∞)` with `(L ω)(x) ≥ Θ(x) cosh(x/2) ω(x)` weakly, where `L` is the
   generator of the archimedean-plus-prime jump form. The identity behind it is the ground-state
   representation `E(v) − ∫ ρ v² = ∫∫ (v(x)/ω(x) − v(y)/ω(y))² ω(x)ω(y) K(x,y)` when `Lω = ρω`. This is
   the exact positive-survivor theorem of the current Pillar 4, and it is new mathematics for this
   kernel.
2. **Record the sharp boundary of the `m_a` gauge.** The absorption law requires `1 < 2 exp(−2|a|)`,
   that is `a < (log 2)/2 ≈ 0.347`, and `coshSinhPolarRatio a M R = 2M cosh(R/2)/(Θ(R) sinh(a/2)) ≤ θ ≤ 1`.
   Since `Θ` is Riemann's kernel `Σ e^{u/2}(4π²n⁴e^{4u} − 6πn²e^{2u}) e^{−πn²e^{2u}}`, the quantity
   `cosh(R/2)/Θ(R)` grows like `exp(πe^{2R})`. So `θ ≤ 1` holds only on a bounded window of apertures
   `R`, while the receiver needs every `R`. Put this boundary on the card. Then test whether any other
   explicit odd positive profile (for instance `Θ(x) tanh(x/2)`, `Θ(x) sinh(x/2)`, or `Θ(x)·x`) is a
   supersolution on a longer window; compute the defect current for each. Item 1 gives the framework in
   which this is a well-posed computation instead of a search.
3. **The first source-specific sign.** The programme has shown the renormalised defect sign is universal
   on iso-state windows. Find the smallest window on which the literal `μ` sign depends on `μ` values,
   and show that the Liouville-twisted weight has the opposite sign there. That is the parity barrier
   stated as a THIM theorem, and it tells exactly which trans-horizon statements can never close.
4. **Function-field calibration of Pillar 3.** Run the downward Buchstab `L²` telescope over `F_q[T]`,
   where Möbius cancellation is a theorem. If the telescope identities are the same over `F_q[T]`, over
   `ℤ` and over Beurling systems, they carry no RH content, and Pillar 3 should be closed as a bridge.

### 3.4 Bézout–Valuation Incidence (127 modules, 42,230 lines)

Frontier. Nine RH receivers (`riemannHypothesis_of_pmBezoutInteriorPronicEnergy_bounded`,
`..._renormalized_pmBezoutInterior_budget` with drift rates `v, κ` against the compensated harmonic sum,
martingale cancellation receivers), exact three-bracket decompositions, `O_ε(1)` compensated remainders,
fixed-linear-horizon source laws, finite polytopes and observability.

Stop. Finite classification laws, polytopes, moment recovery, sharp constants at fixed horizon, and any
new receiver (the ledger: "a bridge into an existing receiver is not a new live route"). Nine receivers
in one folder is already too many.

Next.

1. **Build the parity pair.** Construct two weights `w₊, w₋` with identical Selberg coordinates
   `Y_{N,c}(q)²`, identical Ramanujan covariances at every lag, identical pronic Gram data, and opposite
   trans-horizon energy growth (one bounded, one divergent as `ε ↓ 0`). This is the BVI analogue of
   Selberg's parity examples. It is the programme's positive survivor: an exact description of what
   trans-horizon sieve data cannot see. Every BVI "sign law" should then be checked against the pair;
   any law that survives both is parity-blind and cannot close MC, CTF or PM.
2. **Name the open remainder as a classical object.** Apply the Heath-Brown identity (in the corpus) to
   the interior bracket `pmBezoutInteriorMartingaleSum` and prove: renormalised interior bracket `=`
   explicit Type II bilinear sum `+ O_ε(1)`. Then the "complete log-renormalised remainder" of obstacle
   3.1 is a standard bilinear form in Möbius, and its cancellation is the recognised obstacle, not a
   new one.
3. **Prove the converse of the receiver.** Show: if `ζ` has no zeros with `Re s > 1/2 + ε₀`, then
   `pmBezoutInteriorPronicEnergy ε T` is bounded in `T` for every `ε > ε₀`. If true, the receiver is an
   exact restatement of quasi-RH at level `1/2 + ε` and should be labelled a receiver, not a route. If
   false, BVI is aiming above RH and must be re-aimed. Either outcome changes the ledger.
4. **Close the finite-horizon line.** Record the `5N+4` envelope, the `6(N+1)` defect margin and the
   damping radii as finished results and stop extending them.

---

## 4. Question 3: a new programme

### 4.1 Recommendation

Yes: exactly one, and it should absorb THIM Pillar 4 and APT topic 5 rather than add a fifth umbrella.

**Name.** Arithmetic Criticality Theory: positive solutions and ground states of the arithmetic jump
Laplacian.

**Object.** The Schrödinger-type form on odd functions of the half-line

    Q(v) = E_arch(v) + E_prime(v) − ∫ Θ(x) cosh(x/2) v(x)² dx,

with the archimedean jump density `ω(t) = e^{−t/2}/(1 − e^{−2t})`, prime jumps at lengths `log n` with
weights `Λ(n) n^{−1/2}`, and Doob weight `Θ` = Riemann's kernel. `RiemannHypothesis ⟺ Q ≥ 0` on odd
`C²_c` tests (this is `riemannHypothesis_iff_odd_primeChain_poincare`, already in Lean).

**Questions it tries to answer.**

- Q-a. Is `Q` subcritical, critical or supercritical in the sense of Pinchover? RH is the statement that
  it is not supercritical. Criticality theory gives the dichotomy: either a Hardy weight exists
  (subcritical), or a unique Agmon ground state exists with no Hardy weight (critical), or a negative
  direction exists (supercritical).
- Q-b. What is the ground state in the even sector? The even sector has the known bound state (the
  pole, resolvent eigenvalue `1`, span `{1}` in the quotient). Compute it explicitly and verify that the
  ground-state representation reproduces the even Weil form. This is the calibration milestone.
- Q-c. What asymptotic profile must an odd positive supersolution have? The explicit formula forces the
  behaviour at infinity; determine it. Then: can a supersolution be written from arithmetic data, for
  instance from the Chebyshev discrepancy `ψ(e^x) e^{−x/2}` or from `Θ` and elementary odd factors?
- Q-d. Harnack inequalities for the arithmetic jump kernel: positivity on `[0, R]` propagates to
  `[0, R + log 2]` through the prime-2 jump, and the archimedean kernel couples all scales. A Harnack
  inequality would be a local-to-global principle that does not exist for any arithmetic operator.
- Q-e. The relation between criticality of `Q` and the countermodels: for `ζ(s−a)ζ(s+a)` the potential
  changes (two poles) and the prime weights grow; the form must be supercritical there. Identify which
  term flips the classification. That is the selectivity gate for the programme.

**Milestones, each a falsifiable theorem.**

1. M1. Allegretto–Piepenbrink equivalence for `Q` in Lean: `Q ≥ 0 ⟺ ∃ ω > 0` on `(0,∞)` with
   `Lω ≥ ρω` weakly. Ingredients: the ground-state representation identity (pure algebra on the jump
   form), integrability bookkeeping already present in `WeilPhiDoobPrimeAtoms` and
   `CHMDPrimeChainSourceFactorization`.
2. M2. Even-sector calibration: the explicit even ground state and the identity `Q_even(v) =
   ground-state representation`, matching `CHMDEvenSectorPointSpectrum`.
3. M3. Classification of the `m_a` gauge: `m_a · w` is a supersolution on `(0, R)` if and only if an
   explicit inequality holds; compute its failure set and confirm the aperture window of Section 3.3
   item 2.
4. M4. Forced asymptotics of any odd supersolution at infinity, derived from the explicit formula.
5. M5. Either an explicit arithmetic supersolution on all of `(0, ∞)` (this would be RH), or a theorem
   that every supersolution must encode zero data (then the programme has produced an exact receiver and
   is closed as such).

**Kill criteria.** If M4 shows the forced asymptotics can only be written through zeros of `ζ`, or if
M5 ends in the second alternative, record `NO POSITIVE SALVAGE FOUND` beyond M1–M4 and close. M1–M4 are
worth having regardless: they are new theorems about an explicit operator.

**Why this and not something else.** It is the only candidate that (i) matches an existing
RH-equivalent receiver term for term, (ii) replaces a bounding problem by an existence problem for one
positive function, which is a different kind of mathematics from everything the four programmes do,
(iii) has a first theorem (M1) that is provable now with the corpus's definitions, and (iv) passes the
obstacle summary's rule that a programme needs a distinct falsifiable theorem before it gets an
identity.

### 4.2 Alternatives considered and not recommended

- **Arithmetic intersection theory (`Spec ℤ ×_{F₁} Spec ℤ`, Deninger).** The right dream, but there is
  no falsifiable first theorem within reach; the corpus's Deninger modules and the memory notes on the
  forced shape of the `F₁` object show that the positive-form question is exactly as open as RH.
- **Arithmetic Lee–Yang / stable polynomials (W1C, TH).** Needs an interaction model whose partition
  function converges to `Ξ`; the corpus's own no-go results (`WeightOneCliffordSpectralNoGo`,
  `HermitianPencilEulerFactorObstruction`, `FerromagneticInequalitiesLeeYangBlind`) show finite ports
  cannot do it and that ferromagnetic inequalities do not imply real-rootedness.
- **Trans-horizon renormalisation theory (BVI/THIM as a renormalisation group in the horizon).** It
  reduces to a power saving for `M(x)`, hence to zeros (Barrier 2).
- **GL(2) spectral positivity (Kuznetsov, Hecke traces).** Trades RH for the Ramanujan–Selberg
  conjectures for Maass forms, which are open; the corpus's `SelbergMaassMobiusMultiplierNoGo` points
  the same way.

---

## 5. Two gates and one unit of measurement for all four programmes

- **Gate 1 (selectivity).** No theorem enters a card's "established" column without a one-line statement
  of what it says for `ζ(s−a)ζ(s+a)`, for a Beurling system with an off-line zero, and for the
  Liouville-twisted weight. The corpus has all three objects; the check is cheap in Lean.
- **Gate 2 (function field).** Any method claimed to approach a cofinal sign or cancellation must be
  shown to reproduce the corresponding `F_q[T]` theorem, or explain why it cannot. The corpus has the
  Frobenius infrastructure; a function-field zeta receiver module is missing and should be built once.
- **Unit.** Progress on positivity routes is reported as the level `a` at which `HodgeIndexAtLevel
  zetaZeroConfig a` is certified, or as a bound on the defect `Z(f) − W(f,f)`. Progress on cancellation
  routes is reported as the exponent `θ` in `M(x) ≪ x^{θ+ε}` actually obtained. Identities, finite
  classifications and nonselective positivity count as zero in these units.

---

## 6. Evidence

Documents read in full: `docs/reports/rh-current-frontier-map.md` (677 lines, all routes, candidates,
shared constraints, alias table); `docs/reports/hard-obstacles-summary-1810.md`;
`formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md`;
`formal/GaloisForLFunctions/BiScaleUncertainty/README.md`;
`formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md`;
`formal/GaloisForLFunctions/BezoutValuationIncidence/README.md`. Two of these and the APT README were
modified on disk by another agent during the review; my reading is of the versions as read.

Lean counts (`wc`, `grep -c '^import'`, `git status`): APT 50 files / 15,731 lines / 50 umbrella
imports; BiScale 536 / 116,265 / 538; THIM 95 / 30,237 / 95; BVI 127 / 42,230 / 127; 17 untracked
modules across the four folders.

Lean declarations inspected (statements read in source):
`riemannHypothesis_of_pmBezoutInteriorPronicEnergy_bounded`,
`riemannHypothesis_of_renormalized_pmBezoutInterior_budget`, `pmBezoutInteriorPrefix`,
`riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare`,
`riemannHypothesis_iff_odd_primeChain_poincare`, `phiDoobCoshMass`, `phiDoobPrimeJump`,
`phiDoobArchJumpEnergy`, `phiDoobArchShiftJump`, `archLevyDensity`, `sameSide`, `chainIntegral`,
`vonMangoldtAtom`, `riemannKernelReal`, `cuspSeries`, `riemannCuspPoly`,
`convex_doob_chain_sinh_absorption_le_one`, `phiDoobCoshMass_oddPolarWeight_le_sinh_potential`,
`coshSinhPolarRatio`, `riemannHypothesis_of_odd_eigenvector_four_term_posGraph_ge_groundPotential`,
`vonMangoldt_eq_log_div_lagVisibilityClock` and the other theorems of `ValuationClockChainBridge`,
`exists_smooth_infiniteGrid_positive_origin_defect` and the theorem list of
`InfiniteGridStrictEnergyLoss` and `SignedGridTraceCompactness`, the theorem lists of
`SieveLocalVisibilityClassification`, `SieveLinearVisibility`, `SieveVisibilityPerturbations`,
`SieveVisibilityPhaseSeparation`, `SieveVisibilityRadialEstimates`, `FactorialCriticalPrimeLimit`,
`FactorialCriticalPrimeCumulativeCharge`, `FactorialCriticalPrimeKernelDensity`,
`SourceRelativeSchurMarginAndPerturbationCalculus`; `HodgeIndexAtLevel`,
`zeta_hodge_index_nyquist_horizon`, `zeta_hodge_index_forces_offLine_companion`. The 25 receivers in
the four folders were listed with `rg '^theorem riemannHypothesis'`.

Corpus searches run (`scripts/formal_tools.py research`, lexical or `--any`): `riemannHypothesis_of`
(2,648 declarations corpus-wide); `convex_doob_chain_sinh_interpolation coshSinhPolarRatio`; Chowla and
two-point Möbius correlation (found `AveragedChowlaInterface`, `MoebiusUnweighted`, binary correlation
recurrence; no power-saving or shift-uniform result); Montgomery–Vaughan mean value and large sieve
(found `DirichletMVT`, `DirichletMeanValueSharp`, `HuxleyLargeValues`, `DirichletLargeValues`,
Maynard/Montgomery finite-set variants); Matomäki–Radziwiłł and Halász (found `HalaszMeanSquare`,
Matomäki–Teräväinen type I/II modules, `GallagherRange`, Huxley `7/12` and `20/33` prime gaps);
function fields and Frobenius (found `ABHN` Frobenius infrastructure and Deninger packets; no
function-field zeta receiver); Selberg trace formula and spectral gap (found extensive
`SelbergMaass*` Laplacian modules); Bombieri–Vinogradov, Vaughan, Heath-Brown, Kloosterman (found
`HeathBrownIdentity`, `VinogradovUpperHalfSaving`, `KloostermanBilinear`); pair correlation and GUE
(found `MontgomeryPairCorrelationLeadingOrder`, `ZetaThreeQuartersReduction`); Beurling countermodels
(found `BeurlingSystem`, `rationalPrimeSystem`, `Zeta23` modules); parity barrier (only docstring
mentions in `SignedLcmFractionalDefectAndCompleteFibreCollapse` and `CubicSievePhaseRecovery`; no
theorem); Allegretto–Piepenbrink, ground-state representation, criticality, Agmon (nothing relevant;
only unrelated `gomes*GroundState` and Riccati comparison hits); Hodge index and Castelnuovo–Severi
(found the level-`a` Hodge index family and Deninger–Arakelov pairings; no arithmetic-surface
intersection theory); stable polynomials and Lee–Yang (found `LeeYangAsanoContraction`,
`LeeYangIsingGraphDatum`, `FerromagneticInequalitiesLeeYangBlind`).

Two computations used in the text and checked by hand: `Y_{N,μ}(p) = −1/p` for the largest prime
`p ≤ N` (Bertrand gives `N/p < 2`, so the only multiple of `p` below `N` is `p` itself); and the pair
identity `Z(f) − W(f,f) = Σ_{off-line pairs} m_ρ |F(ρ) − F(1−ρ̄)|²` (with the convention
`W(f,g) = Σ m_ρ F_f(ρ) conj F_g(1−ρ̄)` of the APT README, pair `ρ` with `ρ' = 1−ρ̄`, use `m_ρ = m_{ρ'}`,
and expand `F(ρ)conj(F(ρ)−F(ρ')) + F(ρ')conj(F(ρ')−F(ρ))`).
