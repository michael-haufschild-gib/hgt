# Research frontier: work, open problems and next questions

Status: 28 October 2026, corpus commit `d47ab4b5d`. **RH remains open. The missing input is one selective arithmetic inequality on a complete source.** The corpus now pins down where that inequality must act. Its positive families are proved by twin-blind estimates, and the unpaid residual is a structured, self-similar object.

This summary covers all 31 live routes, the 17 standalone candidates and PW-B. Companions: [route-by-route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md). Evidence comes from corpus searches and Lean-statement inspection; no builds. **[S]** = recent working source (committed on 28 October 2026, or unfinished); per-item status in the frontier map. Research record: [working log](../../../logs/review-2810-refresh-2026-10-28.log).

## What the corpus establishes

There are three destinations, not fifty unrelated problems:

1. **Critical signed arithmetic control:** prime/Möbius histories, approximation energies, regularized series, source work.
2. **Complete Weil positivity:** full, even, odd, incidence, Hodge, effectivity, atomic and moment formulations.
3. **Independent forcing:** a geometric, spectral, dynamical or information structure whose proved property supplies 1 or 2.

Eight results define the present frontier:

- **The complete source is self-similar** [S]. Complete logarithmic cells recover every mixed Weil entry. On them, the Gamma energy pays every adjacent-pair difference with pair averages present. Each average cell is the original cell translated by \(\log 2\), so complete cells are a dyadic multiresolution of themselves. Details above one fixed index carry a horizon-uniform full-form floor. [Gamma payment](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteCellVariancePayment.lean), [self-similarity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellCoarseSplitting.lean), [floor](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellEffectivity.lean).
- **Mixed entries are prime-error integrals** [S]. For ordered tests,
  \[
  W(f,g)=-\int_0^\infty\big(e^h-\psi(e^h)-c\big)\,\Omega_{f,g}'(h)\,dh-\Gamma_{\rm tail}(f,g),
  \]
  with a nonnegative Gamma square reserve inside the tail. The Gamma boundary bound \(\pi/2\) is an identity with an exact square reserve and no nonzero equality case. [Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean), [reserve](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceRetainsItsGammaSquareReserve.lean).
- **The atomic receiver holds at every root** [S]. RH is equivalent to eventual positivity on atomic families of width \((\log N)^\alpha/N\) for any single \(\alpha>0\); the earlier threshold was \(\alpha>1/4\). The Liouville twin, the scalings \(c\Lambda\) (\(c<1\)) and quadratic mixtures are negative at every root, and so is the Markov form. On the pole hyperplane, RH is Markov nonnegativity at every root. [Every root](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheOverlapLawAtEveryRoot.lean), [gauge](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheGaugeAtEveryRoot.lean).
- **Narrow positivity at an explicit fraction** [S]. The prime-form defect pays the pole, and \(W\ge0\) on all atomic tests at \(w\le K_\star(\varphi)\delta_N\). The finite-part component of \(K_\star\) is within \(e^{2+2\varepsilon}\) of the Robin–Euler point where the Markov form fails. [Pole defect](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/ThePoleDefectPaysThePole.lean).
- **Prime-form selectivity is constrained, not global** [S]. A uniform gap \(g>0\) holds on the pole hyperplane, where Liouville reaches the ceiling. For each fixed finite prime set the valuation chain has gap \(2\log2\). The all-prime sharp gap is stated as a Poincaré inequality whose proof is unfinished. Twisted poles read \(2\operatorname{Re}(-L'/L(1,\chi))\). Among sign gauges matched to \(\zeta\)'s divergence, \(\zeta\) uniquely maximizes the prime-form finite part, with each flipped prime costing at least \(4\log p/p\); \(\zeta\) is thus identified but is the hardest member. [Gap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ThePrimeFormHasASpectralGapBelowItsPole.lean), [twisted pole](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheTwistedPoleReadsTheLogarithmicDerivative.lean), [flipped primes](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFinitePartSeesEveryFlippedPrime.lean).
- **Actual prime modes exist** [S]. Ramanujan profiles are quasimodes at \(\log N-E_m\), and every fixed finite conductor packet is realized by actual eigenvalues. [Spectral packets](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFullPrimeMatrixRealizesFiniteAdjunctionPackets.lean).
- **Critical energy separates finite support from RH** [S]. \(\mathcal E_{\rm crit}<\infty\) iff off-line support is finite; \(\mathcal E_{\rm crit}\le Q_*=1294047/2000\) iff RH. [Canonical energy](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalSourceRateHasACanonicalEnergy.lean).
- **Selectivity is localized.** This is an inference from proof hypotheses. Every proved positive family is twin-blind: the high-detail prime bound is an absolute Young/Schur estimate, Gamma payments contain no primes, and the narrow sign holds for twins. The Liouville twin is not Weil-positive, so its negative directions sit in the unpaid coarse, low and cross-level residual. That residual is where the missing inequality must use a property of \(\Lambda\).

## 2.1 Tasks that are just work

"Just work" means the ingredients exist. A finite sign task delivers a certified enclosure, not a guaranteed sign.

| ID | Task / deliverable | Serves | Boundary |
|---|---|---|---|
| W01 | Build finite complete-cell Grams in multiresolution coordinates: \(\log2\)-orbits of cell 1, details at each level, low details \(a<A\), all cross-level blocks; Gamma and both poles retained. | HF, ACS, AIP, RW, SRT | Exact algebra; sign of the result is separate. |
| W02 | Compute a numerical lower index \(A\) for the Haar full-form floor; instantiate fixed-family pole-preserving smoothing. | ACS, AIP, HF | Floor is twin-blind; low details remain. |
| W03 | Compute the level-Toeplitz symbol \(\theta\mapsto\sum_m e^{im\theta}W(f,T_{m\log2}g)\) for the finite generator set (cell 1, low details) on pole-neutral spans. | HF, ACS, AIP | Positivity of the symbol is an RH-type statement (see Q1); computing it is not. |
| W04 | Evaluate the ordered Chebyshev integral for specified block pairs, using explicit \(\psi(x)-x\) data, Vinogradov–Korobov and explicit error bounds; tabulate cross-level coupling sizes. | HF, ACS, AIP, WL, CHMD | Unconditional bounds grow like \(e^{h/2}\) up to a subexponential saving. |
| W05 | Instantiate the every-root receiver in the SRT/AIP/HF interfaces; compute \(K_\star(\varphi)\) for standard profiles; compute atomic Grams at overlap ratios between \(K_\star\) and \((\log N)^\alpha\). | SRT, AIP, HF, ACS | Finite \(N\) computations do not decide the eventual sign. |
| W06 | Projections, Schur residuals, radicals, source-kernel costs and bounded-window scale-transport constants for specified sources. | AID, SAHT, CHMD, HF | Constants are window-dependent; no uniform transport. |
| W07 | Bounded-overlap Schur rows and profile/gauge Grams, separating Markov, full Weil, corrected-twist and pole-hyperplane forms. | SSHA, ALG, SRT, OWU, AIP | Rows grow with overlap. |
| W08 | Formalize the paper-stage full-prime spectrum adjunction-exhaustion proof sitting at the fully-proven stage of the pipeline. | RAPT, HF, ACS | Required by project rules; content not inspected here. |
| W09 | Ramanujan residual/Gram estimates and the Hermitian residual lemma for specified conductor sets; tower deficits at \(p\le43\). | RAPT, HF, ACS | Fixed finite sets only. |
| W10 | Gauge finite parts for given moduli: \(-L'/L(1,\chi)\) values, BV horizon errors, Liouville separation constants. | RAPT, ACG, OWU | Absolute-profile errors; no uniform signed mass control. |
| W11 | Seed/drift/history/cross-block/endpoint ledgers for specified schedules. | FU, RP, LI, TT, PA | Exact accounting, no cofinal cancellation. |
| W12 | Finite Möbius, pronic, Vaughan and Báez–Duarte rows, readout and centered energy reported separately. | MC, PM, CTF, BVI, JAS | No small-damping tail bound. |
| W13 | Apply known fixed-modulus, below-diagonal, low-LCM and finite-prime dispersion estimates. | MC, RP, PM, CTF | Keep parameter ranges and endpoint costs. |
| W14 | Translate supplied strip/rate bounds through the escaped, Hecke-defect, theta-prefix and Vaughan dictionaries; reconcile the external \(7/8\) claim. | MC, WL, SRT, HF, BVI | Transport of a supplied bound only. |
| W15 | Compact cofactor Grams, effective pole orders, record-minimum diagonals. | PM, WL, MC | Compact classification is not tightness. |
| W16 | Certified finite-aperture ground-energy, blind-minimum and shell-relaxation bounds. | RW, EWU, OWU, ACT | Finite windows do not decide all apertures. |
| W17 | Finite prime-collar and joint-allocation bookkeeping with shared reserves. | AIP, OWU, ACT, TT | May leave an explicit unpaid remainder. |
| W18 | Finite heat/Jensen/Hankel heads, both Gaussian grids, half-line Laguerre data; extend certified first-atom quadrature. | LA, TH, WD, HCF, PA | No all-degree inference. |
| W19 | Newton-disc margins, Ward caps, renewal resolvents, transgression traces. | XN, WD, RN, TG | Local certificates only. |
| W20 | Finite-rank Schur charges; compact recurrence approximations. | GTA, BAG | Rank and target-zero exceptions explicit. |
| W21 | Finite Robin/Nicolas extremal ranges with fixed-defect margins. | RB | No conclusion for saturated extremizers. |
| W22 | Theta-prefix readings, finite source-work integrals, finite lower sums of canonical pair energy. | AES, CDG, AID, HF, SRT | Lower sums do not bound the upper tail. |
| W23 | HJ/SEC/HCF residual transport; finite jets, fibres and seams. | HJ, SEC, HCF | No residual vanishing assumed. |
| W24 | Candidate finite calculations: cycle traces, curvatures, repair defects, jets, contours, likelihood contrasts, co-shift defects, finite photonic/Ising stacks, certificate streams, cusp actions. | All 17 candidates and PW-B | Calibration is not forcing. |
| W25 | Finite-net and cycle recovery on stated energy/support classes. | EWU, HF, BVI, PM, CTF | Finite injectivity is not uniform coercivity. |
| W26 | Literature intake: local constants versus published theorems; external announcements. | MC, ACG, LA, pair correlation | Acceptance of new external proofs is not assumed. |

## 2.2 Open mathematical obstacles

### (a) RH-equivalent endpoints — no one has a solution

| ID | Missing result | Routes |
|---|---|---|
| O1 | Critical signed prime/Möbius cancellation in any receiver currency: lag energy, Abel moment, history floor, strict half-power, regularized convergence, extremal remainder, approximation residual, half-power prime budget. Via the Chebyshev identity this is also the content of separated mixed entries of the complete form. | WL, FU, RP, MC, LI, PBM, RB, JAS, CTF |
| O2 | Positivity of the complete Weil form on a source-complete family. Equivalent forms: complete-cell index zero, residual nonnegativity, full/even/odd/allocation/Hodge/effectivity sign, atomic positivity at any unbounded polylog overlap. | RW, HF, SZ, EWU, OWU, AIP, ACS, TT, CHMD, ACT, SRT |
| O3 | Simultaneous all-degree/all-height heat, moment or coefficient signs with a common parameter. | PA, LA, TH, WD, HCF, SEC |
| O4 | Visibility of every escape state (positive gauge mass), cofinal admission, vanishing approximation error. | PM, CTF, MC, EWJ, PCS |
| O5 | Rank-uniform transverse decay; all-point recurrence; covering Newton discs; integer trace cap; directed renewal orientation. | GTA, BAG, XN, TG, RN |
| O6 | \(\mathcal E_{\rm crit}\le Q_*\), or cofinal source work \(\le2\). | HF, SRT, ACS |

### (b) Stronger than RH

| ID | Statement | Note |
|---|---|---|
| S1 | Abel-slope genus saturation; linear Mertens energy budget | RH plus simple zeros and residue summability. |
| S2 | Matching-profile signed pair surplus at the stated strength; strong uniform correlations | Not implied by RH. |

Use these only when the extra strength buys something.

### (c) Intermediate open problems — no known solution, possibly solvable without RH

| ID | Missing result | Why current work stops | Payoff |
|---|---|---|---|
| I1 | **Block dominance of the complete multiresolution.** Pay cross-level couplings (surviving prime orientation, Gamma, poles) by per-level reserves, leaving finitely many \(\log2\)-orbit generators. | High details are paid level by level. Cross-level entries are Chebyshev integrals: pole products growing like \(2^{\lvert j-k\rvert/2}\) are cancelled only up to the prime error \(e^h-\psi(e^h)\). | Reduces O2 to one-prime orbit positivity of a finite generator set. A bounded-index version gives finite off-line support. |
| I2 | **Selective transfer.** A full-form inequality using a twin-selective input — pole-hyperplane gap, Chebyshev main-term cancellation, character finite parts — on coarse/low sections with Gamma and both continuous poles. | All proved positive families are twin-blind; the gap is prime-only and lives on a discrete harmonic hyperplane. | Necessary for any complete positivity proof. |
| I3 | **Finite canonical critical energy** (an upper bound on \(K(R)\)). | Only monotonicity and lower index costs are proved. | Finite off-line support. |
| I4 | **Sharp all-prime gap \(2\log2\)** on the pole hyperplane, i.e. Poincaré constant \(2\log2\) for the multiplicative walk. | Fixed-\(Q\) gap proved. The all-prime statement is in Lean with an unfinished proof; two-scale decomposition, fibres and rough-defect control are done. | Quantitative selective margin for I2. |
| I5 | **Growing-conductor and complement control** of the prime matrix: bulk spectral law, adjunction heat trace / Weyl law. | Only fixed packets are realized. | Spectral producer for I1/I2. |
| I6 | **Full positivity at fixed overlap beyond \(K_\star\)**; the Metzler endpoint \(\rho=1\). | Robin–Euler limits the Markov mechanism, not the full form. | Extends the proved regime toward polylog overlap. |
| I7 | **A fixed zero-free strip \(\Theta<1\)**: a power saving in any escaped or Vaughan dictionary. | Classical open problem. An external \(7/8\) claim is pending intake. | Fixes the first rung of all rate dictionaries. |
| I8 | **Exterior tightness**; exclusion of infinite-height escape. | Record minima give positive diagonals but allow zero gauge mass. | PM progress short of O4. |
| I9 | **Conductor/forcing compatibility** for companion-cluster detectors. | No common aperture range. | OWU/SRT detection. |
| I10 | **Independent faithful constructions** for each candidate (U3). | Calibrations, zero-indexed objects, capacity/gap obstructions. | Candidate promotion. |
| I11 | **Classification of twin-selective invariants** of the full form. | Leading polar matching is blind. On step profiles the prime finite part classifies sign gauges with convergent Mertens error (\(\zeta\) the unique matched maximizer, Liouville the unique anti-matched minimizer), but this makes \(\zeta\) extremal rather than positive. | Identifies which input I2 must use. |

"No known solution" refers to the corpus and the literature consulted. I7 is a well-known open problem in the literature, apart from the pending external claim.

## 2.3 The three questions to answer next

<a id="q1"></a>
### Q1. Does the complete Weil form reduce to finitely many \(\log2\)-orbits?

**Exact object.** Write \(T=T_{\log2}\). By the proved splitting, complete cells \(1,\dots,M\) decompose as

\[
\bigoplus_{j\ge0}T^j(\text{cell }1)\;\oplus\;\bigoplus_{j\ge0}T^j\,\mathrm{Det}(1..\lfloor M/2^{j+1}\rfloor),
\]

where \(\mathrm{Det}(a)\) is the balanced detail of pair \((2a,2a+1)\) and \(T^j(\text{cell }1)\) is the dyadic cell \([j\log2,(j+1)\log2)\). \(W\) is \(T\)-invariant, so:

- diagonal blocks are level-independent;
- high details \(a\ge A\) carry the twin-blind floor;
- the finitely many generators \(G=\{\text{cell }1\}\cup\{\mathrm{Det}(a):a<A\}\) recur at every level;
- cross-level blocks are Toeplitz in the level difference, \(W(T^jf,T^kg)=W(f,T^{k-j}g)\).

For separated supports each cross entry is the Chebyshev integral. The pole product alone would grow like \(2^{(k-j)/2}\); the prime main term cancels it, leaving \(e^h-\psi(e^h)\) tested against \(\Omega'\). The size is polynomial in the level gap under RH, and \(e^{h/2}\) times a subexponential saving unconditionally.

**First useful answer.** Three pieces:

1. The decomposition theorem and finite Grams (W01, W03).
2. A bound on couplings between high details at different levels, and between high details and the generator orbits, by the per-level reserves \(\log(a)h_a\) plus the Gamma square reserve, on pole-neutral sections. This is the research step.
3. A precise statement of what remains: positivity of the generator-orbit Toeplitz form. That is a one-prime orbit condition on a *finite* set, of the same type as the corpus's one-prime and one-shift receivers.

**Payoff.** Complete-cell positivity, an infinite-dimensional problem, becomes a finite-generator orbit problem plus a cross-scale payment. If the payment leaves a bounded index, AID converts it into finite off-line support.

**Why first.** It uses only proved structure: Gamma detail payment, self-similarity, the floor, translation invariance and the Chebyshev identity. It attacks the residual that all complete-form routes share (RW, HF, ACS, AIP, OWU, SRT, CHMD, SZ, EWU).

<a id="q2"></a>
### Q2. Which twin-selective inequality controls the generator orbits?

**Exact object.** The generator-orbit Toeplitz form of Q1, or equivalently the coarse/low residual of the complete source. Since every proved positive family is twin-blind, this is where \(\Lambda\) must differ from its twins.

**Candidate inputs.**

- **The pole-hyperplane prime gap:** \(g>0\) proved; \(2\log2\) for each finite prime set; all-prime \(2\log2\) conjectured. The value \(2\log2\) is the one-prime tower gap \(p\log p/(p-1)\) at \(p=2\), the same prime that generates the multiresolution.
- **Main-term cancellation in the Chebyshev identity.** For \(\Lambda\), \(e^h-\psi(e^h)=o(e^h)\). A twin's prime sum does not reproduce the main term \(e^h\): Liouville gives \(-e^h\), nonprincipal character mixtures \(o(e^h)\), \(c\Lambda\) gives \(ce^h\). The pole is left uncancelled in its cross entries. Finite prime flips do reproduce the main term. They are identified by the finite part, where \(\zeta\) is the unique maximizer and therefore the hardest case, and they fail positivity only through local witnesses such as the radius-181/500 odd witness against the 2-flip.
- **Character finite parts** \(2\operatorname{Re}(-L'/L(1,\chi))\).

**First useful answer.** A full-form lower bound on pole-neutral sections of the cell-1 orbit and the low details, in which the prime defect pays the pole beyond the spacing scale. This is the \(K_\star\) mechanism moved to coarse scale, with the gap compensating the negative Markov finite part beyond the Robin–Euler point. Quantify how much overlap the gap buys. A weaker but useful answer is an exact identification of the twin's negative directions inside the generator orbits.

**Why second.** Q1 without a selective input cannot succeed. The Liouville twin satisfies every twin-blind estimate and still fails.

<a id="q3"></a>
### Q3. What arithmetic upper estimate bounds the canonical critical energy?

**Exact object.** \(K(R)=R^2(\mathcal W(2R)-\mathcal W(R))\uparrow\mathcal E_{\rm crit}\in[0,\infty]\). This is a nonnegative pair energy including off-line/critical exterior interactions. Its finite-support value \((3/2)\sum\gamma_\rho^2d_\rho F_\rho\) has signed summands.

**First useful answer.** Any finite upper bound on \(K\), equivalently \(\mathcal E_{\rm crit}<\infty\), proves finite off-line support. Bounded \(\mathcal W\), \(\Delta\mathcal W\to0\) and eventual \(\Delta\mathcal W\le39/50\) are equivalent intermediate forms. The RH endpoint is \(\mathcal E_{\rm crit}\le Q_*=1294047/2000\); a finite nonempty exceptional set gives a value strictly above \(Q_*\).

**Required mechanism.** An upper estimate from prime/theta structure that keeps critical exterior rows. Lower index costs \(I_*k\) and \(50k^2-3k/2\) convert such an estimate into an index ceiling but do not produce it. A conservation law of virial type, equating \(\mathcal E_{\rm crit}\) with a source moment that arithmetic can bound, is the natural shape. The interior reserve-to-alignment step is unproved.

**Why third.** It is an independent route to a historic intermediate theorem, with an exact threshold for removing the last exception. It does not depend on Q1/Q2.

## 2.4 A wildly different route?

**No route was found that avoids all three walls.** The reason is structural:

- Any proof must use a property that separates \(\zeta\) from its twins. Davenport–Heilbronn-type functions, Beurling/golden curve data and the Liouville twin share the functional equation, growth and many positivity properties, yet violate RH. That is the selectivity wall.
- The proof must act at the critical scale, where the corpus shows every exact criterion is a sign or size statement about the same signed source. That is the critical-estimate wall.
- It must survive exhaustion of an infinite source. That is the transfer wall.

A route that imports positivity from a field where RH-type theorems are proved must realize \(\zeta\) faithfully inside that field — the realization wall.

Four directions far from the current routes were examined:

1. **Approximation by curves over finite fields.** Weil's theorem would supply positivity for free. In the natural normalization, every nonnegative combination of curve explicit-formula distributions is supported on \(\{\pm\log(\text{prime powers})\}\cup\{0\}\), exactly the support of \(\Lambda\) — a striking match. But \(\zeta\)'s zero-side distribution has a nonzero continuous part (pole minus archimedean density) on \((0,\log2)\), which no such limit can produce. Dilating the curves removes this obstruction, but their atoms leave \(\log(\text{prime powers})\), and the approximation becomes one of \(\zeta\)'s zero side, which is circular. The archimedean place cannot arise from finite places, so this route collapses into the realization wall (new face 14.36).
2. **Measure rigidity of higher-rank multiplicative actions.** An off-line zero gives a non-unitary character \(n^{\rho-1/2}\), not an invariant probability measure. The positive-definite and affine-group rigidity that does apply is already the APD programme.
3. **Interlacing families / barrier methods** (Marcus–Spielman–Srivastava). Real-rootedness of averages needs a common interlacer, and the cosine family defining \(\Xi\) has none. What remains merges with LA/ALG.
4. **Modular or conformal bootstrap.** Its linear-functional positivity is Weil's explicit-formula positivity in other coordinates (U2).

If a genuinely new route exists, it would need a structure in which **selectivity is automatic**: one where only Euler products with the exact simple pole can be realized, and realization itself forces positivity. No candidate structure with that property is known.

## 2.5 Would the obstacles in 2.2 need a new field of mathematics?

**Assessment.** The RH-equivalent endpoints (a) are not reachable by the mechanisms the corpus has assembled. Every proved positivity is twin-blind, being absolute, prime-free or local. Every selective statement is either RH-equivalent or prime-only. What is missing is a mechanism class that turns arithmetic selectivity (the Euler product and the exact pole) into quantitative signed control at the critical scale on a complete, self-similar source. Whether this counts as a new field or a new theorem inside analytic number theory cannot be decided from the corpus. It is at least a new *kind* of inequality: no existing discipline proves selective positivity of a renormalized quadratic form under infinite exhaustion.

### What the field would be about

**Selective multiscale arithmetic positivity.** Its subject is the Weil form as a translation-invariant quadratic form on the complete multiplicative source. It has three energy sources — finite places (primes), the archimedean place (Gamma) and the pole — and a renormalization group generated by integer dilations. It asks when such a form is positive, and why only for \(\Lambda\).

### Objects

- Complete logarithmic-cell sources and their dyadic multiresolution; generator orbits under \(T_{\log p}\).
- The Weil form \(W=\Gamma+\text{poles}-P\), its twins \(W_\lambda\) (\(|\lambda|\le\Lambda\)), and the null radical.
- Reserves: Gamma interval-variance and square reserves, the prime Dirichlet defect \(D_N\), per-level detail floors.
- Discrepancy measures: \((e^h-\psi(e^h))\,dh\) against correlation derivatives \(\Omega'_{f,g}\).
- Spectral objects: finite-sieve adjunction operators, Ramanujan modes, the pole hyperplane.
- Global invariants: canonical critical energy and the index.

### Language

- A **selective inequality** is one that fails for some bounded twin.
- A **reserve** is a nonnegative quantity that pays exactly once.
- An **RG step** coarse-grains by a Hecke dilation, with the defect it creates recorded.
- An **exhaustion statement** names its source, form, domain, growth parameter and error currency together.

### Mechanisms it must discover

| Mechanism | Purpose | Test |
|---|---|---|
| Selective Gårding inequality | \(W\ge\text{reserve}-C\cdot\text{selective defect}\), where the defect vanishes in the limit for \(\Lambda\) and not for twins | Must fail for Liouville, \(c\Lambda\), quadratic mixtures, golden data |
| RG monotonicity of the index | Show coarse-graining by \(T_2\) cannot create negative squares once details are paid | Must respect translation escape and nonsummable pole couplings |
| Cross-scale almost-orthogonality | A Cotlar–Stein/Schur lemma for *forms*: cross-level blocks paid by geometric decay in level difference | Must use Chebyshev main-term cancellation at large separation |
| Discrete-to-continuous pole transfer | Move the prime gap from \(\sum x_n/\sqrt n=0\) to the continuous pole moments | Must recover the \(K_\star\) mechanism at spacing scale |
| Virial/conservation law | Bound \(\mathcal E_{\rm crit}\) above by a source moment | Must keep critical exterior rows |
| Spectral exhaustion | Control growing conductor families and their complement | Must match the adjunction energies \(E_m\) and the Weyl law |

### Questions it must answer

- What is the minimal twin-selective quantity, and is it the pole-hyperplane gap, Chebyshev main-term cancellation, or something not yet named?
- Does the negative index of the complete form flow monotonically under dyadic renormalization?
- Why is the conjectural sharp prime gap \(2\log2\), and why does the same prime 2 generate the self-similarity?
- Which conservation law bounds critical energy from above?
- How does the archimedean place couple to the finite places along the RG flow? Gamma variance pays \(\log(1/\text{width})\), and cell widths at level \(a\) are \(\approx1/a\).
- In which topology does exhaustion preserve inequalities, given that no exponential renormalization gives uniform graph control?

### Criteria it must meet

1. **Independence.** Built from arithmetic data, never from zero-indexed objects.
2. **Fidelity.** All mixed entries, Gamma, both poles and multiplicities. Prime-only, collided and complete forms are kept apart.
3. **Selectivity.** Every sufficient hypothesis fails for the battery: Liouville twin, scalings, quadratic mixtures, golden curve, Davenport–Heilbronn-type functions.
4. **Exhaustion.** Uniformity exactly in the growing parameters.
5. **Calibration.** Reproduce Weil's proof over \(\mathbb F_q\) (Frobenius graph positivity), the narrow \(K_\star\) regime, the finite-\(Q\) gap and the Haar floor, without demanding the false all-overlap Metzler gauge or pure-Markov sign.
6. **A new inequality.** A paid sign, index ceiling or energy upper bound — not another equivalence.
7. **Formal closure.** Unconditional Lean statements with every input discharged.

**First evidence of success** would be a theorem answering a substantive part of Q1, Q2 or Q3. The minimal convincing instance is a selective inequality on the cell-1 orbit that the Liouville twin violates.
