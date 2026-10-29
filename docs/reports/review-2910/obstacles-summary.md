# Research frontier: work, open problems and next questions

Status: 29 October 2026, corpus checkpoint `7f191801a3` plus working tree. **RH remains open.** The corpus pins down what the missing input must be:

- **parity-sensitive**: it fails for the Liouville twin, and it must see every prime's sign, since single large-prime flips share the maximal margin;
- **square-root-precise**: any property that implies the count rejects \(\Lambda+\varepsilon n^{-\eta}\), \(\eta<\tfrac12\), and depends on infinitely many coefficients (deciding-input theorem);
- **global**: it acts on at least two primes and at unbounded overlap; locality is twin-blind;
- **point-side**: a producer must vanish at the primes, not at the zeros, and bound one parity class from above.

One unconditional fact changes the map. The complete Weil form of \(\zeta\) is positive definite on atomic families at every fixed overlap ratio \(0<c\le1+10^{-18}\), past the Metzler threshold, where its Liouville twin is negative [L/S]. RH is the same positivity at overlap \(c_N=(\log\log N)(\log\log\log N)^{\beta}\), \(\beta>2\) [L]. In this language the distance to RH is **overlap growth**.

Coverage: 31 live routes, 17 standalone candidates, PW-B. Companions: [route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md). Evidence: corpus searches and Lean statements; no builds. **[L]**/**[S]**/**[K]** as in the [frontier map](../rh-current-frontier-map.md); **[Lean]** = statement read, integration not assessed; **(inference)** = conclusion of this review. Record: [working log](../../../logs/review-2910b-research-2026-10-29.md).

## What the corpus establishes

- **Selection** [L]; the margin \(2\log2\) is sharp and shared at its maximum by single flips \(p\ge11\); finite, prime-tail, sparse and cofinite flips are classified [L]; every flip fails full Weil positivity [Lean].
- **Selective positivity at bounded overlap**: complete positivity at every fixed \(c\in(0,1+10^{-18}]\) for one plateau [L]; the Liouville twin is negative for \(c\ge1/2\) [S]; the Markov form fails above \(e/2\pi\) [L].
- **RH-complete overlap**: \(c_N=(\log\log N)(\log\log\log N)^\beta\), \(\beta>2\), for one profile [L]; compact Gevrey-\(\le1\) profiles vanish [S]; finite support bounds the atomic index uniformly in \(c\); a tempered finite-support model is negative at every \(c\) [S].
- **Index theory** [S]: \(\kappa(K_\zeta)=\#\)right zeros; two primes carry it; Nyquist and blind-prime laws; fine towers decide; locality is twin-blind [L]; exceptional waves count the index; index is priced by \(\mathcal E_{\rm crit}\); index zero is the one-sided \(\psi\) count, and already the odd Liouville class's upper count.
- **Precision** [S/L]: the count has the square-root class as stabilizer, tower positivity the trivial one; integrality over \(\mathbb Z\) is exact and its exponent is \(\Theta\); sup-norm certificates must vanish at small rationals; monotone inversion runs at Mertens precision; the Stirling error splits into smooth, monotone and sawtooth parts.
- **Tower positivity is RH** at every generator size; **precision rigidity** [L]; two primes separate every ordinate difference polynomially [S].
- **Finite-index chain**: every prime layer except the first [L/S/K].
- **Finite support** \(\iff\) RH above a height \(\iff\) finite index \(\iff\) bounded heat counts [S]; \(\Rightarrow\) LH \(\wedge\) \(\Theta<1\) [L].
- **Census**: \(\ge HD(1)+10^{-8}\) simple critical; \(\ge0.8876\) simple or critical; exact bandwidth, capacity and slack exchange rates [L]; 3/4-or-near-line-off-line dichotomy [Lean].
- **Quasi-RH**: complete translation layer; Guth–Maynard Theorem 1.1, \(30/13\), DH on \(\sigma\ge5/6\), \(17/30\) short intervals, VK [L]; no producer.
- **Over \(\mathbb F_q\)**: the count is produced (Stepanov) [L]; the twist tower completes the upper count [S]; zeros of a genus-one zeta function appear as poles of the affine \(A_1\) Weyl sum with full multiplicity [K/L].

## 2.1 Tasks that are just work

"Just work" means the ingredients exist. A sign task delivers a certified enclosure or a transferred proof, not a guaranteed sign.

| ID | Task / deliverable | Serves | Boundary |
|---|---|---|---|
| W01 | Run the Trans-Metzler scheme (reference floor, prime-defect coercivity, \(O((wN)^2)\) overlap perturbation) to the largest ratio it reaches; certified constants for the floor as a function of \(c\). | Q1; HF, SRT, AIP, ACS | Perturbative; locates where the method stops, not an eventual sign beyond it. |
| W02 | Run the same decomposition for single flips \(\omega_p\), \(p\ge11\), and for cofinite flips: a fixed-ratio positivity theorem or an explicit negative atomic witness. | Q1; I2 | The outcome is unknown; either answer is a theorem. |
| W03 | Optimize \(c_{\rm RE}(\varphi)\) over profiles and the narrow survival ratio of the Liouville twin; decide whether the twin has a sharp transition. | Q1 | Model-free optimization of explicit functionals. |
| W04 | Replace the weights \(q!(\log q)^{2q}\) of the Steklov profile by \(q!(\log q)^{(1+\varepsilon)q}\) to reach \(\beta>1\); identify the quasi-analytic edge exactly. | SRT, HF; I3 | The edge \(c_N=O(\log\log N)\) stays open. |
| W05 | Dependency-closed integration of the working sources: ZeroSideStratum, LiouvilleTwinSelectivity, AKLT, ASRP, CACT touching capstone, ACS Haar prime edges, loop-group spherical function. | all | Integration, not new mathematics. |
| W06 | Explicit head sizes \(A\) in every finite-index theorem; first-layer constants \(C_P\) along growing prime sets against the detail reserve. | HF, ACS, AIP; 2.3 | The \(k=1\) layer stays [FS]. |
| W07 | Compose the finite-stratum Krein–Langer structure of \(K_\zeta\) with the blind-prime and tower-Hasse theorems for the actual kernel: under finite support, positivity on infinitely many towers, or on one non-blind tower, gives RH. | 2.3; HKT | Composition of [S] theorems. |
| W08 | Tabulate \(d\mapsto W(f,T_{d\log2}g)\) with certified \(\psi\) data; tabulate \(I_n(F)\) and \(I_n(h)\) of the Stirling split and their cancellation. | WL, HF, CHMD, MC | No sign. |
| W09 | Complete multiresolution Grams: orbits, details, cross-level blocks, Gamma, both poles. | HF, ACS, AIP, RW, SRT | Exact algebra. |
| W10 | Chen–Gupta–Li: formalize the continuation/contour step and capstone; extract the zero-free abscissa as a function of the density exponent, the large-value exponent and the modulus aspect; evaluate at \(q=1\) with \(30/13\) and DH on \(\sigma\ge5/6\). | 2.4; MC | Depends on the external argument. |
| W11 | Best positive-definite-majorant bound for the narrow-strip pair energy \(E(\delta)\); compare with \(E(1/9)\le4\). | 2.5 | Expected to fall short; measures the gap. |
| W12 | Explicit constants in \(hE_h\le CN\) and the deep budget; compare with \(3/20\). | 2.5; WD | Displacement-blind majorant. |
| W13 | Re-run the 3/4-or-near-line dichotomy at \(70\%\): the proportion of simple off-line zeros within \(A/\log T\) forced when \(N_0<0.7N\). | 2.5 | A dichotomy, not a census. |
| W14 | Slack calculus at \(\lambda\in[3/4,1)\): displaced-pair thresholds for \(70\%\) and \(75\%\); lower bounds for the negative-part credit \(2\operatorname{tr}Q_-\) of actual Grams in terms of displacement. | 2.5; ACS | Zero-side quantity; needs data on zeros. |
| W15 | Gabor-pinching slack optimization. | Census | Bounded gain. |
| W16 | Explicit \(N(t)\) bounds on compact time ranges; constants in the \(2/3\) horizon; near-axis count tables. | WD, LA; 2.3 | Finite \(t\)-ranges. |
| W17 | Finish the localized heat-energy evolution estimate from the pair-force, exterior-force and forward-simplicity bounds. | WD, LA | Evolution control, not a uniform count. |
| W18 | Ordered Chebyshev integrals for block pairs with explicit \(\psi\) data and VK bounds. | WL, HF, AIP, CHMD | Unconditional growth \(e^{h/2}\) up to subexponential saving. |
| W19 | Projections, Schur residuals, radicals, bounded-window transport constants. | AID, SAHT, CHMD, HF | Window-dependent. |
| W20 | Ramanujan residual and Gram estimates for fixed conductor sets; infinite-pattern greatest gaps from the actual conductor coordinates. | RAPT, ACP | The zero-density case may be open. |
| W21 | Hecke: removable values, finite-class recombination, normalized functional equation; gauge finite parts \(-L'/L(1,\chi)\). | RAPT, OWU, HLF | Tools. |
| W22 | Seed/drift/history/cross-block/endpoint ledgers; the RP escape constant on computed ranges. | FU, RP, LI, TT, PA | Accounting. |
| W23 | Finite Möbius, pronic, Vaughan and Báez–Duarte rows with readout and centered energy apart. | MC, PM, CTF, JAS | No small-damping tail. |
| W24 | Translate any supplied strip bound through every dictionary, including balanced short windows, Cesàro mean square and the integrality (Siegel-half) form. | MC, WL, BVI | Transport. |
| W25 | Compact cofactor Grams, effective pole orders, record-minimum diagonals. | PM | Compactness is not tightness. |
| W26 | Certified finite-aperture ground energies, blind minima, finite-level feasibility, shell relaxations. | RW, EWU, OWU, ACT | Finite windows. |
| W27 | Finite heat/Jensen/Hankel heads; both Gaussian grids; Laguerre data; the first-atom analytic tail. | LA, TH, WD, HCF, PA | No all-degree inference. |
| W28 | Newton discs, Ward caps, renewal resolvents, transgression traces, Schur charges, compact recurrence; finite Robin, Cayley–Li and Suzuki ranges. | XN, WD, RN, TG, GTA, BAG, RB, LI, SZ | Local certificates. |
| W29 | Constant term of the affine \(A_1\) Eisenstein series over the genus-one \(\mathbb F_3\) base: arithmetic quotient, measures, coset-sum convergence, imaginary-root correction factor; for Garland over \(\mathbb Q\): determinant metric, Bruhat refinement, arithmetic quotient. | Q3; 2.7 | Construction; the polar-divisor constraint is I14. |
| W30 | Candidate calculations: cycle traces, curvatures, repair defects, jets, contours, contrasts, co-shift defects, photonic/Ising stacks, certificate streams, cusp actions. | Candidates, PW-B | Calibration is not forcing. |
| W31 | Literature intake: Garland's Maass–Selberg relations for loop groups; the affine Gindikin–Karpelevich formula of Braverman–Kazhdan–Patnaik; Diaconu–Paşol–Popa; the integer Chebyshev problem; Stepanov–Bombieri over \(\mathbb F_q[t]\); Bui–Heath-Brown; Bourgain's DH on \(\sigma\ge25/32\). | Q2, Q3, 2.4, 2.5 | Acceptance of external proofs is not assumed. |

## 2.2 Open mathematical obstacles

### (a) RH-equivalent endpoints

| ID | Missing result | Routes |
|---|---|---|
| O1 | Critical signed prime/Möbius cancellation in any currency: one-sided \(\psi\) count (= index zero of \(K_\zeta\)), odd-class upper count, lag energy, Abel moment, linear history floor, strict half-power, regularized convergence, extremal remainder, approximation residual, half-power budget, square-root integrality halves, signed inversion of the Stirling smooth term and sawtooth. It is also every separated and cross-level entry of the complete form. | WL, FU, RP, MC, LI, PBM, RB, JAS, CTF |
| O2 | Complete Weil positivity on a source-complete family: atomic positivity at overlap \(c_N\to\infty\) at the super-Gevrey rate, integer-atom Grams, complete-cell index zero, residual sign, full/even/odd/allocation/Hodge/effectivity sign, tent-family first variation. | RW, HF, SZ, EWU, OWU, AIP, ACS, TT, CHMD, ACT, SRT |
| O3 | Positivity on one prime's towers, already for pole-free generators of arbitrarily small support. | HF, ACS, AIP, CHMD, SRT |
| O4 | Simultaneous all-degree/all-height heat, moment or coefficient signs; Cayley–Li ladder sign; both Gaussian grids. | PA, LA, TH, WD, HCF, LI |
| O5 | Visibility of every escape state, cofinal admission, vanishing approximation error. | PM, CTF, MC |
| O6 | Rank-uniform transverse decay; all-point recurrence; covering Newton discs; integer trace cap; directed renewal orientation. | GTA, BAG, XN, TG, RN |
| O7 | \(\mathcal E_{\rm crit}\) at most one exclusion quantum, or cofinal source work \(\le2\). | HF, SRT, ACS |

### (b) Stronger than RH

| ID | Statement | Note |
|---|---|---|
| S1 | Abel-slope genus saturation; linear Mertens energy budget | RH plus simple zeros. |
| S2 | Matching-profile signed pair surplus at the stated strength | Not implied by RH. |

### (c) The finite-support stratum [FS]

Each item is equivalent to finitely many off-line zeros, equivalently to RH above some height; each implies LH and a fixed strip.

| ID | Missing result | Routes |
|---|---|---|
| F1 | Uniform finite index of the complete form: the first prime layer with odd diagonals, heads, coarse error and poles against Gamma. | HF, ACS, AIP |
| F2 | Finite \(\mathcal E_{\rm crit}\); bounded source work; eventual subquantum annular increment. | HF, SRT, ACS |
| F3 | Prime lag minus finitely many exponentials bounded on one side. | WL |
| F4 | Nonreal counts of \(H_t\) bounded as \(t\downarrow0\). | WD, LA |
| F5 | Bounded cosine defects. | WD |
| F6 | Bounded index on a two-prime lattice; a finite exceptional-wave number on a separating tower. | ACS, HKT, AKLT |

### (d) Lindelöf and quasi-RH levels

| ID | Missing result | Status |
|---|---|---|
| L0 | Zeros approach the line (LH plus finitely many nonreal zeros of every \(\cos(hD)\Xi\)). | Implies LH and \(\Theta<1\). |
| L1 | The Lindelöf hypothesis, equivalently Backlund sparsity of off-line zeros. | Open since 1908. |
| Q0 | A fixed zero-free strip \(\Theta<1\): a one-sided power saving in any strip dictionary, including balanced short windows and small integer auxiliaries at a power precision. | Claimed externally at \(7/8\) for Dirichlet \(L\)-functions [E]. |

### (e) Intermediate open problems, possibly below RH strength

| ID | Missing result | Why current work stops | Payoff |
|---|---|---|---|
| I1 | **Overlap growth**: complete positivity at every fixed ratio beyond \(1+10^{-18}\), and a floor uniform in \(c\) up to \(\log\log N\). | The proof is perturbative around touching: errors \(O((wN)^2)\) against a floor \(1/25\) and a defect reserve \(\ge1/128000\). | The first non-perturbative large-overlap theory; at the super-Gevrey rate it is RH (Q1). |
| I2 | **Flip selectivity at fixed ratio**: are \(\omega_p\), \(p\ge11\), and cofinite flips positive at fixed \(c\)? | No module evaluates flips on atomic complete forms. | Decides whether bounded overlap has a second selective layer beyond the pole. |
| I3 | **Bounded-overlap completeness**: does positivity at every fixed \(c\), or at \(c_N=O(\log\log N)\), imply RH or finite support? | The synthesis needs non-quasi-analytic compact profiles; the tempered countermodel lacks \(\zeta\)'s zero density. | Locates the exact overlap at which positivity becomes RH. |
| I4 | **Trans-threshold pair energy** \(E(1/9)\le4\). | Signed coalescent pair sum; one-sided sieves give nothing. | \(70\%\) (2.5). |
| I5 | Displacement-sensitive shallow-energy constant \(hE_h+R_{\rm deep}\le\tfrac3{20}N\). | The majorant sums over all zeros. | \(70\%\). |
| I6 | **Zero-side slack** \(\ge N/30\) (resp. \(N/12\)) at bandwidth just below one. | Small-displacement pairs are blind. | \(70\%\) (resp. \(75\%\)). |
| I7 | Exterior tightness; exclusion of infinite-height escape. | Record minima permit zero gauge mass. | PM progress short of O5. |
| I8 | Conductor/forcing compatibility for companion-cluster detectors. | No common aperture range. | OWU/SRT detection. |
| I9 | **Point-side producer (Stepanov over \(\mathbb Z\))**: an auxiliary construction vanishing at the primes that bounds the odd Liouville class from above. First rungs: beat the sieve's parity factor \(2\) on intervals \(x^\varepsilon\); certify small positive Nair integrals by a signed (not sup-norm) argument. | Compressions are receivers; Euler compressors are index-neutral; integrality speaks only at \(s\in\mathbb Z\); sup-norm certificates are capped by the integer Chebyshev constant \(\approx0.42>1/e\) (classical). | A mechanism that produces counts (Q2). |
| I10 | **Arithmetic Krein–Langer ceiling**: an index bound for \(K_\zeta\) from local data. | Positive parts never pay a pair; locality is twin-blind. | Finite support, then RH via blind primes. |
| I11 | Independent faithful constructions for each candidate. | Calibrations, zero-indexed objects. | Candidate promotion. |
| I12 | Whether \(\zeta\)-only inputs move the Chen–Gupta–Li threshold below \(7/8\). | Threshold not extracted (W10). | An improved quasi-RH, conditional on the external argument. |
| I13 | Growing-conductor spectral control of the prime and complete-Weil matrices. | Only fixed packets and per-conductor eigenlines. | Profile-independent large-overlap spectra (I1). |
| I14 | **Polar-divisor constraint for positive-genus affine Eisenstein series**: a spectral or holomorphy theorem restricting where Frobenius-pole hyperplanes may lie; then the same over \(\mathbb Q\) (Garland). | Zeros enter the polar divisor (genus one); no positivity on the hyperplanes that carry them. | A route outside the three walls (Q3, 2.7). |
| I15 | A many-node Gram floor from pairwise two-prime phase separation. | Baker bounds degenerate as \(\Delta\to0\). | HCF/SRT detection without aliasing. |

"No known solution" refers to the corpus and the literature consulted.

**What all B-items share (inference).** Each needs at least one of: a parity-breaking input; square-root precision; control at unbounded overlap or aperture; an independent construction. The first two have been obtained together only over \(\mathbb F_q\), where the producer works on the point side (Stepanov's polynomial vanishes at rational points) and the parity twin is geometric (a quadratic twist of base changes). Over \(\mathbb Z\) the one selective input proved to pay a full form is the pole, and it is parity-selective only.

## 2.3 Can we prove that off-line zeros, if any, are finitely many?

**Verdict: no, not as a near-term target. Finiteness is RH above some height, and it contains the Lindelöf hypothesis.**

**The stratum is exact [S/L].** For any two distinct primes the following are equivalent: finite index of \(K_\zeta\); finite index on the two-prime lattice; finitely many off-line zeros; bounded nonreal zero counts of \(H_t\); all zeros above some height critical; the subtracted lag bounded on one side [L]. Finiteness implies that zeros approach the line, hence LH and \(\Theta<1\) [L]. [TFAE](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean), [subtracted lag](../../../formal/GaloisForLFunctions/RHTower/FiniteOffLineConverse.lean).

Two consequences (inference):

- Finiteness is not a weaker RH at large height; it **is** RH at large height. A proof with effective \(T_0\) below the verified range would prove RH.
- LH (open since 1908; best \(\mu(1/2)\le13/84\)) asks for \(o(\log t)\) off-line zeros per unit window at fixed depth. Finiteness asks for zero above \(T_0\).

**Structure inside the stratum.** The kernel is positive-definite plus \(\kappa\) hyperbolic pairs; at most \(\binom\kappa2\) primes are blind; positivity on infinitely many towers forces \(\kappa=0\) [S]; on a separating tower \(\kappa\) is the least number of exponential waves leaving a bounded remainder, and small-time heat collisions number \(2(\kappa+\sum(m_\rho-1))\) [L/S]; the atomic index is at most the number of right zeros at every overlap [S]; \(\kappa\le\sqrt{2\mathcal E_{\rm crit}/97}\) [S]. Finiteness would make RH local in the prime: almost every single tower decides (W07).

**Openings, ranked.**

1. **A wave-number or Krein–Langer ceiling (I10).** Finiteness is a bounded remainder after subtracting finitely many waves on one tower. Bounding the wave number is a count with finitely many exceptions; over \(\mathbb F_q\) the index is bounded by the genus through Riemann–Roch before any count. Over \(\mathbb Z\) no Riemann–Roch ceiling exists; this is the same producer problem as RH (I9).
2. **Heat flow.** Uniform \(N(t)\) is finiteness. Available: reality beyond \(2\pi e^{(2/3+\varepsilon)/t}\), deep counts \(\le C\log X\cdot N(t)\) for \(t\log X\le cd^2\). Even \(N(t)\le At^{-a}\) gives only polylogarithmic deep counts. No mechanism controls backward collisions at all heights.
3. **Critical energy.** \(\mathcal E_{\rm crit}<\infty\) is finiteness; virial laws exist for finite configurations; no arithmetic upper bound.

**What does not work.** Proportions (the census controls fractions); density bounds (an envelope never drops below \(1\)); positive majorants (a positive part never pays a pair); twin-blind payments (Liouville satisfies them); locality (twin-blind); compressions (receivers); regular integer counts (over-regular Beurling systems); fixed-ratio positivity (a tempered finite-support model is negative at every ratio, so finiteness does not even follow from or imply bounded-overlap positivity without \(\zeta\)'s zero density).

**Strongest unconditional statements in this direction.** Off-line simple zeros plus twice off-line multiple zeros \(\le(\tfrac13+\varepsilon)N\) [Lean]; at least \(HD(1)\approx67.25\%\) simple critical; zeros within \(4/\log T\) of the line \(\ge3/4\); \(N(\sigma,T)\ll T^{(30/13)(1-\sigma)+\varepsilon}\) and DH on \(\sigma\ge5/6\); \(\mu(11/18)\le1/9\) [L].

**Recommendation.** Do not target finiteness. Use it as a diagnostic: an argument giving finite index without an LH-strength input is wrong. Useful work: W06, W07, W16, W17.

## 2.4 Can we prove a quasi-RH better than \(1/8<\operatorname{Re}\rho<7/8\)?

**Verdict: not with the corpus's own mechanisms. The corpus has no zero-free strip at all; it translates every strip exactly and has the strongest density inputs, but density cannot produce vanishing. The only lever on a constant is the external Chen–Gupta–Li detector, whose threshold has not been extracted.**

The strip \(1/8<\operatorname{Re}\rho<7/8\) is the external claim for Dirichlet \(L\)-functions [E]. For \(\zeta\) the best unconditional region in the corpus is Vinogradov–Korobov, whose width tends to \(0\).

**Translation layer [L/S].** \(\Theta=\tfrac12+\inf\{c\}\) over one-sided exponents of the Möbius-divisor Abel moment, its quotient head and Suzuki residuals; \(\Theta\le1-\theta\) iff escaped rates, Hecke-defect caps or theta-prefix growth; \(\Theta<1\) iff a uniform Vaughan power saving, iff a power saving in balanced short windows for Möbius or primes; \(\Theta\le3/4\) iff the normalized Chebyshev Cesàro mean-square energy is \(\ll N^{3/2+\varepsilon}\) [L]. The integrality exponent is \(\Theta\): \(\Theta<1\) iff for some \(\theta<1\) and all large \(n\) an integer polynomial of degree \(\le n\) has \(0<\int_0^1P\le e^{-(n+1)+Cn^\theta}\) [S].

**Inputs [L].** Guth–Maynard Theorem 1.1; \(N(\sigma,T)\ll T^{(30/13)(1-\sigma)+\varepsilon}\) on \([1/2,5/6]\); DH on \(\sigma\ge5/6\); primes in \((x,x+x^{17/30+\varepsilon}]\); almost-all intervals \(x^\theta\), \(\theta>2/15\); VK.

**Why they cannot produce a strip.**

- A density envelope \(CT^{\theta(1-\sigma)}(\log T)^A\) stays \(\ge1\) throughout the strip [L].
- Short-interval asymptotics hold at relative precision \(o(1)\); a strip needs a power saving uniformly over short windows.
- Zeros approaching the line would give a strip, but that is LH-strength (2.3).
- The integrality form needs a certificate for a small positive integral. Sup-norm certificates must vanish at \(0,\tfrac12,1\) [L], and their reach is the integer Chebyshev constant of \([0,1]\), about \(0.42>1/e\): they do not reach even the prime number theorem (classical). A certificate would have to be signed.

**The external lever.** Chen–Gupta–Li derive zero-freeness for \(\operatorname{Re}s>7/8\) from a zero detector, an explicit-zero-mode bound \((R+1)\le288N^{1-2\sigma}(B+S)^{1/3}+288N^{2-2\sigma}\) and the all-moduli density \((qT)^{7(1-\sigma)/3}\). For \(\zeta\) alone the corpus has better density: \(30/13<7/3\), and DH beyond \(5/6\). Whether these move \(7/8\) depends on (i) whether the detector needs the modulus aspect or only the height aspect, and (ii) whether the threshold is monotone in the density exponent near the threshold. If both are favourable, \(\zeta\)-specific inputs give a strip narrower than \((1/8,7/8)\), conditional on the external argument (inference). The detector floor \(288\) against the collision quantum \(2\) blocks an RH endpoint from this detector, not an improved constant.

**Recommendation.** W10: extract the threshold as a formula. The result is either an improved constant or a precise reason why \(7/8\) is the detector's limit. It is not among the next three questions: its payoff is a constant, not a mechanism.

## 2.5 Can we prove that at least 70% of zeros lie on the critical line?

**Verdict: not with any input the corpus or the literature has. \(70\%\) is priced three ways, and a dichotomy shows where every failure lives: in simple off-line zeros at depth \(O(1/\log T)\).**

**Where the census is [L].** \(\ge HD(1)+10^{-8}\approx0.6725\) simple critical; \(\ge0.8876\) simple or critical. Extremal configurations consist of simple zeros, so simplicity theorems cannot move the critical count.

**The dichotomy [Lean].** Eventually either \(N_0\ge\tfrac34N\), or at least \((HD(1)-\tfrac12-\tfrac1A-\varepsilon)N\) zeros, about \(17\%\) for large \(A\), are simple, off the line and within \(A/\log T\) of it. Any improvement of the census must exclude simple off-line zeros at displacement \(O(1/\log T)\), the scale at which value moments, shallow energies and pair correlation are all blind (inference).

**Price 1: bandwidth beyond one.** The proportion is \(2-\phi(\lambda)\). At \(\lambda=1+\delta\), \(\text{proportion}-\tfrac23=\delta(2-(3E(\delta)-4)\delta)/(3(1+\delta)^2)\) with \(E(\delta)=(2/\delta^2)\int_1^{1+\delta}(1+\delta-\alpha)F\). **\(E(1/9)\le4\) gives exactly \(70\%\)** [L]. In capacity form \(70\%\iff\kappa\le13/10\) against the unconditional \(\kappa=4/3\) at bandwidth one (inference from the \(\kappa\le5/4\iff75\%\) law [L]).

- Nothing is known about \(F\) beyond \(\alpha=1\) unconditionally; under RH only \(E(\delta)\ll1/\delta\).
- The prime side is a signed sum over coalescent prime pairs; its Poisson term cancels only against the exact Hardy–Littlewood term [L]. A positive-definite majorant gives \(8/27\) against the \(1/9\) needed at bandwidth \(4/3\) [L]. One-sided sieves control nothing; two-sided asymptotics are parity problems (inference).

**Price 2: zero-side slack.** For \(\lambda<1\), \((H(\lambda)-\varepsilon)N+\text{slack}\le N_0^*\), \(H(\lambda)=2-1/\lambda-\lambda/3\) [L]. \(70\%\) needs slack \(\ge(0.7-H(\lambda))N\to N/30\) as \(\lambda\to1\); the grid-dimension ceiling rules it out for \(\lambda<0.7\). In the displaced-pair model at \(\kappa=4/3\), slack\(/N=2\eta/(3(1+2\eta))\), so \(N/30\) needs displacement \(\eta\ge1/18\) (inference from the Lean identities).

**Price 3: shallow Cauchy energy.** \(hE_h+R_{\rm deep}\le\kappa N\Rightarrow N_0\ge(1-2\kappa)N\); \(70\%\) is \(\kappa=3/20\). The corpus proves \(O(N)\) at depth \(1/\log T\) with a majorant summing over all zeros [L].

**Closed alternatives.** Mollified moments (value moments are depth-blind); higher trace moments only for \(k\lambda\le1\); the \(0.679\) SDP bound uses a negative tail with no off-RH analogue. Fixed-overlap complete positivity does not feed the census: its test space has dimension \(N\) against \(\asymp N\log N\) zeros in its band, so positivity carries no count (inference).

**Conclusion.** The cheapest input is a two-sided prime-pair estimate in the coalescent band at bandwidth \(10/9\) with constant four times GUE, or a zero-side input that sees pair displacements \(\ge1/18\) at bandwidth just below one. Both are the counting face of the parity wall, the same obstruction as Q2.

## 2.6 The three questions to answer next

<a id="q1"></a>
### Q1. What controls the complete Weil form at large overlap?

**Exact object.** Atomic families \(f_x=\sum_{n\le N}x_n\varphi(\cdot-\log n)\) at width \(c/N\). Proved: eventual positive definiteness at every fixed \(c\in(0,1+10^{-18}]\) for \(\varphi_0=\mathrm{plateau}(1/1000)\) [L]. Needed for RH: positivity at \(c_N=(\log\log N)(\log\log\log N)^\beta\), \(\beta>2\), for the Steklov profile [L].

**Why now.** It is the only programme with a proved selective sign on the full form: on \([1/2,1+10^{-18}]\) the form is positive, the Liouville twin negative, the Markov form negative. The proof is perturbative around touching. The question has three layers, in order:

1. **Every fixed ratio** (I1): non-perturbative positivity at each fixed \(c>1+10^{-18}\), with the floor as a function of \(c\) (W01).
2. **Selectivity** (I2): whether single flips \(\omega_p\) are positive at fixed \(c\) (W02). If they are, the pole is the only selective input at bounded overlap and \(\zeta\)-selectivity must come from overlap growth. If not, bounded overlap has a second selective layer.
3. **Uniformity in \(c\)** up to \(\log\log N\) (I3), where the separated prime error of §8 of the route report must enter (inference).

**First useful answer.** The largest \(c\) the present scheme reaches; a theorem or counterexample for \(\omega_{11}\) at \(c=1\); or a non-perturbative description of the complete atomic matrix at fixed large \(c\) (for example as a Toeplitz-plus-Ramanujan operator in conductor coordinates) with its spectral floor.

**Payoff.** A large-overlap theory of the complete form. At the super-Gevrey rate it is RH; short of that, the location of the exact overlap where positivity becomes RH-strength.

<a id="q2"></a>
### Q2. What point-side construction over \(\mathbb Z\) produces an upper count for one parity class?

**Exact object.** The parity form of the global law: RH iff \(O(t)=\sum_{\lambda(n)=-1}e^{-nt}/n\le\tfrac12(H(t)+Ct^{1/2-\varepsilon})\) [S]. Over \(\mathbb F_q\) the corresponding upper count is produced by Stepanov's polynomial, which vanishes to high order at the rational points; the twist tower turns upper counts into the lower count [S].

**What the corpus excludes.** Compressions certify nothing over \(\mathbb F_q\) and Euler compressors are index-neutral over \(\mathbb Z\): a producer must vanish at the primes, not at the zeros [S]. Locality is twin-blind [L]. Integrality over \(\mathbb Z\) is exact: the least positive Nair integral is \(e^{-\psi(n+1)}\), and the halves of integrality are the halves of the count [S]; sup-norm certificates must vanish at small rationals [L]. Integer Dirichlet polynomials see integrality only at \(s\in\mathbb Z\) [S].

**First rungs**, far below RH and each new:

- beat the sieve's parity constant \(2\) for primes in intervals \(x^\varepsilon\) by an auxiliary construction;
- certify \(0<\int_0^1P\le e^{-(1-\delta)n}\) for explicit integer polynomials by a signed argument that beats the integer Chebyshev constant (\(\delta<0.14\) would already pass the sup-norm barrier);
- a formal no-go: auxiliaries assembled from Dirichlet polynomials of bounded vanishing order at the primes are parity-blind.

**Payoff.** A mechanism that produces counts rather than requiring them. Q2 is the only question aimed at the producer.

<a id="q3"></a>
### Q3. Is there a spectral constraint on the polar divisor of positive-genus affine Eisenstein series?

**Exact object.** Over the genus-one curve \(y^2=x^3-x\) over \(\mathbb F_3\), the affine \(A_1\) Gindikin–Karpelevich coefficients have poles at the Frobenius zeros with full multiplicity, and they survive the complete Weyl sum [K/L]. Over \(\mathbb F_q(t)\) (genus zero) the affine series continues to the Tits cone without RH and its singularities are images of the pole of \(\zeta_K\).

**Question.** Does the full Eisenstein series (or its constant term) satisfy a constraint, from holomorphy on a region proved without RH or from a Maass–Selberg/residual-spectrum positivity, that restricts where Frobenius-pole hyperplanes may lie? Over \(\mathbb F_q\) a yes re-proves the Riemann hypothesis for the curve by a mechanism unrelated to Weil, Stepanov or Bombieri: that is the calibration. Only then is Garland's series over \(\mathbb Q\) worth the cost.

**First useful answer.** The full constant term over the genus-one base (W29); the position of the Frobenius hyperplanes relative to the Tits cone and the dominant chamber; a literature check of Garland's Maass–Selberg relations (W31). A negative answer retires the route with a precise reason.

**Payoff.** The only candidate that bounds no signed sum, uses no exhaustion and builds no carrier.

**Why these three.** Q1 pushes the one proved selective sign toward RH. Q2 asks for the missing producer in its cleanest form. Q3 tests the only structurally different candidate. They are independent. The census (2.5) is the best intermediate milestone but shares Q2's parity obstruction.

## 2.7 Is there a wildly different route?

**One candidate survives, now with a concrete test: analytic continuation by infinite symmetry, in positive genus, where zeros enter the polar divisor.** Every corpus route either bounds a signed quantity (Wall 1), builds an object whose structure forces reality (Wall 14), and must hold at every scale (Wall 3). A route outside all three would obtain zero-freeness from a structural identity: no estimate, no exhaustion, no carrier. I see no other mechanism of that kind.

### Analytic continuation by infinite symmetry

**Mechanism.** Multiple Dirichlet series and Eisenstein series whose functional equations generate an infinite Weyl group \(W\). By Bochner's tube theorem holomorphy extends to the convex hull of the \(W\)-images of the convergence region: all of \(\mathbb C^n\) for finite \(W\), the complexified Tits cone for affine and Kac–Moody \(W\), with a natural boundary. Constant terms carry products of zeta ratios \(\xi(\langle\lambda,\alpha^\vee\rangle)/\xi(\langle\lambda,\alpha^\vee\rangle+1)\) over infinitely many roots, so zeros of \(\xi\) become poles along hyperplanes. The force would be a constraint on the polar divisor, not a sign.

**What is established.**

| Test | Genus zero (\(\mathbb F_q(t)\), Diaconu–Paşol–Popa) | Genus one (\(y^2=x^3-x\) over \(\mathbb F_3\), corpus) |
|---|---|---|
| RH used? | No: absolute convergence, functional equations, one residue comparison. | No. |
| Do zeros enter the polar divisor? | There are none; singularities are images of the pole of \(\zeta_K\). | Yes: Gindikin–Karpelevich coefficients have poles at Frobenius zeros with full multiplicity, surviving the complete Weyl sum [K/L]. |
| Does the output constrain zeros? | Moments see zeros only through the Jensen depth product: Lindelöf-stratum ceiling [L]. | Not yet asked: needs the full constant term and a spectral constraint (Q3). |

**Why it does not face the same walls (inference).** It bounds no signed prime sum, so Wall 1 enters only if the constraint is proved by estimates. It has no exhaustion parameter: Bochner's theorem is global. It builds no carrier whose positivity must be shown faithful; the Eisenstein series is the arithmetic object itself. The Jensen moment ceiling bounds what moments of such series can say, not what their polar divisor can say.

**What would make it a route.** A theorem that the polar divisor of the full series in some region proved without RH contains only hyperplanes of on-line type. Langlands' theory gives such constraints in finite rank (in the positive chamber the poles lie on finitely many real hyperplanes) but in finite rank the \(\xi\)-zero hyperplanes lie where those constraints are silent (inference, as in the finite-rank case). The open point is whether the infinite root system, through its imaginary-root correction factor and natural boundary, pushes a zero hyperplane into a constrained region. Over \(\mathbb F_q\) this is decidable by computation and calibrates against Weil's theorem.

**Risks.** The constraint may be silent exactly on the zero hyperplanes, as in finite rank; Garland's Maass–Selberg relations may hold only in the dominant chamber; the full series over \(\mathbb Q\) needs arithmetic-quotient measure theory the corpus does not have.

### Mechanisms examined and rejected

| Mechanism | Re-entry point |
|---|---|
| Deligne/Kurokawa tensor amplification | The tensor square of the prime error is WL's mean square with abscissa \(2\Theta\); Deligne's extra input is local purity on a base with known cohomology (Wall 14). |
| Fourier interpolation / modular certificates | RH is semidefinite; its dual certificate is \(\Lambda\) itself (EWU existence form). |
| Interlacing families / stability preservers | Needs \(\Xi\) as an expected polynomial of an arithmetic family (Wall 14) and uniform convergence (Wall 3). |
| Measure rigidity on the two-prime lattice | Bochner positivity on \(\mathbb T^2\) is the HKT two-prime index (U2). |
| Local-to-global by towers (Hasse principle for kernels) | Locality is twin-blind: unitary twists preserve every tower statement [L]. |
| Compression / annihilation | A receiver: over \(\mathbb F_q\) the characteristic polynomial annihilates every trace kernel; Euler compressors are index-neutral [S]. |
| Gelfond–Schnirelmann–Nair integer auxiliaries with sup-norm certificates | Integrality is exact; sup-norm certificates are capped by the integer Chebyshev constant (classical) and must vanish at small rationals [L]. Survives only as the signed-certificate rung of Q2. |
| Model-theoretic transfer (ultraproducts of function fields) | RH for \(\zeta\) is not first-order in the valued-field language; ultraproducts do not reach \(\mathbb Q\). |
| o-minimal point counting | The primes are not definable in an o-minimal structure. |
| Fourier quasicrystals | The archimedean continuum breaks the crystalline dual; the real-stable lift is W1C's Bohr-torus landing. |
| Infinite symmetry in genus zero | Blind: no zeros to see; moments capped at the Lindelöf stratum. Superseded by the positive-genus test above. |

## 2.8 Would the obstacles in 2.2 need a new field of mathematics?

**Assessment: for (a), (c), (d), I9, I10 and I14, probably yes; I1–I3, I7, I8, I12, I13 and I15 look reachable with existing tools.** The corpus has built the dictionary of the field this points to (HKT, AKLT, ASRP) far enough to see what it lacks:

1. The selective input must be parity-breaking, square-root-precise and global; locality cannot supply it.
2. Analytic number theory produces parity-breaking only at relative precision \(o(1)\) or on average, and square-root precision only for structured sums.
3. Both together have been obtained only over \(\mathbb F_q\), where the producer acts on the point side and the parity twin is geometric.
4. Over \(\mathbb Z\) the one selective input that pays a full form is the pole, and only at bounded overlap.
5. Integrality over \(\mathbb Z\) is exact but speaks only at integer arguments; the missing piece of an auxiliary method is the analytic certificate.
6. Index passes to limits only pointwise; finite support already contains LH.

### What the field would be about

**Arithmetic Krein–Langer theory with a point side.** Its object is the Weil distribution as an indefinite kernel on the idele class group: a positive part assembled from local factors, plus hyperbolic characters that are exactly the off-line zeros. Its aim is a **local-to-global index theorem**: the hyperbolic part is empty, proved from local data and one count produced on the point side. Over \(\mathbb F_q\) the theorem exists in two steps: Riemann–Roch bounds the index by the genus; Stepanov's count, completed by the twist tower, brings it to zero.

### What exists and what does not

| Pillar | Status |
|---|---|
| Index formula; \(\kappa(K_\zeta)=\#\)right zeros; two primes carry it; Nyquist, blind primes, fine towers | [S] |
| Global law and parity form: index zero is one parity class's upper count | [S] |
| Exceptional-wave number, index continuity, index price, heat collisions | [L/S] |
| Locality is twin-blind; compressions are receivers | [L]/[S] |
| \(\mathbb F_q\) calibration: Stepanov count, twist tower, Riemann–Roch ceiling, golden curve | [L]/[S] |
| Precision classes; integrality lattice and exponent; deciding-input theorem | [S/L] |
| Selective full positivity at bounded overlap | [L/S] |
| **A Riemann–Roch-type index ceiling over \(\mathbb Z\)** | missing |
| **A point-side producer: an auxiliary vanishing at the primes** | missing |
| **A geometric parity twin over \(\mathbb Z\)** | missing |
| **A non-perturbative large-overlap theory of the complete form** | missing |
| **An index-carrying completion of the test space** | missing |

### What it would be like

Weil's proof transported to a setting with an archimedean place, in Stepanov's order: an index ceiling from local data, then a count produced by an auxiliary object on the point side, then positivity as a consequence. Analytic estimates verify local inputs and certify auxiliaries; they never cancel global signs.

### Objects

- The Weil kernel \(K_\zeta\) on \(\mathbb Q_{>0}^\times\), its restrictions to prime towers, fine two-prime towers and integer atoms, and its twins \(K_\lambda\).
- Hyperbolic character pairs, Pontryagin spaces of finite index, exceptional waves.
- The two Liouville parity classes as the point sets to be counted; their harmonic–exponential counts.
- Integer auxiliaries: polynomials on \([0,1]\), integer Dirichlet polynomials, and their certificates.
- Atomic families at overlap \(c\) and their complete matrices in Ramanujan/conductor coordinates.
- Local factors as positive-definite kernels on \(\mathbb Q_v^\times\); the archimedean factor.

### Language

- **Selective**: fails for a bounded twin. **Parity-breaking**: distinguishes \(\lambda\)-twisted from untwisted data. **Precision-faithful**: distinguishes \(\Lambda\) from \(\Lambda+\varepsilon n^{-\eta}\). **Precision class**: the stabilizer of a statement among weights (\(\mathcal Q\) for the count, \(\{0\}\) for positivity).
- **Point side / zero side**: where an auxiliary vanishes. **Producer**: a construction that yields a count without assuming it. **Certificate**: an analytic bound that makes an integral auxiliary small.
- **Blind prime**, **wave number**, **index-carrying topology**, **overlap ratio**.

### Tools it must develop, with tests

| Tool | Purpose | Test |
|---|---|---|
| Point-side producer (Stepanov over \(\mathbb Z\)) | An upper count for one parity class from an auxiliary vanishing at the primes | Reproduce hyperelliptic RH; fail for the Liouville twin; first beat the sieve constant \(2\) or the integer Chebyshev constant (Q2) |
| Index ceiling over \(\mathbb Z\) | Bound \(\kappa(K_\zeta)\) from local factors, as Riemann–Roch bounds it by the genus | Index \(\le\) genus over \(\mathbb F_q\); fail for the golden curve on the lattice, Davenport–Heilbronn and over-regular Beurling systems; imply LH whenever finite |
| Large-overlap renormalization | Positivity of the complete form uniformly in overlap | Reproduce the fixed-ratio floor; fail for the Liouville twin above \(c_{\rm RE}\); decide \(\omega_p\) (Q1) |
| Geometric parity twin | A family of "base changes" over \(\mathbb Z\) on which the Liouville twist acts as a symmetry | Reproduce the twist tower over \(\mathbb F_q\) |
| Two-sided coalescent pair theory | Prime-pair asymptotics beyond bandwidth one at bounded constant | Hardy–Littlewood models; fail for parity-twisted models (2.5) |
| Polar-divisor spectral theory | Constrain the poles of infinite-rank Eisenstein series | Re-prove RH for a genus-one curve (Q3) |
| Index-carrying completion | A completion on which the Weil kernel is continuous for index | Agree with pointwise limits; reproduce tower and Nyquist laws |

### Questions it must answer

- What replaces \(x^q=x\) over \(\mathbb Z\), and what are the "rational points" an auxiliary should vanish at: the primes, the prime powers, or one parity class?
- What replaces Riemann–Roch as a ceiling on the index before any count?
- Is there a family over \(\mathbb Z\) on which the Liouville twist is geometric, as the quadratic twist of base changes is over \(\mathbb F_q\)?
- How does the pole's selectivity propagate from bounded overlap to overlap \(\log\log N\), and which input selects \(\zeta\) against \(\omega_p\)?
- What is the positive form of the parity barrier, and is the \(2\log2\) margin its first quantitative trace?
- In which completion does the Weil kernel carry its index to the limit?

### Criteria it must meet

1. **Independence.** Built from arithmetic data, never from zero-indexed objects.
2. **Fidelity.** All mixed entries, Gamma, both poles and multiplicities; prime-only, collided and complete forms kept apart.
3. **Battery.** Every sufficient hypothesis fails for: the Liouville twin; \(c\Lambda\) and quadratic mixtures; single flips with the maximal margin; cofinite flips; \(\Lambda+\varepsilon n^{-\eta}\); \(\Lambda+1/n\) (for positivity statements); the golden curve on the lattice; over-regular Beurling systems; Davenport–Heilbronn functions.
4. **Parity and precision.** An input that \(\lambda\)-twisting and \(n^{-\eta}\) perturbation both change, and that is not local.
5. **Exhaustion.** Uniformity exactly in the growing parameters, in an index-carrying topology.
6. **Calibration.** Reproduce Weil over \(\mathbb F_q\) by counting, the \(2/3\) census, fixed-ratio positivity and the sharp gap.
7. **A new inequality.** A paid sign, index ceiling, count or energy bound, not another equivalence.
8. **Formal closure.** Unconditional Lean statements.

**First evidence of success:** fixed-ratio positivity at some \(c\ge2\), or a decision for \(\omega_{11}\); any auxiliary construction over \(\mathbb Z\) beating the sieve constant \(2\) or the integer Chebyshev constant; or a polar-divisor constraint that re-proves RH for one curve over a finite field.
