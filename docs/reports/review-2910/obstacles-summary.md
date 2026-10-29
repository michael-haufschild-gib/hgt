# Research frontier: work, open problems and next questions

Status: 29 October 2026, corpus checkpoint `3c5f89e3b2` plus working tree. **RH remains open.** The corpus pins down what the missing input must be:

- **parity-sensitive**: it fails for the Liouville twin (selection theorem) and must see every prime's sign, since single large-prime flips share the maximal margin;
- **square-root-precise**: it fails for \(\Lambda+\varepsilon n^{-\eta}\), \(\eta<\tfrac12\), so no interval statement stable under relative error \(o(1)\) supplies it;
- **global**: it acts at unbounded aperture, on at least two prime towers (one prime aliases).

In index language this is one statement: the Weil kernel of \(\zeta\) on the Hecke lattice has index zero iff \(\psi(x)-x\le C\sqrt x\log^2x\) eventually, the same "one-sided square-root count" that Stepanov produces over \(\mathbb F_q\) [S]. Two strata are exact: finite off-line support is RH above some height and contains the Lindelöf hypothesis; and \(70\%\) is priced three ways, each by a parity- or displacement-sensitive input.

Coverage: 31 live routes, 17 standalone candidates, PW-B. Companions: [route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md). Evidence: corpus searches and Lean statements; no builds. **[L]**/**[S]** as in the [frontier map](../rh-current-frontier-map.md); **(inference)** = conclusion of this review. Record: [working log](../../../logs/review-2910-research-2026-10-29.md).

## What the corpus establishes

- **Selection** [L]; the margin \(2\log2\) is sharp, paid by harmonic correlation, attained exactly by single flips \(p\ge11\); finite, prime-tail and cofinite flips are classified [L]; actual conductor eigenlines exist for every prime pattern [S].
- **Index theory** [S]: \(\kappa(K_\zeta)=\#\)right zeros; two primes carry it; one prime sees ordinate windows shorter than \(2\pi/\log p\); at most \(\binom\kappa2\) primes are blind; \(\kappa\) is priced quadratically by critical energy and counted by heat collisions; index zero is the one-sided \(\psi\) count.
- **Tower positivity is RH** at every generator size [L]; **precision rigidity** [L].
- **Atomic receivers** to \((\log\log N)^{1+\varepsilon}\) overlap; gap/scalar reduction at every width [L].
- **Narrow positivity** to a quarter of Robin–Euler [L]; separated-regime splitting and trial energies [L]; actual complete-Weil eigenlines for every \(0<c<1\) [S].
- **Finite-index chain**: every prime layer except the first [L/S].
- **Finite support** \(\iff\) RH above a height \(\iff\) bounded heat counts \(\iff\) finite index [S]; \(\Rightarrow\) LH \(\wedge\) \(\Theta<1\) [L].
- **Census**: \(\ge HD(1)+10^{-8}\) simple critical; \(\ge0.8876\) simple or critical; exact bandwidth, capacity and slack exchange rates [L].
- **Quasi-RH**: complete translation layer; Guth–Maynard Theorem 1.1, density \(30/13\), DH on \(\sigma\ge5/6\), primes in \(x^{17/30+\varepsilon}\)-intervals, VK region [L]; no producer; density envelopes cannot force vanishing [L].
- **Over \(\mathbb F_q\)** local-to-global is a count, produced by Stepanov [L].

## 2.1 Tasks that are just work

"Just work" means the ingredients exist. A sign task delivers a certified enclosure, not a guaranteed sign.

| ID | Task / deliverable | Serves | Boundary |
|---|---|---|---|
| W01 | Atomic Grams at width ratios from \(K_\star\) through \(K_1\approx0.43\), \(4K_1\) and up to \(1\): Markov form on \(p=0\) and affine scalar on \(p=1\) separately, for \(\zeta\), Liouville and \(\omega_{11},\omega_{13}\), using the actual eigenline and conductor-coordinate theorems. | Q1; AIP, SRT, HF, ACS | Finite \(N\) locates failure points; no eventual sign. |
| W02 | Bottom spectrum past Robin–Euler: turn the per-conductor eigenline law into a uniform statement (all conductors below an energy cut, operator-norm control of replacement errors). | Q1; RAPT | Fixed packets are proved; uniformity in conductor may be [open]. |
| W03 | Explicit head sizes \(A\) in every finite-index theorem. | HF, ACS, AIP | The \(k=1\) layer stays [FS]. |
| W04 | First-layer constants \(C_P\) along growing prime sets against the detail reserve; locate where absolute payment fails. | HF, ACS; 2.3 | Measures the obstruction. |
| W05 | Compose the finite-stratum Krein–Langer structure of \(K_\zeta\) with the blind-prime theorem: under finite support, positivity on infinitely many prime towers, or on one non-blind tower, gives RH. | 2.3; HKT | Composition of proved [S] theorems. |
| W06 | Tabulate \(d\mapsto W(f,T_{d\log2}g)\) for the cell-1 generator with certified \(\psi\) data. | WL, HF, CHMD, AIP | No sign. |
| W07 | Complete multiresolution Grams: orbits, details, cross-level blocks, Gamma, both poles. | HF, ACS, AIP, RW, SRT | Exact algebra. |
| W08 | Chen–Gupta–Li: formalize the continuation/contour step and capstone; extract the zero-free abscissa as a function of the density exponent, the large-value exponent and the modulus aspect; evaluate at \(q=1\) with Guth–Maynard \(30/13\) and DH on \(\sigma\ge5/6\). | 2.4; MC | Depends on the external argument. |
| W09 | Best positive-definite-majorant bound for the narrow-strip pair energy \(E(\delta)\); compare with \(E(1/9)\le4\). | Q2 | Expected to fall short; measures the gap. |
| W10 | Explicit constants in \(hE_h\le CN\) and the deep budget; compare with \(3/20\). | Census, WD | Displacement-blind majorant. |
| W11 | Optimize the Gabor-pinching slack. | Census | Bounded gain. |
| W12 | Explicit \(N(t)\) bounds on compact time ranges; constants in the \(2/3\) horizon; near-axis count tables. | WD, LA; 2.3 | Finite \(t\)-ranges. |
| W13 | Finish the localized heat-energy evolution estimate from the pair-force, exterior-force and forward-simplicity bounds. | WD, LA | Gives evolution control, not a uniform count. |
| W14 | Ordered Chebyshev integrals for block pairs with explicit \(\psi\) data and VK bounds. | WL, HF, AIP, CHMD | Unconditional growth \(e^{h/2}\) up to subexponential saving. |
| W15 | Projections, Schur residuals, radicals, bounded-window transport constants. | AID, SAHT, CHMD, HF | Window-dependent. |
| W16 | Ramanujan residual/Gram estimates for fixed conductor sets; tower deficits at \(p\le43\); infinite-pattern greatest gaps from the actual conductor coordinates. | RAPT, ACP, HF | Classification, not a sign. |
| W17 | Gauge finite parts \(-L'/L(1,\chi)\) and Chebotarev pattern means; identify the unfolded Hecke Mellin integrals with normalized Hecke \(L\)-series and prove the full functional equation. | RAPT, OWU, ACG, HLF | Tools. |
| W18 | Seed/drift/history/cross-block/endpoint ledgers; the RP escape constant on computed ranges. | FU, RP, LI, TT, PA | Accounting. |
| W19 | Finite Möbius, pronic, Vaughan and Báez–Duarte rows with readout and centered energy apart. | MC, PM, CTF, JAS | No small-damping tail. |
| W20 | Translate any supplied strip bound through every dictionary, including the balanced short-window and Cesàro mean-square forms. | MC, WL, BVI | Transport. |
| W21 | Compact cofactor Grams, effective pole orders, record-minimum diagonals. | PM | Compactness is not tightness. |
| W22 | Certified finite-aperture ground energies, blind minima, finite-level feasibility, shell relaxations. | RW, EWU, OWU, ACT | Finite windows. |
| W23 | Finite heat/Jensen/Hankel heads; both Gaussian grids; Laguerre data; the first-atom analytic tail. | LA, TH, WD, HCF, PA | No all-degree inference. |
| W24 | Newton discs, Ward caps, renewal resolvents, transgression traces, Schur charges, compact recurrence. | XN, WD, RN, TG, GTA, BAG | Local certificates. |
| W25 | Finite Robin/Nicolas ranges; finite Cayley–Li ladders; Suzuki tent patterns. | RB, LI, SZ | Finite ranges. |
| W26 | Slack calculus at \(\lambda\in[3/4,1)\): the displaced-pair thresholds for \(70\%\) and \(75\%\); whether the negative-part credit \(2\operatorname{tr}Q_-\) of actual Grams admits a lower bound in terms of zero displacement. | Q2; ACS | Zero-side quantity; needs data on zeros. |
| W27 | Candidate calculations: cycle traces, curvatures, repair defects, jets, contours, contrasts, co-shift defects, photonic/Ising stacks, certificate streams, cusp actions. | Candidates, PW-B | Calibration is not forcing. |
| W28 | Literature intake: Bui–Heath-Brown, Kurasov–Sarnak/Olevskii–Ulanovskii, Bourgain's DH for \(\sigma\ge25/32\), Montgomery's pair-correlation bounds, loop Eisenstein series (Garland; where the \(\xi\)-zero hyperplanes meet the region of Maass–Selberg positivity), Stepanov–Bombieri over \(\mathbb F_q[t]\). | Census, 2.4, 2.7, Q3 | Acceptance of external proofs is not assumed. |

## 2.2 Open mathematical obstacles

### (a) RH-equivalent endpoints

| ID | Missing result | Routes |
|---|---|---|
| O1 | Critical signed prime/Möbius cancellation in any currency: one-sided \(\psi\) count (= index zero of \(K_\zeta\)), lag energy, Abel moment, linear history floor, strict half-power, regularized convergence, extremal remainder, approximation residual, half-power budget. It is also every separated and cross-level entry of the complete form. | WL, FU, RP, MC, LI, PBM, RB, JAS, CTF |
| O2 | Complete Weil positivity on a source-complete family: complete-cell index zero, residual sign, full/even/odd/allocation/Hodge/effectivity sign, atomic sign at unbounded overlap, integer-atom Grams, tent-family first variation. | RW, HF, SZ, EWU, OWU, AIP, ACS, TT, CHMD, ACT, SRT |
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
| F1 | Uniform finite index of the complete form: relative form-compactness of the first prime layer with odd diagonals, heads, coarse error and poles against Gamma. | HF, ACS, AIP |
| F2 | Finite \(\mathcal E_{\rm crit}\); bounded source work. | HF, SRT, ACS |
| F3 | Prime lag minus finitely many exponentials bounded on one side. | WL |
| F4 | Nonreal counts of \(H_t\) bounded as \(t\downarrow0\). | WD, LA |
| F5 | Bounded cosine defects. | WD |
| F6 | Bounded index on a two-prime lattice. | ACS, HKT |

### (d) Lindelöf and quasi-RH levels

| ID | Missing result | Status |
|---|---|---|
| L0 | Zeros approach the line (LH plus finitely many nonreal zeros of every \(\cos(hD)\Xi\)). | Implies LH and \(\Theta<1\). |
| L1 | The Lindelöf hypothesis, equivalently Backlund sparsity of off-line zeros. | Open since 1908. |
| Q0 | A fixed zero-free strip \(\Theta<1\): a one-sided power saving in any strip dictionary, including balanced short windows. | Claimed externally at \(7/8\). |

### (e) Intermediate open problems, possibly below RH strength

| ID | Missing result | Why current work stops | Payoff |
|---|---|---|---|
| I1 | **Selective separated-regime step**: \(W\ge0\) on atomic families at a fixed ratio \(c\in(K_1,1)\). | Narrow positivity keeps absolute values on the pole term; the actual bottom spectrum past \(K_1\) is known only per conductor. | First full positivity where the Markov form is negative, from an input Liouville lacks (Q1). |
| I2 | Metzler endpoint \(\rho=1\); signed/block replacements of the frustrated gauge. | Gauges frustrate for \(\rho>1\). | Hodge structure through the spacing. |
| I3 | Growing-conductor spectral control of the prime and complete-Weil matrices. | Only fixed packets. | Producer for I1, F1. |
| I4 | **Trans-threshold pair energy** \(E(1/9)\le4\). | Signed coalescent pair sum; one-sided sieves give nothing. | \(70\%\) (Q2). |
| I5 | Displacement-sensitive shallow-energy constant \(hE_h+R_{\rm deep}\le\tfrac3{20}N\). | The majorant sums over all zeros. | \(70\%\). |
| I6 | **Zero-side slack** \(\ge N/30\) (resp. \(N/12\)) at bandwidth just below one. | Slack is a zero-side quantity; small-displacement pairs are blind. | \(70\%\) (resp. \(75\%\)). |
| I7 | Exterior tightness; exclusion of infinite-height escape. | Record minima permit zero gauge mass. | PM progress short of O5. |
| I8 | Conductor/forcing compatibility for companion-cluster detectors. | No common aperture range. | OWU/SRT detection. |
| I9 | **Stepanov over \(\mathbb Z\)**: an auxiliary construction producing a one-sided prime count, without a lattice spectrum; first rung: beating the sieve's parity constant. | Sparse annihilators kill only critical lattice symbols; compression is a receiver; sieve upper bounds lose a factor \(2\). | A producer of counts (Q3). |
| I10 | An **arithmetic Krein–Langer ceiling**: an index bound for \(K_\zeta\) from local data. | Positive parts never pay hyperbolic pairs; locality fails on \(\mathbb Z^2\). | Finite support, then RH via blind primes. |
| I11 | Independent faithful constructions for each candidate. | Calibrations, zero-indexed objects. | Candidate promotion. |
| I12 | Whether \(\zeta\)-only inputs move the Chen–Gupta–Li threshold below \(7/8\). | Threshold not extracted (W08). | An improved quasi-RH. |

"No known solution" refers to the corpus and the literature consulted.

**What all B-items share (inference).** Each needs at least one of: a parity-breaking input; square-root precision; control at unbounded aperture or an independent construction. Both of the first two have been obtained together only over \(\mathbb F_q\), from geometry or Frobenius (Weil, Deligne, Stepanov).

## 2.3 Can we prove that off-line zeros, if any, are finitely many?

**Verdict: no, not as a near-term target. Finiteness is RH above some height, and it contains the Lindelöf hypothesis.**

**The stratum is exact.** For any two distinct primes the following are equivalent [S]: finite index of \(K_\zeta\); finite index on the two-prime lattice; finitely many off-line zeros; uniformly bounded nonreal zero counts of \(H_t\); all zeros above some height \(T_0\) critical ([Lean](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean)). Finiteness then implies that zeros approach the line, hence LH and \(\Theta<1\) [L].

Two consequences (inference):

- Finiteness is not a weaker version of RH at large height; it **is** RH at large height. Every hard height is above any fixed \(T_0\). A proof with effective \(T_0\) below the numerically verified range would prove RH.
- LH (open since 1908, best \(\mu(1/2)\le13/84\)) is Backlund's sparsity statement: \(o(\log t)\) off-line zeros per unit window at fixed depth. Finiteness asks for zero, everywhere above \(T_0\).

**Structure inside the stratum [S].** If finite, the kernel is positive-definite plus \(\kappa\) hyperbolic pairs; at most \(\binom\kappa2\) primes are blind to them; positivity on infinitely many prime towers forces \(\kappa=0\); small-time heat collisions number exactly \(2(\kappa+\text{multiplicity excess})\); \(\kappa\le\sqrt{2\mathcal E_{\rm crit}/97}\). So finiteness would make RH "local in the prime": almost every single tower decides (W05).

**Openings, ranked.**

1. **Arithmetic Krein–Langer ceiling (I10).** The global law has a finite-stratum form: the subtracted lag \(\psi(x)-x+\sum_{\text{finitely many}}x^\rho/\rho\) bounded on one side by \(C\sqrt x\log^2x\) is equivalent to finiteness (F3). Over \(\mathbb F_q\) the corresponding count comes from Stepanov. A \(\mathbb Z\)-count with finitely many exceptions needs the same producer as RH (I9).
2. **Heat flow.** Uniform \(N(t)\) is finiteness. Available: reality beyond \(2\pi e^{(2/3+\varepsilon)/t}\) and deep counts \(\le C\log X\cdot N(t)\) for \(t\log X\le cd^2\). Even a polynomial \(N(t)\le At^{-a}\) would give only polylogarithmic deep counts. No mechanism controls backward collisions at all heights.
3. **Critical energy.** \(\mathcal E_{\rm crit}<\infty\) is finiteness; virial laws exist for finite configurations; no arithmetic upper bound.

**What does not work.** Proportions (the census controls only fractions); density bounds (an envelope never drops below \(1\)); positive majorants (a positive part never pays a hyperbolic pair); twin-blind payments (Liouville satisfies them); regular integer counts (over-regular Beurling systems carry off-line zeros).

**Strongest unconditional statements in this direction.** Off-line zero copies are at most \(1-HD(1)\approx32.75\%\); zeros within \(4/\log T\) of the line are \(\ge3/4\); \(N(\sigma,T)\ll T^{(30/13)(1-\sigma)+\varepsilon}\) and DH on \(\sigma\ge5/6\); \(\mu(11/18)\le1/9\) on the way to LH.

**Recommendation.** Do not target finiteness. Use it as a diagnostic: any argument giving finite index without an LH-strength input is wrong. The useful work is W04, W05, W12–W13.

## 2.4 Can we prove a quasi-RH better than \(1/8<\operatorname{Re}\rho<7/8\)?

**Verdict: not with the corpus's own mechanisms. The corpus translates every strip exactly and has the strongest available density inputs, but density cannot produce vanishing. The only lever on a constant is the external Chen–Gupta–Li detector, whose threshold has not been extracted.**

**Translation layer [L].** \(\Theta=\tfrac12+\inf\{c\}\) over one-sided exponents for the Möbius-divisor Abel moment, its quotient head at any cutoff, and finite-contact Suzuki residuals; \(\Theta\le1-\theta\) iff escaped rates, Hecke-defect caps or theta-prefix growth; \(\Theta<1\) iff a uniform Vaughan power saving, iff a power saving in balanced short windows for Möbius or primes; \(\Theta\le3/4\) iff the normalized Chebyshev Cesàro mean-square energy is \(\ll N^{3/2+\varepsilon}\). A strip \(\operatorname{Re}\rho<3/4\) is therefore a one-sided \(M^{1/4+\varepsilon}\) bound in any of these currencies.

**Inputs [L].** Guth–Maynard Theorem 1.1; \(N(\sigma,T)\ll T^{(30/13)(1-\sigma)+\varepsilon}\) on \([1/2,5/6]\); DH on \(\sigma\ge5/6\); primes in \((x,x+x^{17/30+\varepsilon}]\) with the asymptotic; almost-all intervals \(x^\theta\), \(\theta>2/15\); Vinogradov–Korobov zero-free region.

**Why they cannot produce a strip.**

- A density envelope \(CT^{\theta(1-\sigma)}(\log T)^A\) stays \(\ge1\) throughout the strip [L].
- Short-interval results hold at relative precision \(o(1)\); a strip needs a power saving \(x^{-\delta}\) uniformly over short windows. Guth–Maynard gives the former, not the latter.
- Zeros approaching the line would give a strip, but that is LH-strength (2.3).
- The VK region has width \(\to0\).

**The external lever.** Chen–Gupta–Li claim Dirichlet zero-freeness for \(\operatorname{Re}s>7/8\) from a zero detector, the explicit-zero-mode bound \((R+1)\le288N^{1-2\sigma}(B+S)^{1/3}+288N^{2-2\sigma}\) (Proposition 4.6, formalized) and the all-moduli density \((qT)^{7(1-\sigma)/3}\). For \(\zeta\) alone the corpus has better density: \(30/13<7/3\), and DH beyond \(5/6\). Whether these move \(7/8\) depends on two structural facts:

1. whether the detector needs the modulus aspect \(q\) or only the height aspect;
2. whether the threshold is monotone in the density exponent near the threshold.

If both are favourable, \(\zeta\)-specific inputs give a strip narrower than \((1/8,7/8)\), conditional on the external argument (inference). The envelope floor \(288\) against the collision quantum \(2\) blocks an RH endpoint from this detector, not an improved constant.

**Recommendation.** W08: extract the threshold as a formula. The result is either an improved constant or a precise reason why \(7/8\) is the detector's limit. It is not among the three next questions: it is extraction, and its payoff is a constant, not a mechanism.

## 2.5 Can we prove that at least 70% of zeros lie on the critical line?

**Verdict: not with any input the corpus or the literature has. \(70\%\) is now priced three ways, and every price is a parity-sensitive or displacement-sensitive input.**

**Where the census is [L].** \(\ge HD(1)+10^{-8}\approx0.6725\) simple critical; \(\ge0.8876\) simple or critical. The extremal configurations consist of simple zeros, so simplicity theorems cannot move the critical count.

**Price 1: bandwidth beyond one.** The proportion is \(2-\phi(\lambda)\). At \(\lambda=1+\delta\), \(\text{proportion}-\tfrac23=\delta(2-(3E(\delta)-4)\delta)/(3(1+\delta)^2)\) with the Cesàro pair energy \(E(\delta)=(2/\delta^2)\int_1^{1+\delta}(1+\delta-\alpha)F\). **\(E(1/9)\le4\) gives exactly \(+1/30\), i.e. \(70\%\).** In capacity form, \(70\%\iff\kappa\le13/10\) against the unconditional \(\kappa=4/3\) at bandwidth one (inference from the \(\kappa\le5/4\iff75\%\) law [L]).

- Nothing is known about \(F\) beyond \(\alpha=1\) unconditionally; under RH only \(E(\delta)\ll1/\delta\).
- The prime side is a signed sum over coalescent prime pairs; its Poisson main term cancels only against the exact Hardy–Littlewood term [L]. One-sided sieves control nothing; two-sided asymptotics are parity problems (inference).

**Price 2: zero-side spectral slack.** For \(\lambda<1\), \((H(\lambda)-\varepsilon)N+\text{zeroSideSlack}\le N_0^*\) with \(H(\lambda)=2-1/\lambda-\lambda/3\) [L]. \(70\%\) needs slack \(\ge(0.7-H(\lambda))N\), which tends to \(N/30\) as \(\lambda\to1\). The grid-dimension ceiling \(\text{slack}\le(\lambda-H(\lambda)+\varepsilon)N\) rules this out for \(\lambda<0.7\) (inference from [L]). In the displaced-pair model at \(\kappa=4/3\), slack\(/N=2\eta/(3(1+2\eta))\), so \(N/30\) needs displacement \(\eta\ge1/18\) (inference from the Lean identities). Pairs with smaller displacement are invisible to the slack.

**Price 3: shallow Cauchy energy.** \(hE_h+R_{\rm deep}\le\kappa N\Rightarrow N_0\ge(1-2\kappa)N\); \(70\%\) is \(\kappa=3/20\). The corpus proves \(O(N)\) at depth \(1/\log T\) with a majorant summing over all zeros, so the constant cannot separate critical from off-line zeros [L].

**Closed alternatives.** Mollified moments (value moments are depth-blind); higher trace moments only for \(k\lambda\le1\); the \(0.679\) SDP bound uses a negative tail with no off-RH analogue.

**Conclusion.** The cheapest input is a two-sided prime-pair estimate in the coalescent band at bandwidth \(10/9\) with constant four times GUE, or a zero-side input seeing pair displacements of size \(\ge1/18\) at bandwidth just below one. Both are the counting face of the selectivity wall.

## 2.6 The three questions to answer next

<a id="q1"></a>
### Q1. Is the complete Weil form positive in the separated regime past the Robin–Euler ratio?

**Exact object.** Atomic families \(f_x=\sum_{n\le N}x_ng(\cdot-\log n)\) at a fixed ratio \(c\in(K_1,1)\), \(K_1\approx0.43\). There the atoms are disjoint, the Markov form is negative, and
\[
W\ge0\iff M\ge0\text{ on }\textstyle\sum x_n/\sqrt n=0\ \text{ and }\ M+2a_0B\ge0\text{ on }\textstyle\sum x_n/\sqrt n=1 .
\]

**Why now.** The corpus has the exact separated-regime splitting, simple and proper trial energies [L], one actual complete-Weil eigenline per conductor converging to its Ramanujan line at every \(c<1\) [S], and actual conductor coordinates for every prime pattern [S]. The spectral picture of \(\zeta\), the Liouville twin and the \(\omega_p\) flips can be computed on actual eigenlines, not models. The conductor-two energy \(\log(4K_1/c)\) predicts positivity on \(p=0\) throughout the separated regime, while the Liouville twin (gap \(0\)) must fail (inference).

**Caveat.** \(\omega_p\), \(p\ge11\), share the maximal margin, so a positive answer is Liouville-selective, not \(\zeta\)-selective.

**First useful answer.** \(M\ge0\) on \(p=0\) at some \(c>K_1\) with the pole term signed; or the affine scalar there; or a computed counterexample (W01–W02).

**Payoff.** The first theorem in which a selective input pays the full form where the Markov form is negative. A negative answer is equally decisive: the discrete margin would not survive the passage to overlap.

<a id="q2"></a>
### Q2. Can a parity-breaking or displacement-sensitive input push the census to \(70\%\)?

**Exact objects.** Either \(E(1/9)=162\int_1^{10/9}(10/9-\alpha)F(\alpha)\,d\alpha\le4\) (the coalescent-band surplus of prime pairs \(p,q\le T^{10/9}\) with \(|\log p-\log q|\lesssim1/T\), a short-interval prime variance at length \(X^{1/10}\)); or zero-side slack \(\ge N/30\) at bandwidth just below one.

**Why now.** All three exchange rates are exact [L]. The two objects are dual: the first is a prime-side two-sided estimate, the second a zero-side displacement bound, and the slack calculus prices displacement exactly.

**First useful answer.** W09 (the best majorant bound and its distance from \(4\)); an exact reduction of \(E(1/9)\le4\) to a stated Type I/II bilinear estimate; a theorem that every parity-blind input leaves \(E\) unbounded; or a lower bound for the negative-part credit \(2\operatorname{tr}Q_-\) of actual Grams in terms of displacement (W26).

**Payoff.** A new unconditional census theorem, or a sharp location of the parity barrier inside the census.

<a id="q3"></a>
### Q3. What identity over \(\mathbb Z\) can play the role of Frobenius in a Stepanov argument?

**Exact object.** The global law: \(\kappa(K_\zeta)=0\iff\psi(x)-x\le C\sqrt x\log^2x\), and over \(\mathbb F_q\), \(\kappa=0\iff N_k\ge q^k+1-Cq^{k/2}\) [S]. Over \(\mathbb F_q\) the count is produced by an auxiliary polynomial vanishing to high order at the rational points, whose existence uses \(x^q=x\). Over \(\mathbb Z\) the corpus shows that compressions never raise the index and kill a hyperbolic pair only by annihilating its character (a receiver), and that sparse annihilators kill only critical lattice symbols [L/S].

**The first rung.** Selberg-type upper bounds for primes in short intervals lose a factor \(2\); that loss is the parity barrier. An auxiliary-function argument over \(\mathbb Z\) that beats the constant \(2\) on intervals of length \(x^\varepsilon\) is far below RH: precision rigidity shows such statements cannot decide RH. But it would be the first parity-breaking count produced by an auxiliary construction.

**First useful answer.** One of:

- reproduce Stepanov over \(\mathbb F_q[t]\) in the corpus's compression/count language and isolate the single step that uses Frobenius;
- a formal no-go: auxiliaries assembled from Dirichlet polynomials of bounded vanishing order are parity-blind;
- a candidate identity (for example from the Euler product and functional equation used as identities, not estimates) with a computed test against the Liouville twin.

**Payoff.** A mechanism that produces counts rather than requiring them. Q3 is the only one of the three that targets the producer, not the receiver.

**Why these three.** Q1 tests whether the U2 programme's measured selective input can pay the full form. Q2 tests the same parity question in the counting world, where the payoff is concrete. Q3 asks for the missing producer in its cleanest form. They are independent.

## 2.7 Is there a wildly different route?

**No wildly different route survives.** Every corpus route either bounds a signed quantity (Wall 1) or builds an object whose structure forces reality (Wall 14), and must hold at every scale (Wall 3). A route outside all three would get zero-freeness from a structural identity with no estimate and no exhaustion. The one candidate of that kind, analytic continuation by infinite symmetry, was calibrated over \(\mathbb F_q(t)\) and is blind to zeros.

### Analytic continuation by infinite symmetry: calibrated and blind

**Mechanism.** Multiple Dirichlet series whose functional equations generate a group \(G\). By Bochner's tube theorem, holomorphy extends to the convex hull of the \(G\)-images of the region of absolute convergence. For finite Weyl groups this is all of \(\mathbb C^n\); for affine and Kac–Moody Weyl groups it is the complexified Tits cone, beyond which infinitely many poles accumulate at a natural boundary. The force would be holomorphy, not sign, and Bochner's theorem is global, so there would be no estimate and no exhaustion.

**Calibration object.** The quadratic series of type \(D_4^{(1)}\) over \(\mathbb F_q(t)\), \(q\equiv1\bmod4\), whose coefficients are fourth moments \(\sum_d\prod_{i=1}^4L(s_i+\tfrac12,\chi_{d_0})P_d\,|d|^{-s_5}\) of quadratic \(L\)-functions. Diaconu–Paşol–Popa prove \(Z(q^{-1/2}x;q)=F(x^\delta)Z^{CG}_W(x;\sqrt q)\) with \(F(z)=\prod_{n\ge1}(1-qz^{2n-1})^{-2}\), meromorphic continuation to \(\Omega=\{|x^\delta|<1\}\) and none beyond, singularities only on \(x^{2\alpha}=q^{-1}\) for positive affine real roots \(\alpha\), and an exact formula for the weighted fourth moment ([arXiv 2111.11062](https://arxiv.org/abs/2111.11062), Thms 1.1, 1.2, 8.1, 9.1; Rem. 9.1).

**Verdict: blind in three independent ways.**

| Test | Finding |
|---|---|
| Is RH an input? | No. Continuation to \(\Omega\) uses trivial absolute convergence for \(\lvert x_i\rvert<1/q\), the functional equations and one residue comparison at \(x_5=q^{-1/2}\). |
| Do zeros enter the singularities? | No. Every singularity in \(\Omega\) lies on \(x^{2\alpha}=q^{-1}\), the shape of the pole \((1-qu)^{-1}\) of \(\zeta_{\mathbb F_q(t)}\). The natural boundary \(\lvert x^\delta\rvert=1\) is the accumulation of the poles of \(F\), of the same shape. \(\zeta_{\mathbb F_q(t)}\) has no zeros, so the boundary is not made of zeros, and no zero of any \(L(s,\chi_d)\) appears in the polar divisor. |
| Does the output force RH? | No. The series sees the coefficient \(L\)-functions only through moments. Since \(P_d\ge0\), the exact fourth moment gives each member \(\lvert L(\tfrac12,\chi_d)\rvert\ll q^{D/4}D^{5/2}\): the convexity bound, true without RH. |

**Ceiling for every root system.** Moment information certifies zeros only through the Jensen depth product: for \(L(u)=\prod_\alpha(1-\alpha u)\), \(\prod_{|\alpha|r>1}|\alpha|r\le\max_{|u|=r}|L(u)|\), so a weighted \(2k\)-th moment bound \(M\) gives each member depth product \(\le(M/w)^{1/2k}\). Inserting an off-line pair of depths \(\rho\), \(\rho^{-1}\) multiplies the depth product by exactly \(\rho\) and the circle maximum by at most \((1+\rho)(1+\rho^{-1})\), a factor independent of the degree. Domains of holomorphy read exponential growth rates in the degree, so no radius of convergence or natural boundary can see such pairs [L] ([moment ceiling](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MomentBoundsCapTheOffLineDepth.lean)). Granting all moments at their conjectured size (Kac–Moody types from the fifth moment on), the strongest possible output is a family-uniform Lindelöf bound, which allows off-line depth mass \(o(D)\): the Lindelöf stratum, never RH (inference).

**Unchecked branch.** A zero-seeing variant needs zeros in the polar divisor itself. Either (i) a global function field of positive genus, the function field of a curve of genus \(\ge1\) over a finite field \(\mathbb F_q\) (for example a reduction of \(y^2=x^3-x\) mod \(p\)), whose zeta function has \(2g\) zeros, together with an affine quadratic multiple Dirichlet series over it with proved continuation, which the literature consulted does not provide; a function field over \(\mathbb C\) has no zeta function and does not qualify; or (ii) Garland's loop Eisenstein series over \(\mathbb Q\), whose constant terms carry ratios of \(\xi\). Branch (i) can only test whether zeros of \(\zeta_K\) are seen, since they already satisfy RH there (Weil). In Garland's series the \(\xi\)-zero hyperplanes \(\langle\lambda,a^\vee\rangle=\rho-1\) lie outside the dominant chamber, where Maass–Selberg positivity says nothing, as in finite rank (inference, not checked against the loop-group literature). Record: [pipeline card](../../drafts/pipeline/5-failed/infinite-symmetry-continuation-calibration.md).

### Mechanisms examined and rejected

| Mechanism | Re-entry point |
|---|---|
| Deligne/Kurokawa tensor amplification | The tensor square of the prime error is WL's mean square with abscissa \(2\Theta\); Deligne's extra input is local purity on a base with known cohomology (Wall 14). |
| Fourier interpolation / modular certificates | RH is semidefinite; its dual certificate is \(\Lambda\) itself (EWU existence form). |
| Interlacing families / stability preservers | Needs \(\Xi\) as an expected polynomial of an arithmetic family (Wall 14) and uniform convergence (Wall 3). |
| Measure rigidity on the two-prime lattice | Positivity on \(\langle p,q\rangle\) is Bochner positivity of a spectral measure on \(\mathbb T^2\): exactly the HKT two-prime index (U2). |
| Model-theoretic transfer (Ax–Kochen ultraproducts of function fields) | RH for \(\zeta\) is not a first-order statement in the valued-field language; ultraproducts do not reach \(\mathbb Q\). |
| o-minimal point counting (Pila–Wilkie) | The primes are not definable in any o-minimal structure. |
| Fourier quasicrystals (Kurasov–Sarnak, Olevskii–Ulanovskii) | The archimedean continuum breaks the crystalline dual; the real-stable lift is W1C's Bohr-torus Lee–Yang landing. |
| Infinite-symmetry continuation (affine and Kac–Moody multiple Dirichlet series) | A moment generating function: singularities are images of the pole of \(\zeta_K\); moments see zeros only through the Jensen depth product; ceiling at the Lindelöf stratum. |

## 2.8 Would the obstacles in 2.2 need a new field of mathematics?

**Assessment: for (a), (c), (d) and I9–I10, probably yes; I1–I3, I7–I8 and I12 look reachable with existing tools.** The corpus has built its own framework far enough to see what it lacks:

1. The selective input must be parity-breaking, square-root-precise and global.
2. Analytic number theory produces parity-breaking only at relative precision \(o(1)\) or on average (Type II sums, Matomäki–Radziwiłł), and square-root precision only for structured sums.
3. Both together have been obtained only over \(\mathbb F_q\), from geometry or Frobenius.
4. Cross-level couplings are almost-periodic Toeplitz sequences whose symbol is the zero measure, so no summable-cost calculus pays them.
5. Index passes to limits only for pointwise kernel convergence; the Weil form is not continuous on \(L^2\) of tests; locality fails on \(\mathbb Z^2\).
6. Finite support already contains LH: even the intermediate stratum needs a global mechanism.

The corpus has now built the foundations of the field this points to, in HKT. What is missing is the one theorem that would make it a field rather than a dictionary.

### What the field would be about

**Arithmetic Krein–Langer theory: indefinite harmonic analysis on the idele class group, from local data to a global index.** Its object is the Weil distribution as a kernel on \(\mathbb A^\times/\mathbb Q^\times\): a positive part assembled from local factors, plus hyperbolic characters \(|\chi|\ne1\) that are exactly the off-line zeros. Its aim is an **arithmetic Krein–Langer theorem**: the hyperbolic part is empty, proved from local data and one global law. Over \(\mathbb F_q\) the theorem exists (Castelnuovo–Severi gives index zero; Stepanov gives the count that the global law turns into index zero).

### What exists in the corpus and what does not

| Pillar | Status |
|---|---|
| Index formula: positive kernel plus separated hyperbolic pairs has index exactly the number of pairs | [S] |
| Index of \(K_\zeta\) = right zeros; two primes carry it; one prime aliases; blind primes \(\le\binom\kappa2\) | [S] |
| Global law: index zero \(\iff\) one-sided square-root count, over \(\mathbb F_q\) and \(\mathbb Z\) | [S] |
| \(\mathbb F_q\) calibration: hyperelliptic RH by counting; golden curve index \(1\) on its tower, \(\infty\) on the lattice | [L]/[S] |
| Index price (critical energy), heat count, compression law, pointwise-limit closure | [S] |
| **Local-to-global index ceiling** | missing |
| **An arithmetic compressor or count producer over \(\mathbb Z\)** | missing |
| **An index-carrying completion of the test space** | missing |
| **A positive theory of parity at square-root precision** | missing |

### What it would be like

Weil's proof transported to a setting with an archimedean place: index theory first (how many hyperbolic pairs a kernel with given local factors can carry), then counting (square-root counts that bound the index), then positivity as a consequence. Analytic estimates verify local inputs; they never cancel signs globally.

### Objects

- The Weil kernel \(K_\zeta\) on \(\mathbb Q_{>0}^\times\), its restrictions to prime towers and two-prime lattices, and its twins \(K_\lambda\).
- Hyperbolic character pairs and Pontryagin spaces of finite index; compressions by auxiliary measures.
- The multiplicative walk with Poincaré constant \(2\log2\); the harmonic hyperplane; arithmetic modes \(\gamma+\log m+d(m)\); conductor coordinates of prime patterns.
- Square-root counts: one-sided prime and point counts; Sylvester inertia of explicit-formula Grams.
- Local factors as positive-definite kernels on \(\mathbb Q_v^\times\), and the archimedean factor.

### Language

- **Selective**: fails for a bounded twin. **Parity-breaking**: distinguishes \(\lambda\)-twisted from untwisted data. **Precision-faithful**: distinguishes \(\Lambda\) from \(\Lambda+\varepsilon n^{-\eta}\).
- **Blind prime**: a prime whose tower aliases two hyperbolic characters. **Index-carrying topology**: one in which bounded index passes to limits.
- **Count**: a one-sided bound at square-root precision. **Producer**: a construction that yields a count without assuming it. **Local-to-global**: a map from local kernels and one count to a global index.

### Tools it must develop, with tests

| Tool | Purpose | Test |
|---|---|---|
| Arithmetic compressor (Stepanov over \(\mathbb Z\)) | Produce a one-sided prime count from an auxiliary object | Reproduce hyperelliptic RH; fail for Liouville; first beat the sieve constant \(2\) (Q3) |
| Local-to-global index ceiling | Bound \(\kappa(K_\zeta)\) from local factors and one global law | Index zero over \(\mathbb F_q\); fail for Davenport–Heilbronn, the golden curve on the lattice and over-regular Beurling systems; imply LH whenever it gives finite index |
| Selective transfer to overlap | Turn the \(2\log2\) gap into full positivity past Robin–Euler | Q1; fail for Liouville |
| Two-sided coalescent pair theory | Prime-pair asymptotics beyond bandwidth one at bounded constant | Q2; reproduce Hardy–Littlewood models; fail for parity-twisted models |
| Index-carrying completion | A completion on which the Weil kernel is continuous for index | Agree with pointwise kernel limits; reproduce the tower and Nyquist laws |
| Structural precision | Use the Euler product and functional equation as identities | Fail for every \(n^{-\eta}\) perturbation |

### Questions it must answer

- What replaces \(x^q=x\) over \(\mathbb Z\)?
- What is the positive form of the parity barrier, and is the \(2\log2\) margin (the width of an index-one window) its first quantitative trace?
- Why does finite index imply LH, and is there a direct local-to-global argument for it?
- In which completion does the Weil kernel carry its index to the limit?
- Why do two primes suffice, and which arithmetic property makes locality hold for the arithmetic class when it fails on \(\mathbb Z^2\)?
- What arithmetic quantity governs the near-axis collisions of the heat flow?

### Criteria it must meet

1. **Independence.** Built from arithmetic data, never from zero-indexed objects.
2. **Fidelity.** All mixed entries, Gamma, both poles and multiplicities; prime-only, collided and complete forms kept apart.
3. **Battery.** Every sufficient hypothesis fails for: Liouville; \(c\Lambda\) and quadratic mixtures; single-prime flips with the maximal margin; cofinite flips; \(\Lambda+\varepsilon n^{-\eta}\); the golden curve; over-regular Beurling systems; Davenport–Heilbronn functions.
4. **Parity and precision.** An input that \(\lambda\)-twisting and \(n^{-\eta}\) perturbation both change.
5. **Exhaustion.** Uniformity exactly in the growing parameters, in an index-carrying topology.
6. **Calibration.** Reproduce Weil over \(\mathbb F_q\) by counting, the \(2/3\) census, the \(K_\star\) regime and the sharp gap.
7. **A new inequality.** A paid sign, index ceiling, count or energy bound, not another equivalence.
8. **Formal closure.** Unconditional Lean statements.

**First evidence of success:** a positive Q1 that fails visibly for Liouville; \(E(1/9)\le4\) from an input that fails for the parity-twisted model; or any auxiliary construction over \(\mathbb Z\) beating the sieve constant \(2\).

### No second field from infinite symmetry

Analytic continuation by infinite reflection groups does not supply a second field for these obstacles: over \(\mathbb F_q(t)\) its domain and natural boundary are built from the pole of \(\zeta_K\), and its moment content is capped at the Lindelöf stratum by the Jensen depth product (2.7). A version that sees zeros would need zeros in the polar divisor and positivity on the hyperplanes that carry them; neither is available.
