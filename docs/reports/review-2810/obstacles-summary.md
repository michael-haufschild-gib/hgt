# Research frontier: work, open problems and next questions

**RH remains open.** The corpus pins down what the missing input must be:

- **parity-sensitive**: it must fail for the Liouville twin (selection theorem);
- **square-root-precise**: it must fail for \(\Lambda+\varepsilon n^{-\eta}\), \(\eta<\tfrac12\), so no statement about primes in intervals that survives a relative error \(o(1)\) can supply it;
- **global**: it must act at unbounded aperture.

The one quantified selective input, the spectral gap \(2\log2\) on the pole hyperplane, separates \(\zeta\) from Liouville but not from multiplicative twins that flip a single large prime. Two strata are exact: finite off-line support implies the Lindelöf hypothesis and a zero-free strip; and a \(70\%\) census needs a two-sided prime-pair estimate just beyond bandwidth one.

This summary covers all 31 live routes, the 17 standalone candidates and PW-B. Companions: [route-by-route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md). Evidence: corpus searches and Lean statements; **[K]** includes individual Lean and transitive-axiom checks. No full or umbrella builds. **[L]**/**[S]**/**[K]** as in the [frontier map](../rh-current-frontier-map.md); **(inference)** = conclusion of this review, not a Lean theorem. Research record: [working log](../../../logs/review-2810-v3-research-2026-10-28.md).

## What the corpus establishes

There are three destinations:

1. **Critical signed arithmetic control:** prime/Möbius histories, approximation energies, regularized series, source work.
2. **Complete Weil positivity:** full, even, odd, incidence, Hodge, effectivity, atomic, tower and moment formulations.
3. **Independent forcing:** a geometric, spectral, dynamical or counting structure whose proved property supplies 1 or 2.

The following results define the present frontier (sources in the [route report](route-obstacles.md#the-frontier-in-twelve-results)):

- **Selection** is a theorem [L]. The margin \(2\log2\) is sharp, paid by harmonic correlation \((2\log2)c_N^2\) [L], and attained exactly by single-prime flips for every \(p\ge11\), which still fail complete positivity [S].
- **One-prime tower positivity is RH** for one fixed prime [L] and for pole-free generators of arbitrarily small support [S]. Its negative index counts distinct outer eigenvalues \(p^{\rho-1/2}\) [L].
- **Precision rigidity** [S]: \(\lambda\) and \(\lambda+\varepsilon n^{-\eta}\) are never both tower-positive, although they agree on every interval up to relative error \(o(1)\).
- **Atomic receivers** reach \((\log\log N)^{1+\varepsilon}\) overlap. At every width the sign splits into a gap on the pole complement plus one affine scalar.
- **Separated positivity [S]**: for every \(b<2-\log(2\pi)\), one smooth plateau has every complete-Weil eigenvalue at least \(b\), eventually at each fixed \(0<c<1\). A positive \(b\) gives full matrix positivity. The profile can retain arbitrarily near unit mass; the horizon depends on \(c\). Touching and overlap remain outside the theorem. [Complete matrix positivity](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/SmoothPlateausMakeTheSeparatedCompleteWeilMatrixPositive.lean).
- **All-level finite-Euler approximation [K]**: original Gamma pays every real-lag head error by \(96\Gamma(f)/(1+\log A)\), and every fixed finite Euler family by \(96C_P\Gamma(f)/(1+\log A)\). All prime powers and all retained levels remain; one cutoff works for every cell profile and horizon. [all-lag bound](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/EveryTranslationHasAnAllLevelGammaTailBound.lean), [complete finite Euler families](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/FiniteEulerFactorsHaveAllLevelGeneratorApproximation.lean).
- **All-prime higher-power payment [K]**: \(H=\sum_{p,k\ge3}2\log p/p^{k/2}<\infty\), and the sum of absolute coefficientwise head errors is at most \(96H\Gamma(f)/(1+\log A)\). One cutoff pays the complete source and every finite selection, uniformly over cell profiles and horizons. Coefficient summability begins exactly at cubes; both prime and square coefficient masses diverge. This is a method boundary, not divergence of compact-source correlations. [Joint estimate](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/AllHigherPrimePowersHaveAllLevelGeneratorApproximation.lean), [sharp threshold](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/CriticalEulerCoefficientMassStartsAtCubes.lean).
- **Actual averaging and even-power transfer [K]**: the whole-orbit cutoff is logarithmic stopping-block averaging on actual finite real BV sources. Its head $h=P_Af$ preserves the ordinary mean, and its tail $t=f-h$ is L²-orthogonal to the head. The complete even-power source head error is at most $\varepsilon(\Gamma(h)+\Gamma(t))+32C_\varepsilon\Gamma(f)/(1+\log A)$, uniformly over source families and horizons. The projected Gamma energies remain unpaid; ordinary mean preservation does not preserve the exponential Weil moments. [Physical identities](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/ActualGeneratorHeadsPreserveTheSourceMean.lean), [complete error](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/TheSquareSourceHeadErrorHasOnlyAGammaStabilityCost.lean).
- **Finite-index chain**: every prime layer except the first, including the full even-power source with its pole, has uniform finite index [L].
- **One-level Haar Gamma cross-error [S]** is at most \(16e^{1/2}\) times ordinary mass, including the whole head. Its exact boundary remainders are available for joint payment. This does not assert Gamma stability of the generator cutoff across all levels. [Signed boundary cost](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHaarGammaCrossTermsCostOnlyMass.lean).
- **Finite off-line support** \(\Rightarrow\) zeros approach the line \(\Rightarrow\) LH \(\wedge\) \(\Theta<1\) [L]. In the heat flow, uniform high-collision counts are equivalent to zeros approaching the line, so the flow's own content is the near-axis count [S].
- **Census**: \(\ge HD(1)+10^{-8}\) simple critical zeros, and \(\ge0.8876\) of zero copies simple or critical [L]. The exchange rate beyond bandwidth one is exact [L].
- **Shallow Cauchy energy** at depth \(1/\log T\) is \(O(N)\) [L], with a majorant that counts all zeros.
- **Quasi-RH**: complete translation layer; density inputs \(8/3\) and DH on \(\sigma\ge5/6\) [L]; no producer; density envelopes cannot force vanishing [L].

## 2.1 Tasks that are just work

"Just work" means the ingredients exist. A finite sign task delivers a certified enclosure, not a guaranteed sign.

| ID | Task / deliverable | Serves | Boundary |
|---|---|---|---|
| W01 | Finite atomic Grams near \(c=1\) and in overlap. Report the Markov form on \(p=0\) and the affine scalar on \(p=1\) separately, for \(\zeta\), Liouville and the flips \(\omega_{11},\omega_{13}\). | Q1; AIP, SRT, HF, ACS | Finite enclosures diagnose mixed costs; separated positivity is supplied [S], while finite checks do not decide overlap sign. |
| W02 | Instantiate the bounded complete-spectrum count and plateau floor for specified fixed \(c<1\), energy windows and conductor packets; track the explicit constants available in their estimates. | Q1; RAPT | The spectral identification and full separated matrix sign have source proofs [S]. Uniformity as \(c\uparrow1\) is not an instantiation. |
| W03 | Instantiate all-level cutoffs \(A>\exp(96C_P/\delta)\) for fixed Euler families and \(A>\exp(96H/\delta)\) for every prime with exponent≥3; evaluate detail-head sizes in the other finite-index theorems. | HF, ACS, AIP | The higher-power cutoff pays every finite selection and the full series [K]. Complete first-layer finite-index closure still has [FS] strength. |
| W04 | Separate the finite-prime coefficient ledger into \(2\log p/\sqrt p\), \(2\log p/p\) and the higher-power budget \(H\); evaluate the first two costs on specified prime sets. | HF, ACS; 2.3 | Higher powers share one finite all-prime budget [K]. Summability of the first two coefficient layers is false [K]; signed/polar compensation is a research task, not a numerical tail estimate. |
| W05 | Prove "finite off-line support \(\iff\) bounded tower index at two primes with incommensurable logarithms" from the one-prime tower law: pigeonhole on one prime's eigenvalue classes, distinctness of the second prime's phases. | 2.3; HKT, ACS | Short composition of proved theorems. |
| W06 | Tabulate \(d\mapsto W(f,T_{d\log2}g)\) for the cell-1 generator with certified \(\psi\) data, to document the almost-periodic cross-level profile. | WL, HF, CHMD, AIP | No sign. |
| W07 | Complete multiresolution Grams: \(\log2\)-orbits, details, cross-level blocks, Gamma and both poles. | HF, ACS, AIP, RW, SRT | Exact algebra. |
| W08 | Finish the Chen–Gupta–Li intake (continuation/contour step, capstone) and the Guth–Maynard \(S_2/S_3\) propositions (6.1, 11.2). Extract the zero-free threshold as a function of the density and large-value exponents and of the modulus aspect. | Q3; MC, 2.4 | Depends on the external proof being correct. |
| W09 | Best positive-definite-majorant bound for the narrow-strip pair energy \(E(\delta)\) from sub-threshold data and prime-side mean-value positivity; optimize \(\delta\); compare with the \(70\%\) target \(E(1/9)\le4\), also with the Montgomery–Taylor baseline. | Q2; census | Expected to fall short; it measures the gap. |
| W10 | Explicit constants in the shallow-energy bound \(hE_h\le C\,N\) and in the deep budget; compare with \(\kappa=3/20\). | census, WD | Displacement-blind majorant. |
| W11 | Optimize the Gabor-pinching slack. | census | Bounded gain. |
| W12 | Explicit nonreal-count bounds for \(H_t\) on compact time ranges; constants in the reality horizon; tabulate the near-axis count. | WD, LA; 2.3 | Finite \(t\)-ranges. |
| W13 | Ordered Chebyshev integrals for specified block pairs with explicit \(\psi\) data and VK bounds. | WL, HF, AIP, CHMD | Unconditional growth \(e^{h/2}\) up to a subexponential saving. |
| W14 | Instantiate the exact stopping-block averages, physical head/tail identities and even-power error on specified sources; compute Schur residuals, radicals and bounded-window transport constants. | AID, SAHT, CHMD, HF | Algebra and supplied estimates. Uniform Gamma stability is an unresolved analytic target, not a routine instantiation. |
| W15 | Ramanujan residual/Gram estimates for specified conductor sets; tower deficits at \(p\le43\). | RAPT, HF, ACS | Fixed sets only. |
| W16 | Gauge finite parts for given moduli (\(-L'/L(1,\chi)\), Chebotarev pattern means), using Hecke \(L\)-series past \(\operatorname{Re}s=1\). | RAPT, OWU, ACG | Absolute-profile errors. |
| W17 | Seed/drift/history/cross-block/endpoint ledgers for specified schedules; the RP escape constant \(\delta\) on computed ranges. | FU, RP, LI, TT, PA | Exact accounting only. |
| W18 | Finite Möbius, pronic, Vaughan and Báez–Duarte rows, readout and centered energy apart. | MC, PM, CTF, JAS | No small-damping tail bound. |
| W19 | Translate any supplied strip bound through the escaped, Hecke-defect, theta-prefix, Vaughan and quotient-head dictionaries. | MC, WL, BVI | Transport only. |
| W20 | Compact cofactor Grams, effective pole orders, record-minimum diagonals. | PM | Compact classification is not tightness. |
| W21 | Certified finite-aperture ground energies, blind minima, finite-level feasibility of Weil-positive weights, shell relaxations. | RW, EWU, OWU, ACT | Finite windows only. |
| W22 | Finite heat/Jensen/Hankel heads, both Gaussian grids, half-line Laguerre data; the remaining analytic tail of the first-atom quadrature. | LA, TH, WD, HCF, PA | No all-degree inference. |
| W23 | Newton-disc margins, Ward caps, renewal resolvents, transgression traces, finite-rank Schur charges, compact recurrence. | XN, WD, RN, TG, GTA, BAG | Local certificates. |
| W24 | Finite Robin/Nicolas extremal ranges; finite Cayley–Li ladders; Suzuki first variation on specified tent patterns. | RB, LI, SZ | Finite ranges. |
| W25 | Candidate calculations: cycle traces, curvatures, repair defects, jets, contours, likelihood contrasts, co-shift defects, photonic/Ising stacks, certificate streams, cusp actions. | 17 candidates, PW-B | Calibration is not forcing. |
| W26 | Literature intake: Bui–Heath-Brown, Ki–Kim–Lee, Kurasov–Sarnak/Olevskii–Ulanovskii, Bourgain's density hypothesis for \(\sigma\ge25/32\), Montgomery's pair-correlation bounds, Kurokawa tensor products, Fourier interpolation with zeros; standing of the Alpöge–Furman theorem. | census, 2.4, 2.7 | Acceptance of external proofs is not assumed. |

## 2.2 Open mathematical obstacles

### (a) RH-equivalent endpoints

| ID | Missing result | Routes |
|---|---|---|
| O1 | Critical signed prime/Möbius cancellation in any receiver currency: lag energy, one-sided \(\psi\) count, Abel moment, linear history floor, strict half-power, regularized convergence, extremal remainder, approximation residual, half-power budget. It is also the content of every separated and cross-level entry of the complete form. | WL, FU, RP, MC, LI, PBM, RB, JAS, CTF |
| O2 | Complete Weil positivity on a source-complete family: complete-cell index zero, residual sign, full/even/odd/allocation/Hodge/effectivity sign, atomic sign at unbounded overlap, first-variation sign on tent patterns. | RW, HF, SZ, EWU, OWU, AIP, ACS, TT, CHMD, ACT, SRT |
| O3 | Positivity on one prime's towers, for one prime, already for pole-free generators of arbitrarily small support [S]. This is the generator-orbit Toeplitz system of the complete source. | HF, ACS, AIP, CHMD, SRT |
| O4 | Simultaneous all-degree/all-height heat, moment or coefficient signs; Cayley–Li ladder sign. | PA, LA, TH, WD, HCF, LI, SEC |
| O5 | Visibility of every escape state, cofinal admission, vanishing approximation error. | PM, CTF, MC, EWJ, PCS |
| O6 | Rank-uniform transverse decay; all-point recurrence; covering Newton discs; integer trace cap; directed renewal orientation. | GTA, BAG, XN, TG, RN |
| O7 | \(\mathcal E_{\rm crit}\le Q_*\), or cofinal source work \(\le2\). | HF, SRT, ACS |

### (b) Stronger than RH

| ID | Statement | Note |
|---|---|---|
| S1 | Abel-slope genus saturation; linear Mertens energy budget | RH plus simple zeros and residue summability. |
| S2 | Matching-profile signed pair surplus at the stated strength | Not implied by RH. |

### (c) The finite-support stratum [FS]

Each item is equivalent to finitely many off-line zeros, and therefore implies the Lindelöf hypothesis and a fixed zero-free strip.

| ID | Missing result | Routes |
|---|---|---|
| F1 | Uniform finite negative index of the complete form: relative form-compactness of the first prime layer \(k=1\), with odd diagonals, heads, coarse error and poles, against Gamma. | HF, ACS, AIP |
| F2 | Finite \(\mathcal E_{\rm crit}\); bounded source work. | HF, SRT, ACS |
| F3 | Prime lag minus finitely many exponentials bounded on one side. | WL |
| F4 | Nonreal counts of \(H_t\) bounded as \(t\downarrow0\): the high count (equivalent to LH plus cosine-shift finiteness) and the near-axis count. | WD, LA |
| F5 | Uniformly bounded cosine defects. | WD, supporting |
| F6 | Bounded tower index at two primes (W05 makes this an equivalence). | ACS, HKT |

### (d) Lindelöf and quasi-RH levels

| ID | Missing result | Status |
|---|---|---|
| L0 | Zeros approach the line: equivalent to LH together with finitely many nonreal zeros of \(\cos(hD)\Xi\) for every \(h>0\) [L]. | Implies LH and \(\Theta<1\). |
| L1 | The Lindelöf hypothesis. | Open since 1908; implied by every [FS] item. |
| Q0 | A fixed zero-free strip \(\Theta<1\) [≥QRH]: a one-sided power saving in any escaped, Vaughan, theta-prefix, quotient-head or regularized-series dictionary; a pole-regularized abscissa below \(1\). | Claimed externally at \(7/8\); not formalized. |

### (e) Intermediate open problems, possibly below RH strength

| ID | Missing result | Why current work stops | Payoff |
|---|---|---|---|
| I1 | **Touching and overlap transfer.** Control the complete Weil form on a stated family through \(c=1\) and into overlap, retaining the signed pole contribution and every mixed block. | One plateau has a positive floor at every fixed \(c<1\) [S], but the horizon may depend on \(c\); there is no touching/overlap estimate or RH-complete exhaustion. | A source-faithful bridge between separated positivity and the overlapping receivers (Q1). |
| I2 | **Metzler endpoint** \(\rho=1\) and signed/block replacements of the frustrated gauge. | Gauges frustrate for \(\rho>1\). | Hodge structure through the spacing. |
| I3 | **Growing-conductor spectral control** of the prime matrix. | Only fixed packets and bounded-energy counts are proved. | Spectral producer for I1 and F1. |
| I4 | **Trans-threshold pair energy.** \(E(\delta)\le4\) at \(\delta=1/9\): the Cesàro pair-correlation energy on \((1,10/9]\) at four times its GUE value. | The prime side is a signed pair sum in the coalescent band; one-sided sieves control nothing; two-sided asymptotics meet parity (inference). Under RH the classical bound \(\int_b^{b+1}F\ll1\) gives only \(E(\delta)\ll1/\delta\). | \(70\%\) of zeros simple and critical (Q2). |
| I5 | **Displacement-sensitive constant** for the shallow Cauchy energy: \(hE_h+R_{\rm deep}\le\tfrac3{20}N\). | The proved \(O(N)\) majorant is the pair sum over all zeros of the window. | \(70\%\); \(\tfrac18N\) gives \(75\%\). |
| I6 | **Exterior tightness**; exclusion of infinite-height escape. | Record minima permit zero gauge mass. | PM progress short of O5. |
| I7 | **Conductor/forcing compatibility** for companion-cluster detectors. | No common aperture range. | OWU/SRT detection. |
| I8 | **Independent faithful constructions** for each candidate. | Calibrations, zero-indexed objects, capacity/gap obstructions. | Candidate promotion. |
| I9 | **Local-to-global by counting over \(\mathbb Z\):** an auxiliary object playing Stepanov's role without a lattice spectrum. | Sparse annihilators kill only critical lattice symbols; sieve information is parity-blind. | A non-positivity source of positivity (2.7). |
| I10 | **Threshold of the Chen–Gupta–Li detector** as a function of its inputs, and its \(\zeta\)-only (\(q=1\)) value. | The intake has no capstone; the threshold has not been extracted (W08). | An improved quasi-RH (Q3). |
| I11 | **All-level signed transfer for the first-prime and even-power sources**, with original Gamma and both exponential poles. | Actual stopping averages preserve ordinary mean and give full even-power head error≤ε(Γ(head)+Γ(tail))+32C_εΓ(f)/(1+log A) [K]. Uniform payment of the projected Gamma energies remains unproved; the first-prime and two exponential polar terms need separate comparison. | Complete-form comparison of finite-generator orbit approximations. Uniform Gamma stability is a possible intermediate target, not a proved necessary condition. Complete finite-index closure has [FS] strength; the full sign has [RH] strength. |

"No known solution" refers to the corpus and the literature consulted. The subsidiary Gamma-stability target in I11 is only an unresolved corpus estimate; no worldwide-unsolved claim is made for it. Its exact averaging structure suggests classical kernel comparison or weighted Haar upper synthesis. Neither method is a proved input. Closing that estimate would pay the even-power error, while the first-prime source, exponential moments and complete-form sign would remain.

**What the global forcing endpoints share (inference).** The RH/finite-support conclusions and independent constructions in (a), (c), (e) require at least one of:

- a parity-breaking input;
- square-root precision;
- control at unbounded aperture, or an independent construction.

Finite-field geometry supplies concrete models combining the first two: Weil, Deligne and Stepanov. The corpus has no corresponding source-complete forcing theorem for the integer Weil form.

## 2.3 Can we prove that off-line zeros, if any, are finitely many?

**Finiteness remains open. A proof would also establish the Lindelöf hypothesis and a quasi-RH.**

**The strata are exact [L].**
\[
\text{RH}\ \Rightarrow\ \text{finitely many off-line zeros}\ \Rightarrow\ \text{zeros approach the line}\ \Longleftrightarrow\ \text{LH}\wedge\big(\cos(hD)\Xi\text{ has finitely many nonreal zeros }\forall h>0\big)\ \Rightarrow\ \text{LH}\wedge\Theta<1 .
\]
Finitely many off-line zeros means only finitely many zeros at every depth \(h>0\); Backlund's criterion then gives LH, and the finitely many deep zeros bound \(\Theta\) below \(1\). [Lean](../../../formal/GaloisForLFunctions/RHTower/LindelofCosineFiniteDefectDepth.lean). LH has been open since 1908, and the best exponent \(\mu(1/2)\le13/84\) is far from \(0\). Finiteness also excludes infinitely many zeros arbitrarily close to the line, which no density method touches: a density envelope never drops below \(1\) ([density no-go](../../../formal/GaloisForLFunctions/RHTower/DensityEnvelopeNoGo.lean)).

**Exact receivers** ([route report §9](route-obstacles.md#9-finite-off-line-support-implies-the-lindelöf-hypothesis-and-a-zero-free-strip)):

- finite \(\mathcal E_{\rm crit}\), bounded source work, bounded complete-cell index;
- prime lag minus finitely many exponentials bounded on one side;
- bounded cosine defects;
- nonreal counts of \(H_t\) bounded as \(t\downarrow0\). Here the high collisions carry exactly the "zeros approach the line" content and the flow's own content is the near-axis count [S].

**Openings, ranked.**

1. **Krein–Langer finiteness (cleanest).** On a group, a positive-definite kernel plus \(\kappa\) hyperbolic character pairs has index exactly \(\kappa\) when the pairs are separated, and a positive part never pays a pair [S]. On one prime's towers the index is the number of distinct outer eigenvalues \(p^{\rho-1/2}\) [L]; two primes remove aliasing (W05). So finiteness is the statement that the Weil kernel on two prime towers is *positive-definite modulo finitely many exponential characters*. In AID terms this is the last layer of the finite-index chain: relative compactness of the first prime layer against Gamma, where absolute payment diverges like \(\sum_p\log p/\sqrt p\). A signed payment needs "prime error minus finitely many \(x^\rho/\rho\) is \(O(\sqrt x\log^2x)\)".
2. **Heat flow.** Ki–Kim–Lee finiteness holds for each \(t>0\), with an explicit reality horizon \(2\pi e^{(27/40+\varepsilon)/t}\) [S]. Uniformity as \(t\downarrow0\) splits into an LH-level high count and the near-axis count. No mechanism controls backward-heat collisions at all heights.
3. **Critical energy.** An upper bound of virial type on \(K(R)=R^2(\mathcal W(2R)-\mathcal W(R))\). The virial laws of finite configurations exist [L]; no arithmetic conservation law bounds the actual source.

**What does not work.**

- Inertia census methods give proportions; finiteness needs the off-line positive index \(O(1)\), while their Frobenius side carries \(o(N)\) errors.
- Twin-blind payments cannot reach finiteness: the Liouville twin satisfies them. Over-regular Beurling systems show that positive primes with very regular integer counts can carry off-line zeros; only the functional equation excludes them ([count fluctuation](../../../formal/GaloisForLFunctions/RHTower/RiemannFunctionalEquationForcesCountFluctuation.lean)).

**Recommendation.** Do not treat finiteness as a near-term target. Use the LH implication as a diagnostic: any argument that would give uniform finite index without an LH-strength input is wrong. The useful near-term work is W04 and W05: measure where the first-layer payment fails, and record the two-prime equivalence.

## 2.4 Can we prove a quasi-RH better than \(1/8<\operatorname{Re}\rho<7/8\)?

**Verdict: not with the corpus's own mechanisms. The only lever is the external Chen–Gupta–Li detector, whose threshold has not yet been extracted from its formalization.**

**What the corpus offers is translation, not production.**

- \(\Theta=\tfrac12+\inf\{c\}\) over one-sided exponents \(c\) for the Möbius-divisor square-root Abel moment, its quotient head at any power cutoff, and finite-contact Suzuki residuals.
- \(\Theta\le1-\theta\) is equivalent to escaped-endpoint rates, the all-test Hecke-defect cap and integer-theta growth; \(\Theta<1\) is equivalent to a uniform Vaughan power saving.
- A strip \(\operatorname{Re}\rho<3/4\) is therefore equivalent to a one-sided \(M^{1/4+\varepsilon}\) bound in any of these currencies.

[Abscissa laws](../../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean), [balanced statistic](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheBalancedStatisticIsTheQuasiRiemannHypothesis.lean).

**What the corpus proves about the barrier.**

- Density estimates count but never exclude: every envelope \(CT^{\theta(1-\sigma)}(\log T)^A\) stays \(\ge1\) [L]. A quasi-RH needs a *vanishing* mechanism, not a better exponent alone.
- Below the diagonal, Möbius power savings hold at every modulus. On the diagonal the first rung is already quasi-RH. Vinogradov–Korobov gives no fixed power.
- The quotient-head law gives no bootstrap: the head of length \(M^\theta\) is itself \(O(M^{\Theta-1/2+\varepsilon})\).
- Zeros approaching the line imply quasi-RH, but that hypothesis is LH-strength (2.3).

**The external lever.** The Chen–Gupta–Li manuscript claims zero-freeness for \(\operatorname{Re}s>7/8\) from a zero detector combined with an all-moduli density estimate \((qT)^{7(1-\sigma)/3}\). The intake formalizes the detector, Lemmas 4.5 and 6.2, Propositions 4.6 and 5.1, and the exponent consolidation. It has no capstone and lacks the continuation/contour step. Inputs available for \(\zeta\) alone:

- the density hypothesis on \(\sigma\ge5/6\) [L] (Bourgain: \(\sigma\ge25/32\));
- the \(8/3\) box count [L];
- the Guth–Maynard large-values theorem, reduced to its \(S_2/S_3\) propositions.

Two structural facts decide whether these help:

1. whether the detector needs the modulus aspect \(q\) (twisting by characters) or only the height aspect;
2. whether the threshold is monotone in the density exponent near \(\sigma^*\).

If the height aspect suffices and the dependence is monotone, \(\zeta\)-specific exponents move \(7/8\). Otherwise they do not. Exponent optimization cannot reach \(\Theta=\tfrac12\): the Proposition 4.6 envelope has floor \(288\) against the collision quantum \(2\).

**Recommendation.** Make the extraction a research question (Q3), not only intake: the answer is either an improved strip or a precise statement of why the detector is tied to \(7/8\).

## 2.5 Can we prove that at least 70% of zeros lie on the critical line?

**Neither identified input for \(70\%\) is available in the corpus or literature consulted; both meet the parity barrier.**

**Where the census is [L].**

- At least \(HD(1)+10^{-8}\approx0.67250071\) of zeros are simple and critical; off-line copies are at most \(1-HD(1)\approx32.75\%\).
- At least \(0.8876\) of zero copies are simple *or* critical. The census extremal consists of simple zeros, so simplicity theorems cannot move the critical count.

**Route 1: bandwidth beyond one.** The rank–trace certificate proves the proportion \(2-\phi(\lambda)\), with \(\phi(\lambda)=2/\lambda-2/(3\lambda^2)+(2/\lambda^2)\int_1^\lambda(\lambda-\alpha)F(\alpha)\,d\alpha\). Just above \(\lambda=1\) the diagonal gain is first order in \(\delta=\lambda-1\) and the pair penalty second order [L]:
\[
\text{proportion}-\tfrac23=\frac{\delta\,(2-(3E(\delta)-4)\delta)}{3(1+\delta)^2},\qquad E(\delta)=\frac2{\delta^2}\int_1^{1+\delta}(1+\delta-\alpha)F(\alpha)\,d\alpha .
\]
A bound \(E\le B\) yields \(1/(3(3B-2))\) at \(\delta=1/(3(B-1))\). **So \(70\%\) follows from \(E(1/9)\le4\)**: the Cesàro pair-correlation energy on \((1,10/9]\) at most four times its GUE value \(1\). Three quarters follows from twice the GUE value on \((1,4/3]\) (`FrobeniusFourThirds`), and then also with simple zeros [L].

Why it is open:

- Unconditionally nothing is known about \(F\) beyond \(\alpha=1\).
- Under RH, Montgomery's \(\int_b^{b+1}F\ll1\) gives only \(E(\delta)\ll1/\delta\).
- On the prime side, the trans-threshold term is a signed sum over prime pairs \(|p-q|\lesssim p/T\). Its Poisson main term integrates to zero against the dyadic kernel only with the exact Hardy–Littlewood main term [L]. So a one-sided Selberg sieve controls nothing, and a two-sided estimate is a parity problem (inference).
- The positive-definite Fejér majorant from sub-threshold data alone misses the \(3/4\) target by the factor \(8/3\) [L]; its narrow-strip analogue is W09.

[Narrow strip](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/NarrowStripClosePairEnergyAndExchangeRate.lean), [three quarters](../../../formal/GaloisForLFunctions/RHTower/ZetaThreeQuartersReduction.lean), [coalescent anatomy](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/CoalescentSieveAnatomyAndModelCalibration.lean).

**Route 2: displacement-sensitive depth.** Write the depth of an off-line pair as \(\lambda/\log T\).

- Pair correlation sees a pair at \(\lambda\asymp1\) as a double point.
- Value moments see it as two critical zeros ([mimicry](../../../formal/GaloisForLFunctions/RHTower/ValueMomentsCannotSeparateReflectedPairs.lean)).
- Selberg density controls only \(\lambda\gtrsim19\).

The shallow Cauchy energy \(E_h\) charges every off-line copy within depth \(h\), and
\[
hE_h+R_{\rm deep}\le\kappa N\ \Longrightarrow\ N_0\ge(1-2\kappa)N .
\]
\(70\%\) is \(\kappa=3/20\). The corpus proves \(hE_h=O(N)\) at \(h=1/\log T\) [L], but through a Lorentzian pair sum over all zeros of the window, so the constant cannot distinguish critical from off-line zeros. The missing input is a displacement-sensitive estimate with a sufficiently small constant. [Shallow energy](../../../formal/GaloisForLFunctions/ShallowCauchyPrimeEnergy/ShallowCauchyEnergyBound.lean).

**Closed alternatives.**

- Mollified moments (CGG/BHB made unconditional) are falsified as a census tool [L].
- Higher trace moments exist only for \(k\lambda\le1\).
- The \(0.679\) SDP bound under RH uses a negative tail with no off-RH analogue.

**Conclusion.** The cheapest identified input for \(70\%\) is a two-sided prime-pair estimate in the coalescent band at bandwidth \(10/9\), with constant four times the conjectured one. That is a parity-type statement. The census is the counting face of the selectivity wall (Q2).

## 2.6 The three questions to answer next

Fixed finite Euler approximation and all-prime higher-power payment supply quantitative transfer for actual cell sources. They leave the sign and arithmetic-estimate questions below open; general BV sources retain their noncell component. The prime and square layers require signed transfer, while all retained generator families still contain infinitely many level directions.

<a id="q1"></a>
### Q1. What complete-form estimate carries separated positivity through touching and into overlap?

**Exact object.** Atomic families \(f_x=\sum_{n\le N}x_ng(\cdot-\log n)\), with widths \(c/N\), retaining the prime kernel, Gamma, both poles and all cross terms. For every \(0<b<2-\log(2\pi)\), a single smooth plateau already satisfies
\[
\forall c\in(0,1),\quad \exists N_0(c)\quad \forall N\ge N_0(c),\quad
W_{c,N}(x)\ge b\|x\|^2\quad\text{for every }x
\]
[S]. Its square mass can be chosen arbitrarily close to one. This is a full matrix theorem, not only a trial-mode bound. [Plateau theorem](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/SmoothPlateausMakeTheSeparatedCompleteWeilMatrixPositive.lean).

**Missing estimate.** Control the dependence on the separation gap, and the mixed terms at touching and overlap, in a norm that preserves the complete form. A fixed \(c>1\) theorem would be an intermediate result. An RH-complete family still requires a proved exhaustion, such as the existing receivers at \((\log\log N)^\alpha/N\), \(\alpha>1\); a slowly chosen schedule \(c_N\uparrow1\) alone does not supply it.

**First useful answer.** One of:

- a quantitative mixed-block estimate that absorbs the cost of touching or a stated amount of overlap into the positive plateau floor;
- a full-form comparison from those overlapping atoms to an index-carrying complete-source family, with all growth parameters explicit;
- a rigorous obstruction and strongest positive replacement identifying which term exhausts the floor.

**Payoff.** A bridge from a proved positive full matrix to a source family capable of seeing additional index. The maximal margin is also shared by some prime-flip twins, so every eventual RH claim still needs the full selectivity battery. Neither finite generator count nor separated positivity provides that conclusion.

<a id="q2"></a>
### Q2. Is the Cesàro pair energy on \((1,10/9]\) at most four times its GUE value?

**Exact object.** \(E(1/9)=162\int_1^{10/9}(10/9-\alpha)F(\alpha)\,d\alpha\). On the prime side this is the coalescent-band surplus of prime pairs \(p,q\le X=T^{10/9}\) with \(|\log p-\log q|\lesssim1/T\), equivalently a short-interval variance of primes at length \(X^{1/10}\).

**Why now.** The exchange rate is exact [L]. This is the smallest quantified input in the corpus that gives a census beyond the literature (\(70\%\)) and beyond the imported \(2/3\). It isolates the parity question in its cleanest counting form: a two-sided pair estimate on average over shifts, at constant \(4\), not \(1+o(1)\).

**First useful answer.** One of:

- W09: the best positivity/majorant bound and its distance from \(4\);
- an exact reduction showing that \(E(1/9)\le4\) is equivalent to a stated Type-I/Type-II bilinear estimate;
- a proof that every parity-blind input leaves \(E\) unbounded.

**Payoff.** A new unconditional census theorem, or a sharp location of the parity barrier inside the census.

<a id="q3"></a>
### Q3. What zero-free threshold does the Chen–Gupta–Li detector produce from its inputs, and does \(\zeta\) alone do better than \(7/8\)?

**Exact object.** The map (density exponent, large-value exponent, modulus aspect) \(\mapsto\) zero-free abscissa defined by the formalized detector (W08), evaluated at \(q=1\) with the density hypothesis on \(\sigma\ge5/6\) and the Guth–Maynard exponents.

**Why now.** It is the only vanishing mechanism in reach. Density alone provably cannot exclude a zero, and the corpus's own strip dictionaries only translate. Most of the machinery is already formalized (279 + 72 modules).

**First useful answer.** The threshold formula. Payoff: either a quasi-RH with a better constant than \(7/8\), conditional only on the external argument's correctness, or a precise reason why \(7/8\) is the detector's limit.

**Why these three.**

- Q1 tests whether a positive complete form survives the transfer from strict separation to overlap and source exhaustion.
- Q2 tests the same parity question in the counting world, where the payoff is a concrete census.
- Q3 is the only lever on a fixed strip.
- None depends on the others.

The first-layer compactness question is not on the list: it is equivalent to finite off-line support and so implies LH (2.3). The shallow-energy question is answered at order \(O(N)\); what remains of it is I5, a displacement-sensitive constant.

## 2.7 Is there a wildly different route?

**No route was found that avoids the three walls, and there is a structural reason (inference).** Every RH argument does one of two things:

- it bounds an actual signed quantity (Wall 1);
- it builds an object, independent of the zeros, whose structure forces reality (Wall 14).

Either way it must hold at every scale (Wall 3). A route outside all three would have to obtain RH from a finite, structural identity with no infinite exhaustion. The only known identities of that kind are spectral (Hilbert–Pólya, Wall 14) or geometric over \(\mathbb F_q\).

Three mechanisms far from every corpus route and candidate were examined. Searches found none of them in the corpus. Each re-enters the walls at a different point.

**A. Deligne tensor amplification (Kurokawa absolute tensor products).**

- *Idea.* Over \(\mathbb F_q\), the zeta function of \(X\times Y\) has zeros at sums of zeros. Deligne's argument bounds the zeros of all tensor powers by a trivial abscissa, and the bound becomes sharp in the limit, with no positivity estimate. Kurokawa's absolute tensor products \(\zeta\otimes\cdots\otimes\zeta\) have zeros at \(\rho_1+\cdots+\rho_k\). If they had Dirichlet series with abscissa \(k/2+C\), \(C\) independent of \(k\), an off-line zero \(\rho\) would put a zero at \(k\rho\), with real part \(k/2+k\delta\), and RH would follow.
- *Where it re-enters (inference).* Made concrete, the tensor square of the prime error is the pointwise square \((\psi(x)-x)^2\). Its Mellin transform has singularities at \(\rho+\rho'\), and Landau's theorem on the nonnegative integrand gives abscissa \(2\Theta\): this is WL's mean-square receiver. Deligne's extra ingredient is the trivial abscissa supplied by local purity on a base whose cohomology is known (\(\mathbb P^1\)). For \(\operatorname{Spec}\mathbb Z\) that is exactly the missing local-to-global step (Wall 14.37).

**B. Fourier interpolation and modular certificates (Radchenko–Viazovska; Bondarenko–Radchenko–Seip).**

- *Idea.* The explicit formula is a Fourier pair between the zeros and \(\{\log n\}\). Fourier interpolation bases built from modular integrals exist for such pairs. Viazovska-type proofs obtain sharp sign conditions from modularity rather than from estimates.
- *Where it re-enters.* RH is a semidefinite statement (positivity on a cone of autocorrelations), not a single-function linear-programming bound. Its dual certificate is the weight \(\Lambda\) itself ([finite-level existence](../../../formal/GaloisForLFunctions/RHTower/WeilPositivityFiniteLevelExistenceDecidesRH.lean)), whose verification is RH. A modular certificate would have to be an explicit sum-of-squares factorization of the Weil distribution: a Hilbert–Pólya object (Wall 14).

**C. Interlacing families and stability preservers (Marcus–Spielman–Srivastava; Borcea–Brändén).**

- *Idea.* Real-rootedness of an *expected* characteristic polynomial follows from real stability, without knowing any realization.
- *Where it re-enters.* One needs \(\Xi\), or all its Jensen polynomials, as expected polynomials of an arithmetic random family. That is a faithful construction (Wall 14), and it needs uniform convergence of the family (Wall 3). The Pólya–Schur symbol of the obvious operator is \(\Xi\) itself.

**The most different mechanism the corpus does own** is counting before positivity (Stepanov). Over \(\mathbb F_q\) it proves RH for hyperelliptic curves with no positivity input, and trickle-down on every Frobenius ladder is equivalent to a one-sided square-root count [L]. Its \(\mathbb Z\) analogue is the WL count \(\psi(x)-x\le C\sqrt x\log^2x\). The engine, a sparse annihilator, needs a lattice spectrum, and over \(\mathbb Z\) only critical lattice zeros are annihilated [L]. That is I9.

The classical "wildly different" ideas (tensor amplification, modular certificates, expected-polynomial real-rootedness) each reduce to a corpus wall at an identifiable point. The two points they reach most often are the local-to-global step and a faithful construction.

## 2.8 Would the obstacles in 2.2 need a new field of mathematics?

**A new field is a possible research programme, not a mathematical necessity established by these results.** Hilbert-space projections, dyadic variance identities, Gamma translation invariance and coefficient summability prove all-level approximation for every fixed finite Euler family and jointly for every prime with exponent≥3 [K]. Exact stopping-block averaging also supplies finite BV source realization, ordinary mean preservation and the complete even-power error with its projected-Gamma cost explicit [K]. Existing spectral methods supply full separated plateau positivity [S]. Uniform Gamma stability has concrete classical analytic candidates; its absence is not evidence that a new field is necessary. The deeper unresolved tasks concern first-prime payment, the complete form, overlap and the selective sign. Six constraints locate that gap:

1. The selective input must be parity-breaking (selection theorem) and square-root-precise (precision rigidity), and act at unbounded aperture.
2. The proved selective margin is shared by some single-prime flips. Its size alone cannot supply the full arithmetic sign. Fixed separated full-matrix plateau positivity [S] supplies a concrete positive section; extending it to overlap still needs a complete-form estimate.
3. The finite-field constructions supply concrete models for arithmetic forcing through counts, geometry and lattice-spectrum annihilation. Their transfer to the actual integer source remains unproved.
4. Complete Weil couplings on a prime tower carry the zero characters. All-prime higher-power coefficients are summable, while prime and square coefficient masses diverge [K]. Neither fact establishes summability or positivity of complete-form lag sequences; signed source-dependent compensation remains possible.
5. The proved index-limit theorem uses pointwise kernel convergence [S]. L², fixed-Euler and higher-power approximation alone do not control the complete Weil form or both poles. The actual averaging operator preserves ordinary mean and head–tail L² orthogonality, and the complete even-power error has only its stated projected-Gamma and tail-mass costs [K]. One-level Gamma bounds do not automatically pay that projected cost uniformly; neither averaging identity preserves the two exponential Weil moments.
6. Finite off-line support implies LH. A finite-index conclusion therefore requires arithmetic input beyond the proved approximation estimates.

The corpus supplies no theorem turning the available local signs into the required global sign over \(\mathbb Z\). A dedicated theory should organize that missing transfer while using the established finite-factor and all-prime higher-power approximation laws. The need for a new field, rather than a new theorem within existing mathematics, remains speculative.

### What the field would be about

**Arithmetic Krein–Langer theory: local-to-global indefinite harmonic analysis on the idele class group.** Its subject is the Weil distribution as an indefinite kernel on \(\mathbb A^\times/\mathbb Q^\times\): a positive part built from local data, plus hyperbolic characters \(|\chi|\ne1\) that are exactly the off-line zeros. Its aim is an *arithmetic Krein–Langer theorem* proving that the hyperbolic part is empty from local data and global structure. Over \(\mathbb F_q\) that theorem exists: Castelnuovo–Severi gives index zero. Over \(\mathbb Z\) the field would construct its analogue and explain why the result is selective and precise. Its home in the corpus is the HKT programme, whose [README](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/README.md) states the full scope, pillar theorems and acceptance tests.

### What it would be like

It would look like Weil's proof transported to a setting with an archimedean place:

- an index theory first (how many hyperbolic pairs can a kernel with given local factors carry);
- then counting (Riemann–Roch-type square-root counts that bound the index);
- then positivity as a consequence.

Analytic estimates would verify local inputs and quantitative transfer; the global sign would require an arithmetic mechanism with all source terms retained.

### Objects

- The Weil kernel \(W=\Gamma+\text{poles}-P\) on \(\mathbb Q_{>0}^\times\) and on prime towers; its twins \(W_\lambda\); the selection theorem as a boundary condition.
- Hyperbolic character pairs \(h_{\chi,\omega}=\omega\chi+\bar\omega\chi^\dagger\) and Pontryagin/Krein spaces of finite index.
- The multiplicative walk with Dirichlet energy \(D_N\) and Poincaré constant \(2\log2\); the harmonic hyperplane; arithmetic modes \(\gamma+\log m+d(m)\).
- Hecke towers and their Toeplitz symbols on the circle; the Cayley–Li ladder.
- Square-root counts: one-sided point/prime counts; Sylvester inertia of explicit-formula Grams; auxiliary objects vanishing to high order at primes.
- Local factors as positive-definite kernels on \(\mathbb Q_v^\times\), and the archimedean factor.
- The whole-line projection \(Q_A=U(1-P_A)U^*\), its exact logarithmic stopping partition, actual finite BV averages and zero-mean orthogonal tails; original-source Gamma, projected Gamma costs, complete generator orbits, finite Euler masses \(C_P\), higher-power mass \(H\), and centered even-power sources. The ordinary-mean and square-mass identities give exact correction cancellation. The remaining source transfer has separately identified first-prime, Gamma-stability and exponential-pole costs.

### Language

- A **selective** inequality fails for a bounded twin. A **parity-breaking** input distinguishes \(\lambda\)-twisted from untwisted data. A **precision-faithful** input distinguishes \(\Lambda\) from \(\Lambda+\varepsilon n^{-\eta}\) for every \(\eta<\tfrac12\).
- An **index-carrying topology** is one in which bounded negative index passes to limits.
- A **count** is a one-sided bound at square-root precision. **Local-to-global** is a map from local positive kernels and counts to a global index.
- An **exhaustion statement** names source, form, domain, growth parameter and error currency together.

### Tools it must develop, with tests

| Tool | Purpose | Test |
|---|---|---|
| Signed transfer through touching and overlap | Preserve the proved positive complete-matrix floor while paying every mixed block and pole | Q1; state the growing width and horizon together; test Liouville and prime-flip twins |
| Arithmetic Krein–Langer theorem | Index of the Weil kernel from local data | Reproduce index zero over \(\mathbb F_q\); fail for Davenport–Heilbronn and over-regular Beurling systems; imply LH whenever it gives finite index |
| Stepanov over \(\mathbb Z\) | An auxiliary construction for one-sided prime counts at square-root precision without a lattice spectrum | Reproduce hyperelliptic RH; be parity-breaking |
| Two-sided coalescent pair theory | Prime-pair asymptotics beyond bandwidth one, on average, at bounded constant | Q2; reproduce \(E\approx1\) on Hardy–Littlewood models; fail for parity-twisted models |
| Index-carrying completion | A completion of test spaces on which the Weil kernel is continuous for index | Agree with pointwise kernel limits [S]; reproduce the tower law |
| Signed prime/even-power Gamma allocation | Pay the explicit projected-Gamma cost in the complete even-power head error, then the first-prime source and both exponential poles | Recover the exact stopping averages and higher-power budget; establish source/horizon-uniform payment while preserving every level. A Gamma averaging theorem alone is not a complete-Weil sign theorem |
| Structural precision | Use the Euler product and functional equation as identities, so that \(n^{-\eta}\) perturbations fail | Precision battery |

### Questions it must answer

- What is the positive form of the parity barrier, and is the \(2\log2\) margin its first quantitative trace?
- Why does finite off-line support imply LH, and is there a direct local-to-global argument for that implication?
- What replaces Frobenius's lattice spectrum in a \(\mathbb Z\)-Stepanov argument?
- In which completion of the test space does the Weil kernel carry its index to the limit?
- Which estimate pays the projected Gamma cost of the actual stopping averages, and which further arithmetic mechanism controls the first-prime source and exponential moments on the complete retained orbits?
- Why is the prime \(2\) both the multiresolution generator and the bottleneck of the margin?
- What arithmetic quantity governs the near-axis collisions of the heat flow?

### Criteria it must meet

1. **Independence.** Built from arithmetic data, never from zero-indexed objects.
2. **Fidelity.** All mixed entries, Gamma, both poles and multiplicities; prime-only, collided and complete forms kept apart.
3. **Selectivity battery.** Every sufficient hypothesis fails for:
   - the Liouville twin;
   - scalings \(c\Lambda\) and quadratic mixtures;
   - single-prime flips with the maximal margin;
   - \(\Lambda+\varepsilon n^{-\eta}\);
   - the golden curve;
   - over-regular Beurling systems;
   - Davenport–Heilbronn functions.
4. **Parity and precision.** It contains an input that \(\lambda\)-twisting changes and that \(n^{-\eta}\) perturbations change.
5. **Exhaustion.** Uniformity exactly in the growing parameters, in an index-carrying topology.
6. **Calibration.** Reproduce Weil over \(\mathbb F_q\) by counting, the \(2/3\) census, the \(K_\star\) regime and the sharp gap, without demanding the false all-overlap Metzler gauge or pure-Markov sign. Imply LH whenever it claims finiteness.
7. **A new inequality.** A paid sign, index ceiling, count or energy bound, not another equivalence.
8. **Formal closure.** Unconditional Lean statements with every input discharged.

**First evidence of success** would be one of:

- a touching/overlap transfer in Q1 with an explicit full-form error budget and a measured selectivity boundary;
- a bound \(E(1/9)\le4\) (Q2) from an input that also fails for the parity-twisted model;
- an index ceiling for the Weil kernel on two prime towers obtained from local data.
