# Research frontier: work, open problems and next questions

Status: 28 October 2026, corpus commit `389e3f1d10`. **RH remains open.** The corpus now proves that the missing input must be selective, and it measures the one selective input it has: a spectral gap of exactly \(2\log2\) on the pole hyperplane, against \(0\) for the Liouville twin. What is missing is a mechanism that carries that discrete, narrow-width margin to overlapping tests and across scales.

This summary covers all 31 live routes, the 17 standalone candidates and PW-B. Companions: [route-by-route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md). Evidence comes from corpus searches and Lean statements; no builds were run. **[S]** = working source as in the frontier map; **(inference)** = conclusion of this review, not a Lean theorem. Research record: [working log](../../../logs/review-2810-v2-research-2026-10-28.md).

## What the corpus establishes

There are three destinations:

1. **Critical signed arithmetic control:** prime/Möbius histories, approximation energies, regularized series, source work.
2. **Complete Weil positivity:** full, even, odd, incidence, Hodge, effectivity, atomic and moment formulations.
3. **Independent forcing:** a geometric, spectral, dynamical or counting structure whose proved property supplies 1 or 2.

Eight results define the present frontier:

- **Selection is a theorem.** Atomic positivity of a bounded weight \(|\lambda|\le\Lambda\) at any root holds iff RH holds and \(\lambda=\Lambda\). Twin-blind positivity cannot reach an RH-complete family.
- **The selective margin is exactly \(2\log2\)** for \(\zeta\) and exactly \(0\) for Liouville. It is decided by the harmonic correlation \(S_N/H_N\) and survives finite coefficient flips.
- **Atomic receivers reach \((\log\log N)^{1+\varepsilon}\) overlap.** At every width the atomic sign splits into a gap on the pole complement and one affine scalar.
- **Narrow positivity reaches a quarter of the Robin–Euler threshold** [S], for arbitrary per-atom shapes. Arithmetic modes have spacing-scale energies \(\log(K_m/K)\) [S].
- **The complete source has uniform finite index for every prime layer except the first** [S]. The first layer \(k=1\) over all primes is where absolute payment diverges.
- **Cross-level couplings:** pole, Gamma and touching parts are paid. The prime part is a Chebyshev sequence, almost periodic under RH and never summable (inference).
- **Finite off-line support** has exact receivers (critical energy, subtracted lag, cosine defects, heat-flow nonreal counts) and forces \(\Theta<1\).
- **Critical-line census:** at least \(HD(1)+10^{-8}\approx0.67250071\) of zeros are simple and critical, unconditionally. This rests on the imported Alpöge–Furman inertia theorem.

Sources are in the [route report](route-obstacles.md#the-frontier-in-ten-results).

## 2.1 Tasks that are just work

"Just work" means the ingredients exist. A finite sign task delivers a certified enclosure, not a guaranteed sign.

| ID | Task / deliverable | Serves | Boundary |
|---|---|---|---|
| W01 | Finite atomic Grams at fixed overlap ratios \(K\) from \(K_\star\) to past the Robin–Euler ratio \(K_1\) and the first-excitation ratio \(4K_1\), with the Markov form on \(p=0\) and the affine scalar on \(p=1\) reported separately. | AIP, SRT, HF, ACS (Q1) | Finite \(N\) does not decide the eventual sign; it locates the failure point. |
| W02 | Tabulate \(K_m=m\,e^{d(m)}e^{\beta(\varphi)/\|\varphi\|^2}/(2\pi)\) and \(K_\star\) for standard profiles (plateau, Gevrey, Denjoy–Carleman). | SRT, AIP, RAPT | The mode law is proved only for \(K<1/4\). |
| W03 | Explicit detail-head sizes \(A\) in the uniform finite-index theorems (\(k\ge3\), prime two, finite \(P\)); restore the pole in the square-layer Gamma gap \(\ge\gamma_E\). | HF, ACS, AIP (Q2) | Bookkeeping; the \(k=1\) layer stays open. |
| W04 | Compute the first-layer mixed constants \(C_P\) along growing \(P\) against the detail reserve \(\log(a)\,h_a\); locate exactly where the absolute bound fails. | HF, ACS (Q2) | A computation of the obstruction, not its removal. |
| W05 | Tabulate \(d\mapsto W(f,T_{d\log2}g)\) for the cell-1 generator and low details with certified \(\psi\) data, to document the almost-periodic cross-level profile. | WL, HF, CHMD, AIP | Confirms the non-summability inference numerically; no sign. |
| W06 | Complete multiresolution Grams: \(\log2\)-orbits, details, cross-level blocks, Gamma and both poles. | HF, ACS, AIP, RW, SRT | Exact algebra. |
| W07 | Finish the Chen–Gupta–Li intake: the continuation/contour step and a capstone; then extract the threshold \(7/8\) as an explicit function of the large-value and density exponents. | MC, BVI, quasi-RH (2.4) | Outcome depends on the external proof being correct. |
| W08 | Optimize the Gabor-pinching slack: a minimal off-diagonal Frobenius energy for point sets of the required density under the Montgomery–Taylor kernel (LP/energy bound). | IGP, census (2.5) | Bounded gain; cannot reach \(70\%\) (see 2.5). |
| W09 | Hermitianized mollified moments: write the reflected pairing \(a(\rho)\overline{a(1-\bar\rho)}\) for \(a=\zeta'M\) and compute its prime-side main terms where Gonek–Landau-type formulas already apply. | census (Q3) | The asymptotics at mollifier length \(\theta\ge1/2\) are the research part. |
| W10 | Explicit nonreal-count bounds for \(H_t\) on compact time ranges; constants in the reality horizon \(2\pi e^{(27/40+\varepsilon)/t}\). | WD, LA, 2.3 | Finite \(t\)-ranges only. |
| W11 | Ordered Chebyshev integrals for specified block pairs with explicit \(\psi\) data and VK bounds. | WL, HF, AIP, CHMD | Unconditional growth \(e^{h/2}\) up to a subexponential saving. |
| W12 | Projections, Schur residuals, radicals, bounded-window transport constants. | AID, SAHT, CHMD, HF | Window-dependent constants. |
| W13 | Ramanujan residual/Gram estimates for specified conductor sets; tower deficits at \(p\le43\). | RAPT, HF, ACS | Fixed sets only. |
| W14 | Gauge finite parts for given moduli: \(-L'/L(1,\chi)\), Chebotarev pattern means. | RAPT, OWU, ACG | Absolute-profile errors. |
| W15 | Seed/drift/history/cross-block/endpoint ledgers for specified schedules. | FU, RP, LI, TT, PA | Exact accounting only. |
| W16 | Finite Möbius, pronic, Vaughan and Báez–Duarte rows, readout and centered energy apart. | MC, PM, CTF, JAS | No small-damping tail bound. |
| W17 | Translate any supplied strip bound through the escaped, Hecke-defect, theta-prefix, Vaughan and quotient-head dictionaries. | MC, WL, BVI | Transport of a supplied bound. |
| W18 | Compact cofactor Grams, effective pole orders, record-minimum diagonals. | PM | Compact classification is not tightness. |
| W19 | Certified finite-aperture ground energies, blind minima and shell relaxations. | RW, EWU, OWU, ACT | Finite windows only. |
| W20 | Finite heat/Jensen/Hankel heads, both Gaussian grids, half-line Laguerre data; the remaining analytic tail of the first-atom quadrature. | LA, TH, WD, HCF, PA | No all-degree inference. |
| W21 | Newton-disc margins, Ward caps, renewal resolvents, transgression traces, finite-rank Schur charges, compact recurrence. | XN, WD, RN, TG, GTA, BAG | Local certificates. |
| W22 | Finite Robin/Nicolas extremal ranges; finite Cayley–Li ladders. | RB, LI | No saturated-extremizer or all-depth conclusion. |
| W23 | Suzuki first variation on specified factorial/grid tent patterns. | SZ | Finite patterns only. |
| W24 | Candidate calculations: cycle traces, curvatures, repair defects, jets, contours, likelihood contrasts, co-shift defects, photonic/Ising stacks, certificate streams, cusp actions. | 17 candidates, PW-B | Calibration is not forcing. |
| W25 | Literature intake: Bui–Heath-Brown, Ki–Kim–Lee, Kurasov–Sarnak/Olevskii–Ulanovskii; standing of the Alpöge–Furman theorem. | census, WD, 2.7 | Acceptance of external proofs is not assumed. |

## 2.2 Open mathematical obstacles

### (a) RH-equivalent endpoints — nobody has a solution

| ID | Missing result | Routes |
|---|---|---|
| O1 | Critical signed prime/Möbius cancellation in any receiver currency: lag energy, one-sided \(\psi\) count, Abel moment, history floor, strict half-power, regularized convergence, extremal remainder, approximation residual, half-power budget. It is also the content of every separated and cross-level entry of the complete form. | WL, FU, RP, MC, LI, PBM, RB, JAS, CTF |
| O2 | Complete Weil positivity on a source-complete family: complete-cell index zero, residual sign, full/even/odd/allocation/Hodge/effectivity sign, atomic sign at unbounded overlap, Suzuki first-variation sign on tent patterns. | RW, HF, SZ, EWU, OWU, AIP, ACS, TT, CHMD, ACT, SRT |
| O3 | Positivity of the generator-orbit Toeplitz system: the zero measure pushed to the circle by \(\gamma\mapsto\gamma\log2\) (inference: equivalent in kind to a one-prime RH criterion). | HF, ACS, AIP, CHMD |
| O4 | Simultaneous all-degree/all-height heat, moment or coefficient signs; Cayley–Li ladder sign. | PA, LA, TH, WD, HCF, LI, SEC |
| O5 | Visibility of every escape state, cofinal admission, vanishing approximation error. | PM, CTF, MC, EWJ, PCS |
| O6 | Rank-uniform transverse decay; all-point recurrence; covering Newton discs; integer trace cap; directed renewal orientation. | GTA, BAG, XN, TG, RN |
| O7 | \(\mathcal E_{\rm crit}\le Q_*\), or cofinal source work \(\le2\). | HF, SRT, ACS |

### (b) Stronger than RH

| ID | Statement | Note |
|---|---|---|
| S1 | Abel-slope genus saturation; linear Mertens energy budget | RH plus simple zeros and residue summability. |
| S2 | Matching-profile signed pair surplus at the stated strength | Not implied by RH. |

### (c) At least as hard as a fixed zero-free strip [≥QRH]

Each implies finite off-line support or \(\Theta<1\) directly. None is known; the external \(7/8\) claim would settle only the weakest (Q0).

| ID | Missing result | Routes |
|---|---|---|
| Q0 | A fixed zero-free strip \(\Theta<1\): one-sided power saving in any escaped, Vaughan, theta-prefix, quotient-head or regularized-series dictionary. | MC, BVI, PBM |
| Q1′ | Uniform finite negative index of the complete form: relative form-compactness of the first prime layer \(k=1\) (plus the square-layer pole and the coarse source) against Gamma. | HF, ACS, AIP |
| Q2′ | Finite \(\mathcal E_{\rm crit}\); bounded source work; a one-sided bound on the prime lag after subtracting finitely many exponentials. | HF, SRT, WL |
| Q3′ | A uniform-in-\(t\) reality horizon for \(H_t\) up to a bounded nonreal count. | WD, LA |

### (d) Intermediate open problems — possibly solvable without RH-strength input

| ID | Missing result | Why current work stops | Payoff |
|---|---|---|---|
| I1 | **Selective overlap step.** \(W\ge0\) on atomic families at a fixed overlap ratio beyond the Robin–Euler point: \(M\ge0\) on \(p=0\) through the \(2\log2\) gap, and the affine scalar on \(p=1\). | Narrow positivity keeps absolute values on the pole term and stops below about half the threshold. The mode law is proved only for \(K<1/4\). | First positivity that uses a selective input where the Markov form is negative. A test of whether selectivity can become positivity at all. |
| I2 | **Metzler endpoint \(\rho=1\)** and signed/block replacements of the frustrated gauge. | Gauges frustrate for \(\rho>1\). | Hodge structure through the spacing. |
| I3 | **Growing-conductor spectral control** of the prime matrix: bulk law, complement, Gamma/pole coupling of the full spectrum. | Only fixed packets and bounded-energy counts are proved. | Spectral producer for I1 and Q1′. |
| I4 | **Beyond-\(2/3\) census by Hermitianized mollified moments.** | Pair correlation is known only on \(|\alpha|\le1\); IGP slack is \(10^{-8}\). | Unconditional \(19/27\) (see 2.5). |
| I5 | **Exterior tightness**; exclusion of infinite-height escape. | Record minima permit zero gauge mass. | PM progress short of O5. |
| I6 | **Conductor/forcing compatibility** for companion-cluster detectors. | No common aperture range. | OWU/SRT detection. |
| I7 | **Independent faithful constructions** for each candidate. | Calibrations, zero-indexed objects, capacity/gap obstructions. | Candidate promotion. |
| I8 | **Local-to-global by counting over \(\mathbb Z\):** an auxiliary object playing Stepanov's role without a lattice spectrum. | Sparse annihilators kill only critical lattice symbols; sieve information is parity-blind. | A non-positivity source of positivity (2.7). |

"No known solution" refers to the corpus and the literature consulted.

## 2.3 Can we prove that off-line zeros, if any, are finitely many?

**Verdict: the question is sharply posed and reduced, but no available mechanism proves it. Any proof must first prove a quasi-RH.**

**It is strictly between quasi-RH and RH.** Finite off-line support forces \(\Theta<1\) ([index exit](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheIndexExit.lean)). It also excludes infinitely many zeros arbitrarily close to the line, which no density method touches: zero-density theorems bound \(N(\tfrac12+\delta,T)\) by \(T^{c(\delta)}\) with \(c(\delta)>0\), never by a constant.

**Exact receivers** ([route report §8](route-obstacles.md#8-finite-off-line-support-has-exact-receivers-and-costs-at-least-a-strip)):

- finite \(\mathcal E_{\rm crit}\), bounded source work, bounded integer-log spline index;
- the prime lag minus finitely many exponentials bounded on one side;
- bounded cosine defects;
- bounded nonreal zero counts of the heat-flowed \(H_t\) as \(t\downarrow0\).

**Three openings, ranked.**

1. **Finite index of the complete form.** The complete Weil form has uniformly finite negative index iff off-line support is finite (bounded spline index; complete cells capture every finite index). Most layers are already done: Gamma minus the all-prime \(k\ge3\) block, minus the whole prime-two source, and minus any fixed finite prime set each has a horizon-uniform finite index, and the poles cost one direction. The single missing lemma is relative form-compactness of the **first prime layer over all primes** (with the square-layer pole and the coarse source). Absolute payment fails there because \(\sum_p\log p/\sqrt p\) diverges. A signed payment needs exactly "prime error minus finitely many exponentials is \(O(\sqrt x\log^2x)\)". This is the cleanest formulation in the corpus: one operator inequality instead of a sign. In Pontryagin-space terms, \(W\) is a positive form plus a finite-rank form; each off-line quartet adds rank at most four to the orbit Toeplitz sequences (inference).
2. **Heat flow.** For each \(t>0\), \(H_t\) has finitely many nonreal zeros (Ki–Kim–Lee). The corpus proves the explicit horizon \(2\pi e^{(27/40+\varepsilon)/t}\) for \(0<t\le1/8\), and finiteness for \(\Xi\) is equivalent to a nonreal count bounded as \(t\downarrow0\). The obstacle is the horizon \(e^{c/t}\), which comes from a saddle-point analysis that degrades as \(t\to0\). A horizon uniform in \(t\) up to a bounded count is the target. The dynamics are concrete (Rodgers–Tao, Polymath 15), but no mechanism bounds backward-heat collisions at all heights.
3. **Critical energy.** An upper bound on \(K(R)=R^2(\mathcal W(2R)-\mathcal W(R))\) of virial type would do it. No candidate conservation law exists in the corpus.

**What does not work.**

- The inertia method of the census gives proportions only: finiteness would need the off-line positive index \(b=O(1)\), and its Frobenius side carries \(o(N)\) errors.
- Twin-blind payments cannot reach finiteness either: the Liouville twin satisfies all of them, and the Beurling over-regular systems show that positive primes with a very regular integer count can carry off-line zeros. The functional equation is what excludes those systems ([count fluctuation](../../../formal/GaloisForLFunctions/RHTower/RiemannFunctionalEquationForcesCountFluctuation.lean)).

**Recommendation.** Pursue opening 1 as [Q2](#q2): decide the first-layer compactness lemma, or prove that it is equivalent to the subtracted-lag bound. Treat any success as implying a quasi-RH, and test it against that implication.

## 2.4 Can we prove a quasi-RH better than \(1/8<\operatorname{Re}\rho<7/8\)?

**Verdict: not with the corpus's own mechanisms. The only lever is inside the external Chen–Gupta–Li argument, which is not yet formalized far enough to assess.**

**What the corpus offers** is complete translation, not production.

- \(\Theta=\tfrac12+\inf\{c\}\) over one-sided exponents \(c\) for:
  - the Möbius-divisor square-root Abel moment;
  - its quotient head at any power cutoff \(M^\theta\), with tail exponent \(\Theta+\tfrac12-\theta(\Theta-\tfrac12)\);
  - finite-contact Suzuki residuals.
- \(\Theta\le1-\theta\) is equivalent to the escaped-endpoint rates, the all-test Hecke-defect cap and integer-theta growth.
- \(\Theta<1\) is equivalent to a Vaughan power saving.

So a strip \(\operatorname{Re}\rho<3/4\) would follow from, and is equivalent to, a one-sided \(M^{1/4+\varepsilon}\) bound in any of these currencies. [Abscissa laws](../../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean), [balanced statistic](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheBalancedStatisticIsTheQuasiRiemannHypothesis.lean).

**What the corpus proves about the barrier.**

- Below the diagonal, Möbius power savings hold unconditionally at every modulus.
- On the diagonal, the first rung is already quasi-RH, with no weaker intermediate statement.
- Vinogradov–Korobov gives decay \(e^{-c(\log x)^{3/5-o(1)}}\) and no fixed power.
- The quotient-head law is self-consistent but gives no free bootstrap: the head of length \(M^\theta\) is itself \(O(M^{\Theta-1/2+\varepsilon})\) and forces \(\Theta\) back.

**The external route.** The CGL intake (279 modules) formalizes the zero detector, Lemmas 4.5 and 6.2, Propositions 4.6 and 5.1, and the density envelope \((qT)^{7(1-\sigma)/3}\). It has no zero-free capstone, and the continuation/contour step is not formalized. Whether \(7/8\) can be improved depends on how the threshold arises from the detector and the large-value exponents. That dependence must be extracted from the formalized proof (W07) before any improvement can be claimed.

- If the threshold is monotone in the density exponent, the density hypothesis value \(2\) in place of \(7/3\) is the natural first target. This is a known hard problem.
- Exponent optimization alone cannot reach \(\Theta=\tfrac12\). The corpus's collision no-go shows the CGL packet cannot carry the reflection charge needed at the critical endpoint: envelope floor \(288\) against the quantum \(2\).

**Recommendation.** Treat improved quasi-RH as dependent on W07. If the \(7/8\) proof is formalized, the improvement problem becomes a concrete exponent question. Until then, no corpus result supports any strip.

## 2.5 Can we prove that at least 70% of zeros lie on the critical line?

**Verdict: there is a concrete opportunity, but not inside the current mechanism.**

- The current method (inertia plus pair correlation) is capped near \(0.67\)–\(0.68\).
- \(70\%\) matches exactly the classical mollifier main terms at length \(\theta=1/2\), where Bui–Heath-Brown obtain \(19/27\approx70.37\%\) under RH.
- The task is to remove RH from those main terms with the inertia method.

**Where the corpus is.** At least \(HD(1)+10^{-8}\approx0.67250071\) of zeros are simple and critical, and off-line copies are at most \(1-HD(1)\approx32.75\%\). \(70\%\) needs off-line copies at most \(30\%\).

**Why the present mechanism stalls.** The Alpöge–Furman rank–trace argument computes the Frobenius norm of the explicit-formula Gram from Montgomery's pair correlation on \(|\alpha|\le1\). The Montgomery–Taylor window is optimal there. The IGP slack (no three short-window evaluation vectors orthogonal) gains \(10^{-8}\), and an optimized slack (W08) remains a second-order correction. Moving the main term requires either:

- pair correlation beyond \(|\alpha|=1\), which needs Hardy–Littlewood-type prime-pair asymptotics and is open; or
- a different main term.

**The different main term (Q3).** Conrey–Ghosh–Gonek's mollified discrete moments give, under their main terms, a simple-zero proportion \(1-(1+\theta)^{-3}\) for mollifier length \(\theta\) (the corpus records this algebra conditionally in KR-LLM). Two values of \(\theta\) matter:

- \(\theta=\tfrac12\) gives \(19/27\);
- \(70\%\) needs \(\theta\ge0.494\).

The obstacle is RH in the evaluation of \(\sum_\rho|\zeta'(\rho)M(\rho)|^2\). The inertia method suggests a replacement:

- Use the reflected pairing \(a(\rho)\overline{a(1-\bar\rho)}\), with \(a=\zeta'M\). It equals \(|a(\rho)|^2\) on the line, and each off-line pair contributes a \(2\times2\) block of positive index at most one.
- Evaluate it through \(\zeta'(1-\rho)=-\chi(1-\rho)\zeta'(\rho)\) and Gonek–Landau-type sums, which do not use RH.
- Replace Cauchy–Schwarz by the rank–trace inequality, so off-line pairs are charged instead of excluded.

**Open points:**

1. Unconditional asymptotics of the reflected moments at \(\theta\ge1/2\), uniform enough for the trace and Frobenius sides.
2. An inertia analogue of the Cauchy–Schwarz step whose off-line contribution is controlled by the positive index.
3. Whether the reflected pairing really counts critical zeros rather than zeros where \(a\ne0\).

None of these is RH-equivalent; all are open.

## 2.6 The three questions to answer next

<a id="q1"></a>
### Q1. Does the \(2\log2\) margin give Weil positivity where the Markov form is already negative?

**Exact object.** Atomic families \(f_x=\sum_{n\le N}x_ng(\cdot-\log n)\) at a fixed overlap ratio \(K\) just beyond the Robin–Euler ratio \(K_1\). At every width:
\[
W\ge0\iff M\ge0\text{ on }\textstyle\sum x_n/\sqrt n=0\ \text{ and }\ M+2a_0B\ge0\text{ on }\textstyle\sum x_n/\sqrt n=1.
\]
Beyond \(K_1\) the Markov form has exactly one negative direction, the pole vector.

**Why it is the right next step.** On the pole complement the bottom of the arithmetic spectrum is the conductor-two mode. Its spacing-scale energy \(\log(4K_1/K)\) is positive up to \(K=4K_1\) (proved for \(K<1/4\)). On that same hyperplane the Liouville twin has gap \(0\). So the mode picture predicts positivity on \(p=0\) in a window \((K_1,4K_1)\) that is selective: Liouville must fail there.

**First useful answer.** Any of:

- a proof of \(M\ge0\) on \(p=0\) for some \(K>K_1\), using the sharp selective Gårding inequality with the pole term kept signed;
- a proof of the affine scalar condition at the same \(K\);
- a computed counterexample (W01) locating where the mode picture fails.

**Payoff.** The first theorem in which a selective input pays the full form in a regime where the Liouville twin is negative. That negativity is an inference: below the spacing, twins differ from \(\zeta\) only in the prime form; the Liouville prime form reaches its ceiling on the hyperplane; and at that ceiling the Robin–Euler computation makes the Markov energy negative beyond \(K_1\). A negative answer is equally decisive: it would show the discrete margin does not survive the transfer to continuous tests.

<a id="q2"></a>
### Q2. Is the first prime layer relatively compact against Gamma on the complete source?

**Exact object.** On complete logarithmic cells, the form \(\Gamma-P^{(k=1)}\) and the full form \(W\). Here \(P^{(k=1)}\) is the coarse–detail and coarse–coarse prime pairing over all primes, with the square layer's pole restored. The question is whether \(\Gamma-P^{(k=1)}\) has uniformly finite negative index, and hence whether \(W\) does.

**What is proved.** Uniform finite index for the \(k\ge3\) block, the whole prime-two source, and every fixed finite prime set. Poles cost one direction. The square-layer regular symbol has a Gamma gap.

**Payoff.** A yes proves finite off-line support, which is [≥QRH]. A no should come with the exact prime-side statement it is equivalent to, plausibly the subtracted-lag bound. That would merge HF/ACS/AIP with WL at the finite-support stratum.

**First useful answer.** The growth law of the first-layer constants against the detail reserve (W04), and a proof or refutation of compactness for primes in dyadic ranges \(p\sim2^j\) uniformly in \(j\).

<a id="q3"></a>
### Q3. Can the inertia method remove RH from mollified discrete moments?

**Exact object.** The reflected mollified moments \(\sum_\rho a(\rho)\) and \(\sum_\rho a(\rho)\overline{a(1-\bar\rho)}\) with \(a=\zeta'M\), mollifier length \(\theta\ge1/2\), inserted into a rank–trace inequality whose off-line part has bounded positive index.

**Payoff.** An unconditional \(19/27\approx70.4\%\), beyond any pair-correlation method. It would also show that the inertia mechanism, which already made pair correlation unconditional, extends to a second main term. That is evidence that counting with signatures can replace positivity in further arguments (2.7).

**First useful answer.** The unconditional main term of the reflected second moment at \(\theta=1/2\), or an exact reason the reflected pairing cannot be evaluated without RH.

**Why these three.** Q1 tests whether the U2 programme's selective input can work at all. Q2 is the shortest formal path to a historic intermediate theorem (finite support). Q3 is the most likely to yield an unconditional theorem beyond the literature with tools already in the corpus. None depends on the others.

The previous edition's first question, reducing the complete form to finitely many \(\log2\)-orbits, is withdrawn as a priority. The generator-orbit form is a Toeplitz system whose symbol is the zero measure (inference), so the reduction relocates RH without weakening it.

## 2.7 Is there a wildly different route?

**No route was found that avoids all three walls.** Two seeds use a mechanism that none of the 31 routes or 18 candidate branches is built on. Both re-enter the walls, but at different points, which makes them informative.

**Seed A — counting before positivity.**

- Over \(\mathbb F_q\) the corpus proves that the Hodge index on every Frobenius ladder is equivalent to a one-sided square-root point count. Hyperelliptic curves pass it by Stepanov's auxiliary polynomial, with no surface and no positivity input. The local input at one prime is local RH. ([count](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheTrickleDownInequalityIsTheSquareRootCount.lean), [hyperelliptic](../../../formal/GaloisForLFunctions/RHTower/HyperellipticRiemannHypothesis.lean)).
- The \(\mathbb Z\) analogue of the count is the WL receiver \(\psi(x)-x\le C\sqrt x\log^2x\iff\) RH.
- A Stepanov proof over \(\mathbb Z\) would build an auxiliary object vanishing to high order at the primes, with controlled complexity, and count. The inertia method of the census is a weak relative: it locates zeros by counting signatures, not by positivity.
- Where it re-enters the walls:
  - Stepanov's engine is a sparse annihilator, which needs a lattice spectrum. The corpus proves that \(1-T_p^N\) kills a zero symbol only when the zero is critical and on a height lattice ([Stepanov mechanism](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/SparseAnnihilatorsAndTheStepanovMechanism.lean)). That is Wall 14.
  - The sieve form of an auxiliary-function count meets Selberg's parity barrier.

**The parity link (inference).** The selection theorem says that information of the form \(|\lambda|\le\Lambda\) is consistent with the Liouville twin. Selberg's parity problem says sieve information is consistent with the parity-twisted sequence. Both state that majorant information cannot see the sign carried by \(\lambda(n)=(-1)^{\Omega(n)}\). So the selectivity wall is the parity barrier in Weil-form language, and any successful route must contain a parity-breaking input. That is a criterion every route can be tested against, not a route.

**Seed B — crystalline-measure rigidity.**

- Kurasov–Sarnak, Olevskii–Ulanovskii and Alon–Cohen–Vinzant show that a positive measure with uniformly discrete support and discrete Fourier transform is the zero set of a real-rooted exponential polynomial, a restriction of a Lee–Yang polynomial. Reality is forced by structure, not by a sign estimate.
- By the explicit formula, \(\zeta\)'s zero measure has a discrete Fourier side on \(\pm\log n\) plus a smooth archimedean density. A rigidity theorem for "discrete Fourier side plus smooth background, with Euler-product multiplicativity" would put RH into the structure.
- Where it re-enters the walls:
  - The background is the archimedean place, the same obstruction that blocks function-field approximation (face 14.36).
  - Discreteness alone is not selective: Davenport–Heilbronn functions have discrete \(\log n\) support and off-line zeros.
  - With multiplicativity added, the natural lift is the Bohr-torus Lee–Yang structure of the W1C candidate.

**Conclusion.** The honest answer is "none". The new information is the parity criterion and the observation that only counting, not positivity, has ever produced RH-type theorems without a positivity input. Both are reflected in 2.8.

## 2.8 Would the obstacles in 2.2 need a new field of mathematics?

**Assessment.** The previous edition proposed "selective multiscale arithmetic positivity". The corpus has since built it (SMAP) far enough to see what it lacks. It proved selection, measured the margin and computed every cross-level coupling. Its remaining obstacles are not technical gaps inside that framework:

1. a discrete spectral gap must become positivity of continuous, overlapping tests;
2. cross-level couplings are almost-periodic Toeplitz sequences whose symbol is the zero measure itself;
3. every positive mechanism the corpus owns is parity-blind;
4. over \(\mathbb F_q\) positivity comes from counting, and \(\mathbb Z\) has no counting mechanism of that strength.

No existing discipline produces positivity of an arithmetically generated almost-periodic symbol, or breaks parity with a sign. In that sense a new field is likely required: a theory in which positivity is produced by counting and selected by multiplicativity. Whether it is a field or one new theorem inside analytic number theory cannot be decided from the corpus.

### What the field would be about

**Local-to-global positivity over \(\mathbb Z\).** Its subject is the passage from local data (each prime's factor, the archimedean factor, the pole) to a global sign. Over \(\mathbb F_q\) that passage is a count, and the corpus proves the equivalence. The field would construct its \(\mathbb Z\) analogue and explain why the result is selective.

### Objects

- The Weil form \(W=\Gamma+\text{poles}-P\), its twins \(W_\lambda\), and the selection theorem as a boundary condition.
- The multiplicative walk and its Dirichlet energy \(D_N\), with Poincaré constant \(2\log2\); the pole/harmonic hyperplane; arithmetic modes with energies \(\gamma+\log m+d(m)\).
- Hecke orbits, their Toeplitz symbols on the circle, and the Cayley–Li ladder.
- Inertia indices (Sylvester signatures) of explicit-formula Grams; finite-rank (Pontryagin) perturbations.
- Auxiliary objects of bounded complexity vanishing to high order at primes; sparse annihilators in characteristic zero.

### Language

- A **selective inequality** fails for some bounded twin. A **parity-breaking input** distinguishes \(\lambda\)-twisted from untwisted data.
- A **count** is a one-sided bound at square-root precision. **Local-to-global** is a map from counts to signs.
- An **exhaustion statement** names source, form, domain, growth parameter and error currency together.

### Mechanisms it must discover

| Mechanism | Purpose | Test |
|---|---|---|
| Selective transfer to overlap | Turn the \(2\log2\) gap on the discrete hyperplane into continuous positivity past the Robin–Euler point | Q1; must fail for Liouville and for scalings \(c\Lambda\) |
| Arithmetic Herglotz theorem | Positivity of an almost-periodic Toeplitz symbol from properties of its prime-side generation | Must reproduce RH's Toeplitz positivity on one orbit; must fail for Davenport–Heilbronn and Beurling over-regular systems |
| Stepanov over \(\mathbb Z\) | An auxiliary construction giving a one-sided prime count at square-root precision without a lattice spectrum | Must reproduce hyperelliptic RH; must be parity-breaking |
| Finite-rank renormalization | Show the complete form is a positive form plus a finite-rank form | Q2; must give exactly finite support, not RH |
| Exact inertia counting | Signature counts with Frobenius control precise enough for a bounded off-line index | Must reproduce \(2/3\) and \(HD(1)\); Q3 is the next calibration |

### Questions it must answer

- Why is the prime \(2\) both the multiresolution generator and the bottleneck of the margin \(2\log2\)?
- What is the positive form of the parity barrier? Is it the selective margin?
- What replaces Frobenius's lattice spectrum in a \(\mathbb Z\)-Stepanov argument?
- What arithmetic structure explains the reality horizon \(e^{27/40\,t^{-1}}\) of the heat flow?
- In which topology does exhaustion preserve inequalities, given that no exponential renormalization gives uniform graph control?

### Criteria it must meet

1. **Independence.** Built from arithmetic data, never from zero-indexed objects.
2. **Fidelity.** All mixed entries, Gamma, both poles and multiplicities; prime-only, collided and complete forms kept apart.
3. **Selectivity.** Every sufficient hypothesis fails for the battery: the Liouville twin, scalings \(c\Lambda\), quadratic mixtures, the golden curve, Beurling over-regular systems and Davenport–Heilbronn functions.
4. **Parity.** It contains an input that \(\lambda\)-twisting changes.
5. **Exhaustion.** Uniformity exactly in the growing parameters.
6. **Calibration.** Reproduce Weil over \(\mathbb F_q\) by counting, the \(2/3\) census, the \(K_\star\) regime and the sharp gap, without demanding the false all-overlap Metzler gauge or pure-Markov sign.
7. **A new inequality.** A paid sign, index ceiling, count or energy bound, not another equivalence.
8. **Formal closure.** Unconditional Lean statements with every input discharged.

**First evidence of success** would be a positive answer to Q1 that fails visibly for the Liouville twin, or an unconditional proportion beyond \(HD(1)\) from a non-pair-correlation main term (Q3).
