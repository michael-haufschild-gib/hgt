# Research frontier: work, open problems and next questions

Status: 29 October 2026, corpus HEAD `718f741cc7` plus working tree. **RH remains open.** The corpus now pins down where the missing input can come from, not only what it must satisfy.

**Selectivity has two sources [L].** Weil positivity is pointwise-closed, and every twist of \(\Lambda\) (Liouville, every flip) is a pointwise limit of vertical shifts. So selectivity lives either in the shift-fixed terms (pole, Gamma) or in gauge charge carried by non-ratio lags, which is additive structure. Multiplicative data are shared by the whole gauge orbit.

**The pole pays bounded overlap.**

- The complete form is eventually positive for every fixed \(0<c<c_*\), with \(c_*>1+10^{-16}\) [K].
- It rejects the Liouville twin (\(c\ge1/2\)) and \(\omega_{11}\) (\(c\ge99/100\)). Both rejections are pole-mediated.
- \(c_*\) is the exact boundary of the optimized Young-bound family at the present analytic constants. That family needs pole charge \(cq_0<1\).

**RH needs additive structure at one point.** Past touching, successor shells \(n=km+j\) enter the form, every nonpolar reference energy loses \(\log c\), and atom norms degenerate. RH is positivity at overlap \(L(\log L)^2\log\log L\) [S]. In gauge language, RH is the statement that the gauge point \(0\) is typical modulo its pole. Haar-almost every twist already satisfies every square-root law, and the exceptional set is comeager and null.

**The producer must vanish finer than divisibility.** Over \(\mathbb F_q\), Stepanov's multiplicity grows through Frobenius. Over \(\mathbb Z\), divisibility reaches only linear precision and cannot tell the primes from one parity class.

Coverage: 32 live routes, 17 standalone candidates, PW-B; ISC-polar retired.

Companions: [route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md) · [scoped obstructions](../rh-killed-routes.md). Research record: [working log](../../../logs/review-2910c-research-2026-10-29.md).

Evidence labels:

| Label | Meaning |
|---|---|
| **[L]**, **[S]**, **[K]** | As in the frontier map. |
| **[Lean]** | Statement read; integration not assessed. |
| **(inference)** | A conclusion of this review. |

## What the corpus establishes

- **Two-source law** [L]:
  - pointwise-closed statements are twin-blind;
  - the diamagnetic inequality holds;
  - the gauge enters only through non-ratio lags.
- **Gauge torus** [L]:
  - the prime source is typical except for its pole;
  - the Möbius exceptional set is comeager and null;
  - successor correlations, near-incidences and the coalescent surplus are pure gauge charge;
  - the main term of gauge charge is carried by Dirichlet characters of level \(q\mid h\).
- **Bounded overlap** [L/K/S]:
  - positivity for \(c<c_*\), \(c_*>1+10^{-16}\), with floor \(1/400\) at \(1+10^{-16}\) [K];
  - the three fixed estimates alone saturate at \(\delta_*=1/107520002048050000\) [K];
  - the exact reference floor is valid up to pole charge one [K];
  - Liouville and \(\omega_{11}\) witnesses [S].
- **Growing overlap** [L/S/K]:
  - RH receivers at \(L(\log L)^\beta\), \(\beta>2\) [L] and \(L(\log L)^2\log\log L\) [S];
  - explicit schedules reach \(\kappa\) [L];
  - shell thresholds [K]; logarithmic divisor rows [K];
  - nonpolar losses [S]; no atom-norm floor [S]; exact Schur reduction [S]; zero-side stratum [S].
- **Coordinates** [K]: overlap \(=\) length/height. The atomic programme and the census share the bandwidth-one crossing.
- **Index theory** [L/S/K]:
  - \(\kappa=\#\)right zeros;
  - index zero \(=\) one-sided count \(=\) odd-class upper count;
  - height certificates; carriers; attained depth; locality;
  - Bohr-closure twin; exact function-field ceiling.
- **Precision** [S/L/K]:
  - the square-root class is the count's stabilizer;
  - random signs satisfy the count;
  - deciding input; finite aperture cannot decide;
  - Chebyshev ledger (moments, sawtooth, Mertens).
- **Producers** [L]: one ledger over \(\mathbb F_q\) and \(\mathbb Z\); Stepanov's order; divisibility sees prime powers, not parity; divisibility passes the sup-norm cap at linear precision.
- **Finite-index chain** except \(k=1\); **finite support** \(=\) RH above a height \(\Rightarrow\) LH \(\wedge\) \(\Theta<1\).
- **Census**:
  - \(\ge HD(1)+10^{-8}\) simple critical; \(\ge0.8876\) simple or critical;
  - \(70\%\)-or-near-line-core dichotomy [K];
  - projected displacement credit [K].
- **Quasi-RH**: complete translation layer; Guth–Maynard; DH on \(\sigma\ge5/6\); \(17/30\) short intervals; VK; no producer.
- **Infinite symmetry is settled**: confinement is the lower square-root count [L].

## 2.1 Tasks that are just work

"Just work" means the ingredients exist. A sign task delivers a certified enclosure, a sharper constant or a transferred proof, never a guaranteed sign.

| ID | Task / deliverable | Serves | Boundary |
|---|---|---|---|
| W01 | Sharpen the fixed analytic constants of the optimized Young family (the overlap coefficient \(2000\), the cost \(1276c^2\), the plateau variance and shape estimates) by operator-level estimates. This moves the certified boundary \(c_*\) toward the charge barrier \(c<1/q_0\). | Q1; HF, SRT, AIP, ACS | At fixed constants \(c_*\) is exact; the family stops at pole charge one. |
| W02 | The prime-square trial for \(\omega_p\), \(p\ne11\), and a uniform-in-\(p\) version; cofinite flips at fixed \(c\). | I2 | Pole-mediated; no gauge charge. |
| W03 | Optimize \(c_{\rm RE}(\varphi)\); decide whether the Liouville twin has a sharp transition. | I2 | Explicit functionals. |
| W04 | Full-index exhaustion at the Steklov schedule; remove the \(\log\log L\) factor with weaker Denjoy–Carleman weights. | SRT, HF; I3 | The edge \(c_N=O(\log\log N)\) stays open. |
| W05 | Integrate the working sources: TM `BoundedOverlap/*`, `TransMetzlerReferenceFloor`, `TransMetzlerYoungOptimization`, `OptimalYoungDefectFloor`, `GrowingOverlapHasNoUniformGramFloor`, `APositivePrefixGivesTheExactSchurReduction`, `TheFixedProfileReachesAnIteratedLogEndpoint`, `ZeroSideStratum`, `LiouvilleTwinSelectivity`; RAPT `OverlapForcesNewRamanujanTerms`; CAF; CACT prime-prefix domination; `LogarithmicIndependentSigns`; the remaining [S] modules of AKLT and ASRP. | all | Integration only. |
| W06 | Spectrum of the complete matrix at fixed \(c\in(1,3]\), \(N\) up to \(10^5\), in conductor coordinates, with each successor shell's contribution separated; locate negative directions if any. | Q1 | Numerics, not an eventual sign. |
| W07 | Exact first-shell calculus at \(c\in(1,2)\): archimedean overlap of adjacent atoms plus non-ratio lags \(n=km\pm1\). Include the pole-vector collapse \(\sum_{k\mid\ell}\Lambda(k)=\log\ell\) and the decomposition of shell sums by Dirichlet characters of level \(q\mid j\). | Q1; 2.5 | Exact algebra; the discrepancy bound is I1. |
| W08 | The Schur complement \(D-B^*A^{-1}B\) on computed ranges; compare with the arithmetic Dirichlet–Schur cost. | Q1 | The arithmetic Green inverse is not the Weil prefix inverse. |
| W09 | Transfer the Montgomery–Vaughan band bound \(\int_N^{101N}|D_x|^2\ge48N\sum x_n^2\) through the profile multiplier and Gamma weight. | I17 | Gives a norm, not a sign. |
| W10 | Explicit head sizes in every finite-index theorem; first-layer constants along growing prime sets. | HF, ACS, AIP | \(k=1\) stays [FS]. |
| W11 | Tabulate cross-level couplings \(W(f,T_{d\log2}g)\), the Möbius moments \(m,\ell\), the sawtooth inversion \(I_n(h)\) and their cancellation on certified ranges. | WL, MC, HF, CHMD | No sign. |
| W12 | Complete multiresolution Grams (orbits, details, cross-level blocks, Gamma, both poles); ordered Chebyshev integrals with VK. | HF, ACS, AIP, RW | Exact algebra. |
| W13 | The quasi-RH preprint: formalize its continuation step and extract the zero-free abscissa as a function of its density and large-value inputs; evaluate at \(q=1\) with \(30/13\) and DH on \(\sigma\ge5/6\). | MC; I12 | Depends on the external argument. |
| W14 | Census: best positive-definite-majorant bound for \(E(\delta)\); constants in \(hE_h\le CN\); \(E_{\rm proj}\) on explicit near-line configurations. | Q3; ACS | Majorants are displacement-blind. |
| W15 | Heat: explicit \(N(t)\) on compact ranges; sum the localized estimates on fixed height windows. | WD, LA | No uniform count. |
| W16 | Projections, Schur residuals, radicals; Ramanujan residuals for fixed conductor sets. | AID, SAHT, RAPT | Window-dependent. |
| W17 | Hecke: field- and modulus-uniform bounds; the completed FE is already in place. | RAPT, HLF | Tools. |
| W18 | Ledgers and finite rows for FU, RP, LI, TT, PA, MC, PM, CTF, JAS. Also: strip transport; compact cofactor Grams; finite-aperture energies and blind minima; finite heat, Jensen, Hankel and grid heads; Newton discs, Ward caps, renewal resolvents, Schur charges and recurrences. | many | Local certificates. |
| W19 | Constant term of the affine \(A_1\) series over the genus-one base. | calibration | Another receiver of the count. |
| W20 | Candidate calculations: cycle traces, curvatures, jets, contours, ports, stacks, cusp actions. | candidates | Calibration is not forcing. |
| W21 | Lean application of the product-bias classification, which has a paper proof [P]. | WL, MC | Formalization. |
| W22 | Twisted complete forms at Haar-random gauge points and twin tails at fixed \(c\), to measure exactly what the pole pays. | Q1, Q3 | Calibration. |
| W23 | A formal no-go for factorial-ratio auxiliaries: multiplicity \(\le1\) above \(\sqrt N\), and no gain on short intervals. | Q2 | Exact arithmetic. |
| W24 | Intake of level-of-distribution tools: large sieve, Bombieri–Vinogradov, dispersion with the Weil Kloosterman bound (already formalized). | Q3 | Tools for gauge charge at \(0\). |
| W25 | Literature intake: Friedlander–Iwaniec asymptotic sieve; Soundararajan's escape-of-mass argument; Rodgers–Tao; Roth's lemma and Schmidt's subspace theorem; Deuring–Heilbronn; Goldfeld–Gross–Zagier; Borger's \(\Lambda\)-rings. | 2.4–2.6 | External proofs are not assumed. |

## 2.2 Open mathematical obstacles

### (a) RH-equivalent endpoints

| ID | Missing result | Routes |
|---|---|---|
| O1 | Critical signed cancellation in any currency. The currencies include: the one-sided \(\psi\) count (\(=\kappa=0\)); the odd-class upper count; lag energy; Abel moment; linear history floor; strict half-power; regularized convergence; extremal remainder; approximation residual; half-power budget; the integrality halves; joint control of moments, sawtooth and Mertens; the first-clock tail. | WL, FU, CFC, RP, MC, LI, PBM, RB, JAS, CTF |
| O2 | Complete Weil positivity on a source-complete family: atomic positivity at \(L(\log L)^2\log\log L\), integer-atom Grams, complete-cell index zero, residual, odd, allocation or Hodge sign, tent families. | RW, HF, SZ, EWU, OWU, AIP, ACS, TT, CHMD, ACT, SRT |
| O3 | Positivity on one prime's towers, already for pole-free generators of arbitrarily small support. | HF, ACS, AIP, CHMD, SRT |
| O4 | All-degree, all-height heat, moment or coefficient signs; the successor integral at every rank; the Cayley–Li ladder; both Gaussian grids. | PA, LA, TH, WD, HCF, LI |
| O5 | Positive gauge mass of every escape state; vanishing approximation error. | PM, CTF |
| O6 | Rank-uniform transverse decay; all-point recurrence; covering Newton discs; the integer trace cap; directed renewal orientation. | GTA, BAG, XN, TG, RN |
| O7 | \(\mathcal E_{\rm crit}\) at most one quantum; cofinal source work \(\le2\). | HF, SRT, ACS |

**Common content (inference).** Each of O1–O7 is the typicality of the gauge point \(0\) for a gauge-charged statement at square-root precision.

### (b) Stronger than RH

| ID | Statement | Note |
|---|---|---|
| S1 | Abel-slope genus saturation; linear Mertens energy | RH plus simple zeros |
| S2 | Matching-profile signed pair surplus at the stated strength | Not implied by RH |

### (c) The finite-support stratum [FS]

Each item is equivalent to finitely many off-line zeros, that is, RH above some height. Each implies LH and a fixed strip.

| ID | Missing result | Routes |
|---|---|---|
| F1 | Uniform finite index of the complete form (the first prime layer against Gamma) | HF, ACS, AIP |
| F2 | Finite \(\mathcal E_{\rm crit}\); bounded source work; eventual subquantum annular increment | HF, SRT, ACS |
| F3 | Subtracted lag bounded on one side | WL |
| F4 | Bounded nonreal counts of \(H_t\) as \(t\downarrow0\) | WD, LA |
| F5 | Bounded cosine defects | WD |
| F6 | Bounded index on a two-prime lattice; finite wave number | ACS, AKLT |

Finite support makes RH local in the prime: almost every tower decides. **Verdict: not a near-term target.** Use it as a diagnostic: an argument giving finite index without LH-strength input is wrong.

### (d) Lindelöf and quasi-RH levels

| ID | Missing result | Status |
|---|---|---|
| L0 | Zeros approach the line | Implies LH and \(\Theta<1\) |
| L1 | LH, equivalently Backlund sparsity | Open since 1908; \(\mu(1/2)\le13/84\) |
| Q0 | A fixed zero-free strip \(\Theta<1\) in any dictionary | Claimed externally at \(7/8\) for Dirichlet \(L\)-functions [E]; the corpus has no strip of its own. A density envelope never drops below \(1\). |

### (e) Census

| ID | Missing result | Payoff |
|---|---|---|
| C1 | \(E(1/9)\le4\): a two-sided coalescent prime-pair estimate at bandwidth \(10/9\) | \(70\%\) |
| C2 | Prime surplus \(\le N/18\) at bandwidth \(4/3\) | \(75\%\) |
| C3 | A positive census-scale lower bound for \(E_{\rm proj}\), or displacement \(\eta\ge1/18\) near bandwidth one | \(70\%\) |
| C4 | Displacement-sensitive shallow energy \(hE_h+R_{\rm deep}\le\tfrac3{20}N\) | \(70\%\) |

The dichotomy puts every failure in simple off-line zeros within \(A/\log T\) [K]. C1 and C2 hold with budget zero for Haar-almost every gauge twist, so they are gauge charge at \(0\), like I19.

### (f) Intermediate open problems

| ID | Missing result | Why current work stops | Payoff |
|---|---|---|---|
| I1 | **Positivity across the first successor shell**, at every fixed \(c\in[c_*,2]\), and the repayment of \(-\log c\) on nonpolar conductors as \(c\) grows | The optimized Young family has floor zero at \(c_*\) and needs pole charge \(<1\); the shell operator is not small | The first theorem in which additive structure pays Weil positivity (Q1) |
| I2 | **Flip selectivity for all \(p\)**, uniformly in \(p\) | Proved for \(\omega_{11}\) only | Completes the pole-mediated layer |
| I3 | **Bounded-overlap completeness**: does positivity at every fixed \(c\), or at \(c_N=O(\log\log N)\), imply RH or finite support? | The tempered countermodel lacks \(\zeta\)'s density; one off-line pair is swamped at fixed \(c\) (inference) | Locates where positivity becomes RH |
| I7 | Exterior tightness | Record minima permit zero gauge mass | PM short of O5 |
| I8 | Conductor/forcing compatibility | No common aperture range | OWU detection |
| I9 | **Point-side producer over \(\mathbb Z\)**: an auxiliary of controlled size vanishing on one parity class with growing multiplicity. First rung: the sieve parity constant \(2\) on \(x^\varepsilon\) intervals. | Divisibility sees prime powers, not parity; binomial multiplicity \(\le1\) above \(\sqrt N\); sup-norm certificates are capped | A mechanism that produces counts (Q2) |
| I10 | An arithmetic index ceiling (Riemann–Roch substitute) | A positive part never pays a pair; locality is twin-blind | Finite support, then RH via towers |
| I11 | Independent constructions for each candidate | Calibrations; zero-indexed objects | Promotion |
| I12 | Whether \(\zeta\)-specific density inputs move the external \(7/8\) threshold | Threshold not extracted (W13) | A conditional improved strip |
| I13 | Growing-conductor spectral control of the complete matrix | Fixed packets and per-conductor eigenlines only | Large-overlap spectra |
| I15 | A many-node Gram floor from two-prime phase separation | Baker bounds degenerate as \(\Delta\to0\) | HCF and SRT without aliasing |
| I16 | The Schur complement on growing-overlap families | Prefix inverse unidentified | An exact reduction of I1 |
| I17 | A synthesized-mass (Dirichlet-polynomial norm) floor at growing overlap | Atom norms degenerate | The right norm for I1 |
| I18 | Prime-tower detection at an unattained maximal depth | Attainment is used | Closes the tower Hasse principle |
| I19 | **Gauge charge at the point \(0\) beyond major arcs**: any successor, near-incidence or coalescent statistic of \(\Lambda\) within a power saving of its Haar mean beyond the Dirichlet-character main term | Multiplicative data are gauge-invariant; only finite gauge subgroups are controlled | The first point-0-specific input (Q3) |
| I20 | A geometric parity twin over \(\mathbb Z\) | No vertical shift is \(-1\) at two primes; the twin lives only in the Bohr closure | A twist tower over \(\mathbb Z\) |

**What all B-items share (inference).**

- The pole and Gamma give selectivity at linear precision only.
- Every B-item needs gauge charge at the point \(0\) at square-root precision, or an object that produces it.
- Both have been obtained together only over \(\mathbb F_q\). There, Frobenius is simultaneously additive and multiplicative, which couples the two structures. \(\mathbb Z\) has no such endomorphism.

## 2.3 The three questions to answer next

<a id="q1"></a>
### Q1. Can the complete Weil form be made positive across the first successor shell, with the shell as a source rather than an error?

**Exact object.** At fixed \(c\in(1,2]\), the complete matrix of atomic families equals the separated matrix plus the first successor shell. That shell consists of the archimedean overlap of adjacent atoms and the non-ratio lags \(n=km\pm1\).

- **Proved.** Positivity for \(c<c_*\), \(c_*>1+10^{-16}\), by bounding the shell as a perturbation inside the optimized Young family [K].
- **Required as \(c\) grows.** The nonpolar reference energies \(E_m(1)-\log c\) go negative, so under RH something absent at separation repays them.

**Why now.**

- This is the only place where the corpus can watch the second source of selectivity enter, at bounded \(c\) with finitely many shells and fixed conductors.
- The bound family has an exact boundary at the present constants and stops at pole charge one, so progress beyond the charge barrier has to be structural.
- Two exact facts are available on the shell:
  - on the pole vector, the divisor fibre collapses by \(\Lambda*1=\log\) to the archimedean \(\log\ell\);
  - shell statistics have Dirichlet-character main terms of level \(q\mid j\).

**First useful answers.**

1. Numerics of the full spectrum at \(c=1.25,1.5,2\) with the shell separated (W06, W07).
2. A theorem of the form "complete matrix \(=\) positive operator (pole, archimedean, major-arc shell) \(+\) discrepancy of norm \(o(1)\) in synthesized mass" at some \(c>c_*\).
3. Or an eventual negative direction at a fixed \(c\). This would show that bounded-overlap positivity is not monotone in \(c\), and that RH positivity must come from growth effects.

**Payoff.** Either the first Weil-positivity theorem paid by additive structure, or the exact statement of what the shell cannot pay.

<a id="q2"></a>
### Q2. What integer auxiliary vanishes on one parity class finer than divisibility?

**Exact object.** RH iff the odd Liouville class has an upper count [S]. The producer ledger is \(\sum_pm_p\log p\le\log A\) [L].

- Over \(\mathbb F_q\), Stepanov reaches multiplicity \(\approx\sqrt q\) at every counted point through \(x^q=x\), and the twist tower completes the count.
- Over \(\mathbb Z\):
  - binomials have multiplicity \(\le1\) above \(\sqrt N\) and a trivial short-interval ledger;
  - divisibility cannot tell primes, prime powers and the odd class apart at square-root precision;
  - sup-norm certificates are capped at \(\psi(x)\ge0.8644x\), while Chebyshev's divisibility producer passes the cap at linear precision.

**First rungs.**

- An integer \(A\) with \(m_p\ge2\) on a positive proportion of the primes of \((x,2x]\) and \(\log A<2\sum_{x<p\le2x}\log p\). This is multiplicity growth at sub-trivial size.
- Beat the sieve constant \(2\) on \(x^\varepsilon\) intervals by an auxiliary.
- A formal no-go for factorial-ratio classes (W23).

**Payoff.** A mechanism that produces counts, the missing Frobenius substitute. Q2 is the only question aimed at the producer.

<a id="q3"></a>
### Q3. Is the gauge point \(0\) typical for any gauge-charged statistic beyond its major arcs?

**Exact object.**

- Successor correlations, near-incidences \(ab-cd=h\) and the census coalescent surplus are pure gauge charge. They have mean zero and square-root size for Haar-almost every twist, and multiplicative data cannot certify their value at \(0\).
- Their main term is the average over finite gauge subgroups, i.e. Dirichlet characters of level \(q\mid h\) and the singular series.
- The census budgets C1 and C2 hold with budget zero almost surely; at \(0\) they are open.

**Why now.** The only known unconditional inputs of this type come from level of distribution (Bombieri–Vinogradov; Zhang and Maynard via dispersion and the Weil and Deligne bounds). They feed square-root purity over finite fields into horizontal prime statistics. The corpus has the Weil Kloosterman bound and multi-modulus dispersion but no level-of-distribution theorem.

**First useful answers.**

1. Bombieri–Vinogradov in the corpus (W24).
2. Its transfer to the coalescent surplus or to one successor shell.
3. Or a proof that level-of-distribution inputs are blind to the census budget, i.e. the census needs gauge charge beyond every averaged modulus.

**Payoff.** The first point-0-specific gauge-charge input. This is the counting face of the obstruction that Q1 meets as a sign.

**Why these three.** Q1 tests whether additive structure can pay positivity. Q2 asks for the producer. Q3 asks whether point \(0\) can be shown typical anywhere beyond the major arcs. They are three faces of one fact: the pole pays only bounded overlap, and the remaining input is gauge charge at one point.

## 2.4 Is there a wildly different route?

**Verdict: no route escapes the content of the walls, but one framework would meet that content in a form no current route uses.** Any proof must certify, at the single gauge point \(0\), a gauge-charged statement at square-root precision. This follows from three facts:

- the count is RH;
- its stabilizer is the square-root class;
- multiplicative data are gauge-invariant.

What can differ is the logic that delivers it.

### Candidate: Diophantine typicality of special points

**The analogy is exact at the level of sets.** In \(\mathbb R\), Liouville numbers form a comeager null set. Roth's theorem says algebraic numbers avoid it: they have the Haar-typical approximation exponent \(2\). On the gauge torus the analogy is precise [L]:

- The exceptional set of the Möbius half-power law is comeager and null.
- Twin tails play the role of Liouville numbers: they agree with \(0\) on finitely many primes, then follow the Liouville sign, and carry a pole.
- \(0\) lies in the closure of the exceptional set.
- RH says that \(0\), a special point, avoids it.

The special points of the torus are the twists with additive structure: Dirichlet characters times vertical shifts, exactly the points whose \(L\)-function has a functional equation (the degree-one Selberg class).

**What the route would be.** A Thue–Siegel–Roth argument on the torus:

1. **Approximation.** Define a Diophantine exponent of a gauge point: the rate at which it is approximated by twin tails, or by torsion points (Dirichlet characters) of bounded conductor. An off-line zero of depth \(d\) should force exponent \(\ge\tfrac12+d\).
2. **Auxiliary.** Build an integer auxiliary that uses the algebraic relation of the special point. That relation is unique factorization \(\Lambda*1=\log\), or the functional equation as additive self-duality. It must vanish to high index at many simultaneous approximations.
3. **Non-vanishing.** A Roth's-lemma or zero-estimate substitute.
4. **Integrality** turns smallness into contradiction.

**Why it is far from every current route.**

- It signs no quadratic form, so it does not face Wall 1 as a positivity problem.
- It exhausts no overlap, aperture or conductor; Roth needs no uniformity. So it does not face Wall 3.
- Its logic is contradiction from many hypothetical bad approximations, not a construction certifying a sign. Like Siegel's theorem and Roth's theorem, it could be ineffective.
- It uses the arithmetic identity of the special point, not an estimate.

**Precedents.** These are typicality theorems for special points:

- Roth (algebraic numbers);
- Siegel's \(L(1,\chi)\gg_\varepsilon q^{-\varepsilon}\), whose exceptional characters are torsion points close to the Liouville twin in the torus;
- Goldfeld–Gross–Zagier, which makes that typicality effective through a geometric object.

**Ladder.** The trivial (Liouville-type) bound is the prime number theorem. A Thue-type improvement of the exponent at \(0\) would already be a fixed zero-free strip, which is QRH. Roth-type sharpness is RH.

**What would kill it.**

- If the Diophantine exponent of \(0\) is only the count restated, with no auxiliary that uses the identity of the point, the route collapses to Q2.
- Every statement it proves must fail for twin tails.

**First tests.**

- Define the exponent and prove that it is Haar-almost everywhere \(\tfrac12\).
- Show it equals \(\Theta\) at \(0\).
- Recover the Siegel or Deuring–Heilbronn phenomenon in this language as calibration.

### A negative finding: topological (index-continuity) routes

The index is continuous off the discriminant and lower semicontinuous under pointwise limits [S]. A deformation route would connect \(\zeta\) to an index-zero object without crossing the discriminant. Two facts block it (inference):

- **Openness fails.** \(\Lambda_{\rm dBN}\ge0\) (Rodgers–Tao): for every \(t<0\), \(H_t\) has nonreal zeros. So \(\zeta\) lies in the closure of positive index along the backward heat flow, and no argument that index zero is an open condition at \(\zeta\) can work in that direction.
- **Closedness is realization.** Lower semicontinuity makes index zero closed under pointwise limits. Using it requires an independently built family of positive kernels converging to \(K_\zeta\), which is Wall 14.

The same marginality explains why no uniform floor exists at unbounded aperture or growing overlap.

### Mechanisms examined and where they re-enter

| Mechanism | Re-entry point |
|---|---|
| Measure rigidity and QUE-style escape-of-mass control | PM: escape states are spectral measures on the gauge torus; RH is positive gauge mass. Soundararajan's no-escape argument is a technique for PM's exterior tightness, not a new route. |
| Affine \(ax+b\) structure and Mackey rigidity | Mixed Grams of one source are automatically PSD and carry no arithmetic. Content lies in the boundary (the escaped dilation mass \(\log a\) at \(\sigma=\tfrac12\)). This is the frame of 2.5. |
| Bohr compactification and Kronecker flow | BAG: the hull of vertical translates is the gauge orbit; unique ergodicity sees the torus only below the threshold. |
| Level of distribution, dispersion, Kloosterman sums | Gauge charge at \(0\), averaged over moduli: Q3. |
| Pretentious (Halász) methods | Logarithmic savings only: Wall 1 precision. |
| Tensor and functorial amplification | Relative powers of the trivial point are trivial; external powers see the same zeros; multiplicative amplification loses linearly. |
| Fourier interpolation, sign uncertainty, quasicrystals | Dual certificate is \(\Lambda\); the archimedean continuum breaks the crystalline dual. |
| Interlacing families, stability preservers | Need \(\Xi\) as an expected polynomial: Wall 14. |
| Model theory, o-minimality | RH is not first-order over valued fields; the primes are not definable. |
| \(\mathbb F_1\), scaling site, Witt vectors | Effectivity with Riemann–Roch is RH; Witt integrality is not purity. |
| Infinite symmetry (affine Eisenstein) | Confinement is the lower square-root count. |
| Compression and annihilation | Receivers. |

## 2.5 Where a real breakthrough on the hard questions could come from

**Thesis: make additive structure a source of positivity.** Every positivity principle the corpus uses lives on the multiplicative group:

- Bochner on \(\mathbb Q_{>0}^\times\);
- Krein–Langer on orbit kernels;
- Haar on the gauge torus;
- Hodge index on the scaling surface.

Their selective content is the pole, and the pole pays only bounded overlap. Under RH, the \(-\log c\) loss of every nonpolar conductor is repaid at growing overlap by terms that exist only through overlap. These are successor-shell prime lags, which are gauge charge. Positivity there is also marginal: no atom-norm floor, floors decaying doubly exponentially in aperture, \(\Lambda_{\rm dBN}\ge0\). So the repayment cannot be an estimate with a fixed loss. It has to be an identity, or an asymptotically exact structure. That is the breakthrough to aim for: a positivity mechanism in which additive structure enters with a definite sign, exactly.

### Why this is attackable now

1. **Finitely many shells.** At fixed \(c\) only shells \(|j|\lesssim c\) enter [K], and above \(c=1\) only adjacent atoms overlap [L]. The first shell is a single, exactly described operator.
2. **A point-0 identity on the shell.** All divisors of a product have the same lag, and \(\sum_{k\mid\ell}\Lambda(k)=\log\ell\) [K]. On the pole vector the shell's prime terms collapse to the archimedean absolute value \(\log\ell\), which is the kind of term that can meet a \(-\log c\) archimedean loss. The identity is unique factorization, so it fails for every twist: \(\sum_{k\mid\ell}\omega(k)\Lambda(k)\) does not collapse.
3. **Major arcs are controlled.** The main term of every shell statistic is carried by Dirichlet characters of level \(q\mid j\) [Lean], which at fixed \(c\) means finitely many fixed conductors. Their \(L\)-functions are controlled at the needed bounded-conductor level, so only the discrepancy is unknown.
4. **Boundaries see gauge points.** The escaped mass of a dilation is \(\log a\) exactly at \(\sigma=\tfrac12\), and the successor leaves no boundary. The Möbius boundary separates twins with identical multiplicative data [L]. A ring-level positivity has to be a statement with boundary.

### Target theorem

**Shell positivity.** For each fixed \(c\in(1,k+1]\), the complete matrix on atomic families equals a positive operator plus a gauge-charged discrepancy. The positive operator has three parts: the pole, the archimedean overlaps, and the major-arc shell terms with singular-series weights over conductors \(q\mid j\le k\). The discrepancy has operator norm \(o(1)\) relative to synthesized mass.

- It would be the first Weil-positivity theorem paid by additive structure.
- It is selective by construction: twins lack the pole and the collapse.
- It is a statement at bounded overlap, where everything is finite.
- Iterated in \(c\), it becomes a shell-by-shell theory of overlap growth. At \(c_N\asymp\log\log N\) that theory is RH.

### The conceptual frame

**Ring Krein–Langer theory.** Extend the Weil kernel from dilations to the affine semigroup \(n\mapsto an+b\) of \(\mathbb Z\). Its dilation face is \(K_\zeta\), its successor face is the shells, and its boundary carries the archimedean place. Positivity of a kernel on a group is unitarity of a representation. The \(ax+b\) group has a very small unitary dual (Mackey). Positive-definite functions on it are therefore far more rigid than on \(\mathbb Q_{>0}^\times\), where Bochner allows every measure on the torus.

The corpus already shows the pitfall: the mixed Grams of one source are automatically positive and carry no arithmetic. The selective content must sit in the boundary, i.e. the escaped cells, where the archimedean place and the pole live.

### Risks

- The first-shell discrepancy for arbitrary coefficient vectors is a bilinear form with one prime variable. Its \(o(1)\) bound may be as hard as a twin-prime-type estimate.
- Highly composite successors may force the shell operator to be large. That is consistent with treating the shell exactly, but it makes the discrepancy bound harder.
- W06 and W07 decide quickly whether the shell, with its major arcs, is positive numerically.

### What it would open

- A positivity theory for the ring structure.
- A use for level-of-distribution technology inside Weil's form.
- A direct test of whether additive structure, and not only the pole, can select \(\zeta\).

## 2.6 Would the obstacles in 2.2 need a new field of mathematics?

**Assessment.**

- **Probably yes:** the RH-equivalent items (a), the finite-support stratum (c), the Lindelöf and quasi-RH levels (d), the producer I9, the index ceiling I10, gauge charge at \(0\) I19, and the geometric twin I20.
- **Probably reachable with existing tools:** I1–I3 at fixed \(c\), I7, I8, I12, I13, I15–I18, and the census items C1–C4 short of the parity barrier. These need operator theory, sieve and dispersion methods, and computation.

The corpus has built enough of the dictionary to describe what the new field must be.

### What it would be about

**The arithmetic gauge theory of the ring \(\mathbb Z\).** \(\mathbb Z\) carries two dual structures:

- the multiplicative one, whose dual is the gauge torus \(G=\widehat{\mathbb Q_{>0}^\times}\) with Haar measure;
- the additive one, whose dual is the circle and the finite additive characters.

They meet in three places: the archimedean boundary (the pole, the Gamma factor, the escaped dilation mass \(\log a\)), the finite gauge subgroups (Dirichlet characters, Gauss sums), and unique factorization (\(\Lambda*1=\log\)).

The field's central object is the point \(0\in G\). It is the one gauge point that is additively invariant, and it carries a pole. The central theorem to aim for: the additively invariant point is Haar-typical modulo its pole, for every gauge-charged statistic, at square-root precision. RH is the case of partial sums.

### What it would be like

Weil's proof transported to a ring without Frobenius. Over \(\mathbb F_q\), Frobenius \(x\mapsto x^q\) is a ring endomorphism, at once additive and multiplicative. Stepanov uses it to give an auxiliary multiplicity \(\sqrt q\) at every rational point, and the quadratic twist is a vertical shift, so the parity twin is geometric. \(\mathbb Z\) has no nontrivial ring endomorphism, and its Liouville twin is geometric only in the Bohr compactification. So the field must supply one of two substitutes:

1. an approximate ring endomorphism, i.e. a structure on a larger object (Bohr compactification, Witt vectors, an adelic affine group) that couples addition and multiplication with a fixed budget;
2. a positivity principle native to the ring, the affine Krein–Langer theory of 2.5, where additive structure pays.

Analytic number theory would verify local inputs and certify auxiliaries. Global signs would come from structure, because positivity at the limit is marginal and no estimate with a fixed loss survives.

### Objects

| Object | Role |
|---|---|
| Gauge torus \(G\), Haar measure, twists \(\Lambda\chi_x\) | Ambient space; typical behaviour |
| The special locus (Dirichlet characters \(\times\) vertical shifts) | The "algebraic points" |
| Twin tails | The "Liouville points": a comeager null exceptional set |
| Escape states as measures on \(G\) | Visibility of off-line energy |
| Weil kernel on dilations; its affine extension with shells and boundary cocycle | Positivity carriers |
| Successor shells \(n=km+j\) and near-incidences \(ab-cd=h\) | Gauge charge |
| Finite gauge subgroups and their stabilizers \(q\mid h\) | Major arcs; singular series |
| The two Liouville parity classes | The sets to be counted |
| Integer auxiliaries and their ledger \(\sum m_p\log p\le\log A\) | Producers |
| The Bohr compactification of vertical shifts | Home of a geometric parity twin |
| Atomic families in length–height coordinates | Where the crossing at bandwidth one happens |

### Language

- **Gauge-invariant**: equal on the whole orbit. **Gauge-charged**: mean zero over the orbit. **Boundary**: shift-fixed and archimedean.
- **Typical point**: one that satisfies every Haar-almost-sure law. **Special point**: one with additive structure. **Liouville point**: a twin tail.
- **Shell**, **repayment**, **marginal positivity** (zero margin in the limit).
- **Precision class**, **producer**, **certificate**, **multiplicity beyond divisibility**, **geometric parity twin**, **index ceiling**.

### Mechanisms it must build or discover

1. **A ring positivity principle.** Unitarity of an affine action with boundary, whose matrix coefficients include the Weil kernel and its shells.
2. **A repayment law.** How shells repay the \(-\log c\) loss of nonpolar conductors, organized by conductor \(q\mid j\).
3. **A Frobenius substitute.** A source of growing multiplicity at counted primes with a fixed size budget.
4. **A typicality theorem for special points.** Roth/Siegel style: contradiction from many approximations by Liouville points.
5. **An index ceiling.** A Riemann–Roch analogue bounding \(\kappa(K_\zeta)\) from the ring structure before any count.

### Questions it must answer

- What replaces \(x^q=x\) over \(\mathbb Z\)? At which points should an auxiliary vanish, and in what sense finer than divisibility?
- Is there a structure on which the Liouville twist acts geometrically? Its only possible home is the Bohr closure.
- What is the positive form of the affine Weil kernel, and is its boundary the pole?
- Which gauge-charged statistics have values at \(0\) determined by structure (\(\Lambda*1=\log\), singular series), and which are pure discrepancy?
- What is the Diophantine exponent of a gauge point, and is it \(\Theta\) at \(0\)?
- What replaces Riemann–Roch as an index ceiling?
- Why is positivity marginal at the limit, and which exact identity carries the zero margin?

### Tools to develop, with tests

| Tool | Purpose | Test |
|---|---|---|
| Shell calculus | Exact first and higher shells with major-arc decomposition | Reproduce positivity for \(c<c_*\); fail for the Liouville twin and \(\omega_{11}\); predict the sign at \(c=2\) |
| Affine Krein–Langer theory | Index of kernels on the affine semigroup with boundary | Mixed Grams of one source get index \(0\) and no arithmetic; the boundary separates twins |
| Point-side producer | Upper count for one parity class | Reproduce Stepanov over \(\mathbb F_q\); fail for twin tails; beat the sieve constant \(2\) or the binomial ledger |
| Typicality on \(G\) | Exponents of gauge points; special-point theorems | Haar-a.e. exponent \(\tfrac12\); Siegel and Deuring–Heilbronn as calibration |
| Index ceiling | Bound \(\kappa\) from ring data | Index \(\le\) genus over \(\mathbb F_q\); fail for the golden datum, Davenport–Heilbronn and over-regular Beurling systems |
| Dispersion inside Weil's form | Gauge charge at \(0\) averaged over moduli | Recover Bombieri–Vinogradov; fail for Haar-random twists' worst cases |

### Criteria it must meet

1. **Independence**: built from arithmetic data, never from zero-indexed objects.
2. **Fidelity**: all mixed entries, Gamma, both poles and multiplicities.
3. **Battery**: every sufficient hypothesis fails for the Liouville twin, all flips, cofinite flips, twin tails, \(\Lambda+\varepsilon n^{-\eta}\), \(\Lambda+1/n\), the golden datum, over-regular Beurling systems, Davenport–Heilbronn functions, and Haar-random gauge points where relevant.
4. **Two-source compliance**: selectivity from the pole or Gamma, or from gauge charge at \(0\); never from multiplicative data alone.
5. **Marginality**: a mechanism with zero margin in the limit (an identity), not an estimate with fixed loss.
6. **Calibration**: reproduce Weil over \(\mathbb F_q\) by counting, the \(2/3\) census, bounded-overlap positivity and the sharp gap.
7. **A new inequality**: a paid sign, ceiling, count or energy bound, not another equivalence.
8. **Formal closure**: unconditional Lean statements.

**First evidence of success.** Any one of:

- positivity at a fixed \(c\in[c_*,2]\) with the first shell treated as a source;
- an integer auxiliary with multiplicity \(\ge2\) on a positive proportion of the primes of \((x,2x]\) at size below twice their mass;
- any power-saving statement about gauge charge at the point \(0\) beyond its major arcs.
