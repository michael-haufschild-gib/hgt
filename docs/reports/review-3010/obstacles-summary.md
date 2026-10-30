# Research frontier: work, open problems and next questions

Status: 30 October 2026, corpus `a0e8154924` plus working tree. **RH remains open.**

**The pole and the shells pay every bounded overlap.** On atomic families the complete Weil matrix is positive at every fixed overlap \(c\), for every \(C^2\) profile without real Fourier zeros [L].

- Successor shells \(n=km+h\) enter through Ramanujan sums, which are the major arcs of gauge charge.
- Poisson summation on the successor lattice repays the overlap loss exactly.
- The margin is the positive Fourier tail \(E(c)=\frac2M\sum_k\frac1k\int_{kc}^\infty|\hat\varphi(2\pi t)|^2dt\), which tends to \(0\) by Stirling's formula.
- The arithmetic used is the prime number theorem in progressions to a fixed modulus.

**RH is the same positivity at growing overlap.** For \(C^2\) profiles the threshold is \(c_N^4\gg\log N\) [L]; for the Steklov profile it is an iterated logarithm [K]. RH is therefore a rate problem in an explicit window: the decaying margin against the errors.

**RH is an exponent at one special point.** The Möbius exponent is exactly \(1/2\) at Haar-almost every gauge point, equals \(\Theta\) at \(0\), and is never better than typical there. No gauge-invariant certificate gets below \(3/4\) [L].

**Over \(\mathbb Z\) there is still no producer.** Bézout and Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) are exact and linear. Small integer auxiliaries are divisible, and \(\mathbb Z\) has no Frobenius among its self-maps. The equation \(x^q=x\) lives on the gauge torus as the fixed points of the Adams operations [L].

Coverage: 32 live routes, 17 standalone candidates, PW-B.

Companions: [route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md) · [scoped obstructions](../rh-killed-routes.md). Research record: [working log](../../../logs/review-3010-research-2026-10-30.md).

| Label | Meaning |
|---|---|
| **[L]**, **[S]**, **[K]** | As in the frontier map. |
| **[Lean]** | Statement read; integration not assessed. |
| **[P]** | Paper proof only; not audited here. |
| **(inference)** | A conclusion of this review. |

## What the corpus establishes

- **Overlap window.**
  - Fixed-overlap positivity for every profile without real Fourier zeros [L]; uniform on bounded ranges for the tilted spline [K].
  - The low spectrum is the completed conductor spectrum, the pole is the ground state, and the bottom tends to \(E(c)\) [L]. Tilted spline: \(E_m(c)\ge C/c^7\) [K].
  - RH \(\iff\) positivity at \(c_N^4\gg\log N\) [L]. Steklov profile: RH at \(L(\log L)^2\log\log L\), \(L=\log\log N\) [K].
  - An existential unbounded positive schedule [L].
- **Shell mechanism [L].** Upward prime rows are affine prime windows with Ramanujan averages. Downward rows cancel near-Gamma through \(\Lambda*1=\log\). Möbius inversion turns shells into coprimality, and Poisson summation repays \(-\log c\).
- **Selectivity at bounded overlap.**
  - Every flip \(\omega_p\) at its own \(c_0(p)\); no fixed \(c\) rejects all flips [L].
  - The Liouville twin is negative at every \(c\ge1\) for a tilted box plateau [S].
- **Gauge torus [L].**
  - Typical exponent exactly \(1/2\); \(\theta_\mu(0)=\Theta\); RH \(\iff\) \(0\) is typical.
  - Exceptional set residual and null; twin tails have exponent \(1\).
  - No gauge-invariant certificate below \(3/4\); finitely determined certificates \(\ge1\).
  - Coherence: nonnegative statistics are maximal at \(0\), and the pole is coherence.
  - Antipode: \(S_N(\ell)+S_N(0)=2\psi(\sqrt N)\).
  - Special locus: Dirichlet points read GRH and are typical on average.
  - The Möbius escape state is an Euler product blind to zeros.
  - Twin inequality transfers strips [S].
- **Index theory.**
  - \(\kappa\) = number of right zeros; index zero = one-sided count = odd-class upper count [S].
  - Heights, towers, carriers, attained depth, waves [L/K/S].
  - Polar index for curve data [L]; local constituents have index \(0\) or \(\infty\) [S].
- **Precision.** Count stabilizer \(\mathcal Q\); tower positivity precision-exact; finite aperture cannot decide; one-signed perturbations; Chebyshev ledger [L/K/S].
- **Producers [L/K].** One ledger; Stepanov over \(\mathbb F_q\); Bézout and Riemann–Roch for \(\mathbb G_m(\mathbb Q)\); approximate vanishing = divisibility; factorial ratios bounded; twist tower collapses; ring endomorphisms classified; Adams operations.
- **Complete source.** Haar identities; finite index except the first prime layer; prefix Schur reduction and prefix index \(\le N-M\) [K].
- **Theta moments.** Rank seven strict; aperture-free center tails; seam Plancherel Gram; eighth section reduced to one odd tail form [L/K].
- **Heat, census, density.**
  - \(2/3\) horizon and localized dissipation.
  - \(HD(1)+10^{-8}\) and \(0.8876\); \(70\%\) dichotomy.
  - Guth–Maynard, DH, VK, Siegel.
  - No Siegel–Walfisz and no Bombieri–Vinogradov in the corpus.

## 2.1 Tasks that are just work

"Just work" means the ingredients exist. A sign task delivers a certified enclosure, a quantification or a transferred proof, never a guaranteed sign.

| ID | Task / deliverable | Serves | Boundary |
|---|---|---|---|
| W01 | **Formalize the growing-overlap paper cards** [P]: affine shell errors with polynomial harmonic bounds; small width keeps prime geometry polynomial; growing shell sources with logarithmic rates; affine prime shells with polynomial growth; harmonic quotient tail costs a logarithm; residue Mertens finite parts (Lean in progress). Deliverable: an explicit unconditional schedule \(c_N\to\infty\) for the tilted spline. | Q1; HF, SRT, AIP, ACS | Below the synthesis threshold; not RH. |
| W02 | **Siegel–Walfisz** in the corpus: PNT in progressions uniform in \(q\le(\log x)^A\), ineffective constants allowed, from the formalized Siegel theorem and a classical zero-free region. | W01, W03 | Standard. |
| W03 | **Conductor-uniform spectral assembly**: quasimodes, defect reserve and spectral counts for all conductors \(m\le M(c)\), with explicit dependence on \(c\), including near-degenerate energies \(E_m(c)\). | Q1 | The arithmetic Green inverse is not the Weil inverse. |
| W04 | **Tilted Steklov profile**: \(e^{\tau u}\)-tilt of the Steklov profile, \(\tau\) avoiding the countably many imaginary parts of its Fourier zeros. Prove no real Fourier zeros, Denjoy–Carleman log derivative bounds, unit mass and support normalization. One profile then carries fixed-\(c\) positivity and the iterated-log RH receiver. | Q1; SRT, HF | Hypotheses only; no new sign. |
| W05 | **Profile-adapted synthesis**: sharpen the tilted spline's receiver below \(c^4\gg\log N\) with quasi-interpolation that uses the profile's Fourier decay; express the threshold through \(E(c)\). | Q1 | Receiver, not sign. |
| W06 | **Model damage**: a zero configuration with \(\zeta\)'s density plus one off-line quartet; the minimal atomic energy as a function of \((c,N,\text{depth},\text{height})\), compared with \(E(c)\). | Q1 | Model, not \(\zeta\). |
| W07 | Asymptotics of \(E_m(c)\) and of the conductor gap as \(c\to\infty\) (upper and lower), for the tilted spline and tilted Steklov profiles. | Q1, Q3 | Fourier analysis. |
| W08 | **Flip thresholds**: explicit upper bounds on \(c_0(p)\), lower bounds on the survival threshold, the same for finite and cofinite flip sets and twin tails. | Q3 | Pole-mediated. |
| W09 | **Integrate working sources**: `TheLiouvilleTwinInequality`, `ResidueMertensFinitePartsHaveLogarithmicRates`, `PhysicalSuccessorMass`, `WeightedSuccessorReserve`, `ThetaCuspRadialCoefficients`, the modified `FixedOverlapPositivityIsSelectiveAgainstTheLiouvilleTwin`, `ChebyshevCyclotomicCompletion`, `SuccessorMixture`, `WeightedCenterTail`; remaining [S] modules of AKLT, HKT, ASRP, AID. | all | Integration only. |
| W10 | **Exponent calculus on \(G\)**: turn \(\mu^2=\sum_{d^2\mid n}\mu(d)\), \(\mu*1=\delta\), \(\Lambda*1=\log\), Liouville translation and Adams doubling into exponent inequalities. Record which points become better than typical under a supplied strip. | Q3; MC | Transfer, not production; its trivial fixed point is \(1\). |
| W11 | Bombieri–Vinogradov (the gauge-form large sieve exists). | Q1 if conductors exceed Siegel–Walfisz range; Q3 | Averages over moduli. |
| W12 | Full-index exhaustion at the Steklov schedule; remove the extra \(\log\log L\) factor. | SRT, HF | Receiver. |
| W13 | TH: certified evaluation of the aperture-free odd first-moment tail form and the seam-split constants; compact-center numerics at rank eight. | TH | No all-rank sign. |
| W14 | Haar branch: head sizes, first-layer constants, signed graph payment on computed ranges. | HF, ACS, AIP, CHMD | \(k=1\) stays [FS]. |
| W15 | Census: majorant bounds for \(E(\delta)\); constants in \(hE_h\le CN\); \(E_{\rm proj}\) on explicit near-line configurations. | ACS | Majorants are displacement-blind. |
| W16 | Heat: explicit \(N(t)\) on compact ranges; summed localized estimates on fixed height windows. | WD, LA | No uniform count. |
| W17 | Quasi-RH preprint: formalize its continuation step and extract the abscissa as a function of its inputs. | MC | Depends on the external argument. |
| W18 | Product-bias classification in Lean [P]. | WL, MC | Formalization. |
| W19 | Ledgers and finite rows for FU, RP, LI, TT, PA, MC, PM, CTF, JAS, RW, EWU, OWU, SZ, ACT, TG, RN, XN, GTA, BAG, HCF. | many | Local certificates. |
| W20 | Candidate calculations: cycle traces, curvatures, jets, contours, ports, stacks, cusp actions. | candidates | Calibration is not forcing. |
| W21 | **Filtration-window audit**: for each U2 route record the fixed-level positivity, its margin as an identity if one exists, and the RH-complete schedule. Import the Poisson-margin method where it applies. | Unification T | Bookkeeping and transfer. |
| W22 | **Adams–Stepanov calibration**: restate Stepanov's argument over \(\mathbb F_q\) with Frobenius as an Adams operation on characters of \(\mathbb F_q^\times\), so its \(\mathbb Z\) analogue can be posed exactly. | Q2 | Calibration. |
| W23 | Literature intake: Goldston–Montgomery; Selberg's short-interval mean value; Strang–Fix approximation; Roth's lemma and the subspace theorem; Deuring–Heilbronn; Rudolph–Johnson measure rigidity. | 2.4–2.6 | External proofs are not assumed. |

## 2.2 Open mathematical obstacles

### (a) RH-equivalent endpoints

| ID | Missing result | Routes |
|---|---|---|
| O1 | Critical signed cancellation in any currency: one-sided \(\psi\) count (\(=\kappa=0\)); odd-class upper count; lag energy; Abel moment; linear history floor; strict half-power; regularized convergence; extremal remainder; approximation residual; square-root budget; integrality halves; joint moment/sawtooth/Mertens control; first-clock tail; \(\theta_\mu(0)=1/2\). | WL, FU, CFC, RP, MC, LI, PBM, RB, JAS, CTF |
| O2 | Complete Weil positivity on an RH-complete schedule: tilted spline at \(2(\log N)^\alpha\), \(\alpha>1/4\); Steklov at the iterated log; complete-cell index zero; residual, odd, allocation or Hodge sign; tent families. | RW, HF, SZ, EWU, OWU, AIP, ACS, TT, CHMD, ACT, SRT |
| O3 | Positivity on one prime's towers for all generators. | HF, ACS, AIP, CHMD, SRT |
| O4 | All-degree, all-height heat, moment or coefficient signs; all ranks of the center hierarchy; the Cayley–Li ladder; both Gaussian grids. | PA, LA, TH, WD, HCF, LI |
| O5 | Positive gauge mass of every escape state; vanishing approximation error. | PM, CTF |
| O6 | Rank-uniform transverse decay; all-point recurrence; covering Newton discs; integer trace cap; directed renewal orientation. | GTA, BAG, XN, TG, RN |
| O7 | \(\mathcal E_{\rm crit}\) at most one quantum; cofinal work \(\le2\). | HF, SRT, ACS |

**Common content (inference).** Each of O1–O7 is the typicality of the gauge point \(0\) for a statistic that is neither gauge-invariant nor finitely determined, at square-root precision. Every U2 item O2–O7 is also positivity along a cofinal schedule of a resolution parameter.

### (b) Stronger than RH

| ID | Statement | Note |
|---|---|---|
| S1 | Abel-slope genus saturation; linear Mertens energy | RH plus simple zeros |
| S2 | Matching-profile signed pair surplus at the stated strength | Not implied by RH |

### (c) The finite-support stratum [FS]

| ID | Missing result | Routes |
|---|---|---|
| F1 | Uniform finite index of the complete form (first prime layer against Gamma) | HF, ACS, AIP |
| F2 | Finite \(\mathcal E_{\rm crit}\); bounded source work; subquantum annular increment | HF, SRT, ACS |
| F3 | Subtracted lag bounded on one side | WL |
| F4 | Bounded nonreal counts of \(H_t\) as \(t\downarrow0\) | WD, LA |
| F5 | Bounded cosine defects | WD |
| F6 | Bounded index on a two-prime lattice; finite wave number | ACS, AKLT |

Finite support makes almost every prime tower decide. **Verdict: not a near-term target.** An argument giving finite index without LH-strength input is wrong.

### (d) Lindelöf and quasi-RH levels

| ID | Missing result | Status |
|---|---|---|
| L0 | Zeros approach the line | Implies LH and \(\Theta<1\). |
| L1 | LH | Open; \(\mu(1/2)\le13/84\). |
| Q0 | A fixed zero-free strip \(\Theta<1\) in any dictionary | External claim at \(7/8\) for Dirichlet \(L\) [E]. Density envelopes never reach it. |
| Q1′ | Any \(0\)-specific, non-gauge-invariant inequality improving \(\theta_\mu(0)\) below \(1\) | Equivalent to Q0. |

### (e) Census

| ID | Missing result | Payoff |
|---|---|---|
| C1 | \(E(1/9)\le4\): two-sided coalescent pair estimate at bandwidth \(10/9\) | \(70\%\) |
| C2 | Prime surplus \(\le N/18\) at bandwidth \(4/3\) | \(75\%\) |
| C3 | Positive census-scale lower bound for \(E_{\rm proj}\) | \(70\%\) |
| C4 | Displacement-sensitive shallow energy \(hE_h+R_{\rm deep}\le\tfrac3{20}N\) | \(70\%\) |

### (f) Intermediate open problems

| ID | Missing result | Why current work stops | Payoff |
|---|---|---|---|
| I1 | **Window positivity below the synthesis threshold**, with an explicit rate, for one profile | Fixed-\(c\) limits are qualitative. The rate needs uniformity in \(c\) and in conductors \(m\lesssim c\) (W01–W03), and the analytic residuals may cost a logarithm | The first Weil positivity at growing resolution |
| I2 | **The location of the RH transition** inside the window | Receivers come from synthesis (\(c^4\gg\log N\)), not from the margin \(E(c)\); the damage of one off-line zero is bounded only above | Whether RH lives on one critical curve |
| I3 | **Uniform selectivity**: a growing schedule rejecting every flip, cofinite flip and twin tail; a resolution–distance law | \(c_0(p)\to\infty\); thresholds are not quantified | Selectivity at the rate RH needs |
| I4 | Exterior tightness | Record minima permit zero gauge mass | PM short of O5 |
| I5 | Conductor/forcing compatibility | No common aperture range | OWU detection |
| I6 | **Point-side producer over \(\mathbb Z\)** | Divisibility is parity-blind; no self-map Frobenius; small = divisible | The Frobenius substitute |
| I7 | Arithmetic index ceiling | Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) is linear; a positive part never pays a pair | Finite support, then towers |
| I8 | Independent constructions for each candidate | Calibrations; zero-indexed objects | Promotion |
| I9 | Extraction of the external \(7/8\) threshold | Not formalized (W17) | A conditional strip |
| I10 | Many-node Gram floor from two-prime phase separation | Baker bounds degenerate as \(\Delta\to0\) | HCF, SRT without aliasing |
| I11 | Tower detection at unattained depth | Attainment is used | The tower Hasse principle |
| I12 | **Gauge charge at \(0\) beyond major arcs** | Not needed at fixed overlap; its role in the window is unknown | A point-\(0\)-specific input |
| I13 | Geometric parity twin over \(\mathbb Z\) | Only the Bohr closure; Adams operations fix \(0\) | A twist tower over \(\mathbb Z\) |
| I14 | Compact-center compensation of the rank-eight odd block (TH) | Tails positive, center middle region unpaid | TH rank eight |
| I15 | Haar-branch joint payment of the non-arithmetic Gamma graph and signed diagonal | No positivity of \(V_X\) | Complete-cell index |
| I16 | A characteristic-zero surface whose sections count quadratically | Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) is linear | A Hodge index from ring structure |

**What the open items share (inference).**

- The pole, Gamma and the shells' major arcs pay every bounded resolution.
- Every RH-strength item needs information at the point \(0\) that is neither gauge-invariant nor finitely determined, at square-root precision, or a structure producing it.
- Over \(\mathbb F_q\) both come from one ring endomorphism. Over \(\mathbb Z\) the only candidate home is the gauge torus, whose Adams operations fix \(0\).

## 2.3 The three questions to answer next

<a id="q1"></a>
### Q1. Where inside the overlap window does atomic Weil positivity become RH, and how far can unconditional positivity be pushed toward it?

**Exact object.** The complete Weil matrix \(W(\varphi,c,N)\) of one profile on atoms of width \(c/N\), with every prime power, Gamma and both poles.

**Proved.**

- Positivity at every fixed \(c\), with bottom eigenvalue \(\to E(c)\) [L].
- The margin is an exact Poisson remainder [L], at least \(C/c^7\) for the tilted spline [K].
- RH \(\iff\) positivity once \(c_N^4\gg\log N\) [L].
- One off-line zero weighs \(O(c)\) per unit synthesized mass [L].

**Open.** The schedule at which positivity stops being a fixed-modulus theorem and starts to see zeros.

**Why now.**

- This is the only RH-equivalent family where positivity is a theorem at every level of the filtration, with an exact margin.
- Its arithmetic at fixed \(c\) is linear and of fixed modulus. For \(c\le(\log N)^A\) the moduli stay in the Siegel–Walfisz range, so arithmetic error terms are of size \(\exp(-C\sqrt{\log N})\) (inference).
- The obstruction must therefore lie in analytic residuals. The likely candidates are the top-row boundary layer of harmonic mass \(O(1/\log N)\) and the near-degenerate conductor spectrum.

**Heuristic (inference).** Harmonic averaging of an off-line zero's contribution over the upward rows gives relative size \(\asymp1/\log N\). The top-row boundary layer has the same size. If so, the transition is the critical curve \(E(c_N)\log N\asymp1\): \(c\asymp(\log N)^{1/7}\) for the tilted spline, and an iterated logarithm for tilted Steklov.

**First useful answers.**

1. An explicit unconditional schedule (W01–W03).
2. The tilted Steklov window (W04).
3. A sharpened receiver in terms of \(E(c)\) (W05).
4. The model damage law (W06).

**Payoff.** Either the window narrows to one critical curve, or a gap persists and its arithmetic content is identified exactly. Every proved rung is a new theorem of Weil positivity at growing resolution. If damage depends on depth and height in a controlled way, each rung also excludes a region of off-line zeros.

**Risks.** Polynomial losses in \(c\) may stop the unconditional side at \((\log N)^{\delta}\) with \(\delta\) far below the receiver. The \(1/\log N\) residual may be intrinsic, in which case the window cannot close by estimates.

<a id="q2"></a>
### Q2. Can the Adams operations of the gauge torus play the role of Frobenius in a Stepanov producer, once coupled to additive structure?

**Exact object.**

- The \(\psi^q\)-fixed points of the gauge torus are the \((q-1)\)-torsion twists, and \(\psi^2\) fixes only \(0\) [L].
- RH \(\iff\) the odd Liouville class has an upper count [S].
- Producers obey \(\sum m_p\log p\le\log A\) [L].

**What is excluded [L].**

- Self-maps of \(\mathbb Z\) as Frobenius.
- Binomials and factorial ratios: bounded multiplicity above the square root.
- "Small" integer auxiliaries: they are divisible.
- Bézout–Riemann–Roch: linear, so vanishing at all primes up to \(y\) costs length \(e^{\theta(y)}\).
- Any auxiliary built covariantly from multiplicative data: twin-blind and gauge-invariant, hence \(\ge3/4\) at \(0\).

**Why now.** The corpus has just located \(x^q=x\) on characters, and the zero estimate (Bézout) and dimension count (Riemann–Roch) for Dirichlet polynomials are proved. Over \(\mathbb F_q\), Stepanov's auxiliary works because Frobenius makes vanishing at the rational points cheap: the conditions are linear in the auxiliary and shared by all points through \(x^q=x\). The question is whether an auxiliary function on \(G\) can be made to vanish cheaply on \(\psi^q\)-fixed points through \(\psi^q\). It must also break gauge invariance through an additive input, such as \(\Lambda*1=\log\), the successor shells or the functional equation.

**First rungs.**

1. W22: Stepanov over \(\mathbb F_q\) rewritten in Adams language.
2. Over \(\mathbb Z\), an auxiliary with multiplicity \(\ge2\) on a positive proportion of the primes of \((x,2x]\) at size \(<2\sum\log p\).
3. An auxiliary beating the sieve parity constant \(2\) on \(x^\varepsilon\) intervals.
4. Or a formal no-go: every Adams-built auxiliary with only multiplicative input is gauge-covariant, hence certifies nothing at \(0\) below \(3/4\).

**Payoff.** A mechanism that produces counts, or the exact statement that a producer must live on a larger object than the gauge torus.

<a id="q3"></a>
### Q3. How much overlap does Weil positivity need to distinguish a gauge point from \(0\)?

**Exact object.** For a twist \(x\) (a flip set, a twin tail, the Liouville point, a vertical shift), let \(c_0(x)\) be the least overlap beyond which the complete form of \(\Lambda\chi_x\) is eventually not positive while \(\zeta\)'s stays positive.

**Proved.**

- \(c_0(\ell)\le1\) for the Liouville point [S].
- \(c_0(\omega_p)<\infty\) for every \(p\), with \(c_0(\omega_p)\to\infty\) [L].
- Twin tails have Möbius exponent \(1\) [L]; vertical shifts have exponent \(\Theta\) [L].

**Heuristic (inference).** A flip's negative contribution per unit norm is \(\approx-4\log p/p\), and the margin is \(\approx E(c)\). So \(c_0(\omega_p)\asymp(p/\log p)^{1/7}\) for the tilted spline.

**Why now.**

- The window of Q1 and the exponent theory meet here: overlap is resolution on the gauge torus.
- The flip computation is explicit.
- RH asks whether an off-line zero makes \(0\) itself look like a point at positive distance at some resolution \(c_N\) within the window.

**First useful answers.**

1. Quantitative \(c_0\) for single flips, finite flip sets and twin tails (W08).
2. The dependence of \(c_0\) on the gauge distance and on the exponent of \(x\).
3. Whether uniform rejection of all flips with \(p\le P\) forces \(c_N\) into the RH window.

**Payoff.** A resolution–distance law joining the gauge exponent (Wall 1) to the overlap window (Wall 3). It would also supply the "approximation" notion that a Roth-type argument (2.4) needs.

**Why these three.**

- Q1 asks how far the solved bounded-overlap mechanism reaches toward RH, and where zeros enter.
- Q2 asks for the producer that no positivity mechanism supplies.
- Q3 asks how the special point is resolved, which links the two and feeds the one route of a different form.

They are three faces of one fact: the pole, Gamma and major arcs pay every bounded resolution, and the remaining input is \(0\)-specific information at square-root precision.

## 2.4 Is there a wildly different route?

**Verdict: no route can avoid the content of Wall 1.** That content is now a set of theorems:

- pointwise-closed statements are twin-blind;
- gauge-invariant certificates give \(\ge3/4\) at \(0\), and finitely determined ones give \(\ge1\);
- finite aperture cannot decide;
- anything implying the count rejects the Liouville twin.

Any proof must certify, at the special point \(0\), a statement that is neither gauge-invariant nor finitely determined, at square-root precision.

Routes can differ in **logic**. All live routes and candidates use one of three logics:

- positivity of a form along a filtration (Wall 3);
- counting by a producer (Wall 14);
- realization of an operator or limit (Wall 14).

One logic is used by none of them: **contradiction from approximations**, the logic of Thue–Siegel–Roth and of Siegel's class-number theorem. It is the one wildly different route the corpus supports.

### Candidate: Roth-type typicality of the special point

**The analogy is now exact at the level of the dictionary [L].**

| Real line | Gauge torus \(G\) |
|---|---|
| Irrationality exponent, a.e. value \(2\) | Möbius exponent, a.e. value exactly \(1/2\) |
| Liouville numbers: residual and null | Twin tails: exponent \(1\); exceptional set residual and null |
| Algebraic numbers (special points) | The special locus: Dirichlet points \(\times\) vertical shifts; \(0\) is the additively invariant point |
| Roth: algebraic numbers are typical | RH: \(0\) is typical; GRH: every Dirichlet point is typical |
| Height of a rational | Conductor of a Dirichlet point, length of a Dirichlet polynomial |
| Siegel's lemma; zero estimate (Roth's lemma); Liouville inequality | Siegel's lemma for integer Dirichlet polynomials [S]; Bézout for \(\mathbb G_m(\mathbb Q)\) [K]; approximate vanishing = divisibility [L]; the integrality lattice \(\operatorname{lcm}(1,\dots,N)^{-1}\mathbb Z\) [S] |

**What the route would be.**

1. **Approximations.** Assume \(\Theta=\tfrac12+d\), \(d>0\). Derive many good approximations to \(0\) of bounded complexity. Candidates:
   - gauge points of bounded conductor and height at which twisted Möbius sums are simultaneously large (the exponent is constant on the class of \(0\) [L]);
   - an overlap \(c_0(0)<\infty\) at which \(\zeta\) resolves like a twin (Q3).
2. **Auxiliary.** An integer Dirichlet polynomial in several variables, built by Siegel's lemma to vanish to high order at those approximations. Cheapness must come from a \(0\)-specific identity: \(\Lambda*1=\log\), the functional equation, or the Poisson repayment of the shells.
3. **Non-vanishing.** A multi-variable zero estimate extending Bézout for \(\mathbb G_m(\mathbb Q)\).
4. **Integrality.** Small and nonzero contradicts \(\operatorname{lcm}\)-integrality.

**Why it is far from every current route.**

- It signs no form, so it meets Wall 1 only as a selectivity requirement.
- It exhausts no filtration, so it does not face Wall 3. Roth needs no uniformity, and the proof may be ineffective.
- It needs no producer of counts, only an auxiliary that is small at hypothetical approximations. This is Wall 14 in a weaker form: vanishing at finitely many approximation points instead of at all primes.

**Ladder.**

- The trivial (Liouville-type) bound is \(\Theta\le1\).
- A Thue-type improvement at \(0\) would be a strip [≥QRH].
- A Roth-type sharp exponent would be RH.

**What would kill it.**

- If an off-line zero forces no approximation beyond the class of \(0\) (finite modifications and vertical shifts) itself, there is nothing to evaluate at.
- If every auxiliary vanishing at those points is gauge-covariant, it is \(\ge3/4\) at \(0\).
- Over \(\mathbb Z\), small integer auxiliaries are divisible [L], so the auxiliary must gain from multiplicity, not from smallness.

**First tests.**

1. Recover Siegel's \(L(1,\chi)\gg_\varepsilon q^{-\varepsilon}\), or Deuring–Heilbronn, in gauge-torus language as calibration.
2. Prove that an off-line zero forces a quantitative \(c_0(0)\) (Q3).
3. Build the one-variable auxiliary for a toy exponent problem on the special locus.

### Mechanisms examined and where they re-enter

| Mechanism | Re-entry |
|---|---|
| Deligne-style averaging over a family | The natural family \(G\) is infinite-dimensional. Its finite-dimensional special locus is typical only on average (large sieve) [L]. Localizing at one point needs a finite-dimensional family with cohomology: Wall 14. |
| Measure rigidity under the Adams semigroup (\(\times p\times q\)) | \(\psi^k\) fixes \(0\), so rigidity yields almost-sure statements only. The Möbius escape state is an Euler product blind to zeros [L]. |
| Exponent bootstrap from convolution identities | Trivial fixed point \(1\). It transfers strips between points (twin inequality [S]) and does not produce one. First rung = QRH. |
| Newton polygons (Goss–Sheats RH in characteristic \(p\)) | Archimedean Newton polygons see moduli of zeros, not arguments. |
| Jessen functions, amoebas, Bohr–Jessen | See zero densities only; density never forces vanishing [L]. |
| Fourier quasicrystals (Kurasov–Sarnak, Olevskii–Ulanovskii) | Classification presupposes real support; the archimedean density breaks discreteness. |
| Signature or index theorems computing \(\kappa\) from local data | Local constituents have index \(0\) or \(\infty\) and do not sum [S/L]. The archimedean off-axis constituent returns the problem to HF and ACS. |
| Coefficient criteria (Hutchinson, Laguerre–Pólya) | Coefficient ratios of order-one functions tend to \(1\); the LA route. |
| Lee–Yang, Bost–Connes, Hilbert–Pólya | Realization: W1C, PTR, Wall 14. |
| Index-continuity deformation of \(\zeta\) | \(\Lambda_{\rm dBN}\ge0\) blocks openness at \(\zeta\); closedness needs realization. |
| Level of distribution, dispersion, Kloosterman sums | Gauge charge averaged over moduli: Q3 and I12. |

## 2.5 Where a real breakthrough on the hard questions could come from

**Thesis: Weil positivity has just been proved by an identity at every bounded resolution. The breakthrough is to carry that identity, not an estimate, into the critical scaling where RH lives.**

### What the corpus now knows about positivity

- **Mechanism.** At fixed overlap, positivity is Poisson summation of the profile's autocorrelation on the successor lattice, completed by Stirling's formula. The shells' Ramanujan weights collapse to coprimality, and every conductor energy becomes \(\int|\hat\varphi|^2\) over a tail: a Bochner-positive object.
- **Selectivity.** It is pole-mediated and per twin. The Liouville point is the antipode and loses by the sign of the pole. Each flip loses beyond \(c_0(p)\).
- **Marginality.** The margin \(E(c)\to0\) is an identity. No estimate with a fixed loss survives the limit.

### Target theorem: a Poisson–Weil decomposition at growing overlap

For one profile and a schedule \(c_N\) up to the critical curve, prove
\[
W(\varphi,c_N,N)=\mathcal P(c_N,N)+\mathcal Z(c_N,N),
\]
where:

- \(\mathcal P\) is an explicit positive operator: the Poisson remainders of all conductors \(m\lesssim c_N\), with their exact energies \(E_m(c_N)\), plus the archimedean zero-density term that makes fixed-\(c\) positivity work (the tempered single-pair model fails exactly because it lacks this term [S]);
- \(\mathcal Z\) is identified exactly through the explicit formula as the residual zero term, with norm \(o(E(c_N))\) on an RH-complete schedule.

**Why it is a breakthrough target, not a restatement.**

1. **It is exact where it is proved.** At fixed \(c\), \(\mathcal P\) is the completed conductor spectrum and \(\mathcal Z\to0\).
2. **It is selective by construction.** Twins lose the pole's sign, and flips lose at \(c_0(p)\).
3. **It converts residuals into terms.** The \(O(1/\log N)\) residuals become part of \(\mathcal P\) or \(\mathcal Z\). If the top-row boundary layer and the on-line zero density are one positive object, then the margin at the critical scale is not \(E(c)\) alone but \(E(c)\) plus that object (inference).
4. **It is graded.** Each schedule \(c_N\) proved is a theorem, and each one should exclude a region of off-line zeros once the damage law (W06) is known. Weil positivity would become a machine for zero-free regions: a high-dimensional relative of the \(3+4\cos\theta+\cos2\theta\ge0\) argument, the one classical positivity proof of zero-free regions.

### A second opportunity: one Poisson structure for theta and atomic positivity

- **Theta side.** The seam tail is a Plancherel Gram at every order, and center tails are aperture-free [L/K].
- **Atomic side.** The margin is a Poisson remainder of \(|\hat\varphi|^2\) [L].
- **Common structure.** Both positive objects are squares of Fourier transforms, produced by Poisson summation on \(\mathbb Z\). That is the additive side, where the shells live (inference).
- **Bridge to try.** TH's open middle region, compact-center compensation at rank eight, is the theta analogue of the atomic window. A Poisson-remainder identity for the center hierarchy would be the theta form of the shell repayment law.

### Risks

- \(\mathcal Z\) may be genuinely of order \(1/\log N\) with no sign. Then the window closes only by an RH-strength input, and the decomposition has located it exactly.
- Near-degenerate conductor energies at growing \(c\) may require level-of-distribution inputs (Bombieri–Vinogradov), which are averaged and not point-specific.

## 2.6 Would the obstacles in 2.2 need a new field of mathematics?

**Assessment.**

- **Probably yes:** (a) the RH-equivalent endpoints; (c) the finite-support stratum; (d) Lindelöf and QRH; I6 producer; I7 index ceiling; I12 gauge charge at \(0\); I13 geometric parity twin; I16 the quadratic surface.
- **Probably reachable with existing tools:** I1 (window positivity below the threshold), I3 (flip thresholds), I4, I5, I9–I11, I14, I15, and C1–C4 short of the parity barrier. These need quantitative analytic number theory (Siegel–Walfisz, mean values, sieve), operator theory and computation.
- **Undecided:** I2 (location of the RH transition). It is a computation if the transition is a clean critical curve. It needs new structure if the zero term \(\mathcal Z\) has no sign.

### What the field would be about

**The arithmetic harmonic analysis of the ring \(\mathbb Z\) at critical resolution.** \(\mathbb Z\) carries two dual structures:

- the multiplicative dual, the gauge torus \(G\) with Haar measure, Adams operations and the special locus;
- the additive dual, the circle, Ramanujan sums and Poisson summation on lattices.

They meet in four places:

- the archimedean boundary (pole, Gamma, Stirling);
- the finite gauge subgroups (Dirichlet characters, Ramanujan sums = major arcs);
- unique factorization (\(\Lambda*1=\log\));
- the successor shells, where Poisson summation turns additive structure into a positive Fourier tail.

**Central object.** The point \(0\in G\): the unique additively invariant gauge point, the unique fixed point of \(\psi^2\), and the carrier of the pole.

**Central theorems to aim for.**

- \(0\) is typical modulo its pole for every statistic that is neither gauge-invariant nor finitely determined.
- Weil positivity persists at every resolution up to the critical one, by an identity.

### What it would be like

Weil's proof for curves, transported to a ring without Frobenius, with the archimedean place as a full participant.

Over \(\mathbb F_q\) one endomorphism does three jobs:

- it makes the parity twin geometric (the quadratic twist is a vertical shift);
- it makes vanishing cheap (Stepanov);
- it makes the Euler characteristic quadratic (the Hodge index on \(C\times C\)).

Over \(\mathbb Z\) the corpus has shown that none of the three is available on \(\mathbb Z\) itself:

- the twin is geometric only in the Bohr closure;
- small auxiliaries are divisible and ring endomorphisms are trivial;
- Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) is linear.

The field must supply the three jobs from three different structures:

- the Adams operations on characters, for cheap vanishing;
- Poisson summation on the successor lattice, for positivity across shells (already working at bounded resolution);
- a still-unknown two-dimensional object, for a quadratic count.

### Criteria it must meet

1. **Independence.** Built from arithmetic data, never from zero-indexed objects.
2. **Fidelity.** All mixed entries, Gamma, both poles, multiplicities.
3. **Battery.** Every sufficient hypothesis fails for the Liouville twin, every flip, cofinite flips, twin tails, \(\Lambda+\varepsilon n^{-\eta}\), \(\Lambda+1/n\), the golden datum, over-regular Beurling systems, Davenport–Heilbronn functions, and Haar-random gauge points.
4. **Point specificity.** Its decisive input is neither gauge-invariant nor finitely determined, and uses \(0\)'s additive invariance or its pole.
5. **Marginality.** At the critical resolution it works by identity, as the Poisson repayment does at bounded resolution.
6. **Calibration.**
   - Reproduce Weil over \(\mathbb F_q\) by counting.
   - Reproduce bounded-overlap positivity, the per-flip thresholds and the \(2/3\) census.
   - Recover Siegel's theorem as a typicality statement.
7. **A new inequality.** A paid sign, count, exponent bound or ceiling, not another equivalence.
8. **Formal closure.** Unconditional Lean statements.

### Questions it must answer

- What replaces \(x^q=x\)? Can vanishing at the \(\psi^q\)-fixed points of \(G\) be made cheap, and how does an additive input break gauge covariance?
- Is the RH transition in the overlap window a single critical curve? What exact identity governs it?
- What is the two-dimensional object whose sections count quadratically, so that a Hodge index exists over \(\mathbb Z\)?
- How does overlap resolve gauge points: what is the resolution–distance law, and does an off-line zero make \(0\) resolvable from itself?
- Which statistics have \(0\)-values fixed by structure (pole, \(\Lambda*1=\log\), Poisson remainders, singular series), and which are pure discrepancy?
- What replaces Riemann–Roch as an index ceiling, given that local constituents have index \(0\) or \(\infty\)?

### Objects and language

| Object | Role |
|---|---|
| Gauge torus \(G\), Haar measure, Adams operations \(\psi^k\) | Ambient space; typicality; \(x^q=x\) on characters |
| Special locus; twin tails | "Algebraic" points; "Liouville" points |
| Gauge exponent \(\theta_a(x)\) | Diophantine invariant; RH = \(\theta_\mu(0)=1/2\) |
| Successor lattice and Poisson remainders \(E_m(c)\) | Positivity from additive structure |
| Ramanujan sums / finite gauge subgroups | Major arcs |
| Atomic families in length–height coordinates; overlap = resolution | The filtration on which RH is a rate |
| Integer Dirichlet polynomials, Frobenius progressions, Bézout and Riemann–Roch of \(\mathbb G_m(\mathbb Q)\) | Auxiliaries and their zero estimates |
| The two Liouville parity classes | The sets to be counted |
| Krein–Langer index, waves, polar classes | What a ceiling must bound |

**Language.**

- **Gauge-invariant / gauge-charged / boundary.**
- **Typical, special and Liouville points.**
- **Resolution, margin, critical curve, damage.**
- **Repayment by Poisson.**
- **Producer, multiplicity beyond divisibility, Adams vanishing.**
- **Index ceiling, quadratic count.**

### Tools to develop, with tests

| Tool | Purpose | Test |
|---|---|---|
| Critical-window calculus | Margin, damage and residual at growing overlap | Reproduce fixed-\(c\) positivity; predict \(c_0(p)\); place the Steklov receiver |
| Poisson–Weil decomposition | Exact positive part plus zero term | Exact at fixed \(c\); selective against twins |
| Exponent theory on \(G\) | Typicality of special points | Haar value \(1/2\); \(\Theta\) at \(0\); Siegel as calibration |
| Adams–Stepanov producer | Cheap vanishing on torsion twists | Reproduce Stepanov over \(\mathbb F_q\); beat the binomial ledger |
| Resolution–distance law | Overlap needed to resolve \(x\) from \(0\) | Flips, twin tails, Liouville point |
| Quadratic count | Hodge index over \(\mathbb Z\) | Over \(\mathbb F_q\) it is \(C\times C\); fail for the golden datum |

**First evidence of success.** Any one of:

- unconditional complete Weil positivity along an explicit schedule \(c_N\to\infty\);
- a profile whose RH receiver is expressed through its margin \(E(c)\);
- an auxiliary with multiplicity \(\ge2\) on a positive proportion of the primes of \((x,2x]\) at size below twice their mass;
- any \(0\)-specific exponent inequality below \(1\).
