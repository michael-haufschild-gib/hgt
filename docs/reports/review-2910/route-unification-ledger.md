# Route-unification ledger

Status: 29 October 2026, corpus HEAD `718f741cc7` plus working tree. **The 32 live routes, 17 candidates and PW-B are faces of three core problems:**

- **U1**, the selective critical sign;
- **U2**, source-complete positivity;
- **U3**, an independent producer.

Eight facts bind them:

1. **Selectivity has two sources [L].** One is the shift-fixed pole and Gamma terms. The other is gauge charge, which enters only through non-ratio lags, i.e. additive structure. Multiplicative data are shared by the whole gauge orbit, Liouville twin and flips included.
2. **Every RH-strength problem is the typicality of one gauge point [L + inference].** Haar-almost every twist of \(\Lambda\) already satisfies every square-root law. RH says that the point \(0\) is typical modulo its pole.
3. **U1 and U2 are one endpoint [S].** Index zero of the Weil kernel is the one-sided \(\psi\) count, and already the upper count of one parity class. U3 is the search for a producer of that count.
4. **Hecke towers join U1 and U2 entry by entry [L].** Cross-level entries are prime-error sequences, and one prime's tower positivity is RH.
5. **One coordinate [K].** Overlap is length/height, and bandwidth is \(\log(\text{length})/\log(\text{height})\). Atomic overlap growth (U2) and the census beyond bandwidth one sit on the same axis, at the crossing length \(\approx\) height.
6. **The finite-support stratum is one statement [S/L].** It is RH above a height, and it contains LH.
7. **Locality and pointwise closure are twin-blind [L].**
8. **Every producer obeys one ledger [L].** Over \(\mathbb F_q\), Frobenius gives growing multiplicity. Over \(\mathbb Z\), divisibility gives linear precision and cannot see parity.

Links: [route obstacles](route-obstacles.md) · [summary and priorities](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [frontier map](../rh-current-frontier-map.md). Evidence comes from corpus searches and Lean statements; no builds were run.

Labels:

| Label | Meaning |
|---|---|
| **[L]**, **[S]**, **[K]** | As in the frontier map. |
| **(inference)** | A conclusion of this review. |

[Working log](../../../logs/review-2910c-research-2026-10-29.md).

## What "the same problem" means

| Relation | Meaning | What it does not mean |
|---|---|---|
| **E — Endpoint equivalence** | Two stated conditions are both equivalent to RH, or to each other. | A usable estimate between the producers. |
| **T — Proved source transfer** | An identity, approximation or inequality carries the actual source from one formulation to another. | Extension to growing supports, overlap, primes, degrees or another norm. |
| **S — Structural similarity** | Two approaches face the same kind of sign, exhaustion or faithfulness problem. | A theorem identifying their objects. |

All RH criteria are E-equivalent almost tautologically. Unification is meaningful through T-bridges and through a shared unproved producer.

## The three core problems

| Problem | The one missing statement | Faces (routes) | Wall |
|---|---|---|---|
| **U1 — Selective critical sign** | A bound on the actual signed prime/Möbius discrepancy at the critical scale, in some currency: one-sided count, one parity class, history floor, integrality half, Chebyshev ledger, first-clock tail. In gauge language, the partial-sum statistic is typical at \(0\). | WL, FU, CFC, RP, MC, LI, PM, JAS, CTF, PBM, RB. Also the prime-error faces of HF, SRT and AIP, and, via the Chebyshev identity, the off-diagonal of every U2 route. | 1 |
| **U2 — Source-complete positivity** | Index zero of the complete Weil form, with Gamma and both poles, on a source-complete family. On atomic families this is positivity under overlap growth, i.e. across the successor shells up to \(L(\log L)^2\log\log L\). | RW, TT, HF, CHMD, SZ, EWU, OWU, SRT, ACT, AIP, ACS, HCF; through sign receivers, also PA, LA, TH, WD. | 1 and 3 |
| **U3 — Independent producer** | A source-built structure whose proved property supplies the U1 count or U2 index zero. Over \(\mathbb Z\) it must vanish finer than divisibility, or give the twin a geometric home, or give an index ceiling. | TG, RN, XN, BAG, GTA; all 17 candidates and PW-B; the geometric faces of HF and ACS; the Stepanov question. | 14 |

**Cross-cutting requirements on every producer.**

| Requirement | Status | Test object |
|---|---|---|
| Selectivity | Theorem [L] | The Liouville twin, \(c\Lambda\) and quadratic mixtures fail. |
| Beyond the margin | Theorem [L/S] | Single flips share the maximal gap; \(\omega_{11}\) fails at fixed ratio [S]; cofinite flips have gap \(0\). |
| Two-source compliance | Theorem [L] | Pointwise-closed, shift-invariant statements are twin-blind. A selective input uses the pole or Gamma, or gauge charge. |
| Point-0 specificity | Theorem [L] | Haar-random gauge points satisfy every multiplicative and almost-sure law. The input must distinguish \(0\) from them. |
| Parity | Theorem [S] | Deciding-input theorem: any count-implying property rejects the Liouville twin. |
| Precision | Theorem [L/S] | \(\Lambda+\varepsilon n^{-\eta}\) fails; for positivity statements, \(\Lambda+1/n\) fails too. |
| Two primes | Theorem [S] | One prime aliases; the golden curve passes its tower and fails the lattice. |
| Unbounded overlap or aperture | Theorem [K] + inference | Finite aperture reads finitely many weights and cannot decide. Bounded overlap is not known to be RH-complete. |
| Marginality | Inference from [L/S] and external | No uniform floor in the limit, so the input must have zero margin there. |
| Point side | Theorem [S/L] + inference | Zero-side annihilation certifies nothing. Divisibility cannot select parity. |

## Strongest unifications

### A. U1 and U2 meet entry by entry (T)

For \(\operatorname{supp}f<b<\operatorname{supp}g\): \(W(f,g)=-\int_0^\infty(e^h-\psi(e^h)-c)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g)\). On the pole hyperplane only the prime comb remains. WL, FU, RP, PBM and CFC ask for the same signed quantity as HF, ACS, AIP, RW and OWU, in different test norms. [Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean).

### B. The endpoint: positivity = index = count = one parity class (E, with an S-bridge to \(\mathbb F_q\))

| Language | Statement | Route |
|---|---|---|
| Count | \(\psi(x)-x\le C\sqrt x\log^2x\) eventually, either sign | WL, MC |
| Parity class | \(\sum_{\lambda(n)=-1}e^{-nt}/n\le\tfrac12(\sum e^{-nt}/n+Ct^{1/2-\varepsilon})\) | MC, WL |
| Chebyshev ledger | Joint square-root control of the Möbius moments, the sawtooth and Mertens | WL, MC |
| Integrality | Each half of integer-polynomial integrality at square-root scale | MC, WL |
| Index | \(\kappa(K_\zeta)=0\) | HKT, HF, ACS |
| Positivity | Integer-atom Grams; atomic positivity at the RH overlap | SRT, AIP, HF |
| Gauge | \(0\) is typical modulo its pole | MC, PM, BAG |
| \(\mathbb F_q\) | Lower count \(\iff\) trickle-down \(\iff\) index zero; Stepanov on both parity classes gives index zero | ALG, ACP, AKLT |

The E-part is tautological. The content is that the \(\mathbb F_q\) proof runs in the same language, and that over \(\mathbb Z\) the missing step is located: a producer for one parity class (U3). [Global law](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheGlobalLawIsTheOneSidedSquareRootCount.lean), [parity form](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheParityFormOfTheGlobalLaw.lean), [Stepanov's order](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/StepanovsOrderOverTheFiniteField.lean).

### C. Two sources of selectivity (T)

| Face | Statement |
|---|---|
| Pointwise closure [L] | A pointwise-closed, shift-invariant statement contains every unitary twist. Weil selectivity lives in the pole and Gamma. |
| Diamagnetic inequality [Lean] | On \(|\cdot|\)-closed families \(\zeta\) is the ground state of its gauge orbit. A margin needs the pole or overlap. |
| Non-ratio lags [Lean] | The gauge defect lives only on non-ratio lags, which exist from overlap of order one. |
| Margin [L] | Pole hyperplane = harmonic hyperplane; gap \(2\log2\) for \(\zeta\), \(0\) for Liouville. |
| Bounded overlap [K/S] | The complete form is positive for \(c<c_*\). The Liouville twin is negative from \(c=1/2\), and \(\omega_{11}\) from \(99/100\). Both are pole-mediated. |
| Boundary [L] | The escaped mass of a dilation is \(\log a\) exactly at \(\sigma=\tfrac12\). The Möbius boundary separates twins with identical multiplicative data. |

RW, HF, ACS, AIP, OWU, EWU, SRT, SZ, CHMD and ACT all use the first source and none uses the second. U2 at the RH overlap needs the second (inference). [Pointwise closure](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/PointwiseClosedStatementsAreTwinBlind.lean), [diamagnetic](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheDiamagneticInequality.lean), [non-ratio lags](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheGaugeEntersThroughNonRatioLags.lean), [Möbius boundary](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheMoebiusBoundarySeparatesGaugeTwins.lean).

### D. Atomic families: bounded overlap is proved, overlap growth is RH (T)

SRT, AIP, HF and ACS share one family.

- **Proved.**
  - Positivity for \(0<c<c_*\), \(c_*>1+10^{-16}\) [K]; the optimized Young family is exact at its constants.
  - The Markov form fails above \(e/2\pi\) [L].
  - Integer atoms carry the index [S].
- **RH.** Positivity at \(L(\log L)^\beta\), \(\beta>2\) [L], or \(L(\log L)^2\log\log L\) [S]. The explicit schedules reach \(\kappa\) [L].
- **Between them.**
  - Successor shells \(n=km+j\) enter at \(c\approx|j|\) [K].
  - Nonpolar energies lose \(\log c\) [S].
  - Atom norms degenerate [S].
  - Positivity reduces exactly to a Schur complement [S].

The four routes share one open problem: a shell theory of the complete form (Q1). [Young optimization](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TransMetzlerYoungOptimization.lean), [shell thresholds](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/ExactHigherShellThresholds.lean), [Schur reduction](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/APositivePrefixGivesTheExactSchurReduction.lean).

### E. One coordinate: the atomic programme and the census (T)

| Statement | Overlap \(X/T\) | Bandwidth |
|---|---|---|
| Montgomery pair correlation | \(\to0\) | \(<1\) |
| Complete positivity (proved) | fixed \(c<c_*\) | \(\to1\) |
| RH, atomic receiver | \(L(\log L)^2\log\log L\) | \(1+o(1)\) |
| \(70\%\) census | \(\asymp T^{1/9}\) | \(10/9\) |
| \(75\%\) census | \(\asymp T^{1/3}\) | \(4/3\) |

The atomic transform is a mollified Dirichlet polynomial \(h_\varphi(z/T)D_x(z)\). At the crossing length \(\approx\) height, mean values change from diagonal to off-diagonal dominance, and the prime side reads additive correlations. RH asks for a sign just past this crossing; the census asks for averaged information far past it. [Coordinates](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/OverlapCoordinates.lean), [census coordinates](../../../formal/GaloisForLFunctions/RHTower/CensusLengthHeightCoordinates.lean), [transform](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheNormalizedAtomicTransform.lean).

### F. The gauge torus: one point, many statistics (E + T)

| Statistic at the point \(0\) | Haar-almost every twist | At \(0\) | Routes |
|---|---|---|---|
| Partial sums of \(\mu\) | \(O(N^{1/2+\delta})\) | RH | MC, WL |
| Twisted \(\psi\) | Square-root law, no pole | Pole, then RH | WL, PBM |
| Successor correlations | Square-root Chowla | Chowla at \(0\) | MC, CTF |
| Near-incidences \(ab-cd=h\) | Gauge charge | Additive-divisor problem | HF, ACS |
| Coalescent surplus (census) | Budget \(0\) | Open | ACS, census |
| Escape states | Full gauge mass | RH | PM |
| Vertical hull | The orbit | Strong recurrence | BAG |

The exceptional set is comeager and null, and \(0\) lies in its closure. Finite gauge subgroups (Dirichlet characters) carry the main terms of successor statistics. [Typical except for the pole](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/ThePrimeSourceIsTypicalExceptForItsPole.lean), [comeager and null](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheMoebiusExceptionalSetIsComeagerAndNull.lean), [coalescent surplus](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheCoalescentSurplusIsPureGaugeCharge.lean), [escape states](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/RHIsTheVisibilityOfEveryEscapeState.lean), [finite gauge subgroups](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/FiniteGaugeSubgroupsResolveWhatTheArchimedeanLineCannot.lean).

### G. Hecke towers, Toeplitz symbols and aliasing (T)

| Face | Result |
|---|---|
| One prime tower | Index = distinct outer eigenvalues; RH iff positivity on all \(p\)-towers, also for pole-free generators. |
| Nyquist and heights | Windows shorter than \(2\pi/\log p\) are fully seen; \(\kappa_T=O(T\log T)\); the tower \(3^k/2^j\) certifies height \(T\); at most \(\binom{\kappa_T}2\) primes alias. |
| Carriers | Boxes \(p^iq^j\), \(i,j<|S|\), carry the index of a finite spectrum. |
| Attained depth | Seen by almost every prime; under attainment, RH iff infinitely many positive prime towers. |
| Locality | Every tower statement holds for every unitary twin. |
| HCF grids | One grid aliases; two decide. |
| LI and ALG Cayley ladder | RH iff the ladder is primitive nonpositive. |
| Compressions | Euler compressors kill no strip pair. |

Along a \(T_{\log p}\)-tower the lag sequence is \(\sum_\rho p^{d(\rho-1/2)}\). Off-line zeros are hyperbolic characters, and positivity is their absence. The tower language identifies the problem without supplying selection. [Hasse with heights](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheHassePrincipleWithHeights.lean), [attained depth](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/AttainedDepthIsSeenByAlmostEveryPrime.lean), [locality](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/LocalityIsTwinBlind.lean).

### H. The finite-support stratum is Krein–Langer finiteness (E + T)

| Face | Routes | Statement |
|---|---|---|
| Kernel index | HKT, HF, ACS, AIP | \(\kappa(K_\zeta)<\infty\), on \(\mathbb Q_{>0}^\times\) or on two primes |
| Wave number | AKLT, WD | Finitely many waves leave a bounded remainder |
| Eventual criticality | all | Every zero above some \(T_0\) is critical |
| Heat flow | WD, LA | \(N(t)\) bounded; collision mass \(=2(\kappa+\)excess\()\) |
| Critical energy | HF, SRT, ACS | \(\mathcal E_{\rm crit}<\infty\) |
| Complete-form index | HF, ACS, AIP | The last layer \(k=1\) |
| Subtracted lag | WL | Lag minus finitely many exponentials bounded on one side |
| Prime towers | AKLT | At most \(\binom\kappa2\) blind primes; almost every tower decides |

A positive part never pays a pair. Over \(\mathbb F_q\) an index ceiling comes from Riemann–Roch, and the function-field prime-kernel ceiling is exact. The stratum is RH above a height and implies LH. [TFAE](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean), [almost every prime](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/FiniteSupportMakesAlmostEveryPrimeDecideZeta.lean).

### I. Width, rate, strip, integrality and work currencies (E + T)

Fixed strips have exact one-sided readings in escaped Möbius rates, Hecke-defect caps, theta prefixes, Vaughan savings, balanced short windows, the Chebyshev Cesàro energy and the integrality exponent. Work and depth form one chain:
\[
\mathcal E_{\rm crit}\le\text{one quantum}\iff\mathrm{RH}\Rightarrow\mathcal E_{\rm crit}<\infty\iff\text{finite support}\Rightarrow\text{zeros approach the line}\Rightarrow\text{LH}\wedge\Theta<1 .
\]
Density envelopes never cross into this chain. [Density no-go](../../../formal/GaloisForLFunctions/RHTower/DensityEnvelopeNoGo.lean).

### J. Producers and counting faces (S)

| Face | Ledger | Precision |
|---|---|---|
| Stepanov over \(\mathbb F_q\) | \(\sum m_x\le\deg P\), \(m\approx\sqrt q\) via \(x^q=x\) | Square root, both parity classes |
| Chebyshev's binomial over \(\mathbb Z\) | \(\sum m_p\log p\le\log A\), \(m\le1\) above \(\sqrt N\) | Linear, primes only |
| Chebyshev's factorial ratio | Passes the sup-norm cap \(0.8644\) | Linear |
| Sup-norm integer polynomials | Capped by \(-\log t_{\mathbb Z}\); vanish at \(0,\tfrac12,1\) | Linear |
| Census, canonical energy, heat | Count critical zeros, price the index, count collisions | Proportions, not exclusion |

Only over \(\mathbb F_q\) is a count produced, because Frobenius couples addition and multiplication. Divisibility over \(\mathbb Z\) sees prime powers, not parity. [Linear counts](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/IntegralityProducesLinearCounts.lean), [Chebyshev cap](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/ChebyshevsProducerPassesTheIntegerChebyshevCap.lean).

### K. Displacement at depth \(1/\log T\) (S)

The census dichotomy puts every failure of \(70\%\) or \(75\%\) into simple off-line zeros within \(A/\log T\) [K]. Four results are blind exactly there:

- value moments (mimicry);
- shallow Cauchy energy (the majorant sums over all zeros);
- zero-side slack (projected credit may vanish);
- pair correlation (a near pair looks double).

The census, WD and SCP fail at the same place. [Dichotomy](../../../formal/GaloisForLFunctions/RHTower/Zeta23SeventyPercentOrSimpleNearLine.lean), [projected credit](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ProjectedDisplacementPaysNegativePartCredit.lean).

### L. Möbius admission, Haar approximation and escape (E + T)

MC, PM and CTF share Möbius arithmetic. CTF's residual is \((1-\Lambda\text{-readout})^2\) plus centered energy; PM's criterion is positive gauge mass. Escape states are measures on the gauge torus, and power-growth escape is invisible. The unpaid input is complete signed energy at small damping, which is F at the point \(0\).

### M. Heat, Jensen, Ward, moment and seam formulations (E + T)

- LA and WD share finite-head and heat geometry.
- TH and HCF expose moment and grid signs; PA exposes all-order passivity.
- HJ's residual equals SEC's seam charge, and all-divisor vanishing matches HCF's two-grid sign.
- Heat collisions count the index (H).

### N. Adjunction, prime modes and reference energies (T)

- RAPT, CACT and CAF link finite-prime adjunction to the actual matrices: per-conductor eigenlines; the Ramanujan main matrix as reference operator; the exact reference floor up to pole charge one.
- Nonpolar energies \(E_m(1)-\log c\).
- Cyclotomic Gram completion with an exact Dirichlet–Schur cost, and actual prime-prefix domination for fixed conductors.
- These coordinates are where a shell theory would be written (Q1). [Nonpolar loss](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/OverlapForcesNewRamanujanTerms.lean), [reference floor](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TransMetzlerReferenceFloor.lean).

### O. Parity and precision in four coordinates (S)

| Coordinate | Statement |
|---|---|
| Weil positivity (U2) | Twin-blind inputs cannot reach RH-complete families; selectivity lives in the pole or gauge charge. |
| Tower positivity (U1 ∩ U2) | \(n^{-\eta}\)-perturbed weights cannot both be positive. |
| Counts (U1) | The deciding-input theorem; finite aperture cannot decide; random signs satisfy the count. |
| Census | The coalescent surplus is pure gauge charge. |

A producer for any one of these must be parity-breaking and square-root-precise at the point \(0\).

### P. Precision classes (T + S)

Tower positivity implies the count. The count's stabilizer is the square-root class, and the successor enters only modulo that class, which over-regular Beurling systems share. Tower positivity's stabilizer is trivial. So U1 receivers cannot select \(\Lambda\) among its square-root neighbours, while U2 receivers can. Selection must be proved in U2 language, and a producer would most naturally act in U1. [Successor class](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheSuccessorEntersOnlyModuloTheSquareRootClass.lean).

### Q. Point side versus zero side (S)

| Side | Objects | Status |
|---|---|---|
| Zero side | Compressors vanishing at characters; characteristic polynomials; calibrated vanishing laws (BSH, CDC, HJ, IRK, SEC) | Receivers |
| Point side | Stepanov auxiliaries; integer polynomials on \([0,1]\); integer Dirichlet polynomials; factorial ratios | Producers over \(\mathbb F_q\). Over \(\mathbb Z\), linear precision and no parity. |

Every candidate whose mechanism is a vanishing law at zeros is a detector, and its promotion needs a point-side input (inference).

### R. Prime-free existence and the blind cone (E)

RH iff, for every aperture, some real weights make \(\zeta\)'s full functional nonnegative up to that aperture [L]. The dual obstruction is EWU's blind test, and the certificate is \(\Lambda\) itself.

## Complete live-route crosswalk

"Source" names which selective source the route currently uses: **P** = pole/Gamma, **G** = gauge charge, **—** = neither yet.

| Route | Core / cluster | Distinct producer obligation | Source | Stratum below RH |
|---|---|---|---|---|
| **WL** | U1; B, F | One-sided count; Chebyshev ledger at square-root precision | P (main term \(e^h\)) | Subtracted lag [FS] |
| **FU** | U1 | Scheduled Abel history | — | — |
| **CFC** | U1; A | First-clock tail lower bound | P | — |
| **RP** | U1 | Linear floor against linear escape | — | — |
| **MC** | U1; B, F, I | Half-power; odd class | — | Power saving [≥QRH] |
| **LI** | U1 + G | Primitive history; ladder sign | — | — |
| **PM** | U1 + L, F | Positive gauge mass | — | Exterior tightness [open] |
| **JAS** | U1 | Half-power budget | — | — |
| **CTF** | U1 + L | Readout and centered energy | — | — |
| **PBM** | U1 | Cancellation to \(\sigma>\tfrac12\) | P | Abscissa \(<1\) [≥QRH] |
| **RB** | U1 | Saturated extremizers | — | — |
| **RW** | U2 | Aperture relaxation | P | — |
| **TT** | U2 | Reflected-prime correlation | — | — |
| **HF** | U2 + U1 + U3; C, D, E | Shell theory; residual; work ceiling | P | Finite index [FS]; shells [open] |
| **CHMD** | U2 | Residual modulo radical | P | — |
| **SZ** | U2 | Tent-pattern sign | P | — |
| **EWU** | U2 + R | All-aperture payment | P | — |
| **OWU** | U2 | All-aperture odd sign | P | Conductor/forcing [open] |
| **SRT** | U2 + U1; D, E, G | Shells; tower sign; late lag | P | Overlap, completeness [open] |
| **ACT** | U2 | One shift for every profile | P | — |
| **AIP** | U2; C, D | Shells; allocation | P | Overlap [open] |
| **ACS** | U2 + U3; D, E, K | Index zero; census inputs | P | Finite index [FS]; census [open] |
| **PA** | U2 (moment) + M | All-order sign | — | — |
| **LA** | U2 (heat) + M | All-height heads | — | Heat count [FS] |
| **TH** | U2 (moment) + M | Successor integral at every rank | — | — |
| **WD** | U2 (heat) + H, K | Cap extinction | — | Count [FS]; high count [LH] |
| **HCF** | U2 (heat) + G | Both grids | — | Many-node floor [open] |
| **TG** | U3 | Positive residual, trace \(<1\) | — | — |
| **RN** | U3 | Directed boundary work | — | — |
| **XN** | U3 | Paid curvature | — | — |
| **BAG** | U3 + F | Every right-strip point | — | — |
| **GTA** | U3 | Rank uniformity | — | — |

**Strongest shared programmes.**

- **Shell programme** (HF, SRT, AIP, ACS; through A also WL and CHMD): one theory of the complete form across successor shells (Q1).
- **Producer programme** (MC, WL, U3; J, Q): one point-side construction finer than divisibility (Q2).
- **Gauge-charge-at-\(0\) programme** (MC, CTF, PM, ACS census, BAG; F, K): one point-0 statistic beyond the major arcs (Q3).
- **Finite-support programme** (HF, ACS, AIP, WL, WD, LA, HKT, AKLT; H): a Krein–Langer problem at Lindelöf level.

## Candidate crosswalk

The 17 candidates and PW-B are U3 producers whose landing is unproved. Each landing must fail the battery, including Haar-random gauge points and twin tails. "Side" records where the established mechanism acts (inference).

| Candidate | Intended landing | Side | What prevents merger into a live producer |
|---|---|---|---|
| **APF** | U3→U2; cycle-trace orientation | Zero side | Fourier recovery is not exhaustion with trace vanishing. |
| **BSH** | U3→U2; mate curvature | Zero side | Calibrated vanishing equals criticality. |
| **CDC** | U3→U2; descending potential | Zero side | Source-defined descent is unconstructed. |
| **DR** | U3→zero-free endpoint | Zero side | Cusp roots do not reach the strict-right domain. |
| **EGC** | U3→U1/U2; outer contour | Zero side | Inner cancellation does not orient the outer contour. |
| **EWJ** | U3→U1; depth admission | Prime side | Finite jets do not give norm exhaustion. |
| **FEL** | U3→U1; contrast balance | Both | Entropy identities are nonselective. |
| **HJ** | U3→U2; SEC/HCF residual | Zero side | Pre-divisor residual vanishing is unpaid. |
| **IRK** | U3→U2; integral orientation | Zero side | The completed relation is not the charged lift. |
| **MSC** | U3→U2; Sonin sign | Prime side | Admission and divisor transport give no sign. |
| **PCS** | U3→U1; chronological energy | Prime side | The co-shift defect survives. |
| **PTR** | U3→real-rooted Xi | Prime side | No prime-faithful lossless port without zeros. |
| **RFHM** | U3→U1/U2; grade orientation | Prime side | Support entropy forgets the grade. |
| **SC** | U3→U2; cross-fibre index | Index | Locality is twin-blind; a finite index lands only in H. |
| **SEC** | U3→U2; seam sign | Zero side | Asymptotic seam smallness is nonselective. |
| **W1C** | U3→real-rooted Xi | Prime side | No arithmetic ferromagnetic limit; the Bohr-torus lift is the natural landing (F). |
| **WBF** | U3→U2; certificates | Unspecified | No arithmetic coupling. |
| **PW-B** | U3→U1; PM complete energy | Zero-indexed | Zero-indexed action. |

ISC-polar is retired: its confinement is the lower square-root count, so it is a receiver within B.

## Unifications that are not valid

| Tempting identification | Correct distinction |
|---|---|
| Every RH receiver is one programme | Endpoint equivalence is E; producers differ. |
| The global law reduces RH to counting | It identifies the endpoint; the count must still be produced. |
| The count and positivity are the same property | Equal at \(\Lambda\); as weight properties their stabilizers differ. |
| Multiplicative statistics can select \(\zeta\) | They are gauge-invariant: Haar-random twists share them. |
| \(W\), the collided form \(D\) and the prime-only form are interchangeable | \(D\) is positive but its invariance is the problem; prime-only forms omit Gamma and poles. |
| Twin-blind positive families complete to full positivity | Impossible on RH-complete families. |
| The maximal margin selects \(\zeta\) | Single flips \(p\ge11\) attain it. |
| Fixed-ratio positivity is RH-complete | RH needs \(c_N\to\infty\); bounded-overlap completeness is unknown. |
| Fixed-ratio positivity selects \(\zeta\) | Shown against Liouville and \(\omega_{11}\) only, both through the pole. |
| The Trans-Metzler bound family extends indefinitely | It is exact at \(c_*\) for fixed constants, and its reference analysis needs pole charge \(<1\). |
| Atom-normalized floors survive growing overlap | The adjacent dipole's mass ratio tends to \(0\). |
| Markov frustration blocks complete positivity | Complete positivity holds where no Metzler gauge exists. |
| Finite support gives fixed-ratio positivity | A tempered finite-support model is negative at every ratio. |
| Short-interval statistics or finite apertures decide | Precision rigidity; deciding input; window law. |
| One prime tower decides | It aliases; the golden curve passes its tower and fails the lattice. |
| Local or pointwise-closed data select \(\zeta\) | Twin-blind. |
| A vertical shift is the parity twin over \(\mathbb Z\) | Equal to \(-1\) at no more than one prime; the twin lives only in the Bohr closure. |
| Compression or divisibility produces parity | Compression is a receiver; divisibility sees prime powers, not parity. |
| Integrality supplies square-root precision | Integrality is exact; the certificate is missing. |
| One twist completes an upper count | Not over \(\mathbb F_q\); the twist tower does. |
| Narrow generator support shortens the tower problem | Tower positivity is RH at every generator size. |
| A positive correction repairs a finite index | A positive part never pays a pair. |
| Finite negative index means RH | It means finite support. |
| Finite support is easier than RH at large height | It is RH above a height. |
| The \(2/3\) census is a route to RH | Proportions do not exclude zeros. |
| One-sided sieve bounds control pair correlation beyond \(\alpha=1\) | The kernel is signed; the surplus is gauge charge. |
| Better density exponents yield a strip | Envelopes never drop below \(1\). |
| Tensor amplification is independent of WL | Its tensor square is WL's mean square. |
| Infinite symmetry confines the zeros | Confinement is the lower square-root count. |
| Regular integer counts force RH | Over-regular Beurling systems share the successor's class. |
| Index continuity can deform \(\zeta\) to an index-zero object | \(\Lambda_{\rm dBN}\ge0\) blocks openness at \(\zeta\); closedness needs realization. |
| Curves over finite fields donate Weil positivity | The archimedean continuum cannot arise from finite places. |

## How to organize research around the unification

1. **Shell programme** (U2; C, D, E, N): the complete form across the first successor shell, with major arcs and the \(\Lambda*1=\log\) collapse (Q1).
2. **Producer programme** (U3; B, J, Q): an auxiliary finer than divisibility, i.e. a Frobenius substitute (Q2).
3. **Gauge-charge-at-\(0\) programme** (U1; F, K, O): the census surplus and successor statistics beyond the major arcs, with level-of-distribution tools (Q3).
4. **Exploratory**: Diophantine typicality of special points ([2.4](obstacles-summary.md#24-is-there-a-wildly-different-route)), and ring Krein–Langer theory ([2.5](obstacles-summary.md#25-where-a-real-breakthrough-on-the-hard-questions-could-come-from)).
5. **Finite-support programme** at Lindelöf level (H), checked against LH and against "RH above a height".
6. **External extraction** of the quasi-RH threshold (W13).

No route is promoted because its final condition was renamed, and no candidate is retired because another route reaches the same endpoint.
