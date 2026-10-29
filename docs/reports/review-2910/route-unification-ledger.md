# Route-unification ledger

Status: 29 October 2026, corpus checkpoint `3c5f89e3b2` plus working tree. **The 31 live routes and 18 candidate branches are faces of three core problems: the selective critical sign (U1), source-complete Weil positivity (U2) and an independent producer (U3).** Five facts bind them:

1. **Selectivity is common to all three by theorem.** No twin-blind input reaches an RH-complete family, on atomic families or on towers. The measured margin \(2\log2\) separates \(\zeta\) from Liouville but is shared at its maximum by single-prime flips \(p\ge11\).
2. **Precision is common to all three.** \(\Lambda\) and \(\Lambda+\varepsilon n^{-\eta}\) are never both tower-positive.
3. **U1 and U2 are one endpoint in index language.** The Weil kernel of \(\zeta\) has index zero iff \(\psi(x)-x\le C\sqrt x\log^2x\); over \(\mathbb F_q\) the same theorem reads index zero iff the one-sided point count [S]. U3 is the search for a producer of that count.
4. **Hecke towers join U1 and U2 entry by entry.** Along one prime's towers, U2 cross-level entries are U1 prime-error sequences, and tower positivity is RH for one fixed prime at every generator size.
5. **The finite-support stratum is one statement.** Finite index, two-prime index, heat counts, critical energy, subtracted lag, cosine defects and "critical above a height" are equivalent; all imply LH and a fixed strip.

[Route obstacles](route-obstacles.md) · [summary and priorities](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [frontier map](../rh-current-frontier-map.md). Evidence: corpus searches and Lean statements; no builds. **[L]**/**[S]** as in the frontier map; **(inference)** = conclusion of this review. [Working log](../../../logs/review-2910-research-2026-10-29.md).

## What "the same problem" means

| Relation | Meaning | What it does not mean |
|---|---|---|
| **E — Endpoint equivalence** | Two stated conditions are both equivalent to RH, or to each other. | A usable estimate between the producers. |
| **T — Proved source transfer** | An identity, approximation or inequality carries the actual source from one formulation to another. | Extension to growing supports, primes, degrees or another norm. |
| **S — Structural similarity** | Two approaches face the same kind of sign, exhaustion or faithfulness problem. | A theorem identifying their objects. |

All RH criteria are E-equivalent almost tautologically. Unification is meaningful through T-bridges and a shared unproved producer.

## The three core problems

| Problem | The one missing statement | Faces (routes) | Wall |
|---|---|---|---|
| **U1 — Selective critical sign** | A bound on the actual signed prime/Möbius discrepancy at the critical scale, in some currency. | WL, FU, RP, MC, LI, PM, JAS, CTF, PBM, RB; prime-error faces of HF/SRT/AIP; via the Chebyshev identity, the off-diagonal of every U2 route. | 1 |
| **U2 — Source-complete positivity** | Index zero of the complete Weil form, with Gamma and both poles, on a source-complete family. | RW, TT, HF, CHMD, SZ, EWU, OWU, SRT, ACT, AIP, ACS, HCF; via sign receivers PA, LA, TH, WD. | 1 and 3 |
| **U3 — Independent producer** | A source-built structure whose proved property supplies the U1 count or U2 index zero. | TG, RN, XN, BAG, GTA, all 17 candidates and PW-B; geometric faces of HF/ACS; the Stepanov question. | 14 |

**Cross-cutting requirements on every producer.**

| Requirement | Status | Test object |
|---|---|---|
| Selectivity | Theorem [L] | Liouville, \(c\Lambda\), quadratic mixtures fail. |
| Beyond the margin | Theorem [L] | Single flips \(\omega_p\), \(p\ge11\) (maximal gap), cofinite flips (gap \(0\)) fail. |
| Parity | Criterion (inference) | Majorant information \(|\lambda|\le\Lambda\) is consistent with Liouville. |
| Precision | Theorem [L] | \(\Lambda+\varepsilon n^{-\eta}\), \(\eta<\tfrac12\), fails. |
| Two primes | Theorem [S] | One prime aliases; the golden curve passes its tower and fails the lattice. |
| Unbounded aperture | Inference | Finite-aperture inequalities move continuously in \(\varepsilon\). |

## Strongest unifications

### A. U1 and U2 meet entry by entry (T)

For \(\operatorname{supp}f<b<\operatorname{supp}g\): \(W(f,g)=-\int_0^\infty(e^h-\psi(e^h)-c)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g)\). On the pole hyperplane only the prime comb is left. WL/FU/RP/PBM and HF/ACS/AIP/RW/OWU ask for the same signed quantity in different test norms. The pole product, which alone grows across scales, is cancelled by the prime main term \(e^h\); this is where \(\Lambda\) differs from Liouville (prime sum \(\approx-e^h\)) and from character twists (\(o(e^h)\)). [Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean).

### B. U1 and U2 meet at the endpoint: positivity = index = count (E, with an S-bridge to \(\mathbb F_q\))

| Language | Statement | Route |
|---|---|---|
| Count | \(\psi(x)-x\le C\sqrt x\log^2x\) eventually | WL |
| Index | \(\kappa(K_\zeta)=0\) | HKT, HF, ACS |
| Positivity | Weil Grams of integer atoms positive semidefinite | SRT, AIP |
| \(\mathbb F_q\) | \(N_k\ge q^k+1-Cq^{k/2}\) \(\iff\) trickle-down \(\iff\) index zero | ALG, ACP (Stepanov) |

The E-part is tautological; the content is that the \(\mathbb F_q\) proof (count produced, then index zero) runs in the same language, so the missing step over \(\mathbb Z\) is located: a count producer (U3). [Global law](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheGlobalLawIsTheOneSidedSquareRootCount.lean), [integer atoms](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/IntegerFamiliesCarryTheWholeIndex.lean), [trickle-down count](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheTrickleDownInequalityIsTheSquareRootCount.lean).

### C. One measured margin; an index-one window (T)

RW, HF, ACS, AIP, OWU, EWU, SRT, SZ, CHMD and ACT reduce on atomic or complete sources to one form: the pole hyperplane is the harmonic hyperplane; \(\zeta\)'s gap is \(2\log2\), Liouville's \(0\), every gauge's \(\ge(2\log2)c^2\); at every width the sign is the Markov gap on \(p=0\) plus one affine scalar. In HKT language the margin is the width of the window in which the atomic form \(D\delta_1-P\) has index exactly one [S]. The margin is the first layer of selectivity (parity), not \(\zeta\)-selective; the second layer must see every prime at square-root precision. [Margin](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheSelectiveMarginIsTwoLogTwo.lean), [index window](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheMarginIsTheWidthOfTheIndexOneWindow.lean).

### D. Atomic families and the separated regime (T)

SRT, AIP, HF and ACS share the atomic receiver at \((\log\log N)^\alpha/N\), \(\alpha>1\); integer atoms at fixed width carry the whole index [S]. Markov negativity under overlap growth is unconditional; narrow positivity reaches a quarter of Robin–Euler; the separated regime has exact splitting, trial energies [L] and actual eigenlines [S]. The \(\alpha=1\) edge is the quasi-analytic boundary.

### E. Hecke towers, Toeplitz symbols and aliasing (T)

| Face | Result |
|---|---|
| ACS/HKT one-prime tower | Index = distinct outer eigenvalues \(p^{\rho-1/2}\); RH iff positivity on all \(p\)-towers. |
| SMAP pole-free generators | Same for generators in \([-\varepsilon,\varepsilon]\). |
| HKT Nyquist | Windows shorter than \(2\pi/\log p\) are fully seen. |
| HKT two primes / blind primes | Two primes carry the index; \(\le\binom\kappa2\) blind primes; infinitely many positive towers force index zero in the finite stratum. |
| HCF grids | One grid aliases a pair to a positive atom; two grids decide. |
| LI / ALG Cayley ladder | RH iff the Cayley–Li Toeplitz ladder is negative semidefinite on primitive vectors. |
| ACP Stepanov mechanism | \(1-T_p^N\) kills a zero symbol iff the zero is critical and on a height lattice. |
| HKT compressions | Compression kills a pair iff its character is annihilated. |

**Unifying statement.** Along a \(T_{\log p}\)-tower the explicit formula writes the lag sequence as a sum over zeros of \(p^{d(\rho-1/2)}\); off-line zeros are hyperbolic characters; positivity is their absence. HCF aliasing, the Stepanov lattice criterion and the Nyquist law are the same one-prime aliasing; a second prime removes it. The finite-generator reduction of U2 lands here: RH in Toeplitz form, not a reduction. [One prime](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OnePrimeSeesTheWholeDefectOfZeta.lean), [two grids](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/OneGridHidesTwoGridsDecide.lean), [blind primes](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/AllButFinitelyManyPrimesSeeTheWholeIndex.lean).

### F. The finite-support stratum is Krein–Langer finiteness (E + T)

| Face | Routes | Statement |
|---|---|---|
| Kernel index | HKT, HF, ACS, AIP | \(\kappa(K_\zeta)<\infty\), on \(\mathbb Q_{>0}^\times\) or on two primes |
| Eventual criticality | all | Every zero above some \(T_0\) is critical |
| Heat flow | WD, LA | \(N(t)\) bounded; collision mass \(=2(\kappa+\)excess\()\) |
| Critical energy | HF, SRT, ACS | \(\mathcal E_{\rm crit}<\infty\); \(\kappa\le\sqrt{2\mathcal E_{\rm crit}/97}\) |
| Complete-form index | HF, ACS, AIP | Last layer \(k=1\) of the finite-index chain |
| Subtracted lag | WL | Lag minus finitely many exponentials bounded on one side |
| Cosine defects | WD | Uniformly bounded |

Every face says: the Weil kernel is positive-definite modulo finitely many exponential characters. A positive part never pays a pair, so no positive majorant produces finiteness; an index ceiling must come from structure (I10). The stratum is RH above a height and implies LH. [TFAE](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean), [Krein–Langer](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheWeilKernelIsKreinLangerOnTheFiniteStratum.lean), [index price](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/IndexIsEnergy.lean), [heat](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/HeatCollisionsCountTheIndex.lean).

### G. Width, rate, strip and work currencies (E + T)

Fixed strips \(\Theta\le\tfrac12+c\) have exact one-sided readings in escaped Möbius rates, Hecke-defect caps, theta-prefix growth, Vaughan power savings, the Möbius-divisor Abel moment and quotient head, Suzuki residuals, terminal ceilings, balanced short-window power savings and the Chebyshev Cesàro mean-square energy. Work and depth:
\[
\mathcal E_{\rm crit}\le\text{one quantum}\iff\mathrm{RH}\Rightarrow\mathcal E_{\rm crit}<\infty\iff\text{finite support}\Rightarrow\text{zeros approach the line}\Rightarrow\text{LH}\wedge\Theta<1 .
\]
Density envelopes never cross into this ladder, even at \(30/13\). [Abscissa laws](../../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean), [short windows](../../../formal/GaloisForLFunctions/ReflectiveDirichletPolynomialS2/ShortWindowDispersionAtSeventeenThirtieths.lean), [density no-go](../../../formal/GaloisForLFunctions/RHTower/DensityEnvelopeNoGo.lean).

### H. Counting faces (S)

These results locate zeros by counting:

- over \(\mathbb F_q\), the one-sided square-root count, produced by Stepanov;
- over \(\mathbb Z\), the one-sided \(\psi\) count (WL), equal to index zero (B);
- the census counts critical zeros through Sylvester signatures with three exact exchange rates;
- canonical energy pays each off-line quartet a quantum; the index is priced quadratically;
- heat collisions count the index.

Only over \(\mathbb F_q\) is the count produced.

### I. Displacement at depth \(1/\log T\) (S)

Four results ask for the same missing input, a statement that sees how far a zero pair sits from the line at scale \(1/\log T\):

| Face | What is blind |
|---|---|
| Value moments (mimicry) | Equal-valued reflected pairs look critical. |
| Shallow Cauchy energy | The majorant sums over all zeros of the window. |
| Zero-side slack | Displaced pairs with \(\eta<1/18\) (for \(70\%\)) or \(\eta<1/6\) (for \(75\%\)) carry too little slack (inference from [L]). |
| Pair correlation | A pair at depth \(\asymp1/\log T\) looks like a double point. |

This is one obstacle: the census, WD and SCP fail at the same place. [Slack](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/SpectralSlackConservationAndTheHyperbolicDisplacementThreshold.lean), [mimicry](../../../formal/GaloisForLFunctions/RHTower/ValueMomentsCannotSeparateReflectedPairs.lean).

### J. Möbius admission, Haar approximation and chronological residuals (E + T)

MC, PM and CTF share Möbius arithmetic; CTF's residual is \((1-\Lambda\text{-readout})^2\) plus centered energy; PM's criterion is positive gauge mass for every escape state. The common unpaid input is complete signed energy at small damping. [Visibility](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/RHIsTheVisibilityOfEveryEscapeState.lean).

### K. Heat, Jensen, Ward, moment and seam formulations (E + T)

LA and WD share finite-head/heat coefficient geometry; TH and HCF expose moment/grid signs; PA exposes all-order passivity. HJ's reflection residual equals SEC's seam charge; all-divisor vanishing matches HCF's two-grid sign. The heat flow links WD/LA to F: its collisions count the index.

### L. Adjunction, prime modes and gauge finite parts (T)

RAPT and ACP link finite-prime adjunction to the actual matrices: bounded spectrum = adjunction spectrum; per-conductor actual eigenlines of the complete Weil matrix at every \(0<c<1\) [S]; actual conductor coordinates for every prime pattern [S]; \(\chi\)-twisted poles read \(2\operatorname{Re}(-L'/L(1,\chi))\). The link to complete positivity is C and Q1. [Eigenlines](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSimpleCompleteWeilEigenlinesConvergeToRamanujanLines.lean), [conductor coordinates](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/EveryPrimePatternHasActualConductorCoordinates.lean).

### M. Parity and precision are one obstruction in three coordinates (S)

| Coordinate | Statement |
|---|---|
| Weil positivity (U2) | Twin-blind inputs cannot reach RH-complete families [L]. |
| Tower positivity (U1 ∩ U2) | \(n^{-\eta}\)-perturbed weights cannot both be positive [L]. |
| Census | Coalescent prime pairs enter through a signed kernel [L]; two-sided asymptotics are parity problems (inference). |

A producer for any one must be parity-breaking and square-root-precise. Analytic number theory has no input with both; finite-field geometry has several.

### N. Prime-free existence and the blind cone (E)

RH iff for every aperture some real weights make the full Weil functional of \(\zeta\)'s archimedean datum nonnegative up to that aperture [L]. Its dual obstruction is EWU's blind test; its certificate is \(\Lambda\) itself. [Existence](../../../formal/GaloisForLFunctions/RHTower/WeilPositivityFiniteLevelExistenceDecidesRH.lean).

## Complete live-route crosswalk

| Route | Core problem / cluster | Distinct producer obligation | Selective input | Stratum below RH |
|---|---|---|---|---|
| **WL** | U1; prime-error energy; B | One-sided \(\psi\) count | Main-term cancellation \(e^h-\psi(e^h)\) | Subtracted lag [FS] |
| **FU** | U1; Abel moment | Scheduled history | Signed prime channels | — |
| **RP** | U1; history floor | Linear floor vs linear escape | Signed hyperbola/LCM identities | — |
| **MC** | U1; Möbius cancellation | Every strict half-power | Actual \(\mu\) | Any power saving [≥QRH] |
| **LI** | U1 + E; Cayley ladder | Literal primitive; ladder sign | Signed clock | — |
| **PM** | U1 + J; escape visibility | Positive gauge mass | Möbius cofactors | Exterior tightness [open] |
| **JAS** | U1; prime budget | Logarithmic → half-power budget | Prime-product sign | Quasi-RH plus dressed PSD |
| **CTF** | U1 + J; residual | Readout and centered energy | \(-\mu_N\) readout | — |
| **PBM** | U1; regularized series | Cancellation to \(\sigma>1/2\) | Actual coefficients | Fixed abscissa \(<1\) [≥QRH] |
| **RB** | U1; extremal remainder | Saturated extremizers | Divisor arithmetic | — |
| **RW** | U2; ground energy | Aperture relaxation | Margin on low/polar modes (C) | — |
| **TT** | U2; odd/covariance | Reflected-prime correlation | Signed reflected primes | — |
| **HF** | U2 + U1 + U3 | Residual sign / work ceiling | Margin (C); cross-level cancellation (A, E) | Finite index [FS]; separated step [open] |
| **CHMD** | U2; wave/Doob | Residual sign mod radical | Primitive defect | — |
| **SZ** | U2; first variation | Tent-pattern sign | Low modes | — |
| **EWU** | U2 + N | All-aperture low/mixed payment | Weight rigidity | — |
| **OWU** | U2; odd weight | All-aperture odd sign | Finite-aperture witnesses | Conductor/forcing [open] |
| **SRT** | U2 + U1 + D, E | Tower sign or late lag | Margin (C) | Separated step [open] |
| **ACT** | U2; one shift | One shift for every profile | Exterior primes | — |
| **AIP** | U2; allocation | Coarse/cross-level allocation | Margin (C) | Separated step [open] |
| **ACS** | U2 + U3 + E, H, I | RI/height/chirality or index zero; census inputs | Margin (C); towers; slack | Finite index [FS]; census [open] |
| **PA** | U2 (moment) + K | All-order sign | Prime–archimedean trace | — |
| **LA** | U2 (heat) + K | All-height heads | Xi coefficients | Uniform heat count [FS] |
| **TH** | U2 (moment) + K | Signed vectors | Theta moments | — |
| **WD** | U2 (heat) + F, I | Cap extinction | Actual divisor | Uniform count [FS]; high count [LH] |
| **HCF** | U2 (heat) + E | Both grids, all degrees | Two prime grids | — |
| **TG** | U3; trace cap | Positive residual, trace \(<1\) | Euler/Gaussian source | — |
| **RN** | U3; renewal | Directed boundary work | Theta renewal | — |
| **XN** | U3; Newton discs | Paid curvature | Xi jets | — |
| **BAG** | U3; recurrence | Every right-strip point | Euler-product universality | — |
| **GTA** | U3; transverse decay | Rank uniformity | Theta Schur charge | — |

**Strongest shared programmes.**

- U2 cluster (RW, HF, ACS, AIP, OWU, SRT, CHMD, SZ, EWU, ACT): one selective input, one open transfer, the separated-regime step (Q1).
- Census (ACS, WD, SCP): one displacement problem (I) and one parity problem (M) (Q2).
- U1 and U2 endpoints: one count, whose producer is the Stepanov question (B, Q3).
- Finite-support stratum (HF, ACS, AIP, WL, WD, LA, HKT): one Krein–Langer problem at Lindelöf level (F).

## Candidate crosswalk

The 17 candidates and PW-B are U3 producers whose landing is unproved. Each landing must fail for the battery: Liouville, \(\omega_p\) with the maximal margin, cofinite flips, \(\Lambda+\varepsilon n^{-\eta}\), the golden curve on the lattice.

| Candidate | Intended landing | What prevents merger into a live producer |
|---|---|---|
| **APF** | U3→U2; cycle-trace orientation | Fourier recovery is not exhaustion with trace vanishing. |
| **BSH** | U3→U2; mate curvature | Calibrated vanishing equals criticality. |
| **CDC** | U3→U2; descending potential | Source-defined descent unconstructed. |
| **DR** | U3→zero-free endpoint | Cusp roots do not reach the strict-right domain. |
| **EGC** | U3→U1/U2; outer contour | Inner cancellation does not orient the outer contour. |
| **EWJ** | U3→U1; depth admission | Finite jets do not give norm exhaustion. |
| **FEL** | U3→U1; contrast balance | Entropy identities are nonselective. |
| **HJ** | U3→U2; SEC/HCF residual | Pre-divisor residual vanishing unpaid. |
| **IRK** | U3→U2; integral orientation | Completed relation is not the charged lift. |
| **MSC** | U3→U2; Sonin sign | Admission and divisor transport give no sign. |
| **PCS** | U3→U1; chronological energy | The co-shift defect survives. |
| **PTR** | U3→real-rooted Xi | No prime-faithful lossless port without zeros. |
| **RFHM** | U3→U1/U2; grade orientation | Support entropy forgets the grade. |
| **SC** | U3→U2; cross-fibre index | A finite cross-fibre index lands only in F. |
| **SEC** | U3→U2; seam sign | Asymptotic seam smallness is nonselective. |
| **W1C** | U3→real-rooted Xi | No arithmetic ferromagnetic limit; Bohr-torus Lee–Yang lift is the natural landing. |
| **WBF** | U3→U2; certificates | No arithmetic coupling. |
| **PW-B** | U3→U1; PM complete energy | Zero-indexed action. |

## Unifications that are not valid

| Tempting identification | Correct distinction |
|---|---|
| Every RH receiver is one programme | Endpoint equivalence is E; producers differ. |
| The global law reduces RH to counting | It identifies the endpoint; the count must still be produced. |
| \(W\), the collided form \(D\) and the prime-only form are interchangeable | \(D\) is positive but its invariance is the problem; prime-only forms omit Gamma and poles. |
| Twin-blind positive families complete to full positivity | Impossible on RH-complete families. |
| The maximal margin selects \(\zeta\) | Single flips \(p\ge11\) attain it and fail. |
| Pointwise convergence of signs preserves gaps | Cofinite flips converge pointwise to the untwisted sign with gap \(0\). |
| Short-interval prime statistics decide tower or Weil positivity | Precision rigidity. |
| One prime tower decides | It aliases; the golden curve passes its tower and fails the lattice. |
| Positivity on the coordinate axes of \(\mathbb Z^2\) gives positivity | Locality fails; for the arithmetic class infinitely many towers are needed. |
| Compression produces positivity | It never raises the index; it annihilates, it does not produce. |
| Narrow generator support shortens the tower problem | Tower positivity is RH at every generator size. |
| Reducing the complete form to finitely many \(\log2\)-orbits lowers the difficulty | Orbit positivity is one-prime tower positivity. |
| Cross-level couplings are summable | Almost periodic under RH (inference). |
| Hyperbolicity of the atomic Gram is arithmetic | It holds for every sign twin. |
| A positive correction repairs a finite index | A positive part never pays a pair. |
| Finite negative index means RH | It means finite support. |
| Finite support is easier than RH at large height | It is RH above a height. |
| The \(\alpha=1\) atomic receiver is a computation away | It needs quasi-analytic compact profiles, which do not exist. |
| The \(2/3\) census is a route to RH | Proportions do not exclude zeros. |
| Simple-zero theorems raise the census | Value moments cannot separate reflected pairs. |
| Zero-side slack at small bandwidth gives \(3/4\) | False for every \(\lambda<3/4\). |
| One-sided sieve bounds control pair correlation beyond \(\alpha=1\) | The kernel is signed. |
| Better density exponents yield a strip | Envelopes never drop below \(1\), at \(30/13\) as at \(8/3\). |
| Tensor amplification of \(\zeta\) is independent of WL | Its tensor square is WL's mean square. |
| Infinite-symmetry continuation sees zeros | Over \(\mathbb F_q(t)\) the affine series' singularities are images of the pole of \(\zeta_K\); its moments see zeros only through the Jensen depth product. |
| Regular integer counts force RH | Over-regular Beurling systems. |
| \(A_Q\) is the Xi operator | Adjunction energies are prime-matrix eigenvalues. |
| Curves over finite fields donate Weil positivity | The archimedean continuum cannot arise from finite places. |

## How to organize research around the unification

1. **One selective-positivity programme** (U2): the separated-regime step past Robin–Euler (Q1), on actual eigenlines, against Liouville and \(\omega_p\).
2. **One census programme** (H, I, M): the coalescent pair energy and the displacement-sensitive slack (Q2).
3. **One producer programme** (B, U3): a Stepanov-type count over \(\mathbb Z\), first at the parity rung (Q3).
4. **One Krein–Langer programme** at the Lindelöf level (F): every result checked against LH and against "RH above a height".
5. **One vanishing-mechanism extraction** for fixed strips: the Chen–Gupta–Li threshold (W08).
6. **Independent-construction experiments** for U3, each tested against the battery. The infinite-symmetry continuation of [2.7](obstacles-summary.md#27-is-there-a-wildly-different-route) failed its calibration: it is a moment generating function and lands in the Lindelöf stratum.

No route is promoted because its final condition was renamed, and no candidate is retired because another route reaches the same endpoint.
