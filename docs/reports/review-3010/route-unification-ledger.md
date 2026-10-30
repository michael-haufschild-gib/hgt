# Route-unification ledger

Status: 30 October 2026, corpus `66f67bc27f`. **The 32 live routes, 17 candidates and PW-B are faces of three core problems:**

- **U1**, the selective critical sign;
- **U2**, source-complete positivity along a resolution filtration, now located at one critical curve;
- **U3**, an independent producer.

Twelve facts bind them:

1. **Selectivity has two sources, and the pole decides the easy half [L].**
   - One source is the shift-fixed pole and Gamma; the other is gauge charge, entering only through non-ratio lags.
   - Every pole-free \(\pm1\) twin falls at one bounded overlap. Twins that keep the pole are resolved only at overlap growing with their distance from \(0\).
2. **RH is an exponent at one point [L].** The Möbius exponent is \(1/2\) Haar-a.e. and \(\Theta\) at \(0\). Gauge-invariant certificates give \(\ge3/4\) there; finitely determined ones give \(\ge1\).
3. **U1 and U2 are one endpoint [S].** Index zero of the Weil kernel is the one-sided \(\psi\) count, already the upper count of one parity class.
4. **U1 and U2 meet entry by entry [L].** Ordered Weil entries are centered Chebyshev integrals; Hecke towers join them.
5. **U2 is a theorem at every bounded resolution and on every fixed packet at slowly growing resolution [L].** The margin is the Poisson aliasing tail \(E(c)\); packets stay positive to \((\log N)^{1/48}\).
6. **The zeros read every atomic vector through its Möbius horizons [L].** Single-horizon charges are depth-blind. Depth enters only through two-horizon windows (growing conductors), which are Weil's box tests.
7. **Theta and atomic positivity read one horizon boundary [L].** The theta source carries \(B_N(\rho)\), the atomic pole mode \(B_N(1-\rho)\); aperture modes carry the theta aperture current.
8. **The window narrows to one critical curve (inference).** Margin, Gamma reserve and synthesis error are one Fourier tail, separated by the archimedean weight \(\log N\). The Gevrey and Steklov receivers lie on \(E(c_N)\log N\asymp1\).
9. **One coordinate [K].** Overlap = length/height; bandwidth = \(\log(\text{length})/\log(\text{height})\). Atomic positivity, the census and pair correlation sit on one axis.
10. **The finite-support stratum is one statement [S/L].** It is RH above a height, and implies LH.
11. **Locality and pointwise closure are twin-blind [L].**
12. **Every producer obeys one ledger, and \(\mathbb Z\) has no Frobenius [L].**
    - Over \(\mathbb F_q\), Frobenius gives growing multiplicity at points.
    - Over \(\mathbb Z\), divisibility is parity-blind, small integer auxiliaries are divisible, Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) is linear, and Adams vanishing is Bézout-sharp on characters.

Links: [route obstacles](route-obstacles.md) · [summary and priorities](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [frontier map](../rh-current-frontier-map.md). Evidence comes from corpus searches and Lean statements; no builds were run. [Working log](../../../logs/review-3010-rev2-research-2026-10-30.md).

| Label | Meaning |
|---|---|
| **[L]**, **[S]**, **[K]** | As in the frontier map. |
| **[Lean]** | Statement read; integration not assessed. |
| **(inference)** | A conclusion of this review. |

## What "the same problem" means

| Relation | Meaning | What it does not mean |
|---|---|---|
| **E — Endpoint equivalence** | Two stated conditions are both equivalent to RH, or to each other. | A usable estimate between the producers. |
| **T — Proved source transfer** | An identity, approximation or inequality carries the actual source from one formulation to another. | Extension to growing supports, overlap, primes, degrees or another norm. |
| **S — Structural similarity** | Two approaches face the same kind of sign, exhaustion or faithfulness problem. | A theorem identifying their objects. |

All RH criteria are E-equivalent almost tautologically. Unification is meaningful through T-bridges and through a shared unproved input.

## The three core problems

| Problem | The one missing statement | Faces (routes) | Wall |
|---|---|---|---|
| **U1 — Selective critical sign** | A bound on the actual signed prime/Möbius discrepancy at the critical scale, in some currency: one-sided count, one parity class, history floor, integrality half, Chebyshev ledger, first-clock tail, or \(\theta_\mu(0)=1/2\). It must be depth-sensitive and keep \(\zeta\)'s pole. | WL, FU, CFC, RP, MC, LI, PM, JAS, CTF, PBM, RB; the prime-error faces of HF, SRT, AIP; via the Chebyshev identity, the off-diagonal of every U2 route. | 1 |
| **U2 — Positivity along a resolution filtration** | Positivity of the complete form on a source-complete family, along a schedule past the point where its margin falls below the archimedean-weighted aliasing. Atomic families: past \(E(c_N)\log N\asymp1\). Every bounded resolution and every fixed packet to \((\log N)^{1/48}\) is a theorem. | RW, TT, HF, CHMD, SZ, EWU, OWU, SRT, ACT, AIP, ACS, HCF; via sign receivers PA, LA, TH, WD. | 1 and 3 |
| **U3 — Independent producer** | A source-built structure whose proved property supplies the U1 count or U2's index zero. Over \(\mathbb Z\) it must act beyond self-maps, vanish finer than divisibility, carry non-periodic valuations, and convert character vanishing into a prime count. | TG, RN, XN, BAG, GTA; all 17 candidates and PW-B; the geometric faces of HF and ACS; the producer faces of WL and MC. | 14 |

**Cross-cutting requirements on every input.**

| Requirement | Status | Test object |
|---|---|---|
| Selectivity | Theorem [L] | The Liouville twin, \(c\Lambda\) and quadratic mixtures fail. |
| Pole-keeping twins | Theorem [L] | Finite flips need \(c_0(\omega_p)\asymp p^{1/7}\); pole-free twins fall at bounded overlap. |
| Point specificity | Theorem [L] | Not gauge-invariant (else \(\ge3/4\) at \(0\)); not finitely determined (else \(\ge1\)). |
| Depth sensitivity | Theorem [L] | Single-horizon charges cannot see real parts of zeros. |
| Two-source compliance | Theorem [L] | Pole/Gamma or gauge charge; never multiplicative data alone. |
| Parity | Theorem [S] | Anything implying the count rejects the Liouville twin. |
| Precision | Theorem [L/S] | \(\Lambda+\varepsilon n^{-\eta}\) fails; for positivity, \(\Lambda+1/n\) too. |
| Two primes | Theorem [S] | One prime aliases; the golden curve passes its tower and fails the lattice. |
| Unbounded resolution | Theorem [K/L] | Finite aperture cannot decide. Every fixed overlap is positive unconditionally, so a fixed-resolution RH receiver would prove RH outright. |
| Criticality | Identity [L] + inference | \(E(c)\to0\) by Stirling; the RH content sits where \(E(c_N)\log N\asymp1\). |
| Point side | Theorem [S/L] | Zero-side annihilation certifies nothing; divisibility cannot select parity; small integer auxiliaries are divisible; Adams vanishing is Bézout-sharp. |

## Strongest unifications

### A. U1 and U2 meet entry by entry (T)

For \(\operatorname{supp}f<b<\operatorname{supp}g\): \(W(f,g)=-\int_0^\infty(e^h-\psi(e^h)-c)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g)\). WL, FU, RP, PBM and CFC ask for the same signed quantity as HF, ACS, AIP, RW and OWU, in different test norms. [Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean).

### B. The endpoint: positivity = index = count = parity class = exponent at \(0\) (E, with an S-bridge to \(\mathbb F_q\))

| Language | Statement | Route |
|---|---|---|
| Count | \(\psi(x)-x\le C\sqrt x\log^2x\) eventually, either sign | WL, MC |
| Parity class | Upper count of \(\{\lambda=-1\}\) in harmonic–exponential weighting | MC, WL |
| Chebyshev ledger | Joint square-root control of moments, sawtooth, Mertens | WL, MC |
| Integrality | Each half of integer-polynomial integrality at square-root scale | MC, WL |
| Index | \(\kappa(K_\zeta)=0\) | HKT, HF, ACS |
| Positivity | Atomic positivity past the critical curve | SRT, AIP, HF, ACS |
| Exponent | \(\theta_\mu(0)=1/2\) | MC, PM, BAG |
| \(\mathbb F_q\) | Lower count \(\iff\) index zero \(\iff\) polar confinement; Stepanov on both parity classes gives index zero; trivial point of \(\mathbb F_q[T]\) better than typical | ALG, AKLT, AGT |

The E-part is tautological. The content is that the \(\mathbb F_q\) proof runs in the same language and the missing step over \(\mathbb Z\) is located. [Global law](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheGlobalLawIsTheOneSidedSquareRootCount.lean), [exponent](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheGaugeExponent.lean), [function field](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheFunctionFieldCalibrationIsDerived.lean).

### C. Two sources, coherence, the antipode and the pole (T)

| Face | Statement |
|---|---|
| Pointwise closure [L] | Shift-invariant pointwise-closed statements contain every unitary twist. |
| Coherence [L] | Nonnegative statistics are maximal at \(0\); the excess is the pole. |
| Antipode [L] | \(S_N(\ell)+S_N(0)=2\psi(\sqrt N)\): only the pole's sign separates the twins. |
| Affine positivity [L] | Positive affine-invariant forms are \(c\,\delta_0+d\,\)Haar; arithmetic positivity must come from the shells. |
| Non-ratio lags [L] | The gauge enters only on non-ratio lags, present from overlap one. |
| Pole-free twins [L/Lean] | Every completely multiplicative \(\pm1\) gauge with bounded harmonic sums fails at one bounded overlap. |
| Pole-keeping twins [L] | Finite flips fail at their exact thresholds \(c_0\asymp p^{1/7}\). |

The pole is the selector of everything far from \(0\); everything near \(0\) needs resolution.

### D. Atomic families: the overlap window (T)

SRT, AIP, HF and ACS share one family.

| Regime | Statement |
|---|---|
| Fixed \(c\) [L] | Positive for every profile without real Fourier zeros; low spectrum = completed conductor spectrum; pole ground state. |
| Bounded ranges [K] | One horizon for \(0<c\le K\). |
| Fixed packets [L] | Positive for \(1\le c\le(\log N)^{A}\), \(A<1/48\). |
| Gamma reserve [L] | \((\kappa c^{-7}\log N-bc)\cdot\)mass. |
| Mechanism [L] | Shells with Ramanujan weights; Möbius inversion and Poisson summation repay \(-\log c\); \(E(c)\to0\) by Stirling. |
| Arithmetic [L/K] | Linear fixed-modulus PNT in progressions; every inverse-log rate. |
| RH [L/K] | \(c_N^4\gg\log N\) (\(C^2\)); \((\log\log N)^{s+}\) (Gevrey); iterated log (Steklov). |
| Critical curve (inference) | \(E(c_N)\log N\asymp1\): the Gevrey and Steklov receivers lie on it. |

The four routes share one open problem: positivity of growing conductors up to the critical curve, and the identity at it (Q1, Q2). [Fixed packets](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/FixedConductorPacketsStayPositiveAtGrowingOverlap.lean), [shells repay](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheShellsRepayEveryConductor.lean), [every profile](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/EveryProfileWithoutRealFourierZerosIsPositiveAtEveryOverlap.lean).

### E. One coordinate: the atomic programme and the census (T)

| Statement | Overlap \(X/T\) | Bandwidth |
|---|---|---|
| Montgomery pair correlation | \(\to0\) | \(<1\) |
| Complete positivity (theorem) | every fixed \(c\); fixed packets to \((\log N)^{1/48}\) | \(\to1\) |
| Critical curve, \(C^2\) (inference) | \(\asymp(\log N)^{1/7}\) | \(1+o(1)\) |
| RH, atomic receiver (\(C^2\)) | \(\gg(\log N)^{1/4}\) | \(1+o(1)\) |
| RH, Steklov receiver | \(L(\log L)^2\log\log L\) | \(1+o(1)\) |
| \(70\%\) census | \(\asymp T^{1/9}\) | \(10/9\) |
| \(75\%\) census | \(\asymp T^{1/3}\) | \(4/3\) |

RH asks for a sign just past the critical curve on this axis; the census asks for averaged information far past it. [Coordinates](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/OverlapCoordinates.lean), [census coordinates](../../../formal/GaloisForLFunctions/RHTower/CensusLengthHeightCoordinates.lean).

### F. The gauge torus: one point, many statistics (E + T)

| Statistic at \(0\) | Haar-a.e. twist | At \(0\) | Routes |
|---|---|---|---|
| Möbius partial sums | exponent \(1/2\) | \(\Theta\) (RH) | MC, WL |
| Constant source | exponent \(1/2\) | \(1\) (the pole) | — |
| Twisted \(\psi\) | square-root, no pole | pole, then RH | WL, PBM |
| Successor correlations, near-incidences | gauge charge | Chowla / additive divisor at \(0\) | MC, CTF, HF, ACS |
| Shells of the prime pair form | deleted by Haar | read by fixed-modulus prime sums; no multiplicative level sees them for \(c\le2\) | HF, AIP, SRT, ACS |
| Shells on average over conductors | — | level of distribution \(1/2\); \(0\) is one term | MC, HF |
| Coalescent surplus | budget \(0\) | open | ACS census |
| Escape states | full gauge mass | RH; the Möbius escape state is blind to zeros | PM |
| Vertical hull | exponent constant on the line | strong recurrence | BAG |

[Typical exponent](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheTypicalExponentIsOneHalf.lean), [short shells](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheShortShellsHaveNoConductor.lean), [level 1/2](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheShellsHaveLevelOfDistributionOneHalf.lean).

### G. Hecke towers, Toeplitz symbols and aliasing (T)

| Face | Result |
|---|---|
| One prime tower | Index = distinct outer eigenvalues; RH iff positivity on all \(p\)-towers. |
| Nyquist and heights | \(\kappa_T=O(T\log T)\); \(3^k/2^j\) certifies height \(T\); at most \(\binom{\kappa_T}2\) primes alias. |
| Fine towers | Consecutive-ratio towers decide every orbit kernel. |
| Attained depth | Seen by almost every prime. |
| Locality | Every tower statement holds for every unitary twin. |
| HCF grids | One grid aliases; two decide. |
| Compressions | Euler compressors kill no strip pair. |

The tower language identifies the problem without supplying selection. [Fine towers](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/FineTowersDecideEveryOrbitKernel.lean), [locality](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/LocalityIsTwinBlind.lean).

### H. The finite-support stratum is Krein–Langer finiteness (E + T)

| Face | Routes | Statement |
|---|---|---|
| Kernel index | HKT, HF, ACS, AIP | \(\kappa(K_\zeta)<\infty\), on \(\mathbb Q_{>0}^\times\) or two primes |
| Wave number | AKLT, WD | Finitely many waves leave a bounded remainder |
| Heat flow | WD, LA | \(N(t)\) bounded; collision mass \(=2(\kappa+\)excess\()\) |
| Critical energy | HF, SRT, ACS | \(\mathcal E_{\rm crit}<\infty\) |
| Complete-form index | HF, ACS, AIP | The last layer \(k=1\) |
| Subtracted lag | WL | Lag minus finitely many waves bounded on one side |
| Prime towers | AKLT | At most \(\binom\kappa2\) blind primes |

It is RH above a height and implies LH. [TFAE](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean).

### I. Width, rate, strip, integrality, work and aperture currencies (E + T)

Fixed strips have exact one-sided readings: escaped Möbius rates, Hecke-defect caps, theta prefixes, Vaughan savings, the Chebyshev Cesàro energy, the integrality exponent, the gauge exponent at \(0\), and (inference) box-test positivity at a fixed sub-pole aperture.
\[
\mathcal E_{\rm crit}\le\text{one quantum}\iff\mathrm{RH}\Rightarrow\mathcal E_{\rm crit}<\infty\iff\text{finite support}\Rightarrow\text{LH}\wedge\Theta<1 .
\]
Density envelopes never cross into this chain. [Width dictionary](../../../formal/GaloisForLFunctions/ArithmeticOrientationTheory/TheWidthDictionary.lean), [density no-go](../../../formal/GaloisForLFunctions/RHTower/DensityEnvelopeNoGo.lean).

### J. Producers and counting faces (S)

| Face | Ledger | Precision |
|---|---|---|
| Stepanov over \(\mathbb F_q\) | \(\sum m_x\le\deg P\), \(m\approx\sqrt q\) via \(x^q=x\) | Square root, both parity classes |
| Bézout and Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) | \(\prod p^{m_p}\le N\); \(h^0=\lfloor N/\prod p^{m_p}\rfloor\) | Exact, linear |
| Adams fixed locus | Multiplicity \(r\) costs support \(2^{qr}\), sharp | Bézout-exact; on characters |
| Integer auxiliaries | Small = divisible | No gain from smallness |
| Factorial ratios | \((2\log2-\varepsilon)mn\); valuations periodic in \(n\bmod p\) | Chebyshev, not square root |
| Self-maps of \(\mathbb Z\) | Identity or unit-ball gauge points | No growth |
| Census, canonical energy, heat | Proportions, index prices, collision counts | Not exclusion |

Only over \(\mathbb F_q\) is a count produced, because one endomorphism is additive and multiplicative at once and acts on points. [Adams multiplicity](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/AdamsMultiplicityResolution.lean), [Chebyshev precision](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/FactorialRatiosHaveChebyshevPrecision.lean), [Riemann–Roch](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheRiemannRochTheoremOfTheMultiplicativeGroup.lean).

### K. Displacement at depth \(1/\log T\) (S)

The census dichotomy puts every failure of \(70\%\) into simple off-line zeros within \(A/\log T\) [K]. Value moments, shallow Cauchy energy, zero-side slack and pair correlation are blind exactly there. [Dichotomy](../../../formal/GaloisForLFunctions/RHTower/Zeta23SeventyPercentOrSimpleNearLine.lean).

### L. Möbius admission, Haar approximation and escape (E + T)

- CTF's residual is \((1-\Lambda\text{-readout})^2\) plus centered energy; every superlinear exponent is carried by the nonnegative cyclotomic remainder [K]; terminal and probe costs are exact [L].
- PM's criterion is positive gauge mass; the Möbius escape state leans to the Liouville point, blind to zeros [L].

### M. Heat, Jensen, Ward, moment and seam formulations (E + T)

- LA and WD share finite-head and heat geometry.
- TH and HCF expose moment and grid signs; PA exposes all-order passivity.
- HJ's residual equals SEC's seam charge; all-divisor vanishing matches HCF's two-grid sign.
- Heat collisions count the index (H).

### N. Reference energies and the shell repayment law (T)

- RAPT, CACT and CAF link finite-prime adjunction to the actual matrices. Adjunction energies continued past touching lose \(\log c\); the shells restore them; the completed conductor energies are the actual low spectrum at every fixed overlap.
- Cyclotomic Gram completion with Dirichlet–Schur cost; prime-prefix domination; prefix Schur reduction and payment with constant \(20\) [L].

### O. Parity and precision in five coordinates (S)

| Coordinate | Statement |
|---|---|
| Weil positivity (U2) | Twin-blind inputs cannot reach RH-complete schedules. |
| Tower positivity (U1 ∩ U2) | \(n^{-\eta}\)-perturbed weights cannot both be positive. |
| Counts (U1) | Deciding input; finite aperture cannot decide; random signs satisfy the count. |
| Census | The coalescent surplus is pure gauge charge. |
| Exponent | Not gauge-invariant; twin tails at \(1\); the twin inequality transfers strips. |

### P. Precision classes (T + S)

Tower positivity implies the count. The count's stabilizer is \(\mathcal Q\); tower positivity's is trivial. U1 receivers cannot select \(\Lambda\) among its square-root neighbours, while U2 receivers can. [Successor class](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheSuccessorEntersOnlyModuloTheSquareRootClass.lean).

### Q. Point side versus zero side (S)

| Side | Objects | Status |
|---|---|---|
| Zero side | Compressors; characteristic polynomials; calibrated vanishing laws (BSH, CDC, HJ, IRK, SEC) | Receivers |
| Character side | Adams fixed loci; torsion grids | Bézout-exact vanishing; no count |
| Point side | Stepanov auxiliaries; integer polynomials; integer Dirichlet polynomials along Frobenius progressions; factorial ratios | Producers over \(\mathbb F_q\); over \(\mathbb Z\) exact but linear |

Every candidate whose mechanism is a vanishing law at zeros or characters is a detector; its promotion needs a point-side input (inference).

### R. Prime-free existence and the blind cone (E)

RH iff, for every aperture, some real weights make \(\zeta\)'s full functional nonnegative up to that aperture [L]. The dual obstruction is EWU's blind test; the certificate is \(\Lambda\).

### S. Every U2 route is a resolution filtration (S; T for atomic families)

| Route | Parameter | Fixed level | RH schedule | Margin |
|---|---|---|---|---|
| HF, AIP, ACS, SRT | overlap \(c\) | theorem at every \(c\); fixed packets at growing \(c\) [L] | past \(E(c_N)\log N\asymp1\) | \(E(c)\), exact Poisson tail |
| RW | aperture \(A\) | small-aperture floors | every \(A\) | decays doubly exponentially; no identity |
| TH | rank | rank seven strict [L]; rank eight reduced | all ranks | tails strict past a log horizon; center open |
| PA | Hausdorff order | each order at large shift | all orders, all shifts | none |
| LA, WD | degree, height, heat time | finite heads; horizon \(2\pi e^{(2/3+\varepsilon)/t}\) | all heights | none |
| HCF | degree on two grids | fixed rank signs | all degrees | none |
| SZ | tent level | moving-aperture limits | factorial/grid families | none |
| EWU, OWU | aperture | restricted floors; witnesses at fixed radii | every aperture | none |
| GTA | rank | finite-rank charges | rank-uniform decay | none |

Only the atomic filtration has positivity at every level with an exact margin and an identified critical curve. W23 asks whether another filtration admits a Poisson-type identity for its margin.

### T. One horizon for atomic, theta and box-test positivity (T)

| Face | Statement |
|---|---|
| Atomic pole mode [L] | Zero side \(=\operatorname{Re}\sum_\rho m_\rho\hat g\overline{\hat g}\,B_N(1-\rho)B_N(\rho)\). |
| Theta source [L] | Truncated theta transform \(=-\hat f_1(\gamma_\rho)B_N(\rho)\); tail \(=+\hat f_1B_N(\rho)\). |
| Aperture modes [L] | \(y_n=n^{\kappa-1}\): the charge summed over zeros is the theta center-mixed current at aperture \(\kappa\). |
| Windows [L] | Windowed aperture modes are exponential box tests at aperture \(\kappa\) plus aliasing. |
| Every vector [L] | The zeros read each atomic vector through Möbius horizons \(H_a\). |

HF/SRT/AIP/ACS (atomic), TT/TH (theta) and OWU/EWU/RW (aperture and box tests) read one Euler–Maclaurin boundary, from the two sides of the functional equation. [Theta horizon](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheThetaSourceSharesTheHorizonOfThePoleMode.lean), [aperture modes](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheApertureModesCarryTheThetaApertureCharge.lean), [windows](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/AWindowedApertureModeIsAnExponentialBoxTest.lean).

### U. Selectivity is resolution on the gauge torus (T)

| Gauge point | Resolved at |
|---|---|
| Liouville point and every cofinite flip (pole-free) | one bounded overlap above the Robin–Euler ratio [L/Lean] |
| Flip \(\omega_p\) (pole-keeping) | \((p/\log p)^{1/7}\lesssim c_0\lesssim p^{1/7}\) [L] |
| Every finite flip set | exact threshold [L] |
| Every summable twist | sign at fixed \(c\) = sign of a finite Ramanujan-packet form; exact monotone threshold [L] |
| Twin tails | exponent \(1\) [L]; overlap threshold open |
| An off-line zero (pole-keeping, non-summable) | invisible at fixed \(c\); open |

[Packets decide](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ATwistedCompleteWeilMatrixIsDecidedByItsRamanujanPackets.lean), [exact threshold](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheOverlapThatResolvesATwistIsAnExactThreshold.lean), [cofinite flips](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/FixedOverlapPositivityIsSelectiveAgainstEveryCofiniteFlip.lean).

### V. Depth enters only through growing conductors (T + inference)

- Fixed conductors have window ratio \(\le m\), hence gain at most \(m^{|\beta-1/2|}\) from an off-line zero.
- Single horizons are depth-blind [L].
- So the RH content of HF, SRT, AIP and ACS (growing conductors \(m\lesssim c\)) is the same content as OWU/EWU's all-aperture sign and TT/TH's long-window theta sign: sub-pole box tests on long windows.

### W. The critical curve unifies margin, reserve and receivers (S + inference)

- The HF/AIP margin \(E(c)\) [L], the CACT Gamma reserve \(\approx E(c)\log N\) [L] and the SRT/SSHA receivers (synthesis error energy \(\approx E(c)\log N\)) [L/K] are one Fourier tail.
- The Gevrey and Steklov receivers lie on \(E(c_N)\log N\asymp1\); the \(C^2\) receiver lies above it, for a synthesis reason.

### X. The conductor spectrum is an arithmetic Weyl law (S)

- HF/CAF: \(E_m(c)=\log m+O_c(1)\); heat trace converges iff \(\beta>1\) [L].
- APD: the Bost–Connes temperature is the Hecke exponent; \(\beta=1\) is the critical line [L].
- PM, W1C and PTR (physical realization) and the atomic window therefore share one critical temperature (inference). This is a structural similarity, not a transfer.

## Complete live-route crosswalk

"Source" names the selective source the route uses: **P** = pole/Gamma; **G\(_{\rm fix}\)** = gauge charge through fixed-modulus prime sums; **—** = neither yet. "Depth channel" names where the route would read the real part of a zero.

| Route | Core / cluster | Distinct producer obligation | Source | Filtration | Depth channel | Stratum below RH |
|---|---|---|---|---|---|---|
| **WL** | U1; A, B, F, J | One-sided count; Chebyshev ledger; non-periodic producer | P | horizon | lag growth | Subtracted lag [FS] |
| **FU** | U1 | Scheduled Abel history | — | schedule | Abel moment | — |
| **CFC** | U1; A | First-clock tail bound | P | aperture tail | tail coefficient | — |
| **RP** | U1 | Linear floor | — | history length | history escape | — |
| **MC** | U1; B, F, I | Half-power; odd class; \(\theta_\mu(0)\) | — | horizon | exponent | Power saving [≥QRH] |
| **LI** | U1 + G | Primitive history; ladder sign | — | ladder rank | guarded zeros | — |
| **PM** | U1 + L, F, X | Positive gauge mass | — | damping | escape mass | Exterior tightness [open] |
| **JAS** | U1 | Square-root budget | — | prime budget | budget growth | — |
| **CTF** | U1 + L | Covariance upper control | — | cutoff | cyclotomic remainder | — |
| **PBM** | U1 | Cancellation to \(\sigma>1/2\) | P | abscissa | abscissa | Abscissa \(<1\) [≥QRH] |
| **RB** | U1 | Saturated extremizers | — | extremizer size | remainder | — |
| **RW** | U2 + T | Aperture relaxation | P | aperture | apertures | — |
| **TT** | U2 + T | Reflected-prime covariance | — | scale | theta windows | — |
| **HF** | U2 + U1 + U3; C, D, E, N, S, T, V, W, X | Growing conductors; critical-curve sign; work ceiling | P + G\(_{\rm fix}\) | overlap | growing conductors | Finite index [FS]; critical curve [open] |
| **CHMD** | U2 | Residual modulo radical | P | cutoff | retained orbit | — |
| **SZ** | U2 | Tent-family sign | P | tent level | tent modes | — |
| **EWU** | U2 + R, T | All-aperture blind minima | P | aperture | apertures | — |
| **OWU** | U2 + T, V | All-aperture odd sign | P | aperture | box tests | Conductor/forcing [open] |
| **SRT** | U2 + U1; D, E, G, U, W | Growing conductors; tower sign; late lag | P + G\(_{\rm fix}\) | overlap, generator | growing conductors | Critical curve, unattained depth [open] |
| **ACT** | U2 | One shift for every profile | P | profile support | collars | — |
| **AIP** | U2; C, D, U | Growing conductors; allocation | P + G\(_{\rm fix}\) | overlap | growing conductors | Critical curve [open] |
| **ACS** | U2 + U3; D, E, J, K | Index zero; census; quadratic count | P + G\(_{\rm fix}\) | overlap; bandwidth | growing conductors; displacement | Finite index [FS]; census [open] |
| **PA** | U2 (moment) + M | All-order sign | — | order | high orders | — |
| **LA** | U2 (heat) + M | All-height heads | — | degree, height | heat flow | Heat count [FS] |
| **TH** | U2 (moment) + M, T | Rank-uniform compensation | — | rank | center hierarchy | Rank eight [just work] |
| **WD** | U2 (heat) + H, K | Cap extinction | — | heat time | collisions | Count [FS]; high count [LH] |
| **HCF** | U2 (heat) + G | Both grids | — | degree | two-prime grids | Many-node floor [open] |
| **TG** | U3 | Positive residual, trace \(<1\) | — | disc | winding | — |
| **RN** | U3 | Directed boundary work | — | — | resonances | — |
| **XN** | U3 | Paid curvature | — | discs | Newton margins | — |
| **BAG** | U3 + F | Every right-strip point | — | tolerance | returns | — |
| **GTA** | U3 | Rank uniformity | — | rank | transverse charge | — |

**Strongest shared programmes.**

- **Critical-window programme** (HF, SRT, AIP, ACS; D, E, N, S, V, W): place every receiver on the critical curve, push unconditional positivity of growing conductors toward it, and find the identity at it (Q1, Q2).
- **Horizon programme** (HF, SRT, TT, TH, OWU, EWU, RW; T, V): one boundary, two sides of the functional equation, windows as box tests; the damage law (Q3).
- **Resolution programme** (HF, AIP, SRT, MC, PM; C, U): thresholds for summable twists done; extend to pole-keeping, non-summable perturbations.
- **Producer programme** (MC, WL, U3; B, J, Q): non-periodic valuations; the character-to-point duality step.
- **Filtration-transfer programme** (RW, TH, PA, LA, HCF, SZ, EWU; S): import exact-margin identities (W23).
- **Finite-support programme** (H): a Krein–Langer problem at Lindelöf level, as a diagnostic.

## Candidate crosswalk

The 17 candidates and PW-B are U3 producers whose landing is unproved. Each landing must fail the battery, must not be gauge-invariant or finitely determined, and must read depth through more than one horizon. "Side" records where the established mechanism acts (inference).

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
| **PTR** | U3→real-rooted \(\Xi\) | Prime side | No prime-faithful lossless port without zeros. |
| **RFHM** | U3→U1/U2; grade orientation | Prime side | Support entropy forgets the grade. |
| **SC** | U3→U2; cross-fibre index | Index | Locality is twin-blind; a finite index lands only in H. |
| **SEC** | U3→U2; seam sign | Zero side | Asymptotic seam smallness is nonselective. |
| **W1C** | U3→real-rooted \(\Xi\) | Prime side | No arithmetic ferromagnetic limit; the Bost–Connes form of Lee–Yang is the same gap (X). |
| **WBF** | U3→U2; certificates | Unspecified | No arithmetic coupling. |
| **PW-B** | U3→U1; PM complete energy | Zero-indexed | Zero-indexed action. |

## Unifications that are not valid

| Tempting identification | Correct distinction |
|---|---|
| Every RH receiver is one programme | Endpoint equivalence is E; producers differ. |
| Fixed-overlap positivity is RH | It is an unconditional theorem; RH needs growth past the critical curve. |
| Fixed-packet positivity at growing overlap approaches RH | Fixed packets are depth-blind; the RH content is in growing conductors. |
| Positivity at every fixed \(c\) gives an explicit growing schedule | Only an existential schedule; rates need uniformity in \(c\) and conductor. |
| The shell repayment controls gauge charge at \(0\) | It uses fixed-modulus linear prime sums; for \(c\le2\) no multiplicative level sees the shells. |
| Pole-free twin rejection rejects all twins | Pole-keeping twins need overlap \(\asymp p^{1/7}\); off-line zeros are pole-keeping and non-summable. |
| Single-horizon charges detect off-line zeros | They are bounded by \(N(\sum|a_d|/d)^2/|s(1-s)|\) on the whole strip. |
| The global law reduces RH to counting | It identifies the endpoint; the count must still be produced. |
| The count and positivity are the same property | Equal at \(\Lambda\); as weight properties their stabilizers differ. |
| Multiplicative or gauge-invariant data can certify \(0\) | They give \(\ge3/4\) at \(0\). |
| Averaged typicality or level of distribution decides a point | The large sieve is typical on average; \(0\) is one term. |
| \(W\), the collided form and the prime-only form are interchangeable | The collided form is positive but its invariance is the problem; prime-only forms omit Gamma and poles. |
| Atom-normalized floors survive growing overlap | The true floor is \(E(c)\); the proved Gamma reserve lasts while \(c^8=o(\log N)\). |
| Finite support gives fixed-ratio positivity | A tempered finite-support model is negative at every ratio. |
| Short-interval statistics or finite apertures decide | Precision rigidity; deciding input; window law. |
| One prime tower decides | It aliases; the golden curve passes its tower and fails the lattice. |
| A vertical shift is the parity twin over \(\mathbb Z\) | It equals \(-1\) at no more than one prime. |
| The Adams operations give Frobenius-cheap vanishing for a prime count | Adams vanishing is Bézout-exact and lives on characters. |
| Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) gives a Hodge index | It is linear; a Hodge index needs a quadratic Euler characteristic. |
| Small auxiliaries are cheaper than vanishing ones | For integer auxiliaries small = divisible. |
| Factorial ratios reach square-root precision with more factors | Their valuations are periodic; precision stops at \(2\log2\). |
| Iterating integer twists adds independent constraints | The twist tower collapses to level \(0\). |
| Compression or divisibility produces parity | Compression is a receiver; divisibility sees prime powers, not parity. |
| A positive correction repairs a finite index | A positive part never pays a pair. |
| Finite negative index means RH | It means finite support. |
| The \(2/3\) census is a route to RH | Proportions do not exclude zeros. |
| Better density exponents yield a strip | Envelopes never drop below \(1\). |
| The conductor Weyl law at \(\beta=1\) is RH | It is a structural match with Bost–Connes, not a transfer. |
| Index continuity can deform \(\zeta\) to index zero | \(\Lambda_{\rm dBN}\ge0\) blocks openness at \(\zeta\). |
| Curves over finite fields donate Weil positivity | The archimedean continuum cannot arise from finite places. |

## How to organize research around the unification

1. **Critical-window programme** (U2; D, S, V, W): profile-adapted synthesis, conductor-uniform residuals, Siegel–Walfisz, smooth profiles; locate and approach the critical curve (Q1; W01–W05).
2. **Horizon programme** (U2 ∩ U1; T, V): the two-horizon calculus and the identity at the critical curve; the damage law (Q2, Q3; W06, W07).
3. **Resolution programme** (U1 in gauge language; C, U): thresholds beyond summable twists; uniform selectivity along a schedule (W08).
4. **Producer programme** (U3; J, Q): non-periodic valuations; the duality step; Adams minimum-support rigidity (W13).
5. **Filtration transfer** (S): exact-margin identities for RW, TH, PA, LA, HCF, SZ, EWU (W23); TH rank eight (W09).
6. **Exploratory**: the contradiction route ([2.4](obstacles-summary.md#24-is-there-a-wildly-different-route)); the critical Poisson–Weil identity and the trace formula of \(W\) ([2.5](obstacles-summary.md#25-where-a-real-breakthrough-on-the-hard-questions-could-come-from)).
7. **Finite-support programme** at Lindelöf level (H), as a diagnostic.
8. **External extraction** of the quasi-RH threshold (W19).

No route is promoted because its final condition was renamed, and no candidate is retired because another route reaches the same endpoint.
