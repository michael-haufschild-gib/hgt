# Route-unification ledger

Status: 30 October 2026, corpus `a0e8154924` plus working tree. **The 32 live routes, 17 candidates and PW-B are faces of three core problems:**

- **U1**, the selective critical sign;
- **U2**, source-complete positivity, now understood as positivity along a resolution filtration;
- **U3**, an independent producer.

Ten facts bind them:

1. **Selectivity has two sources [L].** One is the shift-fixed pole and Gamma terms. The other is gauge charge, which enters only through non-ratio lags, i.e. additive structure. Nonnegative statistics are maximal at \(0\) (coherence), and the Liouville point is the antipode, separated from \(0\) only by the sign of the pole.
2. **RH is an exponent at one point [L].** The Möbius exponent is \(1/2\) at Haar-almost every gauge point and \(\Theta\) at \(0\). RH says that \(0\) is typical. Gauge-invariant certificates give \(\ge3/4\) there; finitely determined ones give \(\ge1\).
3. **U1 and U2 are one endpoint [S].** Index zero of the Weil kernel is the one-sided \(\psi\) count, already the upper count of one parity class.
4. **Hecke towers join U1 and U2 entry by entry [L].**
5. **U2 is solved at every bounded resolution of the atomic filtration [L].**
   - The complete Weil matrix is positive at every fixed overlap. Shells repay the loss exactly by Poisson summation, and the margin \(E(c)\) is a Fourier tail tending to \(0\).
   - RH is positivity at \(c_N^4\gg\log N\).
   - U2's remaining content is a rate, and at its endpoint it is U1.
6. **One coordinate [K].** Overlap = length/height; bandwidth = \(\log(\text{length})/\log(\text{height})\). Atomic positivity, the census and pair correlation sit on one axis.
7. **The finite-support stratum is one statement [S/L].** It is RH above a height, and it implies LH.
8. **Locality and pointwise closure are twin-blind [L].**
9. **Every producer obeys one ledger, and \(\mathbb Z\) has no Frobenius [L].**
   - Over \(\mathbb F_q\), Frobenius gives growing multiplicity.
   - Over \(\mathbb Z\), divisibility is parity-blind, small integer auxiliaries are divisible, and Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) is linear.
   - The equation \(x^q=x\) lives only on the gauge torus, as the fixed points of the Adams operations.
10. **Overlap is resolution on the gauge torus [L + inference].** Each flip is rejected at its own overlap \(c_0(p)\), and no fixed overlap rejects all. Uniform selectivity needs the same growth that RH needs.

Links: [route obstacles](route-obstacles.md) · [summary and priorities](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [frontier map](../rh-current-frontier-map.md). Evidence comes from corpus searches and Lean statements; no builds were run.

| Label | Meaning |
|---|---|
| **[L]**, **[S]**, **[K]** | As in the frontier map. |
| **(inference)** | A conclusion of this review. |

[Working log](../../../logs/review-3010-research-2026-10-30.md).

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
| **U1 — Selective critical sign** | A bound on the actual signed prime/Möbius discrepancy at the critical scale, in some currency: one-sided count, one parity class, history floor, integrality half, Chebyshev ledger, first-clock tail, or the exponent \(\theta_\mu(0)=1/2\). | WL, FU, CFC, RP, MC, LI, PM, JAS, CTF, PBM, RB; the prime-error faces of HF, SRT, AIP; via the Chebyshev identity, the off-diagonal of every U2 route. | 1 |
| **U2 — Positivity along a resolution filtration** | Positivity of the complete form on a source-complete family, along a schedule of the resolution parameter fast enough to synthesize any negative test. For atomic families: past \(c_N^4\gg\log N\). Every bounded resolution is now a theorem. | RW, TT, HF, CHMD, SZ, EWU, OWU, SRT, ACT, AIP, ACS, HCF; via sign receivers PA, LA, TH, WD. | 1 and 3 |
| **U3 — Independent producer** | A source-built structure whose proved property supplies the U1 count or U2's index zero. Over \(\mathbb Z\) it must act beyond self-maps (no Frobenius), vanish finer than divisibility, and break gauge covariance through additive structure. | TG, RN, XN, BAG, GTA; all 17 candidates and PW-B; the geometric faces of HF and ACS. | 14 |

**Cross-cutting requirements on every input.**

| Requirement | Status | Test object |
|---|---|---|
| Selectivity | Theorem [L] | The Liouville twin, \(c\Lambda\) and quadratic mixtures fail. |
| Beyond the margin | Theorem [L] | Single flips share the maximal gap; cofinite flips have gap \(0\). |
| Point specificity | Theorem [L] | Not gauge-invariant (else \(\ge3/4\) at \(0\)); not finitely determined (else \(\ge1\)). |
| Two-source compliance | Theorem [L] | Pole/Gamma or gauge charge; never multiplicative data alone. |
| Parity | Theorem [S] | Anything implying the count rejects the Liouville twin. |
| Precision | Theorem [L/S] | \(\Lambda+\varepsilon n^{-\eta}\) fails; for positivity, \(\Lambda+1/n\) too. |
| Two primes | Theorem [S] | One prime aliases; the golden curve passes its tower and fails the lattice. |
| Unbounded resolution | Theorem [K/L] | Finite aperture cannot decide; every fixed overlap is positive unconditionally, so a fixed-resolution RH receiver would prove RH outright. |
| Marginality | Identity [L] | The atomic margin \(E(c)\to0\) by Stirling; no fixed-loss estimate survives. |
| Point side | Theorem [S/L] | Zero-side annihilation certifies nothing; divisibility cannot select parity; small integer auxiliaries are divisible. |

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
| Positivity | Atomic positivity past the synthesis threshold | SRT, AIP, HF, ACS |
| Exponent | \(\theta_\mu(0)=1/2\), the Haar-typical value | MC, PM, BAG |
| \(\mathbb F_q\) | Lower count \(\iff\) index zero \(\iff\) polar confinement; Stepanov on both parity classes gives index zero | ALG, AKLT |

The E-part is tautological. The content is that the \(\mathbb F_q\) proof runs in the same language, and that over \(\mathbb Z\) the missing step is located. [Global law](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheGlobalLawIsTheOneSidedSquareRootCount.lean), [exponent](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheGaugeExponent.lean), [polar index](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/ThePolarDivisorCountsTheIndex.lean).

### C. Two sources, coherence and the antipode (T)

| Face | Statement |
|---|---|
| Pointwise closure [L] | Shift-invariant pointwise-closed statements contain every unitary twist. |
| Diamagnetism [L] | On \(|\cdot|\)-closed families \(\zeta\) is the ground state of its gauge orbit. |
| Coherence [L] | Nonnegative statistics are maximal at \(0\); the excess is the pole. |
| Antipode [L] | \(S_N(\ell)+S_N(0)=2\psi(\sqrt N)\): no size statement separates the twins, only the pole's sign. |
| Non-ratio lags [L] | The gauge enters only on non-ratio lags, which exist from overlap one. |
| Bounded overlap [L/S] | The Liouville twin fails at fixed \(c\ge1\) [S]; each flip at \(c_0(p)\) [L]; all pole-mediated. |

Every positivity route uses the first source. The atomic routes now also use gauge charge, but only at its major arcs (D).

### D. Atomic families: the overlap window (T)

SRT, AIP, HF and ACS share one family.

| Regime | Statement |
|---|---|
| Fixed \(c\) [L] | Positive for every profile without real Fourier zeros. Low spectrum = completed conductor spectrum. Pole ground state; bottom \(\to E(c)\). |
| Bounded ranges [K] | One horizon for \(0<c\le K\) (tilted spline). |
| Mechanism [L] | Shells \(n=km+h\) carry Ramanujan weights; Möbius inversion and Poisson summation repay \(-\log c\); \(E(c)\to0\) by Stirling. |
| Arithmetic [L/K] | Linear fixed-modulus PNT in progressions; every inverse-log rate. |
| Growth = RH [L/K] | \(c_N^4\gg\log N\) (\(C^2\)); \((\log N)^\varepsilon\) (smooth); iterated log (Steklov). |
| In between | An existential positive schedule [L]; rates, conductor uniformity and the location of the transition are open. |

The four routes share one open problem: positivity at growing resolution with errors below \(E(c_N)\) (Q1). [Shells repay](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheShellsRepayEveryConductor.lean), [window](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheBottomOfTheCompleteWeilSpectrumIsTheCompletedShellEnergy.lean), [every profile](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/EveryProfileWithoutRealFourierZerosIsPositiveAtEveryOverlap.lean).

### E. One coordinate: the atomic programme and the census (T)

| Statement | Overlap \(X/T\) | Bandwidth |
|---|---|---|
| Montgomery pair correlation | \(\to0\) | \(<1\) |
| Complete positivity (theorem) | every fixed \(c\) | \(\to1\) |
| RH, atomic receiver (\(C^2\)) | \(\gg(\log N)^{1/4}\) | \(1+o(1)\) |
| RH, Steklov receiver | \(L(\log L)^2\log\log L\) | \(1+o(1)\) |
| \(70\%\) census | \(\asymp T^{1/9}\) | \(10/9\) |
| \(75\%\) census | \(\asymp T^{1/3}\) | \(4/3\) |

Bounded-overlap positivity is now proved up to bandwidth \(1+o(1)\). RH asks for a sign a little further along the same axis. The census asks for averaged information far past it. [Coordinates](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/OverlapCoordinates.lean), [census coordinates](../../../formal/GaloisForLFunctions/RHTower/CensusLengthHeightCoordinates.lean).

### F. The gauge torus: one point, many statistics (E + T)

| Statistic at \(0\) | Haar-a.e. twist | At \(0\) | Routes |
|---|---|---|---|
| Möbius partial sums | exponent exactly \(1/2\) | \(\Theta\) (RH) | MC, WL |
| Constant source | exponent \(1/2\) | \(1\) (the pole) | — |
| Twisted \(\psi\) | square-root, no pole | pole, then RH | WL, PBM |
| Successor correlations, near-incidences | gauge charge | Chowla / additive divisor at \(0\) | MC, CTF, HF, ACS |
| Shells of the prime pair form | deleted by Haar | major arcs at level \(q\mid j\) pay bounded overlap | HF, AIP, SRT, ACS |
| Coalescent surplus | budget \(0\) | open | ACS census |
| Escape states | full gauge mass | RH; the Möbius escape state is blind to zeros | PM |
| Vertical hull | the orbit; exponent constant on the line | strong recurrence | BAG |

The exceptional set is residual and null, and \(0\) lies in its closure. Dirichlet points read GRH and are typical on average. [Typical exponent](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheTypicalExponentIsOneHalf.lean), [not gauge invariant](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheExponentIsNotGaugeInvariant.lean), [escape state](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheEscapeStateLeansToTheLiouvillePoint.lean).

### G. Hecke towers, Toeplitz symbols and aliasing (T)

| Face | Result |
|---|---|
| One prime tower | Index = distinct outer eigenvalues; RH iff positivity on all \(p\)-towers. |
| Nyquist and heights | \(\kappa_T=O(T\log T)\); the tower \(3^k/2^j\) certifies height \(T\); at most \(\binom{\kappa_T}2\) primes alias. |
| Fine towers | Consecutive-ratio towers decide every orbit kernel; two primes contain fine towers. |
| Attained depth | Seen by almost every prime. |
| Locality | Every tower statement holds for every unitary twin. |
| HCF grids | One grid aliases; two decide. |
| Compressions | Euler compressors kill no strip pair. |

The tower language identifies the problem without supplying selection. [Fine towers](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/FineTowersDecideEveryOrbitKernel.lean), [locality](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/LocalityIsTwinBlind.lean).

### H. The finite-support stratum is Krein–Langer finiteness (E + T)

| Face | Routes | Statement |
|---|---|---|
| Kernel index | HKT, HF, ACS, AIP | \(\kappa(K_\zeta)<\infty\), on \(\mathbb Q_{>0}^\times\) or on two primes |
| Wave number | AKLT, WD | Finitely many waves leave a bounded remainder |
| Heat flow | WD, LA | \(N(t)\) bounded; collision mass \(=2(\kappa+\)excess\()\) |
| Critical energy | HF, SRT, ACS | \(\mathcal E_{\rm crit}<\infty\) |
| Complete-form index | HF, ACS, AIP | The last layer \(k=1\) |
| Subtracted lag | WL | Lag minus finitely many waves bounded on one side |
| Prime towers | AKLT | At most \(\binom\kappa2\) blind primes |

It is RH above a height and implies LH. [TFAE](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean).

### I. Width, rate, strip, integrality and work currencies (E + T)

Fixed strips have exact one-sided readings: escaped Möbius rates, Hecke-defect caps, theta prefixes, Vaughan savings, the Chebyshev Cesàro energy, the integrality exponent and the gauge exponent at \(0\).
\[
\mathcal E_{\rm crit}\le\text{one quantum}\iff\mathrm{RH}\Rightarrow\mathcal E_{\rm crit}<\infty\iff\text{finite support}\Rightarrow\text{LH}\wedge\Theta<1 .
\]
Density envelopes never cross into this chain. [Density no-go](../../../formal/GaloisForLFunctions/RHTower/DensityEnvelopeNoGo.lean).

### J. Producers and counting faces (S)

| Face | Ledger | Precision |
|---|---|---|
| Stepanov over \(\mathbb F_q\) | \(\sum m_x\le\deg P\), \(m\approx\sqrt q\) via \(x^q=x\) | Square root, both parity classes |
| Bézout and Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) | \(\prod p^{m_p}\le N\); \(h^0=\lfloor N/\prod p^{m_p}\rfloor\) | Exact, linear |
| Integer auxiliaries | Small = divisible | No gain from smallness |
| Binomials, factorial ratios | \(\sum m_p\log p\le\log A\); bounded multiplicity above \(\sqrt{\text{length}}\) | Linear, primes only |
| Self-maps of \(\mathbb Z\) | Identity or unit-ball gauge points | No growth |
| Adams operations on \(G\) | \(\psi^q\)-fixed = \((q-1)\)-torsion twists | Unused as a producer |
| Census, canonical energy, heat | Proportions, index prices, collision counts | Not exclusion |

Only over \(\mathbb F_q\) is a count produced, because one endomorphism is additive and multiplicative at once. [Ring endomorphisms](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/ApproximateRingEndomorphisms.lean), [Adams](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheAdamsOperations.lean), [Riemann–Roch](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheRiemannRochTheoremOfTheMultiplicativeGroup.lean).

### K. Displacement at depth \(1/\log T\) (S)

The census dichotomy puts every failure of \(70\%\) into simple off-line zeros within \(A/\log T\) [K]. Four results are blind exactly there:

- value moments;
- shallow Cauchy energy;
- zero-side slack;
- pair correlation.

The census, WD and SCP fail at the same place. [Dichotomy](../../../formal/GaloisForLFunctions/RHTower/Zeta23SeventyPercentOrSimpleNearLine.lean).

### L. Möbius admission, Haar approximation and escape (E + T)

MC, PM and CTF share Möbius arithmetic.

- CTF's residual is \((1-\Lambda\text{-readout})^2\) plus centered energy. Its covariance is the completed cyclotomic Gram, and every superlinear exponent is carried by the nonnegative cyclotomic remainder [S].
- PM's criterion is positive gauge mass. The Möbius escape state is an Euler product leaning to the Liouville point, blind to zeros [L].

### M. Heat, Jensen, Ward, moment and seam formulations (E + T)

- LA and WD share finite-head and heat geometry.
- TH and HCF expose moment and grid signs; PA exposes all-order passivity.
- HJ's residual equals SEC's seam charge, and all-divisor vanishing matches HCF's two-grid sign.
- Heat collisions count the index (H).

### N. Reference energies and the shell repayment law (T)

- RAPT, CACT and CAF link finite-prime adjunction to the actual matrices. Adjunction energies continued past touching lose \(\log c\); the shells restore them, and the completed conductor energies are the actual low spectrum at every fixed overlap.
- Cyclotomic Gram completion with exact Dirichlet–Schur cost; prime-prefix domination; prefix Schur reduction and prefix index \(\le N-M\).

[Positive Fourier integral](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheCompletedShellEnergyIsAPositiveFourierIntegral.lean), [pole ground state](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ThePoleConductorMinimizesTheCompletedEnergy.lean).

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
| Point side | Stepanov auxiliaries; integer polynomials on \([0,1]\); integer Dirichlet polynomials along Frobenius progressions; factorial ratios | Producers over \(\mathbb F_q\); over \(\mathbb Z\) exact but linear |

Every candidate whose mechanism is a vanishing law at zeros is a detector; its promotion needs a point-side input (inference).

### R. Prime-free existence and the blind cone (E)

RH iff, for every aperture, some real weights make \(\zeta\)'s full functional nonnegative up to that aperture [L]. The dual obstruction is EWU's blind test; the certificate is \(\Lambda\).

### S. Every U2 route is a resolution filtration (S; T for atomic families)

Each U2 route has a resolution parameter. Positivity at a fixed level is weak or provable; RH is positivity along a schedule fast enough to synthesize a negative test.

| Route | Parameter | Fixed level | RH schedule | Margin |
|---|---|---|---|---|
| HF, AIP, ACS, SRT | overlap \(c\) | theorem at every \(c\) [L] | \(c^4\gg\log N\); iterated log (Steklov) | \(E(c)\), exact Poisson tail |
| RW | aperture \(A\) | small-aperture floors | every \(A\) | decays doubly exponentially; no identity |
| TH | rank | rank seven strict [L] | all ranks | tails strict past a log horizon; center open |
| PA | Hausdorff order | each order at large shift | all orders, all shifts | none |
| LA, WD | degree, height, heat time | finite heads; horizon \(2\pi e^{(2/3+\varepsilon)/t}\) | all heights | none |
| HCF | degree on two grids | fixed rank signs | all degrees | none |
| SZ | tent level | moving-aperture limits | factorial/grid families | none |
| EWU, OWU | aperture | restricted floors; witnesses at fixed radii | every aperture | none |
| GTA | rank | finite-rank charges | rank-uniform decay | none |

Only the atomic filtration has positivity at every level with an exact margin. The working transfer question (W21): does another filtration admit a Poisson-type identity for its margin (inference)?

### T. One Poisson structure under theta and atomic positivity (S)

- **Atomic.** The margin is a Poisson remainder \(\int|\hat\varphi|^2\) over a tail [L].
- **Theta.** The seam tail is a Plancherel Gram, and center tails are aperture-free [L/K].
- **Shared.** Both are squares of Fourier transforms produced by Poisson summation on \(\mathbb Z\), the additive structure.
- **Analogy.** TH's open compact-center region is the theta analogue of the atomic window (inference).

### U. Selectivity is resolution on the gauge torus (T + inference)

| Gauge point | Resolved at |
|---|---|
| Liouville point (antipode) | \(c\ge1\) for a tilted box plateau [S] |
| Flip \(\omega_p\) | \(c\ge c_0(p)\); \(c_0(p)\to\infty\) [L] |
| Large flips at fixed \(c\) | not resolved: \(8\log p/\sqrt p<E(c)/2\) [L] |
| Twin tails | exponent \(1\) [L]; overlap threshold open |
| Vertical shifts of \(0\) | same exponent \(\Theta\) as \(0\) [L] |

Flips close to \(0\) need large overlap; the full twin needs little. RH asks whether \(0\) itself becomes resolvable from \(\Lambda\)'s own positivity at some \(c_N\) (Q3).

## Complete live-route crosswalk

"Source" names the selective source the route uses: **P** = pole/Gamma; **G\(_{\rm maj}\)** = gauge charge at its major arcs; **—** = neither yet. Every RH-strength item also needs \(0\)-specific information beyond these.

| Route | Core / cluster | Distinct producer obligation | Source | Filtration | Stratum below RH |
|---|---|---|---|---|---|
| **WL** | U1; A, B, F | One-sided count; Chebyshev ledger | P | horizon | Subtracted lag [FS] |
| **FU** | U1 | Scheduled Abel history | — | schedule | — |
| **CFC** | U1; A | First-clock tail bound | P | aperture tail | — |
| **RP** | U1 | Linear floor | — | history length | — |
| **MC** | U1; B, F, I | Half-power; odd class; \(\theta_\mu(0)\) | — | horizon | Power saving [≥QRH] |
| **LI** | U1 + G | Primitive history; ladder sign | — | ladder rank | — |
| **PM** | U1 + L, F | Positive gauge mass | — | damping | Exterior tightness [open] |
| **JAS** | U1 | Square-root budget | — | prime budget | — |
| **CTF** | U1 + L | Covariance upper control | — | cutoff | — |
| **PBM** | U1 | Cancellation to \(\sigma>1/2\) | P | abscissa | Abscissa \(<1\) [≥QRH] |
| **RB** | U1 | Saturated extremizers | — | extremizer size | — |
| **RW** | U2 | Aperture relaxation | P | aperture | — |
| **TT** | U2 | Reflected-prime covariance | — | scale | — |
| **HF** | U2 + U1 + U3; C, D, E, N, S | Window rate; residual; work ceiling | P + G\(_{\rm maj}\) | overlap | Finite index [FS]; window [open] |
| **CHMD** | U2 | Residual modulo radical | P | cutoff | — |
| **SZ** | U2 | Tent-family sign | P | tent level | — |
| **EWU** | U2 + R | All-aperture blind minima | P | aperture | — |
| **OWU** | U2 | All-aperture odd sign | P | aperture | Conductor/forcing [open] |
| **SRT** | U2 + U1; D, E, G, U | Window rate; tower sign; late lag | P + G\(_{\rm maj}\) | overlap, generator | Window, unattained depth [open] |
| **ACT** | U2 | One shift for every profile | P | profile support | — |
| **AIP** | U2; C, D | Window rate; allocation | P + G\(_{\rm maj}\) | overlap | Window [open] |
| **ACS** | U2 + U3; D, E, K | Index zero; census; quadratic count | P + G\(_{\rm maj}\) | overlap; bandwidth | Finite index [FS]; census [open] |
| **PA** | U2 (moment) + M | All-order sign | — | order | — |
| **LA** | U2 (heat) + M | All-height heads | — | degree, height | Heat count [FS] |
| **TH** | U2 (moment) + M, T | Compact-center compensation; all ranks | — | rank | Rank eight [open] |
| **WD** | U2 (heat) + H, K | Cap extinction | — | heat time | Count [FS]; high count [LH] |
| **HCF** | U2 (heat) + G | Both grids | — | degree | Many-node floor [open] |
| **TG** | U3 | Positive residual, trace \(<1\) | — | disc | — |
| **RN** | U3 | Directed boundary work | — | — | — |
| **XN** | U3 | Paid curvature | — | discs | — |
| **BAG** | U3 + F | Every right-strip point | — | tolerance | — |
| **GTA** | U3 | Rank uniformity | — | rank | — |

**Strongest shared programmes.**

- **Window programme** (HF, SRT, AIP, ACS; D, E, N, S): positivity at growing resolution and the location of the RH transition (Q1).
- **Producer programme** (MC, WL, U3; B, J, Q): an Adams-built, additively coupled auxiliary (Q2).
- **Resolution programme** (MC, PM, BAG, HF; C, F, U): how overlap resolves gauge points (Q3).
- **Filtration-transfer programme** (RW, TH, PA, LA, HCF, SZ, EWU; S, T): import exact-margin identities (W21).
- **Finite-support programme** (H): a Krein–Langer problem at Lindelöf level.

## Candidate crosswalk

The 17 candidates and PW-B are U3 producers whose landing is unproved. Each landing must fail the battery. It must not be gauge-invariant or finitely determined. "Side" records where the established mechanism acts (inference).

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
| **W1C** | U3→real-rooted \(\Xi\) | Prime side | No arithmetic ferromagnetic limit. |
| **WBF** | U3→U2; certificates | Unspecified | No arithmetic coupling. |
| **PW-B** | U3→U1; PM complete energy | Zero-indexed | Zero-indexed action. |

## Unifications that are not valid

| Tempting identification | Correct distinction |
|---|---|
| Every RH receiver is one programme | Endpoint equivalence is E; producers differ. |
| Fixed-overlap positivity is RH | It is an unconditional theorem; RH needs \(c_N\to\infty\) past the synthesis threshold. |
| Positivity at every fixed \(c\) gives an explicit growing schedule | Only an existential schedule; rates need uniformity in \(c\) and conductor. |
| The shell repayment controls gauge charge at \(0\) | It uses only the major arcs (fixed-modulus PNT). |
| The Liouville rejection at fixed \(c\) rejects all twins | Flips need \(c\ge c_0(p)\to\infty\); no fixed overlap rejects all. |
| The global law reduces RH to counting | It identifies the endpoint; the count must still be produced. |
| The count and positivity are the same property | Equal at \(\Lambda\); as weight properties their stabilizers differ. |
| Multiplicative or gauge-invariant data can certify \(0\) | They give \(\ge3/4\) at \(0\). |
| Averaged typicality of the special locus decides a point | The large sieve is typical on average, never at one point. |
| \(W\), the collided form and the prime-only form are interchangeable | The collided form is positive but its invariance is the problem; prime-only forms omit Gamma and poles. |
| Atom-normalized floors survive growing overlap | The adjacent dipole's mass ratio tends to \(0\); the true margin is \(E(c)\). |
| Finite support gives fixed-ratio positivity | A tempered finite-support model is negative at every ratio; \(\zeta\)'s fixed-\(c\) positivity uses its zero density. |
| Short-interval statistics or finite apertures decide | Precision rigidity; deciding input; window law. |
| One prime tower decides | It aliases; the golden curve passes its tower and fails the lattice. |
| A vertical shift is the parity twin over \(\mathbb Z\) | It equals \(-1\) at no more than one prime; the twin lives in the Bohr closure. |
| Self-maps of \(\mathbb Z\) or the Adams operations give a Frobenius on \(\mathbb Z\) | Self-maps are trivial; Adams operations act on characters and fix \(0\). |
| Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) gives a Hodge index | It is linear; a Hodge index needs a quadratic Euler characteristic. |
| Small auxiliaries are cheaper than vanishing ones | For integer auxiliaries small = divisible. |
| Iterating integer twists adds independent constraints | The twist tower collapses to level \(0\). |
| Compression or divisibility produces parity | Compression is a receiver; divisibility sees prime powers, not parity. |
| A positive correction repairs a finite index | A positive part never pays a pair. |
| Finite negative index means RH | It means finite support. |
| The \(2/3\) census is a route to RH | Proportions do not exclude zeros. |
| Better density exponents yield a strip | Envelopes never drop below \(1\). |
| Infinite symmetry confines the zeros | Confinement is the lower square-root count. |
| Index continuity can deform \(\zeta\) to index zero | \(\Lambda_{\rm dBN}\ge0\) blocks openness at \(\zeta\). |
| Curves over finite fields donate Weil positivity | The archimedean continuum cannot arise from finite places. |

## How to organize research around the unification

1. **Window programme** (U2; D, E, N, S): quantify positivity at growing overlap; locate the RH transition; tilted Steklov (Q1; W01–W07).
2. **Producer programme** (U3; B, J, Q): Adams-built auxiliaries coupled to additive structure (Q2; W22).
3. **Resolution programme** (U1 in gauge language; C, F, U): flip and twin thresholds as a law on \(G\) (Q3; W08, W10).
4. **Filtration transfer** (S, T): exact-margin identities for RW, TH, PA, LA, HCF, SZ, EWU (W21).
5. **Exploratory**: Roth-type typicality of the special point ([2.4](obstacles-summary.md#24-is-there-a-wildly-different-route)); the Poisson–Weil decomposition ([2.5](obstacles-summary.md#25-where-a-real-breakthrough-on-the-hard-questions-could-come-from)).
6. **Finite-support programme** at Lindelöf level (H), as a diagnostic.
7. **External extraction** of the quasi-RH threshold (W17).

No route is promoted because its final condition was renamed, and no candidate is retired because another route reaches the same endpoint.
