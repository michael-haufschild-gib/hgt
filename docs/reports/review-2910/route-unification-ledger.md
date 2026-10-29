# Route-unification ledger

Status: 29 October 2026, corpus checkpoint `7f191801a3` plus working tree. **The 31 live routes and 19 candidate branches are faces of three core problems: the selective critical sign (U1), source-complete positivity (U2) and an independent producer (U3).** Seven facts bind them:

1. **Selectivity is common to all three by theorem.** No twin-blind input reaches an RH-complete family. The margin \(2\log2\) separates \(\zeta\) from Liouville but is shared at its maximum by single flips \(p\ge11\).
2. **Precision is common to all three, but U1 and U2 sit in different precision classes.** Any property implying the count rejects \(\Lambda+\varepsilon n^{-\eta}\) [S]. As properties of weights, counts see only the square-root class while tower positivity sees every coefficient [S/L].
3. **U1 and U2 are one endpoint.** Index zero of the Weil kernel is the one-sided \(\psi\) count and already one parity class's upper count [S]. U3 is the search for a producer of that count; the corpus shows it must act on the point side.
4. **Hecke towers join U1 and U2 entry by entry.** U2 cross-level entries are U1 prime-error sequences; tower positivity is RH for one prime at every generator size.
5. **U2's atomic face has a proved bounded-overlap regime.** Complete positivity at fixed ratio \(c\le1+10^{-18}\), selective against the Liouville twin [L/S]. RH is the same positivity at overlap \(c_N\asymp\log\log N\) [L]. Every atomic-family route shares this overlap frontier.
6. **The finite-support stratum is one statement.** Finite index, two-prime index, wave number, heat counts, critical energy, subtracted lag, cosine defects and "critical above a height" are equivalent; all imply LH and a fixed strip.
7. **Locality is twin-blind.** No route or candidate can land through local tower data alone [L].

[Route obstacles](route-obstacles.md) · [summary and priorities](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [frontier map](../rh-current-frontier-map.md). Evidence: corpus searches and Lean statements; no builds. **[L]**/**[S]**/**[K]** as in the frontier map; **(inference)** = conclusion of this review. [Working log](../../../logs/review-2910b-research-2026-10-29.md).

## What "the same problem" means

| Relation | Meaning | What it does not mean |
|---|---|---|
| **E — Endpoint equivalence** | Two stated conditions are both equivalent to RH, or to each other. | A usable estimate between the producers. |
| **T — Proved source transfer** | An identity, approximation or inequality carries the actual source from one formulation to another. | Extension to growing supports, overlap, primes, degrees or another norm. |
| **S — Structural similarity** | Two approaches face the same kind of sign, exhaustion or faithfulness problem. | A theorem identifying their objects. |

All RH criteria are E-equivalent almost tautologically. Unification is meaningful through T-bridges and a shared unproved producer.

## The three core problems

| Problem | The one missing statement | Faces (routes) | Wall |
|---|---|---|---|
| **U1 — Selective critical sign** | A bound on the actual signed prime/Möbius discrepancy at the critical scale, in some currency (one-sided count, one parity class, history floor, integrality half, inversion). | WL, FU, RP, MC, LI, PM, JAS, CTF, PBM, RB; prime-error faces of HF/SRT/AIP; via the Chebyshev identity, the off-diagonal of every U2 route. | 1 |
| **U2 — Source-complete positivity** | Index zero of the complete Weil form, with Gamma and both poles, on a source-complete family; on atomic families, positivity under overlap growth. | RW, TT, HF, CHMD, SZ, EWU, OWU, SRT, ACT, AIP, ACS, HCF; via sign receivers PA, LA, TH, WD. | 1 and 3 |
| **U3 — Independent producer** | A source-built structure whose proved property supplies the U1 count or U2 index zero: over \(\mathbb Z\), a point-side auxiliary or a structural constraint on a polar divisor. | TG, RN, XN, BAG, GTA, all 18 candidates and PW-B; geometric faces of HF/ACS; the Stepanov question; ISC-polar (its confinement is the lower square-root count). | 14 |

**Cross-cutting requirements on every producer.**

| Requirement | Status | Test object |
|---|---|---|
| Selectivity | Theorem [L] | Liouville, \(c\Lambda\), quadratic mixtures fail. |
| Beyond the margin | Theorem [L] | Single flips \(\omega_p\), \(p\ge11\) (maximal gap), cofinite flips (gap \(0\)) fail full positivity. |
| Parity | Theorem [S] | Deciding-input theorem: any count-implying property rejects the Liouville twin. |
| Precision | Theorem [L/S] | \(\Lambda+\varepsilon n^{-\eta}\), \(\eta<\tfrac12\), fails; for positivity statements also \(\Lambda+1/n\). |
| Two primes | Theorem [S] | One prime aliases; the golden curve passes its tower and fails the lattice. |
| Non-locality | Theorem [L] | Every unitary twin passes the same tower statements. |
| Unbounded overlap or aperture | Theorem [S] + inference | Finitely determined properties never imply the count; bounded overlap is not known to be RH-complete. |
| Point side | Theorem [S] + inference | Zero-side annihilation certifies nothing over \(\mathbb F_q\) and is index-neutral for Euler factors over \(\mathbb Z\). |

## Strongest unifications

### A. U1 and U2 meet entry by entry (T)

For \(\operatorname{supp}f<b<\operatorname{supp}g\): \(W(f,g)=-\int_0^\infty(e^h-\psi(e^h)-c)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g)\). On the pole hyperplane only the prime comb is left. WL/FU/RP/PBM and HF/ACS/AIP/RW/OWU ask for the same signed quantity in different test norms. The pole product, which alone grows across scales, is cancelled by the prime main term \(e^h\); this is where \(\Lambda\) differs from Liouville (prime sum \(\approx-e^h\)) and from character twists (\(o(e^h)\)). [Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean).

### B. U1 and U2 meet at the endpoint: positivity = index = count = one parity class (E, with an S-bridge to \(\mathbb F_q\))

| Language | Statement | Route |
|---|---|---|
| Count | \(\psi(x)-x\le C\sqrt x\log^2x\) eventually, either sign | WL, MC |
| Parity class | \(\sum_{\lambda(n)=-1}e^{-nt}/n\le\tfrac12(\sum e^{-nt}/n+Ct^{1/2-\varepsilon})\) | MC, WL |
| Integrality | Each half of integer-polynomial integrality at square-root scale | MC, WL |
| Index | \(\kappa(K_\zeta)=0\) | HKT, HF, ACS |
| Positivity | Weil Grams of integer atoms positive semidefinite; atomic positivity at \(c_N\) | SRT, AIP, HF |
| \(\mathbb F_q\) | Lower point count \(\iff\) trickle-down \(\iff\) index zero; upper counts on the twist tower \(\iff\) unitarity | ALG, ACP, AKLT |

The E-part is tautological. The content is that the \(\mathbb F_q\) proof runs in the same language: Riemann–Roch bounds the index, Stepanov produces an upper count, the twist tower completes it. Over \(\mathbb Z\) the missing step is located: a producer for one parity class (U3). [Global law](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheGlobalLawIsTheOneSidedSquareRootCount.lean), [parity form](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheParityFormOfTheGlobalLaw.lean), [twist tower](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheTwistTowerCompletesTheUpperCount.lean), [integrality exponent](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheIntegralityExponentIsTheZeroWidth.lean).

### C. One margin, one pole: the selective inputs that are proved (T)

RW, HF, ACS, AIP, OWU, EWU, SRT, SZ, CHMD and ACT reduce on atomic or complete sources to one form: the pole hyperplane is the harmonic hyperplane; \(\zeta\)'s gap is \(2\log2\), Liouville's \(0\); at every width the sign is the Markov gap on \(p=0\) plus one affine scalar. In HKT language the margin is the width of an index-one window [S]. At bounded overlap the pole pays the full form: the complete matrix is positive definite through \(c=1+10^{-18}\) by prime-defect coercivity from the plateau's variance reserve, while the Liouville twin, whose Dirichlet series \(\zeta(2s)/\zeta(s)\) lacks the pole, is negative from \(c=1/2\) [L/S]. Both inputs are parity-selective; neither is shown to separate \(\zeta\) from \(\omega_p\). [Margin](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheSelectiveMarginIsTwoLogTwo.lean), [Trans-Metzler](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TransMetzlerPositivity.lean), [twin](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/LiouvilleTwinSelectivity.lean).

### D. Atomic families: bounded overlap is proved, overlap growth is RH (T)

SRT, AIP, HF and ACS share one family. Proved: positivity at every fixed \(c\in(0,1+10^{-18}]\) [L]; the Markov form fails above \(e/2\pi\) [L]; integer atoms at fixed width carry the whole index [S]. RH: positivity at \(c_N=(\log\log N)(\log\log\log N)^\beta\), \(\beta>2\) [L]. Under finite support the atomic index is bounded uniformly in \(c\); a tempered model is negative at every \(c\) [S]. The four routes therefore share one open problem: a positivity theory uniform in overlap (Q1). [Super-Gevrey](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/SuperGevreyCriticalGrowth.lean), [zero-side stratum](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/ZeroSideStratum.lean).

### E. Hecke towers, Toeplitz symbols and aliasing (T)

| Face | Result |
|---|---|
| ACS/HKT one-prime tower | Index = distinct outer eigenvalues \(p^{\rho-1/2}\); RH iff positivity on all \(p\)-towers. |
| SMAP pole-free generators | Same for generators in \([-\varepsilon,\varepsilon]\). |
| HKT Nyquist / ASRP phases | Windows shorter than \(2\pi/\log p\) are fully seen; two primes separate every ordinate difference polynomially. |
| HKT/AKLT two primes, blind primes, fine towers | Two primes carry the index; \(\le\binom\kappa2\) blind primes; fine towers decide the orbit index. |
| AKLT locality | Twin-blind: every tower statement holds for every unitary twin. |
| HCF grids | One grid aliases a pair to a positive atom; two grids decide. |
| LI / ALG Cayley ladder | RH iff the Cayley–Li Toeplitz ladder is negative semidefinite on primitive vectors. |
| ACP Stepanov mechanism | \(1-T_p^N\) kills a zero symbol iff the zero is critical and on a height lattice. |
| HKT/AKLT compressions | Compression kills a pair iff its character is annihilated; Euler compressors kill none in the open strip. |

**Unifying statement.** Along a \(T_{\log p}\)-tower the explicit formula writes the lag sequence as a sum over zeros of \(p^{d(\rho-1/2)}\); off-line zeros are hyperbolic characters; positivity is their absence. HCF aliasing, the Stepanov lattice criterion and the Nyquist law are one aliasing; a second prime removes it. Locality being twin-blind, the tower language identifies the problem without supplying selection. [One prime](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OnePrimeSeesTheWholeDefectOfZeta.lean), [two grids](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/OneGridHidesTwoGridsDecide.lean), [locality](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/LocalityIsTwinBlind.lean).

### F. The finite-support stratum is Krein–Langer finiteness (E + T)

| Face | Routes | Statement |
|---|---|---|
| Kernel index | HKT, HF, ACS, AIP | \(\kappa(K_\zeta)<\infty\), on \(\mathbb Q_{>0}^\times\) or on two primes |
| Wave number | AKLT, WD | Finitely many exponential waves leave a bounded remainder on a separating tower |
| Eventual criticality | all | Every zero above some \(T_0\) is critical |
| Heat flow | WD, LA | \(N(t)\) bounded; collision mass \(=2(\kappa+\)excess\()\) |
| Critical energy | HF, SRT, ACS | \(\mathcal E_{\rm crit}<\infty\) |
| Complete-form index | HF, ACS, AIP | Last layer \(k=1\) of the finite-index chain |
| Subtracted lag | WL | Lag minus finitely many exponentials bounded on one side |
| Cosine defects | WD | Uniformly bounded |

Every face says: the Weil kernel is positive-definite modulo finitely many exponential characters. A positive part never pays a pair, so no positive majorant produces finiteness; an index ceiling must come from structure, as Riemann–Roch supplies it over \(\mathbb F_q\). The stratum is RH above a height and implies LH. [TFAE](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean), [wave number](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheCollisionMassIsTheWaveNumber.lean).

### G. Width, rate, strip, integrality and work currencies (E + T)

Fixed strips \(\Theta\le\tfrac12+c\) have exact one-sided readings in escaped Möbius rates, Hecke-defect caps, theta-prefix growth, Vaughan power savings, the Möbius-divisor Abel moment, Suzuki residuals, balanced short-window savings, the Chebyshev Cesàro mean-square energy and the integrality exponent. Work and depth:
\[
\mathcal E_{\rm crit}\le\text{one quantum}\iff\mathrm{RH}\Rightarrow\mathcal E_{\rm crit}<\infty\iff\text{finite support}\Rightarrow\text{zeros approach the line}\Rightarrow\text{LH}\wedge\Theta<1 .
\]
Density envelopes never cross into this ladder, even at \(30/13\). [Abscissa laws](../../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean), [density no-go](../../../formal/GaloisForLFunctions/RHTower/DensityEnvelopeNoGo.lean).

### H. Counting faces (S)

These results locate zeros by counting:

- over \(\mathbb F_q\), the square-root count, produced by Stepanov and completed by the twist tower;
- over \(\mathbb Z\), the one-sided \(\psi\) count and one parity class's upper count (B);
- the census counts critical zeros through Sylvester signatures with three exact exchange rates;
- canonical energy pays each off-line quartet a quantum; the index is priced quadratically;
- heat collisions and exceptional waves count the index.

Only over \(\mathbb F_q\) is the count produced.

### I. Displacement at depth \(1/\log T\) (S)

The census dichotomy puts every failure of \(3/4\) into simple off-line zeros within \(A/\log T\) of the line [Lean]. Four results are blind exactly there:

| Face | What is blind |
|---|---|
| Value moments (mimicry) | Equal-valued reflected pairs look critical. |
| Shallow Cauchy energy | The majorant sums over all zeros of the window. |
| Zero-side slack | Displaced pairs with \(\eta<1/18\) (for \(70\%\)) or \(\eta<1/6\) (for \(75\%\)) carry too little slack (inference from [L]). |
| Pair correlation | A pair at depth \(\asymp1/\log T\) looks like a double point. |

This is one obstacle: the census, WD and SCP fail at the same place. [Slack](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/SpectralSlackConservationAndTheHyperbolicDisplacementThreshold.lean), [dichotomy](../../../formal/GaloisForLFunctions/RHTower/Zeta23SimpleOffLineNearLine.lean).

### J. Möbius admission, Haar approximation and chronological residuals (E + T)

MC, PM and CTF share Möbius arithmetic; CTF's residual is \((1-\Lambda\text{-readout})^2\) plus centered energy; PM's criterion is positive gauge mass for every escape state. The common unpaid input is complete signed energy at small damping. [Visibility](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/RHIsTheVisibilityOfEveryEscapeState.lean).

### K. Heat, Jensen, Ward, moment and seam formulations (E + T)

LA and WD share finite-head/heat coefficient geometry; TH and HCF expose moment/grid signs; PA exposes all-order passivity. HJ's reflection residual equals SEC's seam charge; all-divisor vanishing matches HCF's two-grid sign. The heat flow links WD/LA to F: its collisions count the index.

### L. Adjunction, prime modes and gauge finite parts (T)

RAPT, CACT and ACP link finite-prime adjunction to the actual matrices: bounded spectrum = adjunction spectrum; per-conductor eigenlines of the complete Weil matrix at every \(0<c<1\) [S]; conductor coordinates for every prime pattern [L]; the Ramanujan main matrix is the reference operator of the Trans-Metzler floor [L]. These coordinates are where a large-overlap theory would be written (Q1). [Eigenlines](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSimpleCompleteWeilEigenlinesConvergeToRamanujanLines.lean).

### M. Parity and precision are one obstruction in four coordinates (S)

| Coordinate | Statement |
|---|---|
| Weil positivity (U2) | Twin-blind inputs cannot reach RH-complete families [L]. |
| Tower positivity (U1 ∩ U2) | \(n^{-\eta}\)-perturbed weights cannot both be positive [L]. |
| Counts (U1) | Deciding-input theorem: rejects Liouville, not finitely determined, square-root-class differences [S]. |
| Census | Coalescent prime pairs enter through a signed kernel [L]; two-sided asymptotics are parity problems (inference). |

A producer for any one must be parity-breaking and square-root-precise. Analytic number theory has no input with both; finite-field geometry has several.

### N. Prime-free existence and the blind cone (E)

RH iff for every aperture some real weights make the full Weil functional of \(\zeta\)'s archimedean datum nonnegative up to that aperture [L]. Its dual obstruction is EWU's blind test; its certificate is \(\Lambda\) itself. [Existence](../../../formal/GaloisForLFunctions/RHTower/WeilPositivityFiniteLevelExistenceDecidesRH.lean).

### O. Precision classes: counts and positivity are equal at \(\Lambda\) and different as weight properties (T + S)

Tower positivity implies the count [S]. The count's stabilizer among weights is the square-root class: sign gauges with flipped prime mass \(O(\sqrt x\log^2x)\), torus gauges at that distance, \(\Lambda+1/n\) [L/S]. Tower positivity's stabilizer is trivial [S]. Consequence (inference): U1 receivers cannot select \(\Lambda\) among its square-root gauge neighbours; U2 receivers can. Selection must be proved in U2 language; U1 is where a producer would most naturally act. [Precision-exact](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TowerPositivityIsPrecisionExact.lean), [gauge stabilizer](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheGaugeStabilizerOfTheCount.lean).

### P. Point side versus zero side (S)

| Side | Objects | Status |
|---|---|---|
| Zero side | Compressors \(\hat P\) vanishing at characters; characteristic polynomials; calibrated vanishing laws (BSH, CDC, HJ, IRK, SEC) | Receivers: they certify a known spectrum or detect criticality [S]. |
| Point side | Stepanov auxiliaries vanishing at rational points; integer polynomials on \([0,1]\); integer Dirichlet polynomials | Producers over \(\mathbb F_q\) [L]. Over \(\mathbb Z\) integrality is exact but speaks only at \(s\in\mathbb Z\); the analytic certificate is missing [S]. |

Consequence (inference): every candidate whose established mechanism is a vanishing law at zeros is a detector, and its promotion needs a point-side input. [Compressions](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/CompressionsAreReceivers.lean), [integer Dirichlet polynomials](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/IntegerDirichletPolynomialsAtArithmeticPoints.lean).

## Complete live-route crosswalk

| Route | Core problem / cluster | Distinct producer obligation | Selective input | Stratum below RH |
|---|---|---|---|---|
| **WL** | U1; B, O | One-sided \(\psi\) count; signed Stirling inversion | Main-term cancellation \(e^h-\psi(e^h)\) | Subtracted lag [FS] |
| **FU** | U1; Abel moment | Scheduled history | Signed prime channels | — |
| **RP** | U1; history floor | Linear floor vs linear escape | Signed hyperbola/LCM identities | — |
| **MC** | U1; B, G, P | Every strict half-power; one parity class | Actual \(\mu\) | Any power saving [≥QRH] |
| **LI** | U1 + E; Cayley ladder | Literal primitive; ladder sign | Signed clock | — |
| **PM** | U1 + J; escape visibility | Positive gauge mass | Möbius cofactors | Exterior tightness [open] |
| **JAS** | U1; prime budget | Logarithmic → half-power budget | Prime-product sign | — |
| **CTF** | U1 + J; residual | Readout and centered energy | \(-\mu_N\) readout | — |
| **PBM** | U1; regularized series | Cancellation to \(\sigma>1/2\) | Actual coefficients | Fixed abscissa \(<1\) [≥QRH] |
| **RB** | U1; extremal remainder | Saturated extremizers | Divisor arithmetic | — |
| **RW** | U2; ground energy | Aperture relaxation | Margin on low and polar modes (C) | — |
| **TT** | U2; odd/covariance | Reflected-prime correlation | Signed reflected primes | — |
| **HF** | U2 + U1 + U3; C, D | Overlap growth; residual sign; work ceiling | Pole (C); cross-level cancellation (A, E) | Finite index [FS]; overlap [open] |
| **CHMD** | U2; wave/Doob | Residual sign modulo radical | Primitive defect | — |
| **SZ** | U2; first variation | Tent-pattern sign | Low modes | — |
| **EWU** | U2 + N | All-aperture low/mixed payment | Weight rigidity | — |
| **OWU** | U2; odd weight | All-aperture odd sign | Finite-aperture witnesses | Conductor/forcing [open] |
| **SRT** | U2 + U1; D, E | Overlap growth; tower sign; late lag | Pole (C) | Overlap; \(O(\log\log N)\) completeness [open] |
| **ACT** | U2; one shift | One shift for every profile | Exterior primes | — |
| **AIP** | U2; C, D | Overlap growth; coarse/cross-level allocation | Pole (C) | Overlap [open] |
| **ACS** | U2 + U3; D, H, I | RI/height/chirality or index zero; census inputs; polar-divisor test | Pole (C); towers; slack | Finite index [FS]; census [open] |
| **PA** | U2 (moment) + K | All-order sign | Prime–archimedean trace | — |
| **LA** | U2 (heat) + K | All-height heads | Xi coefficients | Uniform heat count [FS] |
| **TH** | U2 (moment) + K | Signed vectors | Theta moments | — |
| **WD** | U2 (heat) + F, I | Cap extinction | Actual divisor | Uniform count [FS]; high count [LH] |
| **HCF** | U2 (heat) + E | Both grids, all degrees | Two prime grids | Many-node Gram floor [open] |
| **TG** | U3; trace cap | Positive residual, trace \(<1\) | Euler/Gaussian source | — |
| **RN** | U3; renewal | Directed boundary work | Theta renewal | — |
| **XN** | U3; Newton discs | Paid curvature | Xi jets | — |
| **BAG** | U3; recurrence | Every right-strip point | Euler-product universality | — |
| **GTA** | U3; transverse decay | Rank uniformity | Theta Schur charge | — |

**Strongest shared programmes.**

- Overlap growth (HF, SRT, AIP, ACS; through A also WL and CHMD): one large-overlap theory of the complete form (Q1).
- Producer (MC, WL, U3; B, O, P): one point-side construction for one parity class (Q2).
- Census (ACS, WD, SCP): one displacement problem (I) and one parity problem (M).
- Finite-support stratum (HF, ACS, AIP, WL, WD, LA, HKT, AKLT): one Krein–Langer problem at Lindelöf level (F).

## Candidate crosswalk

The 18 candidates and PW-B are U3 producers whose landing is unproved. Each landing must fail for the battery. "Side" records where the established mechanism acts (inference).

| Candidate | Intended landing | Side | What prevents merger into a live producer |
|---|---|---|---|
| **APF** | U3→U2; cycle-trace orientation | Zero side (reconstruction) | Fourier recovery is not exhaustion with trace vanishing. |
| **BSH** | U3→U2; mate curvature | Zero side (calibrated vanishing) | Calibrated vanishing equals criticality. |
| **CDC** | U3→U2; descending potential | Zero side (confluence on the line) | Source-defined descent unconstructed. |
| **DR** | U3→zero-free endpoint | Zero side (roots on zero-free charts) | Cusp roots do not reach the strict-right domain. |
| **EGC** | U3→U1/U2; outer contour | Zero side (contour copies) | Inner cancellation does not orient the outer contour. |
| **EWJ** | U3→U1; depth admission | Prime side (histories) | Finite jets do not give norm exhaustion. |
| **FEL** | U3→U1; contrast balance | Both | Entropy identities are nonselective. |
| **HJ** | U3→U2; SEC/HCF residual | Zero side (residual vanishing) | Pre-divisor residual vanishing unpaid. |
| **IRK** | U3→U2; integral orientation | Zero side (Xi-jet relation) | Completed relation is not the charged lift. |
| **MSC** | U3→U2; Sonin sign | Prime side (squarefree source) | Admission and divisor transport give no sign. |
| **PCS** | U3→U1; chronological energy | Prime side (co-shift) | The co-shift defect survives. |
| **PTR** | U3→real-rooted Xi | Prime side (lossless port) | No prime-faithful lossless port without zeros. |
| **RFHM** | U3→U1/U2; grade orientation | Prime side (support/grade) | Support entropy forgets the grade. |
| **SC** | U3→U2; cross-fibre index | Index (towers) | Locality is twin-blind; a finite cross-fibre index lands only in F. |
| **SEC** | U3→U2; seam sign | Zero side (seam charge) | Asymptotic seam smallness is nonselective. |
| **W1C** | U3→real-rooted Xi | Prime side (couplings) | No arithmetic ferromagnetic limit; Bohr-torus Lee–Yang lift is the natural landing. |
| **WBF** | U3→U2; certificates | Unspecified | No arithmetic coupling. |
| **ISC-polar** | U3→zero-free endpoint; polar-divisor confinement | Zero side (polar divisor of the continued constant term) | The calculus is a receiver for every curve datum; confinement \(\iff\) the lower square-root count, so the candidate has no input beyond the count (B). |
| **PW-B** | U3→U1; PM complete energy | Zero-indexed | Zero-indexed action. |

## Unifications that are not valid

| Tempting identification | Correct distinction |
|---|---|
| Every RH receiver is one programme | Endpoint equivalence is E; producers differ. |
| The global law reduces RH to counting | It identifies the endpoint; the count must still be produced. |
| The count and positivity are the same property | Equal at \(\Lambda\); as weight properties the count's stabilizer is the square-root class, positivity's is trivial. |
| \(W\), the collided form \(D\) and the prime-only form are interchangeable | \(D\) is positive but its invariance is the problem; prime-only forms omit Gamma and poles. |
| Twin-blind positive families complete to full positivity | Impossible on RH-complete families. |
| The maximal margin selects \(\zeta\) | Single flips \(p\ge11\) attain it and fail full positivity. |
| Fixed-ratio positivity is RH-complete | RH needs overlap \(c_N\to\infty\) at the super-Gevrey rate; bounded-overlap completeness is unknown. |
| Fixed-ratio positivity selects \(\zeta\) | Shown against the Liouville twin only; flips untested. |
| Markov frustration blocks complete positivity | Complete positivity holds where no Metzler gauge exists. |
| Finite support gives fixed-ratio positivity | A tempered finite-support model is negative at every ratio; \(\zeta\)'s zero density is needed. |
| Pointwise convergence of signs preserves gaps | Cofinite flips converge pointwise to the untwisted sign with gap \(0\). |
| Short-interval prime statistics decide tower or Weil positivity | Precision rigidity; deciding-input theorem. |
| One prime tower decides | It aliases; the golden curve passes its tower and fails the lattice. |
| Local tower data select \(\zeta\) | Locality is twin-blind. |
| Positivity on the coordinate axes of \(\mathbb Z^2\) gives positivity | Locality fails; axis kernels have index \(0\) or \(\infty\). |
| Compression produces positivity | It never raises the index; zero-side annihilation is a receiver. |
| Integrality supplies square-root precision | Integrality is exact and its exponent is \(\Theta\); the certificate is the missing analytic input. |
| One twist completes an upper count | Not over \(\mathbb F_q\) (datum \(\pm2,\pm\tfrac12\)); the twist tower does. |
| Narrow generator support shortens the tower problem | Tower positivity is RH at every generator size. |
| Reducing the complete form to finitely many \(\log2\)-orbits lowers the difficulty | Orbit positivity is one-prime tower positivity. |
| Cross-level couplings are summable | Almost periodic under RH (inference). |
| Hyperbolicity of the atomic Gram is arithmetic | It holds for every sign twin. |
| A positive correction repairs a finite index | A positive part never pays a pair. |
| Finite negative index means RH | It means finite support. |
| Finite support is easier than RH at large height | It is RH above a height. |
| The \(2/3\) census is a route to RH | Proportions do not exclude zeros. |
| Simple-zero theorems raise the census | Value moments cannot separate reflected pairs. |
| Zero-side slack at small bandwidth gives \(3/4\) | False for every \(\lambda<3/4\). |
| One-sided sieve bounds control pair correlation beyond \(\alpha=1\) | The kernel is signed. |
| Better density exponents yield a strip | Envelopes never drop below \(1\), at \(30/13\) as at \(8/3\). |
| Tensor amplification of \(\zeta\) is independent of WL | Its tensor square is WL's mean square. |
| Infinite symmetry confines the zeros | Blind in genus zero; in positive genus it sees every zero exactly and places none: confinement is the lower square-root count, and the golden datum has the same calculus with an off-line pole. |
| Regular integer counts force RH | Over-regular Beurling systems. |
| \(A_Q\) is the Xi operator | Adjunction energies are prime-matrix eigenvalues. |
| Curves over finite fields donate Weil positivity | The archimedean continuum cannot arise from finite places. |

## How to organize research around the unification

1. **One large-overlap programme** (U2, D): the complete form at every fixed overlap, then uniformly up to \(\log\log N\); flips at fixed ratio as the selectivity test (Q1).
2. **One producer programme** (B, O, P, U3): a point-side construction for one parity class, first at the parity rung or the integer-Chebyshev rung (Q2).
3. **The infinite-symmetry candidate is settled** (U3, 14.45): confinement of its polar divisor is the lower square-root count, so it joins the producer programme (2) rather than forming its own.
4. **One census programme** (H, I, M): the coalescent pair energy and displacement-sensitive slack, guided by the dichotomy.
5. **One Krein–Langer programme** at the Lindelöf level (F): every result checked against LH and against "RH above a height".
6. **One vanishing-mechanism extraction** for fixed strips: the Chen–Gupta–Li threshold (W10).

No route is promoted because its final condition was renamed, and no candidate is retired because another route reaches the same endpoint.
