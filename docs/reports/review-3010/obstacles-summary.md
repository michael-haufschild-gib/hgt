# Research frontier: work, open problems and next questions

Status: 30 October 2026, corpus `66f67bc27f`. **RH remains open.**

**Bounded resolution is solved by an identity; growing resolution has its first rung.** On atomic families the complete Weil matrix is positive at every fixed overlap \(c\), and every fixed conductor packet stays positive for \(1\le c\le(\log N)^{A}\), \(A<1/48\) [L].

- Successor shells are repaid exactly by Poisson summation on the successor lattice; the margin is the aliasing tail \(E(c)=\frac2M\sum_k\frac1k\int_{kc}^\infty|\hat\varphi(2\pi t)|^2dt\).
- The arithmetic used is the prime number theorem in progressions to a fixed modulus.
- The Gamma reserve survives growing overlap while \(c_N^8=o(\log N)\) [L].

**The zeros see an atomic vector only through its Möbius horizons [L].** Single-horizon charges are blind to the real parts of the zeros. Depth enters only through two-horizon windows, i.e. through growing conductors; windowed aperture modes are Weil's box tests.

**Selectivity is a resolution theory [L].** At fixed overlap a twisted form is decided by a finite Ramanujan-packet form, and each twist has an exact resolution threshold. Pole-free twins (Liouville, cofinite flips) fall at one bounded overlap; twins that keep the pole need overlap \(\asymp p^{1/7}\).

**RH sits, conjecturally, on the critical curve \(E(c_N)\log N\asymp1\).** Margin, Gamma reserve and synthesis error are one Fourier tail, separated by the archimedean weight \(\log N\). For Gevrey and Steklov profiles the RH receiver already lies on this curve (inference).

**Over \(\mathbb Z\) no producer exists.** Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) is linear. Vanishing on the Adams fixed locus is exactly Bézout-sharp [L], and it is vanishing on characters, not on primes.

Coverage: 32 live routes, 17 standalone candidates, PW-B.

Companions: [route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md) · [scoped obstructions](../rh-killed-routes.md). Research record: [working log](../../../logs/review-3010-rev2-research-2026-10-30.md).

| Label | Meaning |
|---|---|
| **[L]**, **[S]**, **[K]** | As in the frontier map. |
| **[Lean]** | Statement read; integration not assessed. |
| **[P]** | Paper proof only. |
| **(inference)** | A conclusion of this review. |

## What the corpus establishes

- **Overlap window.**
  - Fixed \(c\) positive for every profile without real Fourier zeros [L]; uniform on bounded ranges [K].
  - Fixed packets positive up to \((\log N)^{1/48}\) [L]; residual \(c^{10}(\log N/N)^2+c^6/\sqrt{\log N}\) [L]; Gamma reserve \((\kappa c^{-7}\log N-bc)\cdot\)mass [L].
  - RH at \(c_N^4\gg\log N\) (\(C^2\)), \((\log\log N)^{s+}\) (Gevrey \(s\)), \(L(\log L)^2\log\log L\) (Steklov) [L/K].
- **Conductor spectrum.** \(E_m(c)=\log m+O_c(1)\) [L/S]; heat threshold \(\beta=1\) [L]; \(E_m(c)\asymp c^{-7}\) for \(c\ge m\) [S]; Green coordinates and inverse cost \(1/E_1\) [L]; Ramanujan frames well-conditioned to \(Q\approx\sqrt N\) [L].
- **Horizon law [L].** Zero side \(=\operatorname{Re}\sum_\rho m_\rho\hat g\overline{\hat g}\,H_a(1-\rho)H_a(\rho)\) for every vector; charge blindness; aperture modes = theta aperture currents; windows = box tests; theta and atomic positivity read one boundary \(B_N\).
- **Resolution theory [L].** Packet decision; exact monotone thresholds; flips \((p/\log p)^{1/7}\lesssim c_0\lesssim p^{1/7}\); every finite flip set; all pole-free \(\pm1\) gauges at one bounded overlap.
- **Gauge torus [L].** \(\theta_\mu(0)=\Theta\), typical \(1/2\); no gauge-invariant certificate below \(3/4\); coherence; antipode; twin inequality; special locus; short shells have no conductor; level of distribution \(1/2\); affine positivity is pole \(+\) Haar; over \(\mathbb F_q[T]\) the trivial point is better than typical.
- **Index theory.** \(\kappa\) = number of right zeros; index zero = one-sided count = odd-class upper count [S]; heights, towers, carriers, waves, polar index [L/K/S].
- **Producers [L/K].** One ledger; Bézout and Riemann–Roch for \(\mathbb G_m(\mathbb Q)\); small = divisible; no Frobenius; Adams multiplicity costs support \(2^{qr}\), sharply; factorial ratios have Chebyshev precision \(2\log2\); twist tower collapses.
- **Complete source.** Haar identities; finite index except the first prime layer; prefix Schur reduction; prefix payment with constant \(20\).
- **Theta moments.** Rank seven strict; rank eight reduced to one compensation inequality, bulk and three-atom model proved [L], piece certificates [S].
- **Heat, census, density.** \(2/3\) horizon; dissipation; \(HD(1)+10^{-8}\) and \(0.8876\); \(70\%\) dichotomy; Guth–Maynard, DH, VK, Siegel; uniform Dirichlet zero-free region [L]. No Siegel–Walfisz, no Bombieri–Vinogradov.

## 2.1 Tasks that are just work

"Just work" means the ingredients exist. A sign task delivers a certified enclosure, a quantification or a transferred proof, never a guaranteed sign.

| ID | Task / deliverable | Serves | Boundary |
|---|---|---|---|
| W01 | **Conductor-uniform residual.** Make the eight-term constant \(C_m\) explicit and polynomial in \(m\). Extend packet positivity to all conductors \(m\le M(c)\), then to the complement through a quantitative version of the finite orthogonal gap. Deliverable: an explicit unconditional full-matrix schedule \(c_N=(\log N)^{\alpha_0}\). | Q1; HF, SRT, AIP, ACS | Polynomial losses keep \(\alpha_0\) far below \(1/7\). |
| W02 | **Siegel–Walfisz** from the uniform Dirichlet zero-free region and Siegel's theorem; ineffective constants allowed. | W01 | Standard. |
| W03 | **Sharpen the residual.** Replace the coarsened \(c^{10}/\sqrt{\log N}\) by the term-by-term exponents (\(c^k/\log N\) where proved; the harmonic boundary rows separately). | Q1 | Arithmetic is not the bottleneck; harmonic rows are. |
| W04 | **Profile-adapted synthesis.** Quasi-interpolation using \(\hat\varphi\)-decay, moving the \(C^2\) receiver from \((\log N)^{1/4}\) to \((\log N)^{1/7+\varepsilon}\), and stating every receiver as \(E(c_N)\log N\to0\). | Q1 | A receiver, not a sign; it tests the critical-curve conjecture. |
| W05 | **Smooth profiles without real Fourier zeros.** Tilt the Steklov and Gevrey profiles (\(e^{\tau u}\), \(\tau\) avoiding countably many values); prove no real Fourier zeros, unit mass, derivative bounds; then fixed-\(c\) and packet positivity. | Q1; SRT, HF | Hypotheses only; no new sign. |
| W06 | **Damage law in models.** Zero configuration with \(\zeta\)'s density plus one off-line quartet \((\delta,\gamma)\). Using the horizon law, compute the least overlap, window ratio and conductor at which the complete atomic matrix becomes negative. | Q3 | Model, not \(\zeta\). |
| W07 | **Two-horizon calculus at fixed \(c\).** Complete energies of windowed aperture modes on both sides of the explicit formula: shells and Poisson remainders on the prime side, horizon products on the zero side. | Q2 | Fixed \(c\) only. |
| W08 | **Flip thresholds.** Remove the \(\log p\) gap in \(c_0(\omega_p)\); asymptotics for finite flip sets and twin tails; the resolution–distance law on the gauge torus. | Q3; HF | Summable twists only. |
| W09 | **TH rank eight.** Audit and integrate the piece certificates; extend below \(q=31/10\); certified evaluation of the \(r^2\)-weighted compensation for every \(v\in\mathbb R^4\). | TH | A finite inequality that may fail; then TH stops at rank seven. |
| W10 | **Integrate working sources**: `WeilGrowingPackets`, `WeilGrowingOverlap`, `ConductorLogLaw`, `ConductorOverlapDecay`, `BesselGaussianMoments`, `BesselGaussianReserve`, the odd-four piece certificates, and the remaining [S] modules of AKLT, HKT, ASRP and AID. | all | Integration only. |
| W11 | Bombieri–Vinogradov from the gauge-form large sieve and W02. | W01 if conductors exceed SW range; MC | Averages over moduli. |
| W12 | **Exponent calculus on \(G\).** Exponent inequalities from \(\mu^2=\sum_{d^2\mid n}\mu(d)\), \(\mu*1=\delta\), \(\Lambda*1=\log\), Liouville translation and Adams doubling; record the transfer laws between special points. | 2.4; MC | Transfer, not production. |
| W13 | **Adams minimum-support rigidity.** Classify the auxiliaries attaining support \(2^{qr}\). | WL, ACS | Calibration. |
| W14 | **Arithmetic Weyl law.** The physical-multiplicity heat trace of the conductor spectrum; a statement identifying the low spectrum with the Bost–Connes Hamiltonian up to a bounded perturbation at fixed \(c\). | 2.5 | Fixed \(c\). |
| W15 | Steklov full-index exhaustion; removal of the extra \(\log\log L\). | SRT | Receiver. |
| W16 | Haar branch: head sizes, first-layer constants, signed graph payment on computed ranges. | HF, ACS, AIP, CHMD | \(k=1\) stays [FS]. |
| W17 | Census: majorant bounds for \(E(\delta)\); constants in \(hE_h\le CN\); \(E_{\rm proj}\) on explicit near-line configurations. | ACS | Majorants are displacement-blind. |
| W18 | Heat: explicit \(N(t)\) on compact ranges; summed localized estimates on fixed height windows. | WD, LA | No uniform count. |
| W19 | Quasi-RH preprint: formalize the continuation step; extract the abscissa as a function of its inputs. | MC | Depends on the external argument. |
| W20 | Product-bias classification in Lean [P]. | WL, MC | Formalization. |
| W21 | Ledgers and finite rows for FU, RP, LI, TT, PA, MC, PM, CTF, JAS, RW, EWU, OWU, SZ, ACT, TG, RN, XN, GTA, BAG, HCF. | many | Local certificates. |
| W22 | Candidate calculations: cycle traces, curvatures, jets, contours, ports, stacks, cusp actions. | candidates | Calibration is not forcing. |
| W23 | **Filtration-window audit.** For each U2 route record its fixed-level positivity, its margin as an identity where one exists, and its RH schedule; import the Poisson-margin method where it applies. | Unification S | Bookkeeping and transfer. |
| W24 | Literature intake: Strang–Fix approximation orders; Goldston–Montgomery; Selberg's short-interval mean value; Roth's lemma and the subspace theorem; Deuring–Heilbronn; Zagier–Sarnak horocycles; Bost–Connes and Connes' trace formula. | 2.4–2.6 | External proofs are not assumed. |

## 2.2 Open mathematical obstacles

### (a) RH-equivalent endpoints

| ID | Missing result | Routes |
|---|---|---|
| O1 | Critical signed cancellation in any currency: one-sided \(\psi\) count (\(=\kappa=0\)); odd-class upper count; lag energy; Abel moment; linear history floor; strict half-power; regularized convergence; extremal remainder; approximation residual; square-root budget; integrality halves; joint moment/sawtooth/Mertens control; first-clock tail; \(\theta_\mu(0)=1/2\). | WL, FU, CFC, RP, MC, LI, PBM, RB, JAS, CTF |
| O2 | Complete Weil positivity past the critical curve: tilted spline at \(2(\log N)^\alpha\), \(\alpha>1/4\); Steklov at the iterated log; complete-cell index zero; residual, odd, allocation or Hodge sign; tent families. | RW, HF, SZ, EWU, OWU, AIP, ACS, TT, CHMD, ACT, SRT |
| O3 | Positivity on one prime's towers for all generators. | HF, ACS, AIP, CHMD, SRT |
| O4 | All-degree, all-height heat, moment or coefficient signs; all ranks of the center hierarchy; the Cayley–Li ladder; both Gaussian grids. | PA, LA, TH, WD, HCF, LI |
| O5 | Positive gauge mass of every escape state; vanishing approximation error. | PM, CTF |
| O6 | Rank-uniform transverse decay; all-point recurrence; covering Newton discs; integer trace cap; directed renewal orientation. | GTA, BAG, XN, TG, RN |
| O7 | \(\mathcal E_{\rm crit}\) at most one quantum; cofinal work \(\le2\). | HF, SRT, ACS |

**Common content (inference).** Each of O1–O7 is the typicality of the gauge point \(0\) for a statistic that is neither gauge-invariant nor finitely determined, at square-root precision. Each U2 item is positivity along a resolution schedule past the point where its margin falls below the archimedean-weighted aliasing; for the atomic filtration that point is the curve \(E(c_N)\log N\asymp1\).

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

Finite support implies LH and a fixed strip. **Verdict: not a near-term target.** An argument giving finite index without LH-strength input is wrong.

### (d) Lindelöf and quasi-RH levels

| ID | Missing result | Status |
|---|---|---|
| L0 | Zeros approach the line | Implies LH and \(\Theta<1\). |
| L1 | LH | Open; \(\mu(1/2)\le13/84\). |
| Q0 | A fixed zero-free strip \(\Theta<1\) in any dictionary | External claim at \(7/8\) for Dirichlet \(L\) [E]. Density envelopes never reach it. |
| Q0′ | A \(0\)-specific, non-gauge-invariant inequality improving \(\theta_\mu(0)\) below \(1\) | Equivalent to Q0. |
| Q0″ | Box-test positivity at a fixed sub-pole aperture \(\kappa<1/2\) for all windows | A fixed strip (inference from the window law). |

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
| I1 | **Reaching the critical curve from below**: complete positivity on every schedule with \(E(c_N)\log N\to\infty\) | Every current bound loses a polynomial in \(c\); with floor \(c^{-7}\) a loss \(c^k\) stops at \((\log N)^{1/(k+7)}\). The \(\approx c\) near-degenerate conductors \(m\lesssim c\) need uniform, loss-free quasimodes | Unconditional positivity on the whole subcritical side |
| I2 | **The critical-curve conjecture**: RH \(\iff\) positivity on \(\{E(c_N)\log N\to0\}\), for every profile | Receivers come from trapezoid synthesis for \(C^2\) (W04); the unconditional side is I1 | The window becomes a line |
| I3 | **The sign at the critical curve**: an exact decomposition of \(W\) along \(E(c_N)\log N\asymp1\) | Margin, Gamma reserve and aliasing error are of equal size there; no estimate with a fixed relative loss survives | The breakthrough target of 2.5 |
| I4 | **Uniform selectivity**: one growing schedule rejecting every finite flip with \(p\le P\) while \(\zeta\) stays positive | \(c_0(\omega_p)\asymp p^{1/7}\) up to \(\log\); joint control in \(P\) and \(N\) is missing | Selectivity at the rate RH needs |
| I5 | Exterior tightness | Record minima permit zero gauge mass | PM short of O5 |
| I6 | Conductor/forcing compatibility | No common aperture range | OWU detection |
| I7 | **Point-side producer over \(\mathbb Z\)**: the duality step from character vanishing to a prime count | Adams vanishing is Bézout-sharp; divisibility is parity-blind; small = divisible; no self-map Frobenius | The Frobenius substitute |
| I8 | A parity-selective auxiliary with valuations not periodic in \(n\bmod p\) | Factorial ratios are periodic and stop at \(2\log2\) | Square-root producer precision |
| I9 | Arithmetic index ceiling | Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) is linear; a positive part never pays a pair | Finite support, then towers |
| I10 | Independent constructions for each candidate | Calibrations; zero-indexed objects | Promotion |
| I11 | Extraction of the external \(7/8\) threshold | Not formalized (W19) | A conditional strip |
| I12 | Many-node Gram floor from two-prime phase separation | Baker bounds degenerate as \(\Delta\to0\) | HCF, SRT without aliasing |
| I13 | Tower detection at unattained depth | Attainment is used | The tower Hasse principle |
| I14 | Geometric parity twin over \(\mathbb Z\) | Only the Bohr closure; Adams operations fix \(0\) | A twist tower over \(\mathbb Z\) |
| I15 | Rank-uniform theta compensation (beyond rank eight) | Tails strict past a log horizon; no rank-uniform fraction of the new diagonal | TH all ranks short of RH strictness |
| I16 | Haar-branch joint payment of the non-arithmetic Gamma graph and signed diagonal | No positivity of \(V_X\) | Complete-cell index |
| I17 | A characteristic-zero surface whose sections count quadratically | Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) is linear | A Hodge index from ring structure |
| I18 | **Off-line damage law for \(\zeta\)**: the window rung at which an actual off-line zero would first be seen | The horizon law gives the zero side exactly; the coupling to \(\zeta\)'s zero density is unquantified | Zero-free regions from positivity |

**What the open items share (inference).**

- The pole, Gamma and Poisson summation on the successor lattice pay every bounded resolution, and every fixed conductor packet at slowly growing resolution.
- Single horizons, fixed conductors and multiplicative data are depth-blind or gauge-invariant. Every RH-strength item needs information at \(0\) carried by long windows (growing conductors), at the critical curve, and at square-root precision, or a structure producing it.
- Over \(\mathbb F_q\) one ring endomorphism does all of this. Over \(\mathbb Z\) the Adams operations reproduce \(x^q=x\) on characters, Bézout-sharply, and nothing converts it into a count.

## 2.3 The three questions to answer next

<a id="q1"></a>
### Q1. Is the RH transition of the atomic window the single curve \(E(c_N)\log N\asymp1\), and how close to it can unconditional complete positivity be carried?

**Exact object.** The complete Weil matrix \(W(\varphi,c,N)\) of one profile on atoms of width \(c/N\), with every prime power, Gamma and both poles.

**Proved.**

- Positive at every fixed \(c\); bottom \(\to E(c)\) [L].
- Fixed packets positive up to \((\log N)^{1/48}\) [L].
- RH \(\iff\) positivity at \(c_N^4\gg\log N\) (\(C^2\)), \((\log\log N)^{s+}\) (Gevrey), \(L(\log L)^2\log\log L\) (Steklov) [L/K].

**The curve (inference).**

- The margin is the aliasing tail \(E(c)\).
- The receiver's synthesis error energy is (aliasing error)\(^2\times\log N\), the \(\log N\) being Gamma's weight.
- The Gamma reserve is \(\approx E(c)\log N\).
- For Gevrey and Steklov profiles the receiver lies on \(E(c_N)\log N\asymp1\) to leading order. For \(C^2\) it lies at \((\log N)^{1/4}\), against the curve at \((\log N)^{1/7}\), because trapezoid synthesis ignores \(\hat\varphi\)-decay.

**Open.** The receiver half: W04 (and W05) move every receiver onto \(\{E\log N\to0\}\). The unconditional half: I1, positivity on \(\{E\log N\to\infty\}\), which needs loss-free control of the \(\approx c\) near-degenerate conductors.

**Why now.**

- It is the only RH-equivalent family with an unconditional theorem at every bounded level and an exact margin.
- Its arithmetic errors already decay faster than any power of \(1/\log N\); the losses are harmonic boundary rows and polynomial factors in \(c\), both identified [L].
- The three profile classes give an exact prediction to test.

**First useful answers.**

1. W04: the \(C^2\) receiver at \((\log N)^{1/7+\varepsilon}\), or a proof that trapezoid order is optimal for \(C^2\).
2. W01–W03: an explicit full-matrix schedule and its exponent.
3. W05: the critical curve for one smooth profile without real Fourier zeros.

**Payoff.** Either RH is located on one curve, with the window between theorem and RH reduced to a line, or a gap persists and its content is identified.

**Risks.** Polynomial losses may be intrinsic to quasimode methods, and higher-order synthesis may need Strang–Fix conditions the atoms on \(\log n\) do not satisfy.

<a id="q2"></a>
### Q2. What decides the sign of the complete form at the critical curve, and is it a positive object?

**Exact object.** \(W\) along \(E(c_N)\log N\asymp1\), restricted to the depth-sensitive directions: growing conductors \(m\lesssim c\) and windowed aperture modes.

**Proved.**

- At fixed \(c\): \(W\) = completed conductor spectrum (Poisson remainders) plus vanishing errors [L].
- For every vector: zero side = horizon products \(H_a(1-\rho)H_a(\rho)\) [L].
- Single-horizon charge is depth-blind [L]; windows carry \((N/M)^{\pm\operatorname{Re}z}\) [L].
- The Euler–Maclaurin tails of the horizons are the Poisson duals of the successor shells [L].

**Open.** At the curve the margin no longer dominates the archimedean-weighted aliasing; the sign is a property of the exact terms. Is there a **two-horizon Poisson identity**? It would write the complete energy of a window as

\[
W=\underbrace{\mathcal P_{\rm win}}_{\text{Poisson remainder of the window autocorrelation}}+\underbrace{\mathcal G}_{\text{Gamma reserve}}+\underbrace{\mathcal B}_{\text{horizon boundary layer}}+\underbrace{\mathcal Z}_{\text{explicit zero term}} ,
\]

with \(\mathcal P_{\rm win}\ge0\) by construction, \(\mathcal G\ge0\), and \(\mathcal B\) identified exactly.

**Why now.**

- The fixed-\(c\) identity is proved.
- The horizon law isolates the zero side exactly.
- The boundary layer is the one term that the estimates coarsen and that has the critical size \(1/\log N\).

**First useful answers.**

1. W07: the two-horizon calculus at fixed \(c\).
2. The sign and size of \(\mathcal B\) for the pole mode (single horizon, where \(\mathcal B\) is the Euler–Maclaurin tail product).
3. Whether \(\mathcal B+\mathcal G\) is a Fourier tail.

**Payoff.** If the boundary layer is a positive object, positivity at the curve is an identity, the first Weil positivity at RH-relevant resolution. If it has no sign, the decomposition names the exact RH-equivalent quantity at the curve.

**Risks.** \(\mathcal B\) may be of order \(1/\log N\) with no sign; then the curve closes only by an RH-strength input.

<a id="q3"></a>
### Q3. At which window rung does one off-line zero first break atomic positivity, and what zero-free region does each unconditional rung give?

**Exact object.** For an off-line zero \(\rho=\tfrac12+\delta+i\gamma\), the least triple (overlap \(c\), window ratio \(N/M\), conductor \(m\)) at which the complete atomic matrix of a zero configuration containing \(\rho\) has a negative direction.

**Proved.**

- Horizon law [L].
- One zero weighs at most \((N+1)/k\) times \(1/(2\sqrt{\beta(1-\beta)})\) of the diagonal [L].
- Fixed packets are depth-blind (window ratio \(\le m\)) (inference from [L]).
- A tempered single-pair model is negative at every \(c\) [K]; \(\zeta\)'s fixed-\(c\) positivity uses its zero density through Gamma.

**Open.** The coupling of one off-line quartet to \(\zeta\)'s zero density at growing overlap, and the threshold as a function of \((\delta,\gamma)\).

**Why now.** The horizon law makes the zero side explicit for every vector. Without the damage law no rung of the window, proved or not, says anything about zeros.

**First useful answers.**

1. W06 in a density-matched model.
2. The threshold window ratio \((N/M)^{\delta-\kappa}\gtrsim\) (number of competing zeros) for sub-pole apertures.
3. The zero-free region implied by the proved packet range.

**Payoff.** Every unconditional rung becomes a zero-free region obtained from positivity, the high-dimensional analogue of \(3+4\cos\theta+\cos2\theta\ge0\). Comparison with Vinogradov–Korobov calibrates the programme.

**Risks.** Below the critical curve the damage may be invisible, so the rungs give no region. This would itself be a theorem: the subcritical side carries no zero information.

**Why these three.**

- Q1 locates RH in the only filtration with an exact margin.
- Q2 asks for the identity that has to replace estimates exactly there.
- Q3 makes every rung produce information about zeros.

Together they turn the bounded-resolution identity into a theory of the transition.

**Next in line.**

- The producer duality step (I7).
- Uniform selectivity (I4).
- The contradiction route of 2.4 (W12).

The producer question is not in the top three: the Adams calibration moved it to the explicit formula itself, where no current object acts.

## 2.4 Is there a wildly different route?

**Verdict: one, as before, and it is better equipped now.** The content of Wall 1 is unavoidable, and it is a set of theorems:

- pointwise-closed statements are twin-blind;
- gauge-invariant certificates give \(\ge3/4\) at \(0\), finitely determined ones \(\ge1\);
- single-horizon charges are depth-blind;
- finite aperture cannot decide;
- anything implying the count rejects the Liouville twin.

Routes can differ in **logic**. Every live route and candidate uses one of three:

- positivity of a form along a filtration (Wall 3);
- counting by a producer (Wall 14);
- realization of an operator or limit (Wall 14).

None uses **contradiction from approximations**, the logic of Thue–Siegel–Roth and of Siegel's and Deuring–Heilbronn's theorems on exceptional zeros. It signs no form, exhausts no filtration and needs no count.

### Candidate: typicality of the special point by contradiction

**The dictionary [L].**

| Real line | Gauge torus \(G\) |
|---|---|
| Irrationality exponent, a.e. value \(2\) | Möbius exponent, a.e. value \(1/2\) |
| Liouville numbers: residual, null | Twin tails: exponent \(1\); exceptional set residual, null |
| Algebraic numbers | Special locus: Dirichlet points × vertical shifts; \(0\) is the additively invariant point |
| Rationals: exponent \(1\), "better than typical" | \(\mathbb F_q[T]\): trivial point exponent \(0\), better than typical [L] |
| Roth: algebraic numbers are typical | RH: \(0\) is typical; GRH: Dirichlet points are typical |
| Height of a rational | Conductor; length of a Dirichlet polynomial; resolution threshold \(c_0\) |
| Liouville inequality | Integrality lattice \(\operatorname{lcm}(1..N)^{-1}\mathbb Z\) [S]; small integer auxiliaries are divisible [L] |
| Roth's lemma (zero estimate) | Bézout for \(\mathbb G_m(\mathbb Q)\) [K]; Adams multiplicity Bézout-sharp [L]; algebraic first jets faithful (Baker) [L] |
| Siegel's lemma | Siegel's lemma for integer Dirichlet polynomials [S]; Baker machinery in RHTower |
| Deuring–Heilbronn repulsion | Exponent transfer laws between special points: the twin inequality [L] |

**Two forms of the route.**

1. **Repulsion (Siegel / Deuring–Heilbronn form).**
   - Dirichlet points have exponent \(\ge1/2\) unconditionally (twin duality [L]).
   - Target: a transfer law under which atypicality at \(0\) (\(\Theta>1/2\)) forces exponent \(<1/2\) at some Dirichlet point or its twin.
   - The twin inequality is the first transfer law of this kind. It currently bounds twins from above (\(\le(2+\Theta)/6\)) and so goes the harmless way.
2. **Auxiliary (Roth form).**
   - Assume \(\Theta=\tfrac12+d\).
   - Derive many gauge points of bounded conductor or resolution at which twisted Möbius sums are simultaneously large.
   - Build an integer Dirichlet polynomial in several variables by Siegel's lemma, vanishing to high order there, cheaply through a \(0\)-specific identity: \(\Lambda*1=\log\), the functional equation, or the shell/horizon repayment.
   - Show non-vanishing at one point by a multivariable zero estimate extending Bézout and Adams–Bézout.
   - Contradict integrality.

**Why it is far from every current route.**

- It meets Wall 1 only as a selectivity requirement on the transfer law or auxiliary.
- It needs no uniformity across a filtration, so Wall 3 does not arise; Roth-type proofs may be ineffective.
- It needs vanishing at finitely many hypothetical approximations, not a count at all primes: Wall 14 in a weaker form.

**Ladder.** Trivial bound \(\Theta\le1\). A Thue-type improvement at \(0\) is a strip [≥QRH]. A Roth-type sharp exponent is RH.

**What would kill it.**

- An off-line zero forces no approximations outside the class of \(0\) (finite modifications and vertical shifts).
- Every transfer law is gauge-covariant in a way that only moves strips between points; the twin inequality has this property.
- Repulsion near \(\operatorname{Re}s=1/2\) has no positivity mechanism. Deuring–Heilbronn uses nonnegative coefficients of \(\zeta L\), which converge only near \(\operatorname{Re}s=1\).

**First tests.**

1. Recover Siegel's \(L(1,\chi)\gg_\varepsilon q^{-\varepsilon}\) and Deuring–Heilbronn in gauge-exponent language.
2. W12: list every exponent transfer law derivable from the convolution identities and decide whether any can reverse direction.
3. A one-variable Roth auxiliary for a toy exponent problem on the special locus, using the corpus's Baker and Adams–Bézout zero estimates.

### Mechanisms examined and where they re-enter

| Mechanism | Re-entry |
|---|---|
| Deligne-style averaging over a family | The natural family \(G\) is infinite-dimensional; its special locus is typical only on average [L]. Localization needs a finite-dimensional family with cohomology: Wall 14. |
| Measure rigidity under the Adams semigroup | \(\psi^k\) fixes \(0\); rigidity gives almost-sure statements. The Möbius escape state is blind to zeros [L]. |
| Exponent bootstrap from convolution identities | Trivial fixed point \(1\); transfers strips (twin inequality [L]); first rung = QRH. |
| Critical-phenomena logic (duality pins the critical point, Kramers–Wannier) | The functional equation is a \(0\)-specific duality, so this logic is not excluded by Wall 1. Its natural host is the Bost–Connes system, whose partition function in complex \(\beta\) is \(\zeta\), so RH becomes a Lee–Yang property: realization, W1C, Wall 14. Sharp-threshold theorems need product measures, which exist only at Haar-random points. |
| Unipotent dynamics (Zagier–Sarnak horocycles) | RH \(\iff\) closed-horocycle equidistribution at rate \(y^{3/4-\varepsilon}\); the error is carried by Eisenstein scattering poles. Laplace data do not locate them (KR-SEL, KR-AUT). |
| Newton polygons (Goss–Sheats) | Archimedean Newton polygons see moduli, not arguments. |
| Jessen functions, amoebas, Bohr–Jessen | See zero densities only; density never forces vanishing [L]. |
| Fourier quasicrystals | Classification presupposes real support. |
| Signature or index theorems from local data | Local constituents have index \(0\) or \(\infty\) [S]. |
| Coefficient criteria (Laguerre–Pólya) | The LA route. |
| Lee–Yang, Bost–Connes, Hilbert–Pólya | Realization: W1C, PTR, Wall 14. |
| Index-continuity deformation | \(\Lambda_{\rm dBN}\ge0\) blocks openness at \(\zeta\). |
| Level of distribution, dispersion, Kloosterman sums | Averages over moduli; the trivial point is one term (level \(1/2\) theorem [L]). |

## 2.5 Where a real breakthrough on the hard questions could come from

**Thesis: Weil positivity at bounded resolution is an identity. The breakthrough is to find the identity that holds at the critical resolution, where every estimate must fail by construction.**

### What the corpus now knows about positivity

- **Mechanism [L].** At fixed overlap, positivity is Poisson summation of the profile's autocorrelation on the successor lattice, completed by Stirling's formula. Ramanujan weights collapse to coprimality; each conductor energy is \(\int|\hat\varphi|^2\) over a tail.
- **Visibility [L].** The zeros read every atomic vector through Euler–Maclaurin horizon boundaries. The single-horizon charge is a positive Poisson kernel for every zero, on or off the line. Depth is a two-horizon interference effect.
- **Duality of the two sides (inference from [L]).** The shells repaid on the prime side and the Euler–Maclaurin tails seen on the zero side are Poisson duals. Theta positivity reads the same horizon boundary from the other side of the functional equation.
- **Criticality (inference).** Margin, Gamma reserve and synthesis error are one Fourier tail. The window narrows to \(E(c_N)\log N\asymp1\), where they are of equal size.
- **Selectivity [L].** The pole separates pole-free twins at bounded resolution. Twins that keep the pole are separated at resolution growing with their distance from \(0\).

### Target theorem: a critical Poisson–Weil identity

For one profile, along \(E(c_N)\log N\asymp1\) and on the depth-sensitive directions (growing conductors, windowed modes), prove

\[
W=\mathcal P+\mathcal G+\mathcal B+\mathcal Z,
\]

where:

- \(\mathcal P\) is the sum of the Poisson remainders of all conductors and windows (a Fourier tail, nonnegative);
- \(\mathcal G\) is the Gamma reserve (nonnegative, of size \(E(c_N)\log N\));
- \(\mathcal B\) is the horizon boundary layer, identified exactly as a Poisson object;
- \(\mathcal Z\) is the explicit zero term of the horizon law, \(o(\mathcal P+\mathcal G)\) on on-line configurations.

**Why this is a breakthrough target, not a restatement.**

1. **It is true where it is proved.** At fixed \(c\), \(\mathcal B,\mathcal Z\to0\) and \(\mathcal P\) is the completed conductor spectrum.
2. **It acts exactly where RH lives.** Fixed packets and single horizons are depth-blind; the decomposition is taken on the directions where depth enters.
3. **It replaces the last estimate by a term.** At the curve the boundary layer is the one quantity of critical size. If \(\mathcal B+\mathcal G\) is a Fourier tail, positivity at criticality is a theorem by identity.
4. **It is selective by construction.** Pole-free twins lose the pole's sign; pole-keeping twins lose at their thresholds, which the same packet calculus computes.
5. **It produces zeros information.** With the damage law (Q3), every window proved positive excludes a region of off-line zeros.

### A second opening: a trace formula for the complete Weil matrix

- At fixed overlap the low spectrum is \(\log m+O_c(1)\) and its heat trace converges exactly for \(\beta>1\) [L/S]. This is the Bost–Connes Hamiltonian up to a bounded perturbation (inference), and the Bost–Connes critical temperature is the critical line in Hecke-exponent units [L].
- A trace formula \(\operatorname{Tr}e^{-\beta W}\) or \(\operatorname{Tr}f(W)\) with arithmetic (conductor) and spectral (zeros, through the horizon law) sides would give positivity a spectral handle, as the Selberg trace formula does for Laplace spectra. The critical behaviour of RH would become the \(\beta\to1\) behaviour of an explicit trace (inference).

### A third opening: one Poisson structure for theta and atomic positivity

- Aperture modes carry the theta aperture current, and the theta source shares the pole mode's horizon [L].
- TH's open rank-uniform compensation is the theta face of the same window.
- A Poisson-remainder identity for the center hierarchy would be the theta form of shell repayment and the rank-uniform mechanism that TH lacks.

### Risks

- \(\mathcal B\) may be genuinely of order \(1/\log N\) with no sign. Then the curve closes only by an RH-strength input, and the identity names that input exactly.
- Near-degenerate conductors at growing \(c\) may require level-of-distribution inputs, which are averaged and not point-specific.

## 2.6 Would the obstacles in 2.2 need a new field of mathematics?

**Assessment.**

- **Probably yes:**
  - (a) the RH-equivalent endpoints; (c) the finite-support stratum; (d) Lindelöf and quasi-RH;
  - I3 (the sign at the critical curve); I7 (the producer duality step); I8 (a parity-selective auxiliary); I9 (an index ceiling); I14 (a geometric parity twin); I17 (a quadratic surface).
- **Probably reachable with existing tools:**
  - I4 short of full uniformity; I5, I6, I10–I13, I16, I18 in models; C1–C4 short of the parity barrier;
  - the receiver half of I2 (W04, W05).
  These need quantitative analytic number theory (Siegel–Walfisz, mean values, sieves), approximation theory, operator theory and certified computation.
- **Undecided:**
  - I1: reaching the critical curve needs loss-free uniformity, which may be a new kind of estimate.
  - I15: rank-uniform theta compensation.

### What the field would be about

**The harmonic analysis of the ring \(\mathbb Z\) at critical resolution: the scale at which its multiplicative dual, its additive dual and its archimedean place carry equal weight.**

- **Multiplicative dual:** the gauge torus \(G\), Haar measure, Adams operations, the special locus, the gauge exponent.
- **Additive dual:** the successor lattice, Ramanujan sums, Poisson summation, Euler–Maclaurin horizons.
- **Archimedean place:** the pole, Gamma's weight \(\log|t|\), Stirling's formula.

They meet:

- in the shells, repaid by Poisson summation;
- in the horizons, where the zeros read every vector;
- in the conductor spectrum, an arithmetic Weyl law with critical temperature \(\beta=1\);
- in the critical curve \(E(c)\log N\asymp1\), where margin, aliasing and archimedean weight coincide.

**Central object.** The point \(0\in G\): the unique additively invariant gauge point, the unique fixed point of \(\psi^2\), the carrier of the pole and the only point with a functional equation of its own (with the Dirichlet points).

**Central theorems to aim for.**

- Weil positivity at the critical resolution, by identity.
- \(0\) is typical modulo its pole for every statistic that is neither gauge-invariant nor finitely determined.
- A resolution theory for pole-keeping perturbations of \(\Lambda\), including non-summable ones.

### What it would be like

It would be Weil's proof for curves transported to a ring without Frobenius, with the archimedean place as a full participant, and with the logic of critical phenomena in place of fixed-scale inequalities.

Over \(\mathbb F_q\) one endomorphism does three jobs:

- it makes the parity twin geometric;
- it makes vanishing cheap (Stepanov);
- it makes the Euler characteristic quadratic (Hodge index on \(C\times C\)).

Over \(\mathbb Z\) none is available on \(\mathbb Z\) itself:

- the twin is geometric only in the Bohr closure;
- Adams vanishing is Bézout-sharp and lives on characters;
- Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) is linear.

The field must supply the three jobs from different structures:

- **Positivity across shells and horizons:** Poisson summation on the successor lattice (working at bounded resolution).
- **Point specificity:** the functional equation and \(\Lambda*1=\log\), the two \(0\)-specific identities, acting as dualities rather than estimates.
- **A quadratic count:** a still-unknown two-dimensional object.

And it must do so at the critical scale, where the theory is a theory of a transition and not of an inequality with room to spare.

### Criteria it must meet

1. **Independence.** Built from arithmetic data, never from zero-indexed objects.
2. **Fidelity.** All mixed entries, Gamma, both poles, multiplicities.
3. **Battery.** Every sufficient hypothesis fails for the Liouville twin, every finite and cofinite flip, twin tails, \(\Lambda+\varepsilon n^{-\eta}\), \(\Lambda+1/n\), the golden datum, over-regular Beurling systems, Davenport–Heilbronn functions and Haar-random gauge points.
4. **Point specificity.** Its decisive input is neither gauge-invariant nor finitely determined, and uses \(0\)'s additive invariance, its pole or its functional equation.
5. **Depth sensitivity.** Its decisive input acts on two-horizon (long-window) directions; single-horizon data are blind.
6. **Criticality.** At the critical resolution it works by identity, as the Poisson repayment does at bounded resolution.
7. **Calibration.**
   - Reproduce Weil over \(\mathbb F_q\) by counting.
   - Reproduce bounded-overlap positivity, the packet range, the flip thresholds \(p^{1/7}\), the pole-free twin rejection and the \(2/3\) census.
   - Recover Siegel's theorem as a typicality statement.
8. **A new inequality.** A paid sign, count, exponent bound or ceiling, not another equivalence.
9. **Formal closure.** Unconditional Lean statements.

### Questions it must answer

- Is the RH transition a single critical curve, and which identity governs it?
- Does the horizon boundary layer have a sign? Is it a Poisson object?
- What is the trace formula of the complete Weil matrix, and what is its \(\beta\to1\) limit?
- How does resolution extend from summable twists to pole-keeping, non-summable perturbations such as an off-line zero?
- What replaces \(x^q=x\) on the point side? How is character vanishing converted into a count of primes?
- What is the two-dimensional object whose sections count quadratically over \(\mathbb Z\)?
- Which statistics have \(0\)-values fixed by structure (pole, \(\Lambda*1=\log\), Poisson remainders, functional equation), and which are pure discrepancy?

### Objects and language

| Object | Role |
|---|---|
| Gauge torus \(G\), Haar measure, Adams operations | Ambient space; typicality; \(x^q=x\) on characters |
| Special locus; twin tails; pole-free and pole-keeping twins | "Algebraic", "Liouville" and near-\(0\) points |
| Gauge exponent \(\theta_a(x)\); exponent transfer laws | Diophantine invariants; repulsion |
| Successor lattice, Poisson remainders \(E_m(c)\) | Positivity from additive structure |
| Möbius horizons \(H_a\), Euler–Maclaurin boundaries \(B_M\) | How zeros see vectors; depth through windows |
| Conductor spectrum; arithmetic Weyl law; Bost–Connes temperature | Spectral side of positivity |
| Atomic families in length–height coordinates; overlap = resolution | The filtration on which RH is a transition |
| Resolution thresholds \(c_0(\lambda)\) | Distance from \(0\) as seen by positivity |
| Integer Dirichlet polynomials; Bézout, Riemann–Roch and Adams–Bézout for \(\mathbb G_m(\mathbb Q)\) | Auxiliaries and zero estimates |
| Krein–Langer index, waves, polar classes | What a ceiling must bound |

**Language.** Gauge-invariant / gauge-charged / boundary. Typical, special, Liouville, pole-keeping. Resolution, margin, aliasing, critical curve, damage. Horizon, window, depth-blind. Repayment by Poisson. Producer, multiplicity beyond divisibility, Adams–Bézout. Index ceiling, quadratic count.

### Mechanisms it would build on

- **Poisson repayment** on the successor lattice (proved at bounded resolution).
- **The horizon law** (proved for every vector).
- **Coherence and the antipode** (the pole as the only multiplicative selector).
- **Functional-equation duality** between theta and atomic horizons (proved at the level of one boundary).
- **Resolution monotonicity**: thresholds are exact and monotone (proved for summable twists).

### Tools to develop, with tests

| Tool | Purpose | Test |
|---|---|---|
| Critical-window calculus | Margin, aliasing, Gamma reserve and boundary layer at growing overlap | Place every known receiver on \(E\log N\asymp1\); reproduce the packet range |
| Two-horizon Poisson identity | Exact energies of windows and growing conductors | Exact at fixed \(c\); reproduces box-test depth sensitivity |
| Trace formula of \(W\) | Spectral handle on positivity | Heat threshold \(\beta=1\); conductor log law |
| Resolution theory beyond summable twists | Pole-keeping perturbations | Reproduce \(c_0(\omega_p)\asymp p^{1/7}\); predict the damage of an off-line zero |
| Exponent transfer laws on \(G\) | Repulsion between special points | Recover Siegel; the twin inequality |
| Adams–Bézout calculus | Zero estimates on characters | Reproduce Stepanov over \(\mathbb F_q\); the \(2^{qr}\) boundary |
| Quadratic count | Hodge index over \(\mathbb Z\) | Over \(\mathbb F_q\) it is \(C\times C\); fails for the golden datum |

**First evidence of success.** Any one of:

- unconditional complete Weil positivity along an explicit full-matrix schedule \(c_N\to\infty\);
- an RH receiver stated and proved on \(\{E(c_N)\log N\to0\}\) for a \(C^2\) profile;
- an exact identity for the horizon boundary layer with a sign;
- a zero-free region proved from window positivity;
- any \(0\)-specific exponent inequality below \(1\).
