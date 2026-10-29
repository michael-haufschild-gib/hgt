# Walls ledger

Status: 29 October 2026, corpus checkpoint `7f191801a3` plus working tree. **Three core problem families remain: the selective critical sign (Wall 1), transfer and exhaustion (Wall 3), and independent realization or forcing (Wall 14). No core wall was crossed.** One face was solved: a parity-selective input (the pole) pays the complete Weil form at bounded overlap past the Metzler threshold. The face that now separates that theorem from RH is **overlap growth**, from \(c\le1+10^{-18}\) to \(c_N\asymp\log\log N\). The producer side was sharpened: index zero is one parity class's upper count, locality is twin-blind, compressions are receivers, integrality is exact, and a producer must vanish at the primes.

[Route report](route-obstacles.md) · [summary and next questions](obstacles-summary.md) · [route unification](route-unification-ledger.md) · [scoped no-go catalogue](../rh-killed-routes.md). Evidence: corpus searches and Lean statements; no builds. **[L]**/**[S]**/**[K]** as in the frontier map; **[Lean]** = statement read, integration not assessed; **(inference)** = conclusion of this review. [Working log](../../../logs/review-2910b-research-2026-10-29.md).

## The three families

| Family | Question | What would cross it |
|---|---|---|
| **Wall 1 — Selective critical sign** | What bounds the actual signed prime/Möbius source, the complete Weil form or a computed defect at the critical scale, using a property \(\Lambda\) has and its twins lack? | A new inequality that is parity-breaking (fails for Liouville), sees every prime (fails for single large-prime flips), is precision-faithful (fails for \(\Lambda+\varepsilon n^{-\eta}\)), is not local, and keeps all tails and quantifiers. |
| **Wall 3 — Transfer and exhaustion** | Does an estimate survive the needed norm, source realization, shared reserve, overlap growth and simultaneous limit? | A source-faithful comparison in a topology that carries the sign or index, with the right uniformity in overlap, aperture and conductor. |
| **Wall 14 — Realization and forcing** | Which independently built structure produces the inequality? | A faithful object with a proved selective law: over \(\mathbb Z\), a point-side producer of one parity class's upper count, or a structural constraint on a polar divisor. |

How they interlock:

- **Global law (Wall 1 = Wall 14 at the endpoint) [S].** Index zero of the Weil kernel is the one-sided count \(\psi(x)-x\le C\sqrt x\log^2x\), and already the upper count of the odd Liouville class; for curve data over \(\mathbb F_q\) it is the lower point count, reached from upper counts by the twist tower.
- **Entries (Wall 1 inside Wall 3).** Separated entries of the complete form are prime-error integrals; cross-level prime couplings are prime-error sequences; their positivity is one-prime tower positivity, which is RH.
- **Overlap (Wall 3 with Wall 1 content).** Bounded overlap is paid by the pole and the plateau's variance reserve [L]; RH needs overlap \(c_N=(\log\log N)(\log\log\log N)^{\beta}\), \(\beta>2\) [L]. Where the separated prime error enters as \(c\) grows is not located (inference).
- **Precision (Wall 1 → Wall 3).** A deciding input acts at unbounded aperture on at least two primes, and is not determined by finitely many coefficients [S].
- **Producer (Wall 14).** Locality is twin-blind [L]; compressions are receivers [S]; integrality over \(\mathbb Z\) is exact but speaks only at integer arguments [S]. What is missing is a point-side certificate.

Organizing identities:
\[
\operatorname{Re}W(f,f)=D(f,f)-\mathfrak d(f),\qquad
W(f,g)=-\int_0^\infty\big(e^h-\psi(e^h)-c\big)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g),
\]
\[
\kappa(K_\zeta)=\#\{\rho:\operatorname{Re}\rho>\tfrac12\},\qquad
\kappa(K_\zeta)=0\iff \sum_{\lambda(n)=-1}\frac{e^{-nt}}n\le\tfrac12\Big(\sum_n\frac{e^{-nt}}n+Ct^{1/2-\varepsilon}\Big).
\]

**Strata**, weakest first:

1. **[open]**: intermediate.
2. **[≥QRH]**: implies a fixed zero-free strip \(\Theta<1\).
3. **[LH]**: implies the Lindelöf hypothesis; "zeros approach the line" is LH plus finiteness for every \(\cos(hD)\Xi\), and implies \(\Theta<1\) [L].
4. **[FS]**: finitely many off-line zeros \(\iff\) all zeros above some height critical \(\iff\) finite index \(\iff\) bounded heat counts \(\iff\) finite wave number [S]. Implies [LH].
5. **[RH]**: equivalent to RH.
6. **[RH+]**: stronger than RH.

## Status changes against the previous ledger

"Solved" means the stated question is answered, never that a route is closed. "Boundary" means a proved limitation with a positive survivor.

| Face | Change | Current content |
|---|---|---|
| **3.38 Separated-regime spectrum** (with the separated-regime selective step) | **Solved at bounded overlap** | For \(\mathrm{plateau}(1/1000)\) the complete Weil matrix is eventually positive definite at every fixed \(c\in(0,1+10^{-18}]\) [L]; the Liouville twin is negative for \(c\ge1/2\) [S]; the Markov form fails above \(e/2\pi\) [L]. The question of the bottom spectrum past Robin–Euler is answered for this profile without conductor uniformity. |
| **14.32 Actual trickle-down** | **Superseded** | Narrow positivity at a quarter of Robin–Euler is replaced by full positivity through \(c=1+10^{-18}\). |
| **14.34 Overlap frustration** | **Solved (boundary)** | Complete positivity holds at ratios \(\rho>1\) where no unimodular gauge makes the Markov Gram Metzler [L]: frustration does not obstruct complete positivity. |
| **3.37 Quasi-analytic boundary** | **Moved** | One Steklov–Denjoy–Carleman profile gives an RH receiver at \(c_N=(\log\log N)(\log\log\log N)^\beta\), \(\beta>2\), below every \((\log\log N)^{1+\varepsilon}\) [L]. Edge: \(\beta\le2\), \(c_N=O(\log\log N)\). |
| **1.34 Global law** | **Sharpened [S]** | One parity class suffices over \(\mathbb Z\): RH iff the odd Liouville class has an upper count. Over \(\mathbb F_q\) one twist does not complete the upper count; the twist tower does. |
| **14.37 Local-to-global by counting** | **Sharpened [S]** | Over \(\mathbb F_q\): Riemann–Roch bounds the index by the genus; Stepanov produces the upper count; the twist tower turns it into the lower count. Over \(\mathbb Z\) the Liouville twist is not a vertical shift (inference). |
| **14.43 Compression** | **Extended [S]** | Over \(\mathbb F_q\) the characteristic polynomial annihilates every trace kernel and certifies nothing; over \(\mathbb Z\) Euler compressors \(\delta_1-c\delta_p\), \(|c|\le p^{-1/2}\), are index-neutral on strip pairs. |
| **3.40 Aliasing and Nyquist** | **Extended [S]** | Two primes separate every ordinate difference polynomially (Baker); one prime aliases at \(2\pi/\log p\). |
| **3.41 Locality** | **Extended [S/L]** | Tempered orbit index is the supremum over consecutive-ratio towers or fine two-prime towers; axis-supported kernels on \(\mathbb Z^S\) have index \(0\) or \(\infty\); locality is twin-blind [L]. |
| **3.39 Index topology** | **Extended [S]** | Index is continuous off the discriminant (vanishing weights, collisions, unit-circle contact). |
| **14.39 Heat-flow horizon** | **Extended [L/S]** | On finite index the exceptional-wave number on a separating tower is \(\kappa\), and collision mass is \(2(\kappa+\sum(m_\rho-1))\). |
| **14.45 Infinite-symmetry continuation** | **Ends in the global law [S]** | For every curve datum with zeros in the strip the complete affine \(A_1\) Weyl sum has a pole of exact multiplicity at every zero; confinement of the poles \(\iff\) eventual holomorphy off \(\operatorname{Re}s=-\tfrac12\) \(\iff\) the lower square-root point count; the golden datum passes every other arithmetic test and fails; the closed chamber certifies only \(\operatorname{Re}\rho\ge1\); the cuspidal pair is a receiver. |
| **1.27 Critical-line census** | **Dichotomy [Lean]** | Either \(N_0\ge\tfrac34N\) or \(\ge(HD(1)-\tfrac12-\tfrac1A-\varepsilon)N\) simple off-line zeros lie within \(A/\log T\). |
| **1.25 Parity form / 1.29 Precision rigidity** | **Formalized [S]** | Deciding-input theorem: any property implying the count rejects the Liouville twin, never holds for \(a\) and \(a+\varepsilon n^{-\eta}\), is not finitely determined, and its weights differ by square-root-class sequences. |
| **3.42 Overlap growth** | **New** | See Wall 3. |
| **3.43 Zero-side fixed-ratio stratum** | **New [S]** | See Wall 3. |
| **1.35 Integrality** | **New [S/L]** | See Wall 1. |
| **1.36 Precision classes** | **New [S/L]** | See Wall 1. |
| **1.37 Inversion precision** | **New [S]** | See Wall 1. |
| **1.38 Flip selectivity at bounded overlap** | **New (open)** | See Wall 1. |
| **14.46 Locality is twin-blind** | **New [L]** | See Wall 14. |
| **14.47 Geometry of the parity twin** | **New [S]** | See Wall 14. |

## Wall 1 — Selective critical sign

| Face | Status | Content and remaining obligation |
|---|---|---|
| **1.0 Fixed-strip first rung** | Open [≥QRH]; external claim | All strip dictionaries read \(\Theta\), including the integrality form. Density envelopes never force vanishing [L]. Guth–Maynard \(30/13\), DH on \(\sigma\ge5/6\) [L]. Chen–Gupta–Li \(7/8\) has no capstone; threshold not extracted. |
| **1.1 Critical signed cancellation** | Open [RH] | Lag, Abel, history, regularized-series, one-sided \(\psi\) and odd-class receivers need the signed bound. RP: RH-equivalent linear floor and an unconditional cofinal linear escape. |
| **1.2 Axis orientation** | Open [RH] | Ward caps, winding and Newton margins detect; extinction missing. |
| **1.3 Complete Weil positivity** | Open [RH]; bounded overlap proved | Fixed-ratio positivity to \(1+10^{-18}\) [L]; high details, narrow sections, eigenlines, complete-cell realization known; index zero on an RH-complete family not. |
| **1.4 Arithmetic cone membership** | Open [RH] | Identification says what the source is, not that it is positive. |
| **1.5 Contrast equality** | Open [RH] | BSY/Jensen/Li identities keep a defect. |
| **1.6 Required uniformity** | Open | Fixed rank, order, height and orthant positivity leave the simultaneous receiver unproved. |
| **1.7 Amplification bookkeeping** | Closed diagnostic | Amplification transfers a supplied cap. |
| **1.8 Critical pronic energy** | Open [RH] | Complete signed energy at small damping. |
| **1.9 Signed continuation** | Open | Integrated signed loss needs horizon-uniform control. |
| **1.10 Absolute compensation** | Open | Relative error \(\to0\) coexists with unbounded raw energy. |
| **1.11 Norm-specific rates** | Open | Norms are not interchangeable. |
| **1.12 Interior anti-alignment** | Open | Exterior field laws do not enter the strip. |
| **1.13 Aperture shell flux** | Open [RH] | Cumulative relaxation must not exceed the initial reserve. |
| **1.14 Actual divisor heat sign** | Open [RH] | Half-line Laguerre, Turán and positive tails leave all-height, all-degree signs. |
| **1.15 Depth homogeneity** | Boundary | Amplification pays at the scale it gains. |
| **1.16 Payment for actual zeros** | Open | Defect, field, inertia and index payments are lower laws. |
| **1.17 Loss-rate improvement** | Open | A sublinear tensor loss must be proved. |
| **1.18 Arithmetic gauge selection** | Classified for flips; not selective at its maximum | Gap \(2\log2\) shared by \(\omega_p\), \(p\ge11\); cofinite flips gap \(0\); one probe selects within finite flips [L]; every flip fails full positivity [Lean]. |
| **1.19 Budget strength** | Boundary | Some budgets are RH-equivalent; Abel/Mertens saturation is [RH+]. |
| **1.20 Arithmetic-point completion** | Open | Periodic and finite-field counts keep their periods; integrality speaks only at integer arguments (1.35). |
| **1.21 Source reserve / work ceiling** | Open [RH] | Cofinal work \(\le2\) is RH-equivalent. |
| **1.22 Finite versus zero exceptions** | Exact boundary | Finite \(\mathcal E_{\rm crit}\iff\) [FS]; \(\mathcal E_{\rm crit}\) within one quantum \(\iff\) RH; quadratic index price [S]. |
| **1.23 Ordered Chebyshev identity** | Exact identity; payment open | Separated couplings are the signed prime error. |
| **1.24 Selectivity** | Theorem | Selection on atomic families and towers; twin-blind positivity cannot reach RH-complete families. |
| **1.25 Parity form** | Theorem [S] | Deciding-input theorem: rejects Liouville. |
| **1.26 Finite-support stratum** | Exact [FS] = RH above a height | Implies LH and \(\Theta<1\); excludes near-line zeros above \(T_0\), which density methods cannot. |
| **1.27 Critical-line census** | Priced; open beyond \(HD(1)\) | Bandwidth: \(E(1/9)\le4\) gives \(70\%\); capacity: \(75\%\iff\kappa\le5/4\); dichotomy places every failure in near-line simple off-line zeros. |
| **1.28 Value-moment mimicry** | Closed [L] | Equal-valued reflected pairs have every value moment of two critical zeros. |
| **1.29 Precision rigidity** | Theorem [L/S] | \(\lambda\) and \(\lambda+\varepsilon n^{-\eta}\) never both tower-positive; formal deciding-input properties. |
| **1.30 Census parity** | Boundary (inference) | Coalescent prime pairs enter with a signed kernel; Poisson term cancels only against the exact Hardy–Littlewood term [L]. |
| **1.31 Shallow energy constant** | Order closed; constant open | \(hE_h=O(N)\); \(70\%\) needs \(\le\tfrac3{20}N\). |
| **1.32 Prime-free existence form** | Closed receiver [L] | Certificate weight is \(\Lambda\) itself. |
| **1.33 Zero-side spectral slack** | Boundary [L] | Grid-dimension ceiling; displacement thresholds \(\eta\ge1/18\) (\(70\%\)) and \(\eta\ge1/6\) (\(75\%\)). |
| **1.34 Global law** | Exact [S] | Index zero \(\iff\) one-sided \(\psi\) count \(\iff\) odd-class upper count. |
| **1.35 Integrality** | Exact; certificate open | \(\{\int_0^1P\}=\mathrm{lcm}(1,\dots,n+1)^{-1}\mathbb Z\); Siegel half = lower count, Liouville half = upper count; integrality exponent \(=\Theta\) [S]; sup-norm certificates vanish at \(0,\tfrac12,1\) [L] and are capped by the integer Chebyshev constant (classical). |
| **1.36 Precision classes** | Theorem [S/L] | The count's stabilizer is the square-root class (gauge flips of square-root prime mass) [L]; tower positivity's is trivial; \(\Lambda+1/n\) has the count iff RH and is never tower-positive [S]. |
| **1.37 Inversion precision** | Boundary [S] | Monotone errors invert at Mertens precision; uniform monotone inversion at every \(\tfrac12+\delta\) is RH; the Stirling error leaves the smooth term and the sawtooth as the only carriers of precision. |
| **1.38 Flip selectivity at bounded overlap** | Open | Fixed-ratio positivity is shown selective against the Liouville twin only. Whether \(\omega_p\) are positive at fixed ratio is untested. |

Evidence: [lag](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean), [Guth–Maynard](../../../formal/GaloisForLFunctions/RHTower/GuthMaynardCorollariesUnconditional.lean), [selection](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/PositivityAtEveryRootSelectsTheVonMangoldtWeight.lean), [cofinite flips](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/CofinitePrimeFlipsHaveZeroGap.lean), [deciding input](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheDecidingInputTheorem.lean), [precision-exact](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TowerPositivityIsPrecisionExact.lean), [integrality exponent](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheIntegralityExponentIsTheZeroWidth.lean), [Stirling split](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheStirlingErrorSplits.lean), [parity form](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheParityFormOfTheGlobalLaw.lean), [index price](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/IndexIsEnergy.lean), [capacity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/BreakingTheCoalescenceBlindSpotAndThreeQuarters.lean), [dichotomy](../../../formal/GaloisForLFunctions/RHTower/Zeta23SimpleOffLineNearLine.lean).

## Wall 3 — Transfer, norms and exhaustion

| Face | Status | Content and remaining obligation |
|---|---|---|
| **3.1 Information retained** | Boundary | Magnitudes, complete-period covariances and collided counts can lose orientation. |
| **3.2 Aperture escape** | Open | Finite windows admit hidden configurations. |
| **3.3 Norms and completions** | Scoped graph control closed | No global norm equivalence. |
| **3.4 Shared resources** | Open | A reserve cannot be spent on each block separately. |
| **3.5 Endpoint logarithms** | Open | Pole cancellation leaves Dini/log remainders. |
| **3.6 Moving horizons** | Open | No free below-half-damping interchange. |
| **3.7 Damping topology** | Open | Half-damped boundedness gives no sub-half trace-ideal control. |
| **3.8 Multiplicity and index** | Clarified | Index counts distinct right zeros; heat collisions add multiplicity excess. |
| **3.9 Observation cost** | Open | Finite-window coercivity has explicit horizon cost. |
| **3.10 Invertible filters** | Boundary | Repair needs non-unit arithmetic content. |
| **3.11 Coupled quantifiers** | Open | Degree, rank, height, time, damping, overlap and support limits do not commute. |
| **3.12 Residual reconstruction** | Open | Coordinate maps need not have bounded inverses. |
| **3.13 Joint orientation** | Open | One-channel signs do not orient the joint form. |
| **3.14 Averages to selected zeros** | Open | Proportions, Schur slack and large-value counts allow exceptions. |
| **3.15 Escape states** | Open [RH] | RH iff every escape state has positive gauge mass. |
| **3.16 Prime to spectral sign** | Open | Prime-side margins must reach the full form with poles intact. |
| **3.17 Archimedean-line horizon** | Open | Near-incidence estimates have bandwidth limits. |
| **3.18 Localization** | Boundary | Positivity constrains a fibre only where the carrier localizes. |
| **3.19 Conductor versus forcing** | Open | No common aperture range. |
| **3.20 Collided-form norm** | Closed locally | Fixed-aperture collided form \(\asymp\) log-weighted Fourier norm. |
| **3.21 Lattice to continuum** | Open | Lattice payment must keep the continuum remainder. |
| **3.22 Computed detection** | Closed diagnostic | Detection is not exclusion. |
| **3.23 Local to global Hodge** | Open | Hyperbolicity is not additive. |
| **3.24 Horizon regulator** | Closed construction | Counterterms explicit. |
| **3.25 Narrow spacing payment** | Closed | Archimedean self-energy and prime defect pay at fixed fractions. |
| **3.26 Complete overlap transfer** | Bounded overlap closed; growth open | Fixed-ratio positivity to \(1+10^{-18}\) [L]; integer atoms carry the whole index [S]; see 3.42. |
| **3.27 Complete residual** | Exact boundary | Residual radical = Weil radical; complete cells capture every finite index. |
| **3.28 All-prime/class exhaustion** | Gap classified; bulk open | Fixed packets and per-conductor eigenlines realized; growing conductors, complement and Gamma/pole coupling open. |
| **3.29 Valuation versus residue classes** | Exact boundary | Residue counterterm rank one; character finite parts \(-L'/L(1,\chi)\). |
| **3.30 Balanced Haar completion** | Details closed | Gamma pays details; single-cell floors; prime edges keep a Gamma reserve [S]. |
| **3.31 Dyadic self-similarity** | Exact; reduction is RH | Positivity on one prime's towers is RH at every generator size. |
| **3.32 Cross-level coupling** | Three parts closed; one is 3.31 | Prime part almost periodic under RH, never summable (inference). |
| **3.33 Renormalization topology** | Boundary | No exponential amplitude renormalization gives uniform graph control. |
| **3.34 Gamma boundary rigidity** | Closed | Norm \(\pi/2\), square reserve, no maximizer [S]. |
| **3.35 Uniform finite-index chain** | Closed except the last layer [FS] | Even powers have a uniform original-Gamma approximation [K]; remaining: \(k=1\), odd diagonals, heads, coarse error, poles; prime–polar cancellation has \(e^R\) loss [S]. |
| **3.36 Orbit approximation versus compactness** | Boundary | One Haar orbit is noncompact. |
| **3.37 Quasi-analytic boundary** | Moved | Super-Gevrey receiver at \(c_N=(\log\log N)(\log\log\log N)^\beta\), \(\beta>2\) [L]; edge \(\beta\le2\), \(c_N=O(\log\log N)\) (inference: weaker log-weights reach \(\beta>1\)). |
| **3.38 Separated-regime spectrum** | Solved at bounded overlap | Exact splitting and per-conductor eigenlines; full positivity for one plateau through \(1+10^{-18}\). |
| **3.39 Index topology** | Boundary [S] | Bounded index closed under pointwise kernel limits; continuous off the discriminant; not closed under \(L^2\) limits of tests. |
| **3.40 Aliasing and Nyquist** | Exact [S] | One tower sees ordinate windows shorter than \(2\pi/\log p\); \(\le\binom\kappa2\) blind primes; two primes carry the index and separate phases polynomially. |
| **3.41 Locality** | Boundary [S/L] | Fine towers decide the orbit index; axis kernels have index \(0\) or \(\infty\); \(\mathbb Z^2\) cyclic positivity fails; infinitely many positive towers force index zero in the arithmetic class. |
| **3.42 Overlap growth** | Open; RH at the super-Gevrey rate | Positivity is proved at fixed \(c\le1+10^{-18}\) by a perturbation \(O((wN)^2)\) around a floor \(1/25\) with a defect reserve; RH needs \(c_N\to\infty\) at the super-Gevrey rate. Missing: every fixed \(c\), a floor uniform in \(c\), and the point where the separated prime error enters. |
| **3.43 Zero-side fixed-ratio stratum** | Boundary [S] | Under RH every ratio is positive; finite support bounds the atomic index by \(\#\)right zeros uniformly; a tempered one-pair model with a constant-density on-line lattice is negative at every \(c\). Fixed-ratio arguments from the zero side must use \(\zeta\)'s zero density. |

Evidence: [Trans-Metzler positivity](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TransMetzlerPositivity.lean), [super-Gevrey](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/SuperGevreyCriticalGrowth.lean), [zero-side stratum](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/ZeroSideStratum.lean), [quasi-analytic boundary](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheReceiversEndAtTheQuasiAnalyticBoundary.lean), [one prime](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OnePrimeSeesTheWholeDefectOfZeta.lean), [even powers](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/AllEvenPrimePowersHaveOriginalGammaApproximation.lean), [nonfirst reserve](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheFullNonfirstSourceRetainsAlmostAllGamma.lean), [eigenlines](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSimpleCompleteWeilEigenlinesConvergeToRamanujanLines.lean), [index closure](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/BoundedIndexIsClosedUnderPointwiseLimits.lean), [index continuity](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheIndexIsContinuousOffTheDiscriminant.lean), [Nyquist](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheNyquistLawOfAPrimeTower.lean), [two-prime phases](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TwoPrimeTowersSeeEveryOrdinateDifference.lean), [fine towers](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/FineTowersDecideEveryOrbitKernel.lean).

## Wall 14 — Realization and forcing

| Face | Status | Content and remaining obligation |
|---|---|---|
| **14.1 Capacity and limits** | Open | A faithful limit must carry orientation. |
| **14.2 Algebra without orientation** | Boundary | Correspondence identities hold for impure data. |
| **14.3 Detector without producer** | Open | Calibrated vanishing laws are equivalent to criticality. |
| **14.4 Effectivity receiver** | Closed equivalence | Section/effectivity hypotheses are Hodge receivers. |
| **14.5 Pre-divisor weld** | Open | Prime and Gamma reservoirs need source-level compatibility. |
| **14.6 Section selectivity** | Open | Counts and positive sections do not give full-source RR/Hodge. |
| **14.7 Theta degree coupling** | Closed scoped law | Linear RR/count relation. |
| **14.8 Blind-carrier exhaustion** | Open | The maximal blind ideal is full only at RH. |
| **14.9 Positivity versus faithfulness** | Boundary | Strong invariant positivity may force RH plus simplicity. |
| **14.10 Invariant positive carriers** | Boundary | Off-line boosts force isotropy. |
| **14.11 Multiplicative forcing capacity** | Closed scoped boundary | Boundary forcing does not move interior zeros. |
| **14.12 Degree-one rigidity** | Closed scoped law | The simple-pole class is \(\mathbb R\cdot\zeta\). |
| **14.13 Zero–pole budget** | Closed diagnostic | Inserted-zero bookkeeping is not \(\zeta\)'s budget. |
| **14.14 Amplification base** | Open | A fixed tensor loss can encode RH. |
| **14.15 Successor coupling** | Structure closed; sign open | Periodic holonomy flat only at the Euler point. |
| **14.16 Correspondence ring** | Closed identity | Square identities hold without purity. |
| **14.17 Local representation type** | Closed diagnostic | No automatic conformal Frobenius. |
| **14.18 Arithmetic polarization** | Open | A form faithful, positive and equivariant at once. |
| **14.19 Zero contraction** | Closed scoped boundary | Contraction laws do not move nonreal quartets. |
| **14.20 Collision and conductor** | Closed obstruction | Finite carriers meet localization/conductor barriers. |
| **14.21 Collided polarization** | Open sign | \(D\) positive; \(D=W\) needs zero defect. |
| **14.22 Central order** | Open forcing | Central-ceiling forcing missing. |
| **14.23 Polar-configuration criterion** | Closed receiver | One vertical section decides positivity. |
| **14.24 Torsion renormalization** | Scoped bounds closed | Positive index \(\le N^{4/5+\varepsilon}\). |
| **14.25 Deformation** | Boundary | Deformation-stable properties need not select. |
| **14.26 Field and energy** | Open upper bound | Lower costs and virial laws explicit; source ceiling missing. |
| **14.27 Coupled counterterm rank** | Closed scoped boundary | Partner-rank costs. |
| **14.28 Counterterm covariance** | Closed classification | Covariant diagonal finite parts are scalar. |
| **14.29 Arithmetic base across primes** | Construction boundary | Ramanujan local factors excluded from Lorentzian closure. |
| **14.30 Zero moments** | Closed identification | Zero moments are Rosati-type pairings. |
| **14.31 Horizon finite part** | Local payment closed | Sharp all-prime gap \(2\log2\). |
| **14.32 Actual trickle-down** | Superseded | Replaced by full positivity at bounded overlap (3.38). |
| **14.33 Conformal replacement** | Open beyond tested maps | Hecke dilation has factor one. |
| **14.34 Overlap frustration** | Solved (boundary) | Frustration coexists with complete positivity at \(\rho>1\) [L]. |
| **14.35 Adjunction versus Xi** | Fidelity boundary | Adjunction energies are prime-matrix eigenvalues, not Xi zeros. |
| **14.36 Function-field approximation** | Boundary (inference) | Curves reproduce the prime support, not the archimedean continuum. |
| **14.37 Local-to-global by counting** | Closed over \(\mathbb F_q\); open over \(\mathbb Z\) | Over \(\mathbb F_q\): Riemann–Roch ceiling, Stepanov upper count, twist tower [S]. Over \(\mathbb Z\): no ceiling, no producer, and sparse annihilators need a lattice spectrum. |
| **14.38 Blind hyperbolicity, selective sign** | Exact boundary | Hodge index at proved scales carries no arithmetic; the Metzler sign does. |
| **14.39 Heat-flow horizon** | Sharpened; near-axis open | \(2/3\) horizon [L]; wave number and collision mass [L/S]; total count bounded iff [FS]. |
| **14.40 Over-regular Beurling systems** | Boundary | Regular counts with positive primes do not force RH. |
| **14.41 Krein–Langer structure** | Boundary [S] | A positive part never pays a pair; the finite stratum is exactly the Krein–Langer class. |
| **14.42 Tensor amplification over \(\mathbb Z\)** | Boundary (inference) | The tensor square of the prime error is WL's mean square. |
| **14.43 Compression** | Boundary [S] | Receivers on both sides: characteristic-polynomial annihilation over \(\mathbb F_q\), index-neutral Euler compressors over \(\mathbb Z\). A producer must vanish at the primes. |
| **14.44 Golden calibration** | Boundary [S] | Tower data do not decide; the lattice does. |
| **14.45 Infinite-symmetry continuation** | Receiver of the count | Genus zero: blind, moment ceiling at the Lindelöf stratum [L]. Positive genus: exact pole calculus for every curve datum; confinement \(\iff\) unitarity \(\iff\) the lower square-root count; closed-chamber holomorphy certifies only \(\operatorname{Re}\rho\ge1\); a pole of the cuspidal \(L\)-ratio is a zero of the negative series [S]. No input beyond the count. |
| **14.46 Locality is twin-blind** | Boundary [L] | Unitary twists translate pair spectra and preserve tower faithfulness and the tower Hasse principle: a selective statement must enter through a count or a carrier. |
| **14.47 Geometry of the parity twin** | Boundary [S] (inference over \(\mathbb Z\)) | Over \(\mathbb F_q\) the quadratic twist of base changes is the vertical shift \(s\mapsto s+i\pi/\log q^{2^j}\), so an upper-count producer applies to every twist. Over \(\mathbb Z\) the Liouville twist acts on prime constituents and is not a vertical shift. |
| **14.48 Point side versus zero side** | Boundary [S] | Integer auxiliaries see integrality only at \(s\in\mathbb Z\), never at a nontrivial zero; Stepanov-type certificates must vanish at rational points. |

Evidence: [moment ceiling](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MomentBoundsCapTheOffLineDepth.lean), [affine Weyl poles](../../../formal/GaloisForLFunctions/HTGeometry/LoopEisenstein/AffineA1FiniteFieldWeylPoles.lean), [trickle-down count](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheTrickleDownInequalityIsTheSquareRootCount.lean), [Stepanov mechanism](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/SparseAnnihilatorsAndTheStepanovMechanism.lean), [twist tower](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheTwistTowerCompletesTheUpperCount.lean), [compressions](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/CompressionsAreReceivers.lean), [locality](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/LocalityIsTwinBlind.lean), [wave number](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheCollisionMassIsTheWaveNumber.lean), [integer Dirichlet polynomials](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/IntegerDirichletPolynomialsAtArithmeticPoints.lean), [horizon](../../../formal/GaloisForLFunctions/RHTower/KiKimLeeTwoThirdsHorizon.lean), [Krein–Langer](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheWeilKernelIsKreinLangerOnTheFiniteStratum.lean), [golden](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheGoldenCurveIsDecidedOnItsTowerButNotOnTheLattice.lean).

## Sharp obstructions and their positive survivors

| Excluded shortcut | Strongest survivor | Replacement question |
|---|---|---|
| Twin-blind positivity on RH-complete families | Selection on atomic families and on towers | A parity-breaking input that survives overlap growth (Q1). |
| The maximal margin as a selector | Margin classified for all flips; one probe selects within finite flips | An input that sees every prime's sign; first, flips at fixed ratio (W02). |
| Markov positivity or a Metzler gauge as the route to full positivity | Full positivity at bounded overlap past \(c=1\) [L] | Overlap growth (Q1). |
| Fixed-ratio positivity as a consequence of finite support | Uniform atomic index bound under finite support | An argument using \(\zeta\)'s zero density. |
| Gevrey profiles to reach \(c_N\asymp\log\log N\) | Logarithmic Denjoy–Carleman profiles at \((\log\log N)(\log\log\log N)^{\beta}\), \(\beta>2\) | The exact quasi-analytic edge (W04). |
| Interval-stable prime information as a sign input | Precision rigidity; deciding-input theorem | A structural input (Euler product and functional equation as identities). |
| The count as a selector of \(\Lambda\) | Tower positivity selects exactly | Positivity statements, not counts, for selection. |
| Narrow generators to shorten towers | Tower positivity is RH at every generator size | None; the tower must be unbounded. |
| One prime tower as a decider | Nyquist law; two primes carry the index and separate phases | Two-prime or infinitely-many-tower arguments. |
| Local (tower) data as a selector | Tower Hasse principle in the arithmetic class | A count or a carrier; locality is twin-blind. |
| Absolute payment of all prime layers | Uniform finite index except \(k=1\) | The last layer is [FS]. |
| Positive-part repair of a finite index | Krein–Langer: separated pairs keep their index | A structural index ceiling. |
| Compression as a producer | Annihilation law; Euler compressors index-neutral | A point-side producer (Q2). |
| Sup-norm integer auxiliaries | Exact integrality lattice; vanishing at small rationals | A signed certificate for small Nair integrals (Q2). |
| Own-tower Frobenius data as a decider | Golden curve: tower index \(1\), lattice \(\infty\) | Global (lattice) data. |
| One quadratic twist completing the upper count over \(\mathbb F_q\) | The twist tower over \(2\)-power base changes | A geometric parity twin over \(\mathbb Z\). |
| Zero-side slack below bandwidth \(3/4\) | Slack conservation; displacement thresholds | Displacement-sensitive slack near bandwidth one. |
| Value moments as a criticality certificate | Mimicry; corrected Cauchy–Schwarz | A displacement-sensitive count at depth \(1/\log T\). |
| One-sided sieve bounds beyond bandwidth one | Exact exchange rate | A two-sided coalescent pair estimate. |
| Density estimates as zero exclusion | \(30/13\) on \([1/2,5/6]\), DH on \(\sigma\ge5/6\) | A vanishing mechanism. |
| Finite support as a sub-Lindelöf target | Finite support = RH above a height \(\Rightarrow\) LH \(\wedge\) QRH | Treat as LH-level. |
| Regular counts as forcing | Over-regular Beurling systems | Use the functional equation. |
| Function-field or tensor amplification as imported positivity | Curves reproduce prime support; tensor square = WL mean square | A base with known cohomology. |
| Infinite-symmetry continuation in genus zero as a zero detector | Jensen moment ceiling; zeros enter the polar divisor in positive genus | Zero-seeing in positive genus (below). |
| Continuation under infinite symmetry as confinement (positive genus) | Exact zero detector for every curve datum; chamber certifies exactly \(\operatorname{Re}\rho\ge1\); confinement \(\iff\) lower square-root count | The count itself (Q2). |
| Detection or quantization as an upper bound | Canonical energy; quadratic index price | A virial-type upper estimate. |

## Consequences for priorities

- [Q1](obstacles-summary.md#q1) targets **3.42 / 3.37 / 1.38 / 3.26**: overlap growth and flip selectivity.
- [Q2](obstacles-summary.md#q2) targets **1.34 / 1.35 / 14.37 / 14.43 / 14.47 / 14.48**: the point-side producer.
- [Q3](obstacles-summary.md#q3) targets **1.27 / 1.30 / 1.31 / 1.33**: displacement at depth \(1/\log T\) and the coalescent pair energy. **14.45** is settled: it ends in the count.
- **1.26 / 3.35 / 14.39 / 14.41** (finite support) are LH-level and RH-hard at large height; not near-term priorities.

No route is declared dead by these priorities. Finite calculations, compositions, integration and intake are [just work](obstacles-summary.md#21-tasks-that-are-just-work).
