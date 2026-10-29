# Walls ledger

Status: 29 October 2026, corpus HEAD `718f741cc7` plus working tree.

**Three core problem families remain:**

- the selective critical sign (Wall 1);
- transfer and exhaustion (Wall 3);
- independent realization or forcing (Wall 14).

No core wall was crossed. The ledger now records where each wall's missing input can come from.

- **Selectivity has exactly two sources [L].** One is the shift-fixed pole and Gamma terms. The other is gauge charge, which enters only through non-ratio lags, i.e. additive structure.
- **The first source is in use.** It pays the complete form up to a certified overlap \(c_*>1+10^{-16}\). It rejects the Liouville twin and \(\omega_{11}\) there. Its present method ends at pole charge one.
- **The second source is untouched.** RH is gauge charge at the single gauge point \(0\), at square-root precision. Over \(\mathbb Z\) no producer of it is known: divisibility sees prime powers, not parity, and \(\mathbb Z\) has no Frobenius.

Links: [route report](route-obstacles.md) · [summary and next questions](obstacles-summary.md) · [route unification](route-unification-ledger.md) · [scoped no-go catalogue](../rh-killed-routes.md). Evidence comes from corpus searches and Lean statements; no builds were run.

Labels:

| Label | Meaning |
|---|---|
| **[L]**, **[S]**, **[K]** | As in the frontier map. |
| **[Lean]** | Statement read; integration not assessed. |
| **(inference)** | A conclusion of this review. |

[Working log](../../../logs/review-2910c-research-2026-10-29.md).

## The three families

| Family | Question | Where the input can come from | What would cross it |
|---|---|---|---|
| **Wall 1 — Selective critical sign** | What bounds the actual signed prime/Möbius source, the complete Weil form or a computed defect at the critical scale, using a property \(\Lambda\) has and its twins lack? | Only the pole and Gamma (linear precision) or gauge charge at the point \(0\) (additive structure) [L]. | A square-root-precise statement about gauge charge at \(0\): parity-breaking, beyond the major arcs, not local, all tails and quantifiers kept. |
| **Wall 3 — Transfer and exhaustion** | Does an estimate survive the needed norm, overlap growth, aperture, conductor and simultaneous limit? | The crossing at length \(\approx\) height (bandwidth one), where non-ratio lags and near-incidences start to count. | A comparison in a norm that carries the sign through that crossing, with zero margin in the limit. |
| **Wall 14 — Realization and forcing** | Which independently built structure produces the inequality? | Over \(\mathbb F_q\), Frobenius couples addition and multiplication; over \(\mathbb Z\), nothing is known. | A producer that vanishes finer than divisibility, a geometric parity twin, or an index ceiling from ring structure. |

**How the walls interlock.**

- **Global law (Wall 1 = Wall 14 at the endpoint) [S].** Index zero of the Weil kernel is the one-sided count. That is already the upper count of the odd Liouville class.
- **Two sources (Wall 1) [L].**
  - Pointwise-closed statements are twin-blind.
  - The diamagnetic inequality makes \(\zeta\) the ground state of its gauge orbit on \(|\cdot|\)-closed families.
  - The gauge defect lives only on non-ratio lags.
- **Overlap (Wall 3 with Wall 1 content).** Above \(c=1\), shells \(n=km+j\), \(|j|\lesssim c\), enter [K], and nonpolar reference energies lose \(\log c\) [S]. Under RH, terms that exist only through overlap repay this loss (inference).
- **Marginality (Wall 3).** No atom-norm floor exists at growing overlap [S]. Aperture floors decay doubly exponentially [L]. \(\Lambda_{\rm dBN}\ge0\) (external). Positivity at the RH limit has zero margin, so no estimate with a fixed loss can carry it (inference).
- **Producer (Wall 14) [L].** Every producer obeys the ledger \(\sum m_p\log p\le\log A\). Stepanov's multiplicity comes from \(x^q=x\). Over \(\mathbb Z\) divisibility cannot tell the primes from one parity class at square-root precision.

**Organizing identities.**

The complete form and an ordered entry:
\[
\operatorname{Re}W(f,f)=D(f,f)-\mathfrak d(f),\qquad
W(f,g)=-\int_0^\infty\big(e^h-\psi(e^h)-c\big)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g).
\]

The gauge defect of a twist lives only on non-ratio lags:
\[
\mathrm{prime}_\omega(f_x)-\mathrm{prime}(f_{\omega x})=\sum_k\Lambda_k\sum_{m,n}\big(\omega(k)-\omega(m)\omega(n)\big)x_mx_n\,(\cdots).
\]

The index is the count of right zeros, and its vanishing is the odd-class upper count:
\[
\kappa(K_\zeta)=\#\{\rho:\operatorname{Re}\rho>\tfrac12\},\qquad
\kappa(K_\zeta)=0\iff \sum_{\lambda(n)=-1}\frac{e^{-nt}}n\le\tfrac12\Big(\sum_n\frac{e^{-nt}}n+Ct^{1/2-\varepsilon}\Big).
\]

Length–height coordinates:
\[
\text{overlap}=\frac XT,\qquad \text{bandwidth}=\frac{\log X}{\log T}.
\]

**Strata**, weakest first:

| # | Stratum | Meaning |
|---|---|---|
| 1 | **[open]** | Intermediate. |
| 2 | **[≥QRH]** | Implies a fixed strip \(\Theta<1\). |
| 3 | **[LH]** | Implies Lindelöf. |
| 4 | **[FS]** | Finitely many off-line zeros, equivalently RH above a height. Implies LH and \(\Theta<1\). |
| 5 | **[RH]** | Equivalent to RH. |
| 6 | **[RH+]** | Stronger than RH. |

## Status changes against the previous ledger

"Solved" means the stated question is answered, never that a route is closed. "Boundary" means a proved limitation with a positive survivor.

| Face | Change | Current content |
|---|---|---|
| **1.38 Flip selectivity at bounded overlap** | **Solved for \(p=11\) [S]** | \(\omega_{11}\) is negative at every large horizon for every fixed \(c\ge99/100\), by a three-conductor prime-square trial. Gamma and both poles are identical on both sides, so the failure is pole-mediated. Other \(p\) and a uniform version are open (W02). |
| **3.42 Overlap growth** | **Sharpened** | Three new boundaries (3.44, 3.45, 3.47) and two new structures (3.46, 3.49), detailed in the Wall 3 table. |
| **3.38 Separated-regime spectrum** | **Extended past touching** | Positivity for \(c<c_*\), \(c_*>1+10^{-16}\) [K]. |
| **3.37 Quasi-analytic boundary** | **Moved** | \(L(\log L)^2\log\log L\) [S]; explicit \((\log\log N)^\alpha/N\) schedules reach \(\kappa\) for every \(\alpha>1\) [L]. |
| **1.35 Integrality** | **Extended [L]** | Producer ledger; binomial multiplicity \(\le1\) above \(\sqrt N\); divisibility sees prime powers, not parity. Chebyshev's factorial ratio passes the sup-norm cap \(0.8644\) at linear precision. |
| **1.36 Precision classes** | **Extended** | Finite aperture cannot decide [K]; complex count lifts [K]; the successor enters only modulo the square-root class [K]; independent random signs satisfy the count [S]. |
| **1.37 Inversion precision** | **Sharpened [L]** | Chebyshev ledger: \(\psi\) is two Möbius moments, a sawtooth of size \(<n\), and Mertens. |
| **1.27 Critical-line census** | **Extended [K]** | \(70\%\) or a simple near-line off-line core. |
| **1.33 Zero-side slack** | **Extended [K]** | Projected displacement pays the negative-part credit; model thresholds at every bandwidth. |
| **3.40 Aliasing and Nyquist** | **Made effective [L]** | Height filtration \(\kappa_T=O(T\log T)\); certifying towers \(3^k/2^j\); carriers \(p^iq^j\); fine towers with unbounded windows. |
| **3.41 Locality** | **Extended [L]** | Attained maximal depth is seen by almost every prime. The unattained case is open. |
| **14.46 Locality is twin-blind** | **Generalized [L]** | Every pointwise-closed, shift-invariant statement is twin-blind. Weil selectivity lives in the pole and Gamma. |
| **14.47 Geometry of the parity twin** | **Settled [L]** | Geometric only in the Bohr closure: no vertical shift is \(-1\) at two primes. |
| **14.37 Local-to-global by counting** | **Sharpened [L]** | Stepanov's order over \(\mathbb F_q\) (both parity classes, index zero); the function-field ceiling \(D\ge N\log q\) is exact. |
| **14.39 Heat-flow horizon** | **Extended [K]** | Localized dissipation through collisions and \(t=0\). |
| **14.45 Infinite-symmetry continuation** | **Closed; candidate retired** | Confinement \(\iff\) the lower square-root count [L]. |
| **1.39 Two-source law** | **New [L]** | See Wall 1. |
| **1.40 Point-0 typicality** | **New [L]** | See Wall 1. |
| **1.41 Major arcs of gauge charge** | **New [Lean]** | See Wall 1. |
| **3.44 Certified-method boundary** | **New [K]** | See Wall 3. |
| **3.45 Charge barrier** | **New [K]** | See Wall 3. |
| **3.46 Successor shells and nonpolar loss** | **New [K/S]** | See Wall 3. |
| **3.47 Atom-norm degeneration** | **New [S]** | See Wall 3. |
| **3.48 Length–height coordinate** | **New [K]** | See Wall 3. |
| **3.49 Prefix Schur reduction** | **New [S]** | See Wall 3. |
| **3.50 Marginality** | **New (inference)** | See Wall 3. |
| **14.49 Producer ledger** | **New [L]** | See Wall 14. |
| **14.50 Frobenius gap** | **New (inference)** | See Wall 14. |

The three new boundaries of 3.42, in detail:

- The three fixed estimates saturate at \(\delta_*\approx9.3\cdot10^{-18}\) [K].
- The optimized Young family certifies every \(c<c_*\), \(c_*>1+10^{-16}\), with floor \(1/400\) at \(1+10^{-16}\), and is exact at its constants [K].
- The reference floor needs pole charge \(<1\) [K].

The two new structures are the successor shells and the exact Schur reduction. Nonpolar energies lose \(\log c\) [S], and atom-normalized floors fail [S].

## Wall 1 — Selective critical sign

| Face | Status | Content and remaining obligation |
|---|---|---|
| **1.0 Fixed-strip first rung** | Open [≥QRH]; external claim | Every strip dictionary reads \(\Theta\), including integrality. Density envelopes never force vanishing. Guth–Maynard \(30/13\), DH on \(\sigma\ge5/6\) [L]. The external \(7/8\) claim has no corpus capstone. |
| **1.1 Critical signed cancellation** | Open [RH] | Lag, Abel, history, series, one-sided \(\psi\), odd-class and first-clock receivers need the signed bound. |
| **1.2 Axis orientation** | Open [RH] | Ward caps, winding and Newton margins detect; extinction is missing. |
| **1.3 Complete Weil positivity** | Open [RH]; bounded overlap proved | Positivity for \(c<c_*\) [K]; index zero on an RH-complete family is not proved. |
| **1.4 Arithmetic cone membership** | Open [RH] | Identification says what the source is, not that it is positive. |
| **1.5 Contrast equality** | Open [RH] | BSY, Jensen and Li identities keep a defect. |
| **1.6 Required uniformity** | Open | Fixed rank, order, height and orthant positivity leave the simultaneous receiver open. |
| **1.7 Amplification bookkeeping** | Closed diagnostic | Multiplicative amplification loses linearly. |
| **1.8 Critical pronic energy** | Open [RH] | Complete signed energy at small damping. |
| **1.9 Signed continuation** | Open | Horizon-uniform integrated signed loss. |
| **1.10 Absolute compensation** | Open | Relative error \(\to0\) coexists with unbounded raw energy. |
| **1.11 Norm-specific rates** | Open | Norms are not interchangeable. |
| **1.12 Interior anti-alignment** | Open | Exterior field laws do not enter the strip. |
| **1.13 Aperture shell flux** | Open [RH] | Cumulative relaxation must not exceed the initial reserve. |
| **1.14 Actual divisor heat sign** | Open [RH] | All-height, all-degree signs. |
| **1.15 Depth homogeneity** | Boundary | Amplification pays at the scale it gains. |
| **1.16 Payment for actual zeros** | Open | Defect, field, inertia and index payments are lower laws. |
| **1.17 Loss-rate improvement** | Open | A sublinear loss law needs gauge charge or a fixed-budget correspondence [L]. |
| **1.18 Arithmetic gauge selection** | Classified for flips | Gap \(2\log2\) shared by \(\omega_p\), \(p\ge11\); one probe selects within finite flips [L]; \(\omega_{11}\) fails at fixed ratio [S]. |
| **1.19 Budget strength** | Boundary | Some budgets are RH-equivalent; Abel/Mertens saturation is [RH+]. |
| **1.20 Arithmetic-point completion** | Open | Periodic counts keep their periods; integrality speaks only at integer arguments. |
| **1.21 Source reserve / work ceiling** | Open [RH] | Cofinal work \(\le2\). |
| **1.22 Finite versus zero exceptions** | Exact boundary | Finite \(\mathcal E_{\rm crit}\iff\) [FS]; one quantum \(\iff\) RH. |
| **1.23 Ordered Chebyshev identity** | Identity; payment open | Separated couplings are the signed prime error. |
| **1.24 Selectivity** | Theorem | Selection on atomic families and towers; twin-blind positivity cannot reach RH-complete families. |
| **1.25 Parity form** | Theorem [S] | The deciding-input theorem rejects Liouville. |
| **1.26 Finite-support stratum** | Exact [FS] | RH above a height; implies LH and \(\Theta<1\). |
| **1.27 Critical-line census** | Priced; dichotomy [K] | \(E(1/9)\le4\) gives \(70\%\); \(75\%\iff\kappa\le5/4\). Every failure lies in near-line simple off-line zeros. |
| **1.28 Value-moment mimicry** | Closed [L] | Reflected pairs mimic critical moments. |
| **1.29 Precision rigidity** | Theorem [L/S] | \(\lambda\) and \(\lambda+\varepsilon n^{-\eta}\) are never both tower-positive. |
| **1.30 Census parity** | Boundary | Coalescent pairs enter with a signed kernel. The surplus is pure gauge charge with budget zero almost surely [L]. |
| **1.31 Shallow energy constant** | Order closed; constant open | \(70\%\) needs \(\le\tfrac3{20}N\). |
| **1.32 Prime-free existence form** | Closed receiver | The certificate weight is \(\Lambda\). |
| **1.33 Zero-side slack** | Boundary [K] | Projected credit \(E_{\rm proj}\le2\operatorname{tr}Q_-\le\) slack. A positive lower bound for \(E_{\rm proj}\) is open. |
| **1.34 Global law** | Exact [S] | Index zero \(\iff\) one-sided count \(\iff\) odd-class upper count. |
| **1.35 Integrality** | Exact; certificate open | Integrality lattice and exponent \(\Theta\) [S]. Producer ledger; divisibility cannot select parity [L]. |
| **1.36 Precision classes** | Theorem | Count stabilizer = square-root class; tower positivity's stabilizer is trivial; finite aperture is window-determined; random signs satisfy the count. |
| **1.37 Inversion precision** | Boundary [L] | Chebyshev ledger; monotone inversion at Mertens precision. |
| **1.38 Flip selectivity** | Solved for \(\omega_{11}\) [S]; general open | Pole-mediated prime-square trial. |
| **1.39 Two-source law** | Theorem [L] | See note (a) below. |
| **1.40 Point-0 typicality** | Exact reformulation [L] | See note (b) below. |
| **1.41 Major arcs of gauge charge** | Theorem [Lean] | See note (c) below. |

Notes on the new Wall 1 faces:

- **(a) Two-source law.**
  - Pointwise-closed, shift-invariant statements contain every unitary twist.
  - \(\zeta\) is the ground state of its gauge orbit on \(|\cdot|\)-closed families.
  - The gauge enters only through non-ratio lags.
  - Selectivity therefore comes from the pole and Gamma, or from overlapping and signed families.
- **(b) Point-0 typicality.**
  - Haar-almost every twist cancels to the square root and has no pole.
  - The exceptional set is comeager and null, and \(0\) lies in its closure.
  - RH says that \(0\) is typical modulo its pole.
  - Every argument that uses only multiplicative data proves an almost-sure statement.
- **(c) Major arcs of gauge charge.**
  - Dirichlet characters mod \(q\) keep a successor pair \((n,n+h)\) iff \(q\mid h\).
  - The singular series is the average over these stabilizers.
  - The discrepancy at \(0\) is open (I19).

Evidence: [two sources](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/PointwiseClosedStatementsAreTwinBlind.lean), [diamagnetic](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheDiamagneticInequality.lean), [non-ratio lags](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheGaugeEntersThroughNonRatioLags.lean), [typical except for the pole](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/ThePrimeSourceIsTypicalExceptForItsPole.lean), [comeager and null](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheMoebiusExceptionalSetIsComeagerAndNull.lean), [finite gauge subgroups](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/FiniteGaugeSubgroupsResolveWhatTheArchimedeanLineCannot.lean), [coalescent surplus](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheCoalescentSurplusIsPureGaugeCharge.lean), [eleven flip](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/BoundedOverlap/ElevenFlipAtEveryHorizon.lean), [linear counts](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/IntegralityProducesLinearCounts.lean), [smooth term](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheSmoothTermInvertsToMobiusMoments.lean), [finite aperture](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/FiniteAperturePositivityCannotDecide.lean), [70% dichotomy](../../../formal/GaloisForLFunctions/RHTower/Zeta23SeventyPercentOrSimpleNearLine.lean), [projected credit](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ProjectedDisplacementPaysNegativePartCredit.lean), [parity form](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheParityFormOfTheGlobalLaw.lean).

## Wall 3 — Transfer, norms and exhaustion

| Face | Status | Content and remaining obligation |
|---|---|---|
| **3.1 Information retained** | Boundary | Magnitudes, complete-period covariances and collided counts can lose orientation. |
| **3.2 Aperture escape** | Open | Finite windows admit hidden configurations; aperture \(A\) reads only \(n\le e^{2A}\). |
| **3.3 Norms and completions** | Scoped graph control closed | No global norm equivalence. |
| **3.4 Shared resources** | Open | A reserve cannot be spent on each block separately. |
| **3.5 Endpoint logarithms** | Open | Pole cancellation leaves Dini/log remainders. |
| **3.6 Moving horizons** | Open | No free below-half-damping interchange. |
| **3.7 Damping topology** | Open | Half-damped boundedness gives no sub-half trace-ideal control. |
| **3.8 Multiplicity and index** | Clarified | Index counts distinct right zeros; collisions add multiplicity excess. |
| **3.9 Observation cost** | Open | Finite-window coercivity has explicit horizon cost. |
| **3.10 Invertible filters** | Boundary | Repair needs non-unit arithmetic content. |
| **3.11 Coupled quantifiers** | Open | Degree, rank, height, time, damping, overlap and support limits do not commute. |
| **3.12 Residual reconstruction** | Open | Coordinate maps need not have bounded inverses. |
| **3.13 Joint orientation** | Open | One-channel signs do not orient the joint form. |
| **3.14 Averages to selected zeros** | Open | Proportions, Schur slack and large-value counts allow exceptions. |
| **3.15 Escape states** | Open [RH] | RH iff every escape state has positive gauge mass; power-growth escape has zero mass [L]. |
| **3.16 Prime to spectral sign** | Open | Prime-side margins must reach the full form with poles intact. |
| **3.17 Archimedean-line horizon** | Boundary [L] | Below the threshold the line sees the whole torus; beyond it, near-incidence is gauge charge. |
| **3.18 Localization** | Boundary | Positivity constrains a fibre only where the carrier localizes. |
| **3.19 Conductor versus forcing** | Open | No common aperture range. |
| **3.20 Collided-form norm** | Closed locally | Log-weighted Fourier norm at fixed aperture. |
| **3.21 Lattice to continuum** | Open | Lattice payment must keep the continuum remainder. |
| **3.22 Computed detection** | Closed diagnostic | Detection is not exclusion. |
| **3.23 Local to global Hodge** | Open | Hyperbolicity is not additive. |
| **3.24 Horizon regulator** | Closed construction | Counterterms explicit. |
| **3.25 Narrow spacing payment** | Closed | Archimedean self-energy and prime defect pay at fixed fractions. |
| **3.26 Complete overlap transfer** | Bounded overlap closed; growth open | Positivity for \(c<c_*\); integer atoms carry the index. |
| **3.27 Complete residual** | Exact boundary | Residual radical = Weil radical; complete cells capture every finite index. |
| **3.28 All-prime/class exhaustion** | Bulk open | Fixed packets realized; growing conductors open. |
| **3.29 Valuation versus residue classes** | Exact boundary | Residue counterterm rank one. |
| **3.30 Balanced Haar completion** | Details closed | Gamma pays details; prime edges keep a Gamma reserve [L]. |
| **3.31 Dyadic self-similarity** | Exact; RH | One prime's towers at every generator size. |
| **3.32 Cross-level coupling** | Three parts closed | The prime part is 3.31. |
| **3.33 Renormalization topology** | Boundary | No exponential amplitude renormalization gives uniform graph control. |
| **3.34 Gamma boundary rigidity** | Closed | Norm \(\pi/2\), no maximizer. |
| **3.35 Uniform finite-index chain** | Closed except \(k=1\) [FS] | Prime–polar cancellation has an \(e^R\) loss. |
| **3.36 Orbit approximation** | Boundary | One Haar orbit is noncompact. |
| **3.37 Quasi-analytic boundary** | Moved | Receiver at \(L(\log L)^2\log\log L\) [S]; explicit schedules reach the index [L]; Gevrey-\(\le1\) profiles vanish. |
| **3.38 Separated-regime spectrum** | Solved; extended past touching | Positivity for \(c<c_*\). |
| **3.39 Index topology** | Boundary [S] | Continuous off the discriminant; lower semicontinuous pointwise. |
| **3.40 Aliasing and Nyquist** | Exact and effective [L/S] | Heights, certifying towers, carriers; two primes separate phases. |
| **3.41 Locality** | Boundary [L] | Fine towers decide; attained depth is seen by almost every prime; unattained depth open. |
| **3.42 Overlap growth** | Open; RH at the super-Gevrey rate | See 3.44–3.50. |
| **3.43 Zero-side fixed-ratio stratum** | Boundary [S] | A tempered countermodel is negative at every \(c\); \(\zeta\)'s density is needed. |
| **3.44 Certified-method boundary** | Exact at fixed constants [K] | The optimized Young family certifies \(0<c<c_*\), \(1+10^{-16}<c_*<(1+1/q_0)/2\). Scalar data attain its floor. The three fixed estimates alone stop at \(\delta_*\). Sharper constants or new information move \(c_*\) (W01). |
| **3.45 Charge barrier** | Boundary [K] | The exact reference floor \(F(c)=F(1)-\log c+(c-1)\alpha(1)\) holds while \(\alpha(c)=c\alpha(1)<1\), \(\alpha(1)\ge99/100\). The method's Young parameter \(2/(1-\alpha)\) diverges at \(c=1/q_0\). |
| **3.46 Successor shells and nonpolar loss** | Structure [K/S]; payment open | Shell \(k\) enters at \(N\log(1+k/N)\to k\). At fixed \(c>1\) the weighted successor fibre grows like \(\log N\). Nonpolar reference energies are \(E_m(1)-\log c\). The repayment is I1. |
| **3.47 Atom-norm degeneration** | Boundary [S] | No atom-normalized floor at \(c_N\to\infty\). A Montgomery–Vaughan band bound holds for the bare polynomial; its transfer is open (I17). |
| **3.48 Length–height coordinate** | Exact [K] | Overlap \(X/T\), bandwidth \(\log X/\log T\). The atomic programme and the census meet at bandwidth one. |
| **3.49 Prefix Schur reduction** | Exact [S] | Full positivity \(\iff D-B^*A^{-1}B\ge0\), with the prefix paid through touching. The tail bound is open (I16). |
| **3.50 Marginality** | Boundary (inference) | No atom-norm floor, doubly exponential aperture decay, \(\Lambda_{\rm dBN}\ge0\). RH positivity has zero margin in the limit; a fixed-loss estimate cannot carry it, and openness of index zero at \(\zeta\) fails along the backward heat flow. |

Evidence: [optimized boundary](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TransMetzlerYoungOptimization.lean), [Young floor](../../../formal/GaloisForLFunctions/HTGeometry/OptimalYoungDefectFloor.lean), [reference floor](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TransMetzlerReferenceFloor.lean), [three estimates](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/OptimizedTransMetzlerFloor.lean), [shell thresholds](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/ExactHigherShellThresholds.lean), [divisor rows](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/FixedOverlapHasLogarithmicDivisorRows.lean), [nonpolar loss](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/OverlapForcesNewRamanujanTerms.lean), [no uniform floor](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/GrowingOverlapHasNoUniformGramFloor.lean), [coordinates](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/OverlapCoordinates.lean), [Schur reduction](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/APositivePrefixGivesTheExactSchurReduction.lean), [iterated log](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TheFixedProfileReachesAnIteratedLogEndpoint.lean), [schedules reach the index](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheExplicitSchedulesReachTheIndex.lean), [Hasse with heights](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheHassePrincipleWithHeights.lean), [attained depth](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/AttainedDepthIsSeenByAlmostEveryPrime.lean), [zero side](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/ZeroSideStratum.lean), [threshold](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheThresholdIsThePriceOfTheArchimedeanLine.lean).

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
| **14.15 Successor coupling** | Structure closed; sign open | Successor correlations are pure gauge charge [L]; mixed Grams of one source are automatically PSD [L]. |
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
| **14.26 Field and energy** | Open upper bound | Source ceiling missing. |
| **14.27 Coupled counterterm rank** | Closed scoped boundary | Partner-rank costs. |
| **14.28 Counterterm covariance** | Closed classification | Covariant diagonal finite parts are scalar. |
| **14.29 Arithmetic base across primes** | Construction boundary | Ramanujan local factors excluded from Lorentzian closure. |
| **14.30 Zero moments** | Closed identification | Rosati-type pairings. |
| **14.31 Horizon finite part** | Local payment closed | Sharp gap \(2\log2\); over \(\mathbb F_q[T]\) the ceiling is exact [L]. |
| **14.33 Conformal replacement** | Open beyond tested maps | Hecke dilation has factor one. |
| **14.34 Overlap frustration** | Solved (boundary) | Complete positivity where no Metzler gauge exists [L]. |
| **14.35 Adjunction versus Xi** | Fidelity boundary | Adjunction energies are prime-matrix eigenvalues. |
| **14.36 Function-field approximation** | Boundary (inference) | Curves reproduce prime support, not the archimedean continuum. |
| **14.37 Local-to-global by counting** | Closed over \(\mathbb F_q\); open over \(\mathbb Z\) | Stepanov on both parity classes gives index zero; Riemann–Roch ceiling; twist tower. Over \(\mathbb Z\) there is no ceiling and no producer. |
| **14.38 Blind hyperbolicity, selective sign** | Exact boundary | Hodge index at proved scales carries no arithmetic. |
| **14.39 Heat-flow horizon** | Sharpened; near-axis open | \(2/3\) horizon [L]; wave number [L/S]; localized dissipation [K]. |
| **14.40 Over-regular Beurling systems** | Boundary | They share the successor's square-root class [K]. |
| **14.41 Krein–Langer structure** | Boundary [S] | A positive part never pays a pair. |
| **14.42 Tensor amplification** | Boundary | The tensor square of the prime error is WL's mean square. |
| **14.43 Compression** | Boundary [S] | Characteristic-polynomial annihilation; Euler compressors are index-neutral. |
| **14.44 Golden calibration** | Boundary [S] | Tower data do not decide; the lattice does. |
| **14.45 Infinite-symmetry continuation** | Closed; candidate retired | Confinement \(\iff\) lower square-root count [L]. |
| **14.46 Locality is twin-blind** | Theorem [L] | Every pointwise-closed, shift-invariant statement is twin-blind. |
| **14.47 Geometry of the parity twin** | Settled [L] | Geometric only in the Bohr closure. A geometric twin over \(\mathbb Z\) must live in the Bohr compactification (I20). |
| **14.48 Point side versus zero side** | Boundary [S] | Integer auxiliaries see integrality only at \(s\in\mathbb Z\). |
| **14.49 Producer ledger** | Theorem [L] | \(\sum m_x\le\deg P\) over \(\mathbb F_q\); \(\sum m_p\log p\le\log A\) over \(\mathbb Z\). Binomial multiplicity \(\le1\) above \(\sqrt N\). Divisibility information on the odd class is within \(2\sqrt x\log x\) of \(\theta(x)\). |
| **14.50 Frobenius gap** | Boundary (inference) | Over \(\mathbb F_q\), \(x\mapsto x^q\) is additive and multiplicative: it gives Stepanov multiplicity \(\sqrt q\) and makes the twin geometric. \(\mathbb Z\) has no such endomorphism; a substitute must couple addition and multiplication with a fixed budget. |

Evidence: [Stepanov's order](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/StepanovsOrderOverTheFiniteField.lean), [function-field ceiling](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheFunctionFieldCeilingIsExact.lean), [Bohr closure](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheParityTwinIsGeometricOnlyInTheBohrClosure.lean), [linear counts](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/IntegralityProducesLinearCounts.lean), [Chebyshev cap](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/ChebyshevsProducerPassesTheIntegerChebyshevCap.lean), [compressions](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/CompressionsAreReceivers.lean), [twist tower](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheTwistTowerCompletesTheUpperCount.lean), [successor charge](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/SuccessorCorrelationsArePureGaugeCharge.lean), [affine Grams](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/MixedGramsOfAnAffineOrbitAreLinearIncidences.lean), [confinement](../../../formal/GaloisForLFunctions/RHTower/InfiniteSymmetry/ConfinementIsTheSquareRootCount.lean), [dissipation](../../../formal/GaloisForLFunctions/RHTower/Heat/HeatLocalizedEnergyDissipation.lean).

## Sharp obstructions and their positive survivors

| Excluded shortcut | Strongest survivor | Replacement question |
|---|---|---|
| Multiplicative data as a selector | Two-source law; \(\zeta\) is the ground state of its gauge orbit | Gauge charge at \(0\) (Q3) or the pole |
| Pole-mediated positivity as the route to RH | Positivity for \(c<c_*\); Liouville and \(\omega_{11}\) rejected | Additive structure across the first shell (Q1) |
| Tuning the three fixed Trans-Metzler estimates | Optimized Young family to \(c_*>1+10^{-16}\), exact at fixed constants | Sharper constants up to the charge barrier (W01); a structural shell theory beyond it |
| Atom-normalized floors at growing overlap | Montgomery–Vaughan band bound for the bare polynomial | A synthesized-mass floor (I17) |
| Fixed-ratio positivity from finite support | Uniform atomic index bound under finite support | An argument that uses \(\zeta\)'s zero density |
| Gevrey profiles to reach \(\log\log N\) | Denjoy–Carleman profiles at \(L(\log L)^2\log\log L\) | The exact quasi-analytic edge (W04) |
| Interval-stable or finite-aperture information | Precision rigidity; deciding input; window law | Infinitely determined structural input |
| The count as a selector of \(\Lambda\) | Tower positivity selects exactly | Positivity statements for selection |
| One prime tower as a decider | Nyquist; height certificates; two primes carry the index | Two-prime or infinitely-many-tower arguments; unattained depth (I18) |
| Pointwise-closed or local data | Selectivity lives in the pole and Gamma | A count, a carrier, or gauge charge |
| Absolute payment of all prime layers | Uniform finite index except \(k=1\) | The last layer is [FS] |
| Positive-part repair of a finite index | Krein–Langer: separated pairs keep their index | A structural index ceiling (I10) |
| Compression or annihilation as a producer | Annihilation law; Euler compressors are index-neutral | A point-side producer (Q2) |
| Divisibility as a parity producer | Producer ledger; Chebyshev passes the sup-norm cap at linear precision | Multiplicity beyond divisibility (Q2) |
| A vertical shift as the parity twin | The twin lies in the Bohr closure of the shifts | A geometric twin in the Bohr compactification (I20) |
| One quadratic twist completing an upper count over \(\mathbb F_q\) | The twist tower | Its \(\mathbb Z\) analogue |
| Zero-side slack below bandwidth \(3/4\) | Slack conservation; projected credit | A positive \(E_{\rm proj}\) bound (C3) |
| Value moments as a criticality certificate | Mimicry; corrected Cauchy–Schwarz | A displacement-sensitive count at depth \(1/\log T\) |
| One-sided sieve bounds beyond bandwidth one | Exact exchange rate; surplus is gauge charge | A two-sided coalescent estimate (C1/C2) |
| Density estimates as zero exclusion | \(30/13\); DH on \(\sigma\ge5/6\) | A vanishing mechanism |
| Finite support as a sub-Lindelöf target | Finite support \(=\) RH above a height \(\Rightarrow\) LH \(\wedge\) QRH | Treat as LH-level |
| Infinite-symmetry continuation | Exact zero detector; confinement \(=\) lower count | The count itself (Q2) |
| Index-continuity deformation of \(\zeta\) | Index continuous off the discriminant | None at \(\zeta\): \(\Lambda_{\rm dBN}\ge0\) blocks openness; closedness is realization |
| Detection or quantization as an upper bound | Canonical energy; quadratic index price | A virial-type upper estimate |

## Consequences for priorities

- [Q1](obstacles-summary.md#q1) targets 3.42–3.49 and 1.39: the first successor shell as a source.
- [Q2](obstacles-summary.md#q2) targets 1.34, 1.35, 14.37, 14.43, 14.47, 14.49 and 14.50: a producer finer than divisibility.
- [Q3](obstacles-summary.md#q3) targets 1.30, 1.40 and 1.41, and the census budgets: gauge charge at \(0\) beyond the major arcs.
- 1.26, 3.35, 14.39 and 14.41 (finite support) are LH-level and RH-hard at large height; they are not near-term priorities.

No route is declared dead by these priorities. Finite calculations, compositions, integration and intake are [just work](obstacles-summary.md#21-tasks-that-are-just-work).
