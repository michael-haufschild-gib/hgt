# Walls ledger

Status: 30 October 2026, corpus `66f67bc27f`.

**Three core problem families remain:**

- the selective critical sign (Wall 1);
- transfer and exhaustion (Wall 3), now located at one critical curve inside the overlap window;
- independent realization or forcing (Wall 14).

No core wall was crossed. Each wall moved:

- **Wall 3 gained its first growing-resolution rung.** Every fixed conductor packet is positive for \(1\le c\le(\log N)^{1/48}\) [L], and the Gamma reserve survives while \(c^8=o(\log N)\) [L]. The open part is now sharply located:
  - loss-free control of the \(\approx c\) near-degenerate conductors \(m\lesssim c\);
  - the critical curve \(E(c_N)\log N\asymp1\), where margin, Gamma reserve and synthesis error coincide (inference).
- **Wall 1 became a resolution theory at bounded overlap.**
  - Twisted forms are decided by finite Ramanujan packets and have exact thresholds [L].
  - Pole-free twins fall at one bounded overlap [L/Lean]; pole-keeping twins need \(c_0\asymp p^{1/7}\) [L].
  - The zeros read atomic vectors only through Möbius horizons, and single-horizon charges are depth-blind [L]. The \(0\)-specific input RH needs is depth information carried by long windows.
- **Wall 14 lost its Adams hope at the level posed.** Full multiplicity on the Adams fixed locus costs support exactly \(2^{qr}\) [L]: Bézout-sharp, and on characters. Factorial-ratio producers stop at Chebyshev precision \(2\log2\) [L]. The producer problem has moved to a duality step from characters to primes.

Links: [route report](route-obstacles.md) · [summary and next questions](obstacles-summary.md) · [route unification](route-unification-ledger.md) · [scoped no-go catalogue](../rh-killed-routes.md). Evidence comes from corpus searches and Lean statements; no builds were run. [Working log](../../../logs/review-3010-rev2-research-2026-10-30.md).

| Label | Meaning |
|---|---|
| **[L]**, **[S]**, **[K]** | As in the frontier map. |
| **[Lean]** | Statement read; integration not assessed. |
| **[P]** | Paper proof only. |
| **(inference)** | A conclusion of this review. |

## The three families

| Family | Question | Where the input can come from | What would cross it |
|---|---|---|---|
| **Wall 1 — Selective critical sign** | What bounds the actual signed prime/Möbius source, the complete Weil form or a defect at the critical scale, using a property \(\Lambda\) has and its twins lack? | The pole and Gamma (they decide every pole-free twin at bounded overlap); gauge charge through non-ratio lags, read by linear prime sums to fixed moduli; the functional equation and \(\Lambda*1=\log\). RH needs depth information at \(0\), carried only by two-horizon (long-window) directions, at square-root precision. | A \(0\)-specific, depth-sensitive statement: an exponent bound at \(0\), a parity-class count, or positivity past the critical curve. |
| **Wall 3 — Transfer and exhaustion** | Does an estimate survive the needed overlap growth, aperture, rank, conductor and simultaneous limit? | The atomic window: theorem at every fixed \(c\), on fixed packets to \((\log N)^{1/48}\); RH past \(E(c_N)\log N\asymp1\). The near-degenerate conductors \(m\lesssim c\) and the harmonic boundary layer carry the losses. | Loss-free positivity up to the critical curve, and an exact identity at it. |
| **Wall 14 — Realization and forcing** | Which independently built structure produces the inequality? | Over \(\mathbb F_q\), Frobenius couples addition and multiplication. Over \(\mathbb Z\), self-maps cannot; Adams operations vanish Bézout-sharply on characters; Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) is linear. | A character-to-point duality producing counts, a producer with non-periodic valuations, or an index ceiling from ring structure. |

**How the walls interlock.**

- **Global law (Wall 1 = Wall 14 at the endpoint) [S].** Index zero of the Weil kernel is the one-sided count, already the upper count of the odd Liouville class.
- **Window (Wall 3 meets Wall 1).**
  - Fixed overlap uses the pole, Gamma and fixed-modulus linear prime sums; it resolves exactly the summable-defect twists [L].
  - An off-line zero is a pole-keeping, non-summable perturbation. It is invisible at fixed \(c\) and visible only through growing conductors.
- **Criticality (Wall 3).** The margin \(E(c)\) is the aliasing tail; the Gamma reserve and the receiver's synthesis error are the same tail times the archimedean weight \(\log N\) (inference). No estimate with a fixed relative loss crosses the curve where they are equal.
- **Depth (Walls 1 and 3).** Single-horizon charges satisfy \(\|P_a(s)P_a(1-s)\|\le N(\sum|a_d|/d)^2/|s(1-s)|\) throughout the strip [L]. Depth enters only as \((N/M)^{|\operatorname{Re}z|}\) through windows [L].
- **Producer (Wall 14) [L].** One ledger, \(\sum m_p\log p\le\log A\). Divisibility is parity-blind. Adams vanishing costs \(2^{qr}\). Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) is linear, while a Hodge index needs a quadratic Euler characteristic.
- **Point \(0\) (Walls 1 and 14) [L].** Multiplicative, gauge-invariant data prove almost-sure laws and certify nothing below \(3/4\) at \(0\). The Adams operations fix \(0\). Over \(\mathbb F_q[T]\) the trivial point is better than typical; over \(\mathbb Z\) it is never better than typical.

**Organizing identities.**

The complete form and an ordered entry:
\[
\operatorname{Re}W(f,f)=D(f,f)-\mathfrak d(f),\qquad
W(f,g)=-\int_0^\infty\big(e^h-\psi(e^h)-c\big)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g).
\]

Shell repayment at overlap \(c\):
\[
E_m(c)=\frac{2}{M\varphi(m)}\sum_{(a,m)=1}\frac ma\int_{ac/m}^\infty|\hat\varphi(2\pi t)|^2dt ,\qquad \log m+F(c)-B(c)\le E_m(c).
\]

The horizon law, for every atomic vector \(y\), \(a=(\sqrt n\,y_n)*\mu\):
\[
Q(f_y)=\operatorname{Re}\sum_\rho m_\rho\,\hat g(\gamma_\rho)\overline{\hat g(\bar\gamma_\rho)}\,H_a(1-\rho)H_a(\rho),\qquad H_a(s)=\sum_{d\le N}a_dd^{-s}B_{\lfloor N/d\rfloor}(s).
\]

The resolution bottom of a twist \(\lambda\) with summable defect:
\[
\lambda_\lambda(c)=\inf_{\sum\beta_m^2=1}\Big[\sum_m\beta_m^2E_m(c)+2\sum_kd_\lambda(k)k^{-1/2}M(y\cdot y(k\cdot))\Big],\qquad y=\sum\beta_me_m .
\]

The index, the parity law and the exponent:
\[
\kappa(K_\zeta)=\#\{\rho:\operatorname{Re}\rho>\tfrac12\},\qquad
\kappa=0\iff\sum_{\lambda(n)=-1}\frac{e^{-nt}}n\le\tfrac12\Big(\sum_n\frac{e^{-nt}}n+Ct^{1/2-\varepsilon}\Big),\qquad
\theta_\mu(0)=\Theta .
\]

**Strata**, weakest first:

| # | Stratum | Meaning |
|---|---|---|
| 1 | **[open]** | Intermediate. |
| 2 | **[≥QRH]** | Implies a fixed strip \(\Theta<1\). |
| 3 | **[LH]** | Implies Lindelöf. |
| 4 | **[FS]** | Finitely many off-line zeros; implies LH and \(\Theta<1\). |
| 5 | **[RH]** | Equivalent to RH. |
| 6 | **[RH+]** | Stronger than RH. |

## Status changes against the previous ledger

"Solved" means the stated question is answered, never that a route is closed. "Superseded" means a later theorem makes the face moot. "Boundary" means a proved limitation with a positive survivor.

| Face | Change | Current content |
|---|---|---|
| **3.52 The rate problem** | **Partly solved [L]** | Fixed conductor packets positive for \(1\le c\le(\log N)^A\), \(A<1/48\); residual \(c^{10}(\log N/N)^2+c^6/\sqrt{\log N}\). Growing conductors and the complement remain. |
| **3.51 The overlap window** | **Lower endpoint moved [L]** | Theorem at fixed \(c\) and on fixed packets to \((\log N)^{1/48}\); RH past the critical curve. |
| **3.47 Atom-norm degeneration** | **Survivor extended [L]** | The Gamma reserve \((\kappa c^{-7}\log N-bc)\cdot\)mass survives growing overlap while \(c^8=o(\log N)\). |
| **3.53 Profile thresholds** | **Aligned with the critical curve (inference)** | Gevrey and Steklov receivers lie on \(E(c_N)\log N\asymp1\); \(C^2\) lies above it because of trapezoid synthesis. |
| **3.56 Critical scaling** | **Superseded by 3.66** | The conjectured transition now has evidence from three profile classes and an explanation (one Fourier tail). |
| **3.54 Flip thresholds** | **Sharp exponent [L]** | \((p/\log p)^{1/7}\lesssim c_0(\omega_p)\lesssim p^{1/7}\); margin at resolution \(\asymp\log^2p/(p\log(p/c))\). |
| **1.38 Flip selectivity** | **Solved for every finite flip set [L]** | Exact thresholds for every finite set; each twist's sign at fixed \(c\) is a finite packet form. |
| **1.18 Arithmetic gauge selection** | **Extended [L]** | Exact resolution thresholds for every summable twist. |
| **1.41 Major arcs of gauge charge** | **Refined [L]** | Bounded overlap reads shells by linear prime sums in fixed residue classes (additive major arcs). For \(c\le2\) every multiplicative level-\(q\ge3\) average of the shells is zero. |
| **1.46 Twin inequality** | **Upgraded to [L]** | Quadratic Dirichlet twins \(\le(2+\Theta)/6\); a universal floor \(1/2\) forces \(\Theta=1\). |
| **1.47 Fixed-modulus sufficiency** | **Kept; scope sharpened** | Fixed overlap needs only fixed-modulus linear prime sums. Depth needs growing conductors. |
| **14.54 Adams operations** | **Extended to a sharp cost [L]** | Full multiplicity \(r\) on the \(\psi^{q+1}\)-fixed locus forces support \(\ge2^{qr}\); \((\chi(2)^q-1)^r\) is sharp. |
| **14.49 Producer ledger** | **Extended [L]** | Balanced factorial ratios cost \((2\log2-\varepsilon)mn\); the central binomial is optimal. |
| **14.37 Local-to-global by counting** | **Calibration derived [L]** | Möbius degree sums of \(\mathbb F_q[T]\) derived from unique factorization; trivial point better than typical there. |
| **1.48 Pole-free twin selectivity** | **New [L/Lean]** | One profile at one bounded overlap rejects every completely multiplicative \(\pm1\) gauge with bounded harmonic sums. |
| **1.49 Packet decision** | **New [L]** | Twisted forms at fixed \(c\) are decided by finite Ramanujan packets; exact monotone thresholds. |
| **1.50 Short shells** | **New [L]** | For \(c\le2\) no finite gauge subgroup sees the shells. |
| **1.51 Level of distribution of the shells** | **New [L]** | Large sieve over conductors \(\le Q\); the trivial point is one term. |
| **1.52 Charge blindness** | **New [L]** | Single-horizon charges cannot see real parts of zeros. |
| **1.53 Function-field calibration** | **New [L]** | Trivial point better than typical over \(\mathbb F_q[T]\); twin at exponent \(1\). |
| **1.54 The pole decides bounded selectivity** | **New (inference)** | Pole-free twins at bounded \(c\); pole-keeping ones at growing \(c\). |
| **3.57–3.66** | **New [L]/(inference)** | Growing packets; residual; conductor Weyl law; Green coordinates; horizon law; windows; depth-blind packets; frames; the critical curve. |
| **14.57–14.63** | **New [L]/(inference)** | Adams–Bézout cost; jets; factorial precision; affine positivity; successor rigidity; the duality step; Bost–Connes temperature. |

## Wall 1 — Selective critical sign

| Face | Status | Content and remaining obligation |
|---|---|---|
| **1.0 Fixed-strip first rung** | Open [≥QRH]; external claim | Every strip dictionary reads \(\Theta\). Density envelopes never force vanishing. Guth–Maynard and DH \(\sigma\ge5/6\) [L]. External \(7/8\) [E]. |
| **1.1 Critical signed cancellation** | Open [RH] | Lag, Abel, history, series, one-sided \(\psi\), odd-class and first-clock receivers need the signed bound. |
| **1.2 Axis orientation** | Open [RH] | Ward caps, winding and Newton margins detect; extinction missing. |
| **1.3 Complete Weil positivity** | Bounded overlap and fixed packets proved [L]; past the critical curve open [RH] | Every fixed \(c\); every fixed packet to \((\log N)^{1/48}\). |
| **1.4 Arithmetic cone membership** | Open [RH] | Identification is not positivity. |
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
| **1.17 Loss-rate improvement** | Open | A sublinear loss law needs gauge charge or a fixed-budget correspondence. |
| **1.18 Arithmetic gauge selection** | Classified for summable twists [L] | Gap \(2\log2\) shared by \(\omega_p\), \(p\ge11\). Every summable twist has an exact resolution threshold. |
| **1.19 Budget strength** | Boundary | Abel/Mertens saturation is [RH+]. |
| **1.20 Arithmetic-point completion** | Open | Integrality speaks only at integer arguments. |
| **1.21 Source reserve / work ceiling** | Open [RH] | Cofinal work \(\le2\). |
| **1.22 Finite versus zero exceptions** | Exact boundary | Finite \(\mathcal E_{\rm crit}\iff\) [FS]; one quantum \(\iff\) RH. |
| **1.23 Ordered Chebyshev identity** | Identity; payment open | Separated couplings are the signed prime error. |
| **1.24 Selectivity** | Theorem | Selection on atomic families and towers; twin-blind positivity cannot reach RH-complete families. |
| **1.25 Parity form** | Theorem [S] | The deciding-input theorem rejects Liouville. |
| **1.26 Finite-support stratum** | Exact [FS] | RH above a height; implies LH and \(\Theta<1\). |
| **1.27 Critical-line census** | Priced; dichotomy [K] | \(E(1/9)\le4\Rightarrow70\%\); every failure lies in near-line simple off-line zeros. |
| **1.28 Value-moment mimicry** | Closed [L] | Reflected pairs mimic critical moments. |
| **1.29 Precision rigidity** | Theorem [L/S] | \(\lambda\) and \(\lambda+\varepsilon n^{-\eta}\) are never both tower-positive. |
| **1.30 Census parity** | Boundary | The coalescent surplus is pure gauge charge with budget zero almost surely. |
| **1.31 Shallow energy constant** | Order closed; constant open | \(70\%\) needs \(\le\tfrac3{20}N\). |
| **1.32 Prime-free existence form** | Closed receiver | The certificate weight is \(\Lambda\). |
| **1.33 Zero-side slack** | Boundary [K] | \(E_{\rm proj}\le2\operatorname{tr}Q_-\le\) slack; a positive lower bound is open. |
| **1.34 Global law** | Exact [S] | Index zero \(\iff\) one-sided count \(\iff\) odd-class upper count. |
| **1.35 Integrality** | Exact; certificate open | Integrality exponent \(\Theta\); divisibility cannot select parity [L]. |
| **1.36 Precision classes** | Theorem | Count stabilizer \(\mathcal Q\); tower stabilizer trivial; finite aperture cannot decide; random signs satisfy the count. |
| **1.37 Inversion precision** | Boundary [L] | Chebyshev ledger; monotone inversion at Mertens precision. |
| **1.38 Flip selectivity** | Exact for finite flip sets [L] | \(c_0(\omega_p)\asymp p^{1/7}\) up to \(\log p\); no fixed \(c\) sees all flips. |
| **1.39 Two-source law** | Theorem [L] | Twin-blind closure; diamagnetism; non-ratio lags. |
| **1.40 Point-\(0\) typicality** | Exact [L] | Typical exponent \(1/2\); \(\theta_\mu(0)=\Theta\ge1/2\); RH \(\iff\) equality. |
| **1.41 Major arcs of gauge charge** | Theorem [L]; refined | Level-\(q\) Dirichlet averages keep shells with \(q\mid j\). Bounded overlap reads shells through Ramanujan weights in fixed residue classes. |
| **1.42 Gauge non-invariance** | Theorem [L] | Gauge-invariant certificates \(\ge3/4\) at \(0\); finitely determined \(\ge1\). |
| **1.43 Coherence principle** | Theorem [L] | Nonnegative statistics are maximal at \(0\); excess = pole. |
| **1.44 Antipode** | Theorem [L] | \(S_N(\ell)+S_N(0)=2\psi(\sqrt N)\). |
| **1.45 Special locus** | Theorem [L] | Dirichlet points read GRH, typical on average; constant source exponent \(0\) or \(1\). |
| **1.46 Twin inequality** | Theorem [L] | \(\exp_\mu(x+\ell)\le(1+2\exp_1(x)+\exp_\mu(2x)/2)/3\); quadratic twins \(\le(2+\Theta)/6\). |
| **1.47 Fixed-modulus sufficiency** | Inference from [L] | Fixed overlap needs only linear prime sums to fixed moduli; depth needs growing conductors. |
| **1.48 Pole-free twin selectivity** | Theorem [L/Lean] | One profile at one bounded overlap above its Robin–Euler ratio rejects the Liouville twin and every cofinite flip. |
| **1.49 Packet decision** | Theorem [L] | \(W_\lambda\) at fixed \(c\) has the sign of a finite Ramanujan-packet form; complement costs \(\ge T\). |
| **1.50 Short shells** | Theorem [L] | \(c\le2\): shells \(|n-km|\le2\), every level-\(q\ge3\) average zero; sign is a property of \(0\) alone. |
| **1.51 Level of distribution** | Theorem [L] | \(\sum_{q\le Q}|P|\le\|g\|_1\|a\|_1(N+Q^2)\|x\|^2\); says nothing about one point. |
| **1.52 Charge blindness** | Theorem [L] | Single-horizon charge \(\le N(\sum|a_d|/d)^2/|s(1-s)|\); \(\operatorname{Re}1/(\rho(1-\rho))>0\) on or off the line. |
| **1.53 Function-field calibration** | Theorem [L] | \(\mathbb F_q[T]\): Möbius sums \(1-q\), exponent \(0\) at the trivial point. |
| **1.54 The pole decides bounded selectivity** | Inference from [L] | Pole-free twins: bounded \(c\). Pole-keeping twins: \(c\) growing with distance from \(0\). An off-line zero is pole-keeping and non-summable. |

Evidence: [packets decide](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ATwistedCompleteWeilMatrixIsDecidedByItsRamanujanPackets.lean), [exact threshold](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheOverlapThatResolvesATwistIsAnExactThreshold.lean), [flip conductors](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFlipThresholdIsSetByTheConductorsOfThePrime.lean), [finite flip sets](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/EveryFiniteFlipSetHasAnExactResolutionThreshold.lean), [cofinite flips](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/FixedOverlapPositivityIsSelectiveAgainstEveryCofiniteFlip.lean), [pole-free twins](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/EveryPoleFreeSignTwinBreaksAboveTheRobinEulerRatio.lean), [short shells](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheShortShellsHaveNoConductor.lean), [level 1/2](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheShellsHaveLevelOfDistributionOneHalf.lean), [charge blindness](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheHorizonChargeIsBlindToTheRealPartsOfTheZeros.lean), [function field](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheFunctionFieldCalibrationIsDerived.lean), [twin inequality](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheLiouvilleTwinInequality.lean), [coherence](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheCoherencePrinciple.lean), [not gauge invariant](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheExponentIsNotGaugeInvariant.lean), [parity form](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheParityFormOfTheGlobalLaw.lean).

## Wall 3 — Transfer, norms and exhaustion

| Face | Status | Content and remaining obligation |
|---|---|---|
| **3.1 Information retained** | Boundary | Magnitudes, complete-period covariances and collided counts can lose orientation. |
| **3.2 Aperture escape** | Open | Aperture \(A\) reads only \(n\le e^{2A}\). |
| **3.3 Norms and completions** | Scoped graph control closed | No global norm equivalence. |
| **3.4 Shared resources** | Open | A reserve cannot be spent on each block separately. |
| **3.5 Endpoint logarithms** | Open | Pole cancellation leaves Dini/log remainders. |
| **3.6 Moving horizons** | Open | No free below-half-damping interchange. |
| **3.7 Damping topology** | Open | Half-damped boundedness gives no sub-half trace-ideal control. |
| **3.8 Multiplicity and index** | Clarified | Index counts distinct right zeros; collisions add multiplicity excess. |
| **3.9 Observation cost** | Open | Finite-window coercivity has an explicit horizon cost. |
| **3.10 Invertible filters** | Boundary | Repair needs non-unit arithmetic content. |
| **3.11 Coupled quantifiers** | Open | Degree, rank, height, time, damping, overlap and support limits do not commute. |
| **3.12 Residual reconstruction** | Open | Coordinate maps need not have bounded inverses. |
| **3.13 Joint orientation** | Open | One-channel signs do not orient the joint form. |
| **3.14 Averages to selected zeros** | Open | Proportions, slack and large-value counts allow exceptions. |
| **3.15 Escape states** | Open [RH] | Positive gauge mass of every escape state; the Möbius escape state is blind to zeros [L]. |
| **3.16 Prime to spectral sign** | Partly closed | At fixed overlap and on fixed packets the prime-side margins reach the full form with poles intact [L]. Growing conductors open. |
| **3.17 Archimedean-line horizon** | Boundary [L] | Below the threshold the line sees the whole torus; beyond it, near-incidence is gauge charge. |
| **3.18 Localization** | Boundary | Positivity constrains a fibre only where the carrier localizes. |
| **3.19 Conductor versus forcing** | Open | No common aperture range. |
| **3.20 Collided-form norm** | Closed locally | Log-weighted Fourier norm at fixed aperture. |
| **3.21 Lattice to continuum** | Open | Lattice payment must keep the continuum remainder. |
| **3.22 Computed detection** | Closed diagnostic | Detection is not exclusion. |
| **3.23 Local to global Hodge** | Open | Hyperbolicity is not additive. |
| **3.24 Horizon regulator** | Closed construction | Counterterms explicit. |
| **3.25 Narrow spacing payment** | Closed | Self-energy and prime defect pay at fixed fractions. |
| **3.26 Complete overlap transfer** | Every fixed \(c\) closed [L]; fixed packets at growing \(c\) closed [L] | Full matrix at growing \(c\) open. |
| **3.27 Complete residual** | Exact boundary | Residual radical = Weil radical; complete cells capture every finite index. |
| **3.28 All-prime/class exhaustion** | Bulk open | Fixed packets realized; growing conductors open. |
| **3.29 Valuation versus residue classes** | Exact boundary | Residue counterterm rank one. |
| **3.30 Balanced Haar completion** | Details closed | Gamma pays details; prime edges keep a Gamma reserve. |
| **3.31 Dyadic self-similarity** | Exact; RH | One prime's towers at every generator size. |
| **3.32 Cross-level coupling** | Three parts closed | The prime part is 3.31. |
| **3.33 Renormalization topology** | Boundary | No exponential amplitude renormalization gives uniform graph control. |
| **3.34 Gamma boundary rigidity** | Closed | Norm \(\pi/2\), no maximizer. |
| **3.35 Uniform finite-index chain** | Closed except \(k=1\) [FS] | Prime–polar cancellation has an \(e^R\) loss. |
| **3.36 Orbit approximation** | Boundary | One Haar orbit is noncompact. |
| **3.37 Quasi-analytic boundary** | Moved [K] | Steklov receiver at \(L(\log L)^2\log\log L\); no compact Gevrey-\(\le1\) profile. |
| **3.38 Conductor spectrum** | Solved at every fixed \(c\) [L] | Low spectrum = completed conductor spectrum; pole ground state; bottom \(\to E(c)\). |
| **3.39 Index topology** | Boundary [S] | Continuous off the discriminant. |
| **3.40 Aliasing and Nyquist** | Exact and effective [L/S] | Heights, certifying towers, carriers. |
| **3.41 Locality** | Boundary [L] | Attained depth seen by almost every prime; unattained depth open. |
| **3.43 Zero-side fixed-ratio stratum** | Boundary [K] | A tempered single-pair model is negative at every \(c\); \(\zeta\)'s fixed-\(c\) positivity uses its zero density through Gamma. |
| **3.44 Certified-method boundary** | Superseded | Pertains to the plateau's Young family only. |
| **3.45 Charge barrier** | Superseded | Pertains to the plateau reference method only. |
| **3.46 Successor shells** | Solved [L] | Exact repayment by Poisson summation. |
| **3.47 Atom-norm degeneration** | Boundary [K]; survivor extended [L] | No uniform coefficient floor; the Gamma reserve survives while \(c^8=o(\log N)\). |
| **3.48 Length–height coordinate** | Exact [K] | Overlap \(X/T\), bandwidth \(\log X/\log T\). |
| **3.49 Prefix Schur reduction** | Exact [K]; payment [L] | \(W\ge0\iff D-B^*A^{-1}B\ge0\); \(D-20B^*B\le S\le D\). |
| **3.50 Marginality** | Identity [L] | \(E(c)\to0\) by Stirling; tilted spline \(E\asymp c^{-7}\). |
| **3.51 The overlap window** | Lower endpoint moved [L] | Fixed \(c\); fixed packets to \((\log N)^{1/48}\); RH past the critical curve. |
| **3.52 The rate problem** | Partly solved [L]; open for the full matrix | Residual polynomial in \(c\); arithmetic at every inverse-log rate; harmonic boundary rows give \(1/\sqrt{\log N}\). Siegel–Walfisz absent. |
| **3.53 Profile thresholds** | Exact receivers [L/K]; aligned (inference) | Gevrey and Steklov on the critical curve; \(C^2\) above it. |
| **3.54 Flip thresholds** | Theorem [L] | \((p/\log p)^{1/7}\lesssim c_0(\omega_p)\lesssim p^{1/7}\). |
| **3.55 Single-profile window** | Inference | A tilted Steklov profile should carry fixed-\(c\) positivity and the iterated-log receiver. |
| **3.56 Critical scaling** | Superseded by 3.66 | — |
| **3.57 Growing-overlap packets** | Theorem [L]; variant [S] | Every fixed conductor set positive for \(1\le c\le(\log N)^{A}\), \(A<1/48\); CAF \(\alpha<1/40\) [S]. |
| **3.58 Polynomial residual** | Theorem [L] | Eight-term residual \(C_m[c^{10}(\log N/N)^2+c^6/\sqrt{\log N}]\); \(C_m\) not explicit in \(m\). |
| **3.59 Growing Gamma reserve** | Theorem [L] | \((\kappa c^{-7}\log N-bc)\cdot\)mass. |
| **3.60 Arithmetic Weyl law** | Theorem [L]; ratio limit [S] | \(E_m(c)=\log m+O_c(1)\); heat threshold \(\beta=1\); Fermi level at \(m\approx c\) (inference). |
| **3.61 Green coordinates** | Theorem [L] | Inverse cost \(1/E_1\); finite readings control \(W^{-1}\) at fixed \(c\); \(\sum E_m^{-k}=\infty\). |
| **3.62 Horizon law** | Theorem [L] | Zeros see every atomic vector through Möbius horizon boundaries. |
| **3.63 Windows are box tests** | Theorem [L] | Windowed aperture modes: cross modulus \(N^\kappa M^\kappa(N/M)^{\pm\operatorname{Re}z}\). |
| **3.64 Depth-blind packets** | Inference from [L] | Fixed conductors have window ratio \(\le m\); depth requires \(m\to\infty\). |
| **3.65 Ramanujan frames** | Theorem [L/K] | Harmonic Gram \(\ge(\log(N+1)-2\log Q)\sum d_m^2\); annular frames \(1/4,5/4\) [K]. |
| **3.66 The critical curve** | Conjecture (inference from [L/K]) | Margin = aliasing tail; synthesis error energy = tail \(\times\log N\); Gamma reserve \(\approx\) tail \(\times\log N\). RH receiver on \(E(c_N)\log N\to0\) for every profile; unconditional range \(E(c_N)\log N\to\infty\). |

Evidence: [fixed packets](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/FixedConductorPacketsStayPositiveAtGrowingOverlap.lean), [quasimodes](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/CompletedConductorQuasimodesHavePolynomialError.lean), [polynomial residual](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/WeilPolynomialResidual.lean), [prime boundary](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/PrimeBoundaryErrorsHavePolynomialHarmonicBounds.lean), [Gamma reserve](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheGammaReserveSurvivesGrowingOverlap.lean), [heat threshold](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/ConductorHeatThreshold.lean), [Green tail](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/WeilGreenTail.lean), [Möbius horizons](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheZerosSeeEveryAtomicVectorThroughItsMobiusHorizons.lean), [windows](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/AWindowedApertureModeIsAnExponentialBoxTest.lean), [frames](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/GrowingRamanujanFamiliesHaveASquareRootHorizon.lean), [second-order synthesis](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheSecondOrderSynthesis.lean), [Gevrey](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheDenjoyCarlemanProfiles.lean), [Steklov](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TheFixedProfileReachesAnIteratedLogEndpoint.lean), [log overlap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis.lean), [zero side](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/ZeroSideStratum.lean).

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
| **14.15 Successor coupling** | Structure closed; sign open | Successor correlations are pure gauge charge; mixed Grams of one source are PSD. |
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
| **14.31 Horizon finite part** | Local payment closed | Sharp gap \(2\log2\); over \(\mathbb F_q[T]\) the ceiling is exact. |
| **14.33 Conformal replacement** | Open beyond tested maps | Hecke dilation has factor one. |
| **14.34 Overlap frustration** | Solved (boundary) | Complete positivity where no Metzler gauge exists. |
| **14.35 Adjunction versus Xi** | Fidelity boundary | Adjunction energies are prime-matrix eigenvalues; at fixed overlap they are the completed conductor energies [L]. |
| **14.36 Function-field approximation** | Boundary (inference) | Curves reproduce prime support, not the archimedean continuum. |
| **14.37 Local-to-global by counting** | Closed over \(\mathbb F_q\); open over \(\mathbb Z\) | Stepanov on both parity classes gives index zero over \(\mathbb F_q\); calibration derived from unique factorization [L]. Over \(\mathbb Z\), Bézout and Riemann–Roch are exact and linear [K/L]. |
| **14.38 Blind hyperbolicity, selective sign** | Exact boundary | Hodge index at proved scales carries no arithmetic. |
| **14.39 Heat-flow horizon** | Near-axis open | \(2/3\) horizon [L]; wave number [L/S]; localized dissipation [K]. |
| **14.40 Over-regular Beurling systems** | Boundary | They share the successor's square-root class [K]. |
| **14.41 Krein–Langer structure** | Boundary [S] | A positive part never pays a pair. |
| **14.42 Tensor amplification** | Boundary | The tensor square of the prime error is WL's mean square. |
| **14.43 Compression** | Boundary [S] | Characteristic-polynomial annihilation; Euler compressors are index-neutral. |
| **14.44 Golden calibration** | Boundary [S] | Tower data do not decide; the lattice does. |
| **14.45 Infinite-symmetry continuation** | Closed; retired | Confinement \(\iff\) lower count [L]. |
| **14.46 Locality is twin-blind** | Theorem [L] | Every pointwise-closed shift-invariant statement is twin-blind. |
| **14.47 Geometry of the parity twin** | Settled [L] | Geometric only in the Bohr closure. |
| **14.48 Point side versus zero side** | Boundary [S] | Integer auxiliaries see integrality only at \(s\in\mathbb Z\). |
| **14.49 Producer ledger** | Theorem [L] | \(\sum m_p\log p\le\log A\); binomials \(\le1\) above \(\sqrt N\); factorial ratios Chebyshev-precise at \(2\log2\). |
| **14.50 Frobenius gap** | Theorem [L] | Bounded-defect ring endomorphisms of \(\mathbb N\) are trivial. |
| **14.51 Bézout and Riemann–Roch** | Theorem [K/L] | Exact and linear in \(e^{\deg}\). Over \(\mathbb F_q[T]\) places of one degree share a progression; over \(\mathbb Z\) each prime costs its own. |
| **14.52 Approximate vanishing** | Theorem [L] | Integer auxiliaries: small = divisible. |
| **14.53 Twist tower over \(\mathbb Z\)** | Theorem [L] | Collapses to level \(0\). |
| **14.54 Adams operations** | Theorem [L] | \(\psi^q\)-fixed = \((q-1)\)-torsion twists; \(\psi^2\) fixes only \(0\). |
| **14.55 Polar index** | Theorem [L] | Index of curve data = number of right pole classes. |
| **14.56 Affine-invariant kernels** | Theorem [L] | Three constants; the successor must enter as a boundary. |
| **14.57 Adams–Bézout cost** | Theorem [L] | Full multiplicity \(r\) on the \(\psi^{q+1}\)-fixed locus forces support \(\ge2^{qr}\); \((\chi(2)^q-1)^r\) sharp. Torsion grids read valuations mod \(q\); first collision at \(2^q\). |
| **14.58 Jets** | Theorem [L] | Vertical jets miss transverse directions (transcendental coefficients); algebraic first jets are faithful; two-prime log monomials independent of fixed degree. |
| **14.59 Factorial-ratio precision** | Theorem [L] | Valuations periodic in \(n\bmod p\); precision \(\ge2\log2\); square-root precision needs non-periodic valuations. |
| **14.60 Affine positivity** | Theorem [L] | Positive affine-invariant forms are \(c\,\delta_0+d\,\)Haar; index \(\le1\) via the pole. |
| **14.61 Successor rigidity** | Theorem [L] | Successor defect \(\delta_N\) controls \(|\chi(n)-1|\le2k\delta_N\) for \(n\le\min(N,2^k)\); zero defect fixes exactly the primes \(\le N\). |
| **14.62 The duality step** | Open (inference) | Adams vanishing acts on characters, Stepanov counts points. A producer must convert character vanishing into a prime count; the available converter is the explicit formula itself. |
| **14.63 Bost–Connes temperature** | Theorem [L] | Temperature \(\beta\) forces Hecke exponent \(\beta/2\); \(\beta=1\) is the critical line. The conductor heat threshold is \(\beta=1\) (inference link). |

Evidence: [Adams multiplicity](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/AdamsMultiplicityResolution.lean), [torsion boundary](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/TorsionMultiplicityBoundary.lean), [vertical jets](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/VerticalJetsMissTransverseDirections.lean), [first jets](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/AlgebraicVerticalFirstJets.lean), [successor rigidity](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/DyadicSuccessorRigidity.lean), [Chebyshev precision](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/FactorialRatiosHaveChebyshevPrecision.lean), [affine positivity](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/AffinePositivityIsThePoleAndHaar.lean), [Adams](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheAdamsOperations.lean), [ring endomorphisms](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/ApproximateRingEndomorphisms.lean), [Bézout](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheBezoutTheoremOfTheMultiplicativeGroup.lean), [Riemann–Roch](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheRiemannRochTheoremOfTheMultiplicativeGroup.lean), [small auxiliaries](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/SmallIntegerAuxiliariesAreDivisible.lean), [Bost–Connes](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheBostConnesTemperatureIsTheHeckeExponent.lean), [polar index](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/ThePolarDivisorCountsTheIndex.lean), [Stepanov](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/StepanovsOrderOverTheFiniteField.lean).

## Sharp obstructions and their positive survivors

| Excluded shortcut | Strongest survivor | Replacement question |
|---|---|---|
| Multiplicative or gauge-invariant data as a selector | No certificate below \(3/4\); coherence; antipode | A \(0\)-specific, depth-sensitive input |
| Single-horizon charges as depth detectors | Exact horizon law; pole charge positive for every zero | Two-horizon (window) identities (Q2) |
| Fixed-overlap positivity as RH | Theorem at every fixed \(c\); margin \(E(c)\) | The critical curve (Q1) |
| Fixed packets at growing overlap as RH | Positive to \((\log N)^{1/48}\); depth-blind | Growing conductors \(m\lesssim c\) |
| Estimates with fixed relative loss across the window | Margin, reserve, aliasing are one tail | An identity at \(E\log N\asymp1\) (Q2) |
| One fixed overlap against every flip | Exact thresholds \(c_0\asymp p^{1/7}\) | Uniform selectivity along a schedule |
| Fixed overlap against off-line zeros | Exact resolution of summable twists | Resolution of non-summable, pole-keeping perturbations (Q3) |
| Separated reference continued past touching | Shells repay exactly by Poisson | Uniformity in \(c\) and conductor |
| Trapezoid synthesis for \(C^2\) profiles | Receiver at \((\log N)^{1/4}\) | Profile-adapted synthesis at \((\log N)^{1/7}\) |
| Gevrey profiles at \(\log\log N\) | Steklov at \(L(\log L)^2\log\log L\) | The exact quasi-analytic edge; tilted Steklov |
| Interval-stable or finite-aperture information | Precision rigidity; window law | Infinitely determined input |
| The count as a selector of \(\Lambda\) | Tower positivity selects exactly | Positivity statements for selection |
| One prime tower | Nyquist; height certificates | Two primes or fine towers; unattained depth |
| Absolute payment of all prime layers | Finite index except \(k=1\) | The last layer is [FS] |
| Positive-part repair of finite index | Separated pairs keep index | A structural index ceiling |
| Compression as a producer | Annihilation law | A point-side producer |
| Divisibility, binomials, factorial ratios as parity producers | Ledger; precision \(2\log2\) | Non-periodic valuations (I8) |
| Adams operations as cheap Frobenius vanishing | Exact cost \(2^{qr}\), sharp | The character-to-point duality step (14.62) |
| Self-maps of \(\mathbb Z\) as Frobenius | Classification; Adams operations on \(G\) | A producer acting on characters and coupled to addition |
| "Small" auxiliaries instead of vanishing ones | Small = divisible | Non-integral or archimedean auxiliaries |
| A vertical shift as the parity twin | The twin lies in the Bohr closure | A geometric twin there |
| Zero-side slack below bandwidth \(3/4\) | Slack conservation; projected credit | A positive \(E_{\rm proj}\) bound |
| Value moments as certificates | Mimicry | A displacement-sensitive count |
| One-sided sieve bounds beyond bandwidth one | Exact exchange rate | A two-sided coalescent estimate |
| Density estimates as exclusion | \(30/13\); DH \(\sigma\ge5/6\) | A vanishing mechanism |
| Level of distribution at one point | Large sieve on average | Individual-point (Siegel–Walfisz-type) input |
| Finite support as a sub-Lindelöf target | Finite support \(\Rightarrow\) LH \(\wedge\) QRH | Treat as LH-level |
| Index-continuity deformation of \(\zeta\) | Continuity off the discriminant | None: \(\Lambda_{\rm dBN}\ge0\) blocks openness |
| Kernels invariant under the whole affine semigroup | Pole \(+\) Haar | Successor as a boundary term |

## Consequences for priorities

- [Q1](obstacles-summary.md#q1) targets 3.51–3.53, 3.57–3.60 and 3.66: place every receiver on the critical curve and push unconditional positivity toward it.
- [Q2](obstacles-summary.md#q2) targets 3.62–3.66 and 1.52: the identity at the critical curve on depth-sensitive directions.
- [Q3](obstacles-summary.md#q3) targets 1.49, 1.54, 3.43 and 3.64: the resolution of an off-line zero and zero-free regions from positivity.
- 14.62 (the duality step) is the next producer question; 1.26, 3.35, 14.39 and 14.41 (finite support) are LH-level and not near-term.

No route is declared dead by these priorities. Finite calculations, compositions, quantifications, formalizations and integration are [just work](obstacles-summary.md#21-tasks-that-are-just-work).
