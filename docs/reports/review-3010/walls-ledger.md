# Walls ledger

Status: 30 October 2026, corpus `a0e8154924` plus working tree.

**Three core problem families remain:**

- the selective critical sign (Wall 1);
- transfer and exhaustion (Wall 3), now located inside one explicit overlap window;
- independent realization or forcing (Wall 14).

No core wall was crossed. One major face was solved, and the remaining content of each wall is sharper:

- **Wall 3 lost its bounded-overlap part.** The complete Weil matrix is positive at every fixed overlap, for every profile without real Fourier zeros [L].
  - The successor shells repay the nonpolar \(-\log c\) loss exactly, by Poisson summation on the successor lattice.
  - The margin is a positive Fourier tail \(E(c)\) that tends to \(0\) by Stirling's formula.
  - The open part is the rate at which \(c_N\) may grow: RH is the same positivity at \(c_N^4\gg\log N\).
- **Wall 1's gauge-charge source is now in use, at its major arcs only.** Bounded-overlap positivity reads the shells through Ramanujan sums, i.e. through finite gauge subgroups, controlled by fixed-modulus PNT in progressions. The point \(0\) is still uncertified beyond them.
  - RH is an exponent statement at \(0\): the typical Möbius exponent is exactly \(1/2\), and \(0\) is never better than typical.
  - No gauge-invariant certificate gets below \(3/4\) [L].
- **Wall 14 is sharper.**
  - \(\mathbb Z\) has no Frobenius substitute among its self-maps [L].
  - Bézout and Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) are exact but linear.
  - Approximate vanishing of integer auxiliaries is exact divisibility.
  - The Frobenius equation \(x^q=x\) lives on the gauge torus, as the fixed points of the Adams operations.

Links: [route report](route-obstacles.md) · [summary and next questions](obstacles-summary.md) · [route unification](route-unification-ledger.md) · [scoped no-go catalogue](../rh-killed-routes.md). Evidence comes from corpus searches and Lean statements; no builds were run.

| Label | Meaning |
|---|---|
| **[L]**, **[S]**, **[K]** | As in the frontier map. |
| **[Lean]** | Statement read; integration not assessed. |
| **[P]** | Paper proof only; not audited here. |
| **(inference)** | A conclusion of this review. |

[Working log](../../../logs/review-3010-research-2026-10-30.md).

## The three families

| Family | Question | Where the input can come from | What would cross it |
|---|---|---|---|
| **Wall 1 — Selective critical sign** | What bounds the actual signed prime/Möbius source, the complete Weil form or a defect at the critical scale, using a property \(\Lambda\) has and its twins lack? | The pole and Gamma; gauge charge through non-ratio lags. Major arcs suffice at bounded overlap. RH needs information that is not gauge-invariant and not finitely determined at the point \(0\) [L]. | A square-root-precise, \(0\)-specific statement: an exponent bound at \(0\), a parity-class count, or positivity on an RH-complete schedule. |
| **Wall 3 — Transfer and exhaustion** | Does an estimate survive the needed overlap growth, aperture, rank, conductor and simultaneous limit? | For atomic families, the window between fixed \(c\) (theorem) and \(c_N^4\gg\log N\) (RH). The margin \(E(c_N)\) decays; errors must be controlled uniformly in \(c\) and in conductors \(m\lesssim c\). | Positivity with an error rate below \(E(c_N)\) along a schedule past the synthesis threshold, or an exact identity at zero margin. |
| **Wall 14 — Realization and forcing** | Which independently built structure produces the inequality? | Over \(\mathbb F_q\), Frobenius couples addition and multiplication. Over \(\mathbb Z\), self-maps cannot; the Adams operations of the gauge torus satisfy \(x^q=x\) on characters. | A producer that vanishes finer than divisibility, a geometric parity twin, or an index ceiling from ring structure. |

**How the walls interlock.**

- **Global law (Wall 1 = Wall 14 at the endpoint) [S].** Index zero of the Weil kernel is the one-sided count, already the upper count of the odd Liouville class.
- **Window (Wall 3 meets Wall 1).**
  - Fixed overlap uses the pole, Gamma and the shells' major arcs. Selectivity there is per twin: each flip at its own \(c_0(p)\), and no fixed \(c\) rejects every flip [L].
  - RH requires \(c_N\to\infty\), the same growth that uniform selectivity requires.
- **Marginality is an identity (Wall 3).** \(E(c)=\frac2M\sum_k\frac1k\int_{kc}^\infty|\hat\varphi(2\pi t)|^2dt\to0\) [L]. No estimate with a fixed loss survives the limit. The obstruction is now quantitative: the margin against the error rate.
- **Producer (Wall 14) [L].** One ledger, \(\sum m_p\log p\le\log A\). Divisibility is parity-blind. Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) is linear, while a Hodge index needs a quadratic Euler characteristic.
- **Point \(0\) (Walls 1 and 14) [L].** Multiplicative, gauge-invariant data prove almost-sure laws and certify nothing below \(3/4\) at \(0\). The Adams operations fix \(0\), so a producer built from them must also use additive structure.

**Organizing identities.**

The complete form and an ordered entry:
\[
\operatorname{Re}W(f,f)=D(f,f)-\mathfrak d(f),\qquad
W(f,g)=-\int_0^\infty\big(e^h-\psi(e^h)-c\big)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g).
\]

Shell repayment at overlap \(c\) (Ramanujan weights, Möbius inversion, Poisson):
\[
E_m(c)=E^{\rm ref}_m(c)-\frac{2}{M\varphi(m)}\sum_{1\le h<c}c_m(h)\int_{h/c}^1\frac{G(u)}u\,du
=\frac{2}{M\varphi(m)}\sum_{(a,m)=1}\frac ma\int_{ac/m}^\infty|\hat\varphi(2\pi t)|^2dt .
\]

The index and the parity form of the global law:
\[
\kappa(K_\zeta)=\#\{\rho:\operatorname{Re}\rho>\tfrac12\},\qquad
\kappa=0\iff\sum_{\lambda(n)=-1}\frac{e^{-nt}}n\le\tfrac12\Big(\sum_n\frac{e^{-nt}}n+Ct^{1/2-\varepsilon}\Big).
\]

The exponent at the trivial point, and Riemann–Roch for \(\mathbb G_m(\mathbb Q)\):
\[
\theta_\mu(0)=\Theta,\qquad \theta_\mu(x)=\tfrac12\ \text{Haar-a.e.},\qquad h^0(N,m)=\Big\lfloor N\Big/\prod p^{m_p}\Big\rfloor .
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
| **3.46 Successor shells and nonpolar loss** | **Solved [L]** | Shells \(n=km+h\) enter with weights \(c_m(h)\). Möbius inversion and Poisson summation repay \(-\log c\) exactly. Every completed conductor energy is a positive Fourier integral. |
| **3.26 Complete overlap transfer** | **Bounded part solved [L/K]** | Positive at every fixed \(c\) for profiles without real Fourier zeros [L]; uniform on \(0<c\le K\) for the tilted spline [K]. |
| **3.38 Separated-regime spectrum** | **Extended to every overlap [L]** | Low spectrum = completed conductor spectrum; pole ground state; bottom \(\to E(c)\). |
| **3.44 Certified-method boundary** | **Superseded** | \(c_*\) bounds only the plateau's Young family. Tilted profiles are positive at every \(c\). |
| **3.45 Charge barrier** | **Superseded** | The pole-charge restriction belongs to the plateau reference method, not to complete positivity. |
| **3.50 Marginality** | **Proved as an identity [L]** | \(E(c)\to0\) is Stirling; the margin is exact and decays (\(\ge C/c^7\) for the tilted spline [K]). |
| **3.42 Overlap growth** | **Restated as 3.51–3.56** | The window, its rate problem and its thresholds. |
| **3.47 Atom-norm degeneration** | **Boundary kept; survivor extended** | Still no uniform coefficient floor as \(c\to\infty\) [K]. At fixed \(c\) the Montgomery–Vaughan band mass becomes a Gamma reserve for every profile without real Fourier zeros [L]. |
| **3.37 Quasi-analytic boundary** | **Upgraded to [K]** | Steklov profile: RH at \(L(\log L)^2\log\log L\). |
| **1.3 Complete Weil positivity** | **Bounded overlap proved [L]** | RH-complete schedules remain [RH]. |
| **1.38 Flip selectivity** | **Solved per prime [L]; uniform version impossible at fixed \(c\) [L]** | \(c_0(p)<\infty\) for every \(p\); thresholds \(\to\infty\) with \(p\). |
| **1.40 Point-\(0\) typicality** | **Exact [L]** | Typical exponent exactly \(1/2\); \(0\) never better than typical; RH \(\iff\) equality. |
| **1.41 Major arcs of gauge charge** | **Theorem [L]; used [L]** | Level-\(q\) averaging keeps the shells with \(q\mid j\). Bounded-overlap positivity needs only these major arcs. |
| **14.50 Frobenius gap** | **Theorem [L]** | Bounded-defect ring endomorphisms of \(\mathbb N\) are the identity or unit-ball gauge points. |
| **14.37 Local-to-global by counting** | **Extended [K/L]** | Bézout and Riemann–Roch for \(\mathbb G_m(\mathbb Q)\), exact and linear. |
| **14.49 Producer ledger** | **Extended [L]** | Factorial ratios have bounded multiplicity above \(\sqrt{\text{length}}\). Approximate vanishing is divisibility for integer auxiliaries. |
| **14.47 Geometry of the parity twin** | **Extended [L]** | The Adams operations give \(x^q=x\) a home on characters; \(\psi^2\) fixes only \(0\). |
| **1.42 Gauge non-invariance of the exponent** | **New [L]** | No gauge-invariant certificate below \(3/4\); finitely determined certificates \(\ge1\). |
| **1.43 Coherence principle** | **New [L]** | Nonnegative statistics are maximal at \(0\); the pole is coherence. |
| **1.44 Antipode** | **New [L]** | The pole separates \(0\) from the Liouville point by sign only. |
| **1.45 Special locus** | **New [L]** | Dirichlet points read GRH, typical on average; the constant source is atypical on the special locus. |
| **1.46 Twin inequality** | **New [S]** | Exponents propagate between \(x\), \(2x\) and \(x+\ell\); \(1/2\) is not a floor on \(G\). |
| **1.47 Fixed-modulus sufficiency** | **New (inference from [L])** | Positivity at every fixed overlap needs only linear prime sums to a fixed modulus. |
| **3.51 The overlap window** | **New [L/K]** | Fixed \(c\): theorem. \(c_N^4\gg\log N\): RH. An existential unbounded positive schedule exists. |
| **3.52 The rate problem** | **New [open]** | Errors uniform in \(c\) and in conductors \(m\lesssim c\). Paper cards on polynomial and logarithmic rates exist [P]. |
| **3.53 Profile thresholds** | **New [L/K]** | \(C^2\): \(c^4\gg\log N\). Smooth: \((\log N)^\varepsilon\). Gevrey \(s\): \((\log\log N)^s\). Steklov: iterated log. |
| **3.54 Flip thresholds** | **New [L]** | \(c_0(p)<\infty\); \(c^*(p)\to\infty\). |
| **3.55 Single-profile window** | **New (inference)** | A generically tilted Steklov profile should carry both fixed-\(c\) positivity and the iterated-log receiver. |
| **3.56 Critical scaling** | **New (inference)** | The margin \(E(c_N)\) and the off-line damage are both of relative order \(1/\log N\) at the transition; conjecturally RH lives on \(E(c_N)\log N\asymp1\). |
| **14.51 Bézout and Riemann–Roch for \(\mathbb G_m(\mathbb Q)\)** | **New [K/L]** | \(h^0=\lfloor e^{\deg}\rfloor\); a Hodge index needs a quadratic Euler characteristic. |
| **14.52 Approximate vanishing** | **New [L]** | For integer auxiliaries, smallness below \(1/\sqrt2\) on long progression stretches is divisibility. |
| **14.53 Twist tower over \(\mathbb Z\)** | **New [L]** | Collapses to its first level. |
| **14.54 Adams operations** | **New [L]** | \(\psi^q\)-fixed points are the \((q-1)\)-torsion twists. |
| **14.55 Polar index** | **New [L]** | For curve data, index = number of right pole classes; confinement = index zero. |
| **14.56 Affine-invariant kernels** | **New [L]** | Kernels invariant under dilation and successor carry three constants. A ring positivity principle must carry broken successor invariance as a boundary term. |

## Wall 1 — Selective critical sign

| Face | Status | Content and remaining obligation |
|---|---|---|
| **1.0 Fixed-strip first rung** | Open [≥QRH]; external claim | Every strip dictionary reads \(\Theta\). Density envelopes never force vanishing. Guth–Maynard and DH \(\sigma\ge5/6\) [L]. External \(7/8\) [E]. |
| **1.1 Critical signed cancellation** | Open [RH] | Lag, Abel, history, series, one-sided \(\psi\), odd-class and first-clock receivers need the signed bound. |
| **1.2 Axis orientation** | Open [RH] | Ward caps, winding and Newton margins detect; extinction missing. |
| **1.3 Complete Weil positivity** | Bounded overlap proved [L]; RH-complete open [RH] | Every fixed \(c\) for profiles without real Fourier zeros. Index zero on an RH-complete schedule open. |
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
| **1.18 Arithmetic gauge selection** | Classified for flips [L] | Gap \(2\log2\) shared by \(\omega_p\), \(p\ge11\); one probe selects within finite flips. Complete form: each flip at its own \(c_0(p)\). |
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
| **1.38 Flip selectivity** | Per prime [L]; uniform impossible at fixed \(c\) [L] | Prime-square trial at \(c\ge c_0(p)\); flips with \(8\log p/\sqrt p<E(c)/2\) survive at \(c\). |
| **1.39 Two-source law** | Theorem [L] | Twin-blind closure; diamagnetism; non-ratio lags. |
| **1.40 Point-\(0\) typicality** | Exact [L] | Typical exponent \(1/2\); \(\theta_\mu(0)=\Theta\ge1/2\); RH \(\iff\) equality. |
| **1.41 Major arcs of gauge charge** | Theorem [L]; used | Level-\(q\) averages keep shells with \(q\mid j\). |
| **1.42 Gauge non-invariance** | Theorem [L] | Gauge-invariant certificates \(\ge3/4\) at \(0\); finitely determined \(\ge1\). |
| **1.43 Coherence principle** | Theorem [L] | Nonnegative statistics are maximal at \(0\); excess = pole; diamagnetic prime pair form. |
| **1.44 Antipode** | Theorem [L] | \(S_N(\ell)+S_N(0)=2\psi(\sqrt N)\); the twins are separated only by the sign of the pole. |
| **1.45 Special locus** | Theorem [L] | Dirichlet points: exponent \(\Theta_\chi\), GRH = typical, typical on average. Constant source: exponent \(0\) or \(1\). |
| **1.46 Twin inequality** | Theorem [S] | \(\exp_\mu(x+\ell)\le(1+2\exp_1(x)+\exp_\mu(2x)/2)/3\). Any strip produces points better than typical. |
| **1.47 Fixed-modulus sufficiency** | Inference from [L] | Fixed overlap needs only linear fixed-modulus prime sums; minor arcs at \(0\) are not needed there. |

Evidence: [coherence](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheCoherencePrinciple.lean), [antipode](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheLiouvillePointIsTheAntipode.lean), [not gauge invariant](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheExponentIsNotGaugeInvariant.lean), [typical exponent](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheTypicalExponentIsOneHalf.lean), [trivial point](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheTrivialPointIsNeverBetterThanTypical.lean), [special locus](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheSpecialLocusReadsGRH.lean), [twin inequality](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheLiouvilleTwinInequality.lean), [major arcs](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheMajorArcsOfTheShells.lean), [flips seen](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/EveryFlippedPrimeIsSeenAtLargeOverlap.lean), [no fixed overlap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/NoFixedOverlapSeesEveryFlip.lean), [affine windows](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/WeightedAffinePrimeWindowsAreUniform.lean), [parity form](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheParityFormOfTheGlobalLaw.lean).

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
| **3.15 Escape states** | Open [RH] | Positive gauge mass of every escape state; the Möbius escape state is an Euler product blind to zeros [L]. |
| **3.16 Prime to spectral sign** | Partly closed | At fixed overlap the prime-side margins reach the full form with poles intact [L]. Growing overlap open. |
| **3.17 Archimedean-line horizon** | Boundary [L] | Below the threshold the line sees the whole torus; beyond it, near-incidence is gauge charge. |
| **3.18 Localization** | Boundary | Positivity constrains a fibre only where the carrier localizes. |
| **3.19 Conductor versus forcing** | Open | No common aperture range. |
| **3.20 Collided-form norm** | Closed locally | Log-weighted Fourier norm at fixed aperture. |
| **3.21 Lattice to continuum** | Open | Lattice payment must keep the continuum remainder. |
| **3.22 Computed detection** | Closed diagnostic | Detection is not exclusion. |
| **3.23 Local to global Hodge** | Open | Hyperbolicity is not additive. |
| **3.24 Horizon regulator** | Closed construction | Counterterms explicit. |
| **3.25 Narrow spacing payment** | Closed | Self-energy and prime defect pay at fixed fractions. |
| **3.26 Complete overlap transfer** | Every fixed \(c\) closed [L]; growth open | Uniform on bounded ranges [K]; RH beyond \(c_N^4\gg\log N\). |
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
| **3.43 Zero-side fixed-ratio stratum** | Boundary [S] | A tempered single-pair model is negative at every \(c\). Fixed-\(c\) positivity of \(\zeta\) uses its zero density, through Gamma. |
| **3.44 Certified-method boundary** | Superseded | Pertains to the plateau's Young family only. |
| **3.45 Charge barrier** | Superseded | Pertains to the plateau reference method only. |
| **3.46 Successor shells** | Solved [L] | Exact repayment by Poisson summation. |
| **3.47 Atom-norm degeneration** | Boundary [K] | No uniform floor as \(c\to\infty\). Fixed-\(c\) Gamma reserve for profiles without real Fourier zeros [L]. |
| **3.48 Length–height coordinate** | Exact [K] | Overlap \(X/T\), bandwidth \(\log X/\log T\). |
| **3.49 Prefix Schur reduction** | Exact [K] | Full \(W\ge0\iff D-B^*A^{-1}B\ge0\); negative dimension \(\le N-M\). |
| **3.50 Marginality** | Identity [L] | \(E(c)\to0\) by Stirling; tilted spline \(E\ge C/c^7\). |
| **3.51 The overlap window** | Exact endpoints [L/K] | Fixed \(c\): theorem. \(c_N^4\gg\log N\): RH. Existential unbounded positive schedule [L]. |
| **3.52 The rate problem** | Open [open] | Control replacement, shell and quasimode errors uniformly in \(c\) and in conductors \(m\lesssim c\), below \(E(c_N)\). Paper cards report polynomial-in-\(c\) harmonic bounds and logarithmic rates [P]. Siegel–Walfisz is not in the corpus. |
| **3.53 Profile thresholds** | Exact receivers [L/K] | Thresholds by profile class; sharpness per profile open. |
| **3.54 Flip thresholds** | Theorem [L] | \(c_0(p)<\infty\) for every \(p\); no fixed \(c\) sees all flips. |
| **3.55 Single-profile window** | Inference | A tilted Steklov profile, with \(\tau\) avoiding countably many values, keeps the Denjoy–Carleman derivative class and has no real Fourier zeros. |
| **3.56 Critical scaling** | Inference | One off-line zero's weight is \(O(c)\cdot\)mass [L]. Harmonic averaging of its row errors heuristically gives relative order \(1/\log N\), the same order as the top-row boundary layer. Conjecture: the RH transition is \(E(c_N)\log N\asymp1\). |

Evidence: [every fixed overlap](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/EveryProfileWithoutRealFourierZerosIsPositiveAtEveryOverlap.lean), [one horizon](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/OneHorizonMakesEveryBoundedOverlapPositive.lean), [shells repay](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheShellsRepayEveryConductor.lean), [Fourier integral](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheCompletedShellEnergyIsAPositiveFourierIntegral.lean), [spectrum](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheBottomOfTheCompleteWeilSpectrumIsTheCompletedShellEnergy.lean), [log overlap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis.lean), [second-order synthesis](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheSecondOrderSynthesis.lean), [polynomial floor](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheTiltedSplineHasAPolynomialConductorFloor.lean), [upward rows](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheUpwardPrimeWindowsCarryTheShellCorrection.lean), [one zero](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheWeightOfOneZero.lean), [zero side](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/ZeroSideStratum.lean), [Steklov](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TheFixedProfileReachesAnIteratedLogEndpoint.lean), [prefix index](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/WeilPrefixIndex.lean).

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
| **14.37 Local-to-global by counting** | Closed over \(\mathbb F_q\); open over \(\mathbb Z\) | Stepanov on both parity classes gives index zero over \(\mathbb F_q\). Over \(\mathbb Z\), Bézout and Riemann–Roch are exact and linear [K/L], with no ceiling and no producer. |
| **14.38 Blind hyperbolicity, selective sign** | Exact boundary | Hodge index at proved scales carries no arithmetic. |
| **14.39 Heat-flow horizon** | Near-axis open | \(2/3\) horizon [L]; wave number [L/S]; localized dissipation [K]. |
| **14.40 Over-regular Beurling systems** | Boundary | They share the successor's square-root class [K]. |
| **14.41 Krein–Langer structure** | Boundary [S] | A positive part never pays a pair. |
| **14.42 Tensor amplification** | Boundary | The tensor square of the prime error is WL's mean square. |
| **14.43 Compression** | Boundary [S] | Characteristic-polynomial annihilation; Euler compressors are index-neutral. |
| **14.44 Golden calibration** | Boundary [S] | Tower data do not decide; the lattice does. |
| **14.45 Infinite-symmetry continuation** | Closed; retired | Confinement \(\iff\) lower count [L]; polar index = number of right pole classes [L]. |
| **14.46 Locality is twin-blind** | Theorem [L] | Every pointwise-closed shift-invariant statement is twin-blind. |
| **14.47 Geometry of the parity twin** | Settled; extended [L] | The twin is geometric only in the Bohr closure. The Adams operations host \(x^q=x\) on characters. |
| **14.48 Point side versus zero side** | Boundary [S] | Integer auxiliaries see integrality only at \(s\in\mathbb Z\). |
| **14.49 Producer ledger** | Theorem [L] | \(\sum m_p\log p\le\log A\). Binomials \(\le1\) and factorial ratios \(\le\#T-1\) above the square root. Divisibility on the odd class is within \(2\sqrt x\log x\) of \(\theta\). |
| **14.50 Frobenius gap** | Theorem [L] | No bounded-defect ring endomorphism of \(\mathbb N\) besides the identity and unit-ball gauge points; integer-valued ones in \(\{-1,0,1\}\). |
| **14.51 Bézout and Riemann–Roch** | Theorem [K/L] | Exact and linear in \(e^{\deg}\). Over \(\mathbb F_q[T]\) places of one degree share a progression; over \(\mathbb Z\) each prime costs its own. |
| **14.52 Approximate vanishing** | Theorem [L] | Integer auxiliaries: small = divisible. |
| **14.53 Twist tower over \(\mathbb Z\)** | Theorem [L] | Collapses to level \(0\). |
| **14.54 Adams operations** | Theorem [L] | \(\psi^q\)-fixed = \((q-1)\)-torsion twists; \(\psi^2\) fixes only \(0\); Dirichlet points of order \(d\) are \(\psi^{d+1}\)-fixed. |
| **14.55 Polar index** | Theorem [L] | Index of curve data = number of right pole classes. |
| **14.56 Affine-invariant kernels** | Theorem [L] | Three constants. The successor must enter as a boundary, not as an invariance. |

Evidence: [ring endomorphisms](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/ApproximateRingEndomorphisms.lean), [Adams](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheAdamsOperations.lean), [factorial ratios](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/FactorialRatiosHaveBoundedMultiplicity.lean), [affine-invariant kernels](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/AffineInvariantKernelsAreTrivial.lean), [Bézout](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheBezoutTheoremOfTheMultiplicativeGroup.lean), [Riemann–Roch](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheRiemannRochTheoremOfTheMultiplicativeGroup.lean), [approximate vanishing](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/ApproximateVanishingIsAlmostDivisibility.lean), [small auxiliaries](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/SmallIntegerAuxiliariesAreDivisible.lean), [twist tower](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheTwistTowerCollapsesOverTheIntegers.lean), [polar index](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/ThePolarDivisorCountsTheIndex.lean), [Stepanov](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/StepanovsOrderOverTheFiniteField.lean), [linear counts](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/IntegralityProducesLinearCounts.lean).

## Sharp obstructions and their positive survivors

| Excluded shortcut | Strongest survivor | Replacement question |
|---|---|---|
| Multiplicative or gauge-invariant data as a selector | No certificate below \(3/4\); coherence; antipode | A \(0\)-specific input (Q3) |
| Fixed-overlap positivity as RH | Theorem at every fixed \(c\), margin \(E(c)\) | Rates in the window (Q1) |
| One fixed overlap against every flip | Per-prime thresholds \(c_0(p)\) | A resolution–distance law (Q3) |
| Separated reference continued past touching | Shells repay exactly by Poisson | Uniformity in \(c\) and conductor |
| Atom-normalized floors at growing overlap | Fixed-\(c\) Gamma reserve; exact margin | Floors relative to \(E(c_N)\) |
| Gevrey profiles at \(\log\log N\) | Steklov at \(L(\log L)^2\log\log L\) | The exact quasi-analytic edge; tilted Steklov |
| Interval-stable or finite-aperture information | Precision rigidity; window law | Infinitely determined input |
| The count as a selector of \(\Lambda\) | Tower positivity selects exactly | Positivity statements for selection |
| One prime tower | Nyquist; height certificates | Two primes or fine towers; unattained depth |
| Absolute payment of all prime layers | Finite index except \(k=1\) | The last layer is [FS] |
| Positive-part repair of finite index | Krein–Langer: separated pairs keep index | A structural index ceiling |
| Compression as a producer | Annihilation law | A point-side producer (Q2) |
| Divisibility, binomials, factorial ratios as parity producers | Ledger; bounded multiplicity | Multiplicity beyond divisibility (Q2) |
| Self-maps of \(\mathbb Z\) as Frobenius | Classification; Adams operations on \(G\) | A producer acting on characters and coupled to addition (Q2) |
| "Small" auxiliaries instead of vanishing ones | Small = divisible for integers | Non-integral or archimedean auxiliaries |
| A vertical shift as the parity twin | The twin lies in the Bohr closure | A geometric twin there |
| Zero-side slack below bandwidth \(3/4\) | Slack conservation; projected credit | A positive \(E_{\rm proj}\) bound |
| Value moments as certificates | Mimicry | A displacement-sensitive count |
| One-sided sieve bounds beyond bandwidth one | Exact exchange rate | A two-sided coalescent estimate |
| Density estimates as exclusion | \(30/13\); DH \(\sigma\ge5/6\) | A vanishing mechanism |
| Finite support as a sub-Lindelöf target | Finite support \(\Rightarrow\) LH \(\wedge\) QRH | Treat as LH-level |
| Index-continuity deformation of \(\zeta\) | Continuity off the discriminant | None: \(\Lambda_{\rm dBN}\ge0\) blocks openness |
| Kernels invariant under the whole affine semigroup | Three constants | Successor as a boundary term |

## Consequences for priorities

- [Q1](obstacles-summary.md#q1) targets 3.51–3.56 and 1.47: the rate and location of the RH transition inside the overlap window.
- [Q2](obstacles-summary.md#q2) targets 14.37, 14.47, 14.49–14.54: a producer acting on characters through the Adams operations and coupled to additive structure.
- [Q3](obstacles-summary.md#q3) targets 1.18, 1.38, 1.42–1.46 and 3.54: how overlap resolves gauge points near \(0\).
- 1.26, 3.35, 14.39 and 14.41 (finite support) are LH-level and not near-term priorities.

No route is declared dead by these priorities. Finite calculations, compositions, quantifications, formalizations and integration are [just work](obstacles-summary.md#21-tasks-that-are-just-work).
