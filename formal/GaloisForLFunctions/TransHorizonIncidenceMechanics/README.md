# Trans-Horizon Incidence Mechanics (`GaloisForLFunctions.TransHorizonIncidenceMechanics`)

This program studies quantitative transfers between finite divisor observations,
Fermi boundary traces, valuation clocks and continuous arithmetic energies.
Its purpose is to preserve signs, endpoints and parameter dependence when passing
between these descriptions. An exact transfer identity does not supply the
arithmetic bound needed to close an RH route.

This guide was corrected on 19 October 2026 against the Lean corpus. The
[obstacles report](../../../docs/reports/hard-obstacles-summary-1810.md) and
[route ledger](../../../docs/reports/rh-current-frontier-map.md) give the broader
status. The obstacle groups organize this repository's open dependencies; they
are not a proof that mathematics lacks six irreducible theories.

## 1. Scope and receiving inequalities

BVI already proves trans-horizon results, including cofinal discrepancy estimates
and fixed polynomial-window defect laws. It is not restricted to $M+1\le N$.
The full period $L_N=\operatorname{lcm}(1,\ldots,N)$ and the convenient period
$N!$ are different integers. Full-period diagonalization does not by itself
control a short or moving observation window. No universal assertion that RH
“lives” only in $N<M\le N^2$ is justified.

The program has three principal receiving problems:

| Receiving problem | Required statement | What remains unpaid |
|---|---|---|
| PM/BVI source admission | A finite horizon-uniform pure-interior pronic-energy bound at arbitrarily small positive dampings. The bound may depend on damping. | Actual coefficient-weighted cancellation below damping $1/2$; the source-energy endpoint $\varepsilon\ge1/2$ is already proved. |
| CHMD odd-sector positivity | On the specified odd source domain, edge energy dominates source mass, retaining the literal prime and archimedean measures. | A quantitative signed bound for the complete form, with arbitrary support radius and all collar costs controlled. |
| Fermi/Nyman approximation | Global $L^2(dx)$ approximation of the target, or a valid weak-closure argument with both boundedness and identification of the weak limit. | Coefficient-dependent origin control and bulk approximation on the same sequence. |

The source mass is not an invariant of the signed-radical quotient. A Poincaré
inequality cannot be placed on that quotient without constructing a norm that
descends and proving the appropriate domain theorem. Likewise, finite
multiplicity of each above-threshold eigenvalue does not prove compactness of
the full CHMD resolvent or finite dimension of its entire above-threshold band.

## 2. Core objects and exact conventions

For a finite divisor row $c$, use
$$s_{N,c}(k)=\sum_{\substack{d\mid k\\1\le d\le N}}c(d),\qquad
Y_{N,c}(q)=\sum_{\substack{1\le d\le N\\q\mid d}}\frac{c(d)}d.$$
The observation state is `horizonObservationState N k`; for squarefree-supported
rows its radical version is `horizonRadicalState N k`. State equality is a
finite observability statement, not an additive successor dynamics theorem.

For $d\ge1$, the visibility clock is $\tau(d)=d/\operatorname{rad}(d)$.
The correct reconstruction of the von Mangoldt function is
$$\Lambda(d)=\begin{cases}
\log(d/\tau(d)),&d/\tau(d)\text{ is prime},\\
0,&\text{otherwise}.
\end{cases}$$
The prime guard is essential: $d=6$ has clock $1$ but $\Lambda(6)=0$.
The clock describes nonvanishing of a Ramanujan lag multiplier. It does not say
that every integer's valuation state changes exactly when the clock divides the
translation. See [`ValuationClockChainBridge.lean`](ValuationClockChainBridge.lean).

For $\rho_k(x)=\{1/(kx)\}$, the Nyman–Beurling space is
$L^2((0,\infty),dx)$. If $g$ denotes the actual approximation error, its origin
contribution transforms as
$$\int_0^{1/N}|g(x)|^2\,dx
=\int_N^\infty |g(1/u)|^2\,\frac{du}{u^2}.$$
Putting $dx/x^2$ on the left instead produces an unweighted reciprocal-variable
integral and is not this criterion. A tail estimate alone does not identify the
weak limit or control the bulk. Natural-scale Fermi/Haar statements must be used
with their own change of variables and normalization.

Literal Möbius and tapered rows also have different heads. For $N>1$,
$c(d)=\mu(d)\log(N/d)/\log N$ gives
$s_{N,c}(k)=\Lambda(k)/\log N$ on $2\le k\le N$.
This is not the zero head of the untapered Möbius row. The deletion-averaged
source has its own cancellation identity and must not be substituted silently.

## 3. Established mechanisms and their limits

| Mechanism | Established content | Limitation |
|---|---|---|
| Observation fibers and endpoints | Finite coefficient recovery, return-state tests and exact boundary terms in successor-energy identities. | A finite observation schedule does not supply a cofinal source estimate. |
| Valuation clocks and prime chains | Exact reconstruction of prime-power weights and the corresponding prime-chain energy decomposition. | Arithmetic encoding alone does not prove a favorable sign. |
| Buchstab steps and pronic centering | Exact cutoff-step laws, active/interior decompositions and cancellation of specified drift terms. | Bounded differences of uncontrolled energies do not bound either energy. |
| Fermi sampling | Selected jumps recover finite rows; sharp forward and inverse estimates quantify the observation cost. | The universal complete selected-trace inverse loses order $(\log_2 N)^2$. This loss is sharp for that observation model. |
| Odd-sector collar transport | High-prime absorption under support hypotheses, low-prime diagonal/reflection decomposition, and exact Chebyshev transport. | The remaining all-radius absorption estimate is still a premise; transport is not positivity. |
| Spectral/source identities | Signed graph polarization and exact eigenvector balance formulas. | Rewriting an eigenvalue bound as a four-term inequality does not prove that inequality independently. |

Useful entry points:

- [`ValuationClockChainBridge.lean`](ValuationClockChainBridge.lean): guarded von Mangoldt reconstruction and exact prime-chain linkage.
- [`StrictMobiusMarginAndUniformDampingStability.lean`](StrictMobiusMarginAndUniformDampingStability.lean): strict finite-region margins and damping neighborhoods. The neighborhood can shrink with cutoff.
- [`SupportRadiusCollarCutoffAndAllScaleObstacleBBridge.lean`](SupportRadiusCollarCutoffAndAllScaleObstacleBBridge.lean): support-radius split and high-prime collar bounds.
- [`CollectiveLowPrimeChebyshevTransportAndSinhAbsorption.lean`](CollectiveLowPrimeChebyshevTransportAndSinhAbsorption.lean): the existing Stieltjes/partial-summation identity `sum_vonMangoldtAtom_lt_eq_pole_add_chebyshevDiscrepancy_transport`, plus conditional sinh absorption. Reimplementing partial summation would duplicate existing work.
- [`FermiValuationSamplingAndPronicObservability.lean`](FermiValuationSamplingAndPronicObservability.lean): odd/four-divisible sampling and the Möbius-twisted inverse estimate with constant $4$, under its stated support/trace conventions.
- [`FermiCompleteTraceValuationStability.lean`](FermiCompleteTraceValuationStability.lean) and [`FermiPhysicalOptimalConstants.lean`](FermiPhysicalOptimalConstants.lean): complete selected-trace conditioning and sharp loss.
- [`FermiDyadicAntichainPrimeCapacityClassification.lean`](FermiDyadicAntichainPrimeCapacityClassification.lean): bounded prime-capacity classification for the specified antichain support class. This supplies a positive boundary for the no-go, not a uniform inverse on all rows.
- [`../BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean`](../BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean): the actual pure-interior receiver and its unconditional $\varepsilon\ge1/2$ baseline.

## 4. Research next

1. **Quantitative low-prime absorption.** Apply the existing Chebyshev transport
   to the actual collar kernel. Keep support radius, profile parameter, derivative
   cost and endpoints explicit. Prove a bound absorbable by the available
   positive form, or exhibit a sharp obstruction and its surviving source class.
2. **Observation cost on the actual source.** Test whether the PM/cofactor row
   satisfies an established bounded-capacity or twisted-sampling hypothesis.
   Adding the $2\parallel n$ cells changes the observation model and is a research
   question; it cannot erase a sharp loss for the original model by assertion.
3. **Uniform transfer in the receiver's parameters.** Connect a concrete BVI
   cancellation estimate to a complete continuous energy with all coefficient,
   damping and cutoff costs retained. Constants may depend on fixed damping;
   horizon dependence must be controlled before damping is taken smaller.
4. **Controlled limits.** Prove origin and bulk tightness for one explicit
   approximation sequence, or continuity of the complete signed form on one
   useful source family. A bounded norm, a formal trace expression, or a finite
   numerical cutoff alone does not supply this step.

These are source-specific inequalities and domain/limit questions. The existing
bridges make them precise; they do not establish that the listed obstacles have
been overcome.
