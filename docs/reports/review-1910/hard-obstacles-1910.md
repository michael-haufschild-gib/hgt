# Hard mathematical obstacles: current route status

19 October 2026. Companion: [routine work, open problems and research directions](hard-obstacles-summary-1910.md).

## 1. Current assessment

**Every current route has an unresolved mathematical step. None has a demonstrated path to RH consisting entirely of known-method work.** The central gaps are independent arithmetic cancellation, positivity of a complete form, uniform control through a critical limit, or construction of an arithmetic object that supplies one of those properties.

Coverage: **27 routes, 19 named candidates and PM's embedded PW-B candidate**. Sections 3–4 assess all 47 entries individually. Section 5 states the 15 shared walls with their exact scope. Section 6 gives the quantitative status of BVI, BiScale, APT, THIM, ACT and SRT, which support several routes.

The entries use the following classification:

| Category | Meaning |
|---|---|
| **Established** | Available mathematical results, with their stated hypotheses. |
| **(a) Known-method work** | A specified application or finite calculation supported by existing results. This is “just work”; it can still require substantial effort. These applications are useful when a research target needs them, rather than mandatory tasks for every route. |
| **(b) Open mathematics — B-RH** | An unproved target whose stated form would imply RH. Equivalence is asserted only where established. |
| **(b) Open mathematics — B-C** | An unproved construction or transfer. It may be insufficient, stronger than necessary, or false; its truth is itself a research question. |
| **Obstruction** | A proved failure of a specified mechanism. Its scope and any useful replacement are stated explicitly. |

RH remains [an unsolved problem](https://www.claymath.org/millennium/riemann-hypothesis/). Accordingly, no established unconditional proof of a complete RH-equivalent target is available. For bespoke constructions, “open” means that no solution is established for the stated task; it does not imply that every such task is a recognized conjecture throughout mathematics.

A **receiver** below means an established implication from a precisely stated estimate or construction to RH. Having the receiver does not supply its premise. The open families O1–O8, referenced in individual entries, are defined in the [summary](hard-obstacles-summary-1910.md#2-open-mathematical-obstacles-deduplicated).

## 2. Common quantitative requirements

| Requirement | What the closing theorem must control |
|---|---|
| **Complete expression** | Diagonal and mixed terms, prime and Gamma contributions, polar costs, endpoints and inherited history. A sign for one component does not determine the complete form. |
| **Exact quantifiers** | All required tests, apertures, orders or heights in the regime used by the receiver. Fixed-order eventual positivity and a common all-order bound are different assertions. |
| **Arithmetic fidelity** | The literal coefficients and source, including completion, poles and multiplicity. A model with the desired spectral property must also be identified with the arithmetic object. |
| **Limit control** | Convergence in the norm or topology that carries the conclusion, with explicit dependence on every growing parameter. Strong convergence alone does not imply norm, trace-norm or graph convergence. |
| **Exclusion of exceptions** | A bound that rules out every relevant off-line configuration, including clusters and finite exceptional sets. Recovery of a hypothetical obstruction does not exclude it. |

Two normalizations are especially important:

- **Nyman inversion uses `dx`.** Under `u=1/x`, `∫₀^(1/N)|Σ a_k{1/(kx)}|² dx` becomes `∫_N^∞|Σ a_k{u/k}|² du/u²`. Using `dx/x²` in the first integral instead produces an unweighted periodic tail, generally divergent. The target `1_(0,1]` does not belong to `L²(dx/x²)`.
- **PM/BVI constants may depend on damping.** The sufficient criterion needs horizon-uniform bounds for arbitrarily small fixed positive damping. It does not require one constant uniform as damping tends to zero.

## 3. Routes: all 27 entries

### WL — Weil lag function

**Established.** One-sided lag receivers, sampling transfers and prime–archimedean trace identification exist. Chebyshev/packet Plancherel formulas expose the complete energy, including endpoint squares and fine-block deviations. The available Cramér mean-square theorem assumes RH.

**(a) Known-method work.** Reuse those identities to express a chosen finite-cutoff estimate in the receiver's normalization; retain endpoints. No missing hard step is certified routine.

**(b) Open mathematics — B-RH.** Prove an independent one-sided exponent-zero prime-lag bound, or the stated one-sided logarithmic Chebyshev-deficit primitive bound, uniformly in its full range. Alternative sparse-sampling receivers also require their chain/exception hypotheses. Mean-square identities and unconditional logarithmic/subpower savings do not establish that sign. Do not replace this target by the false pointwise `ψ(x)−x=O(√x)` claim.

Walls 1, 7, 10; open family O1 in the summary.

### RW — Restricted Weil ground energy

**Established.** All-aperture positivity/vanishing negative index is an RH criterion. Ground operators, finite negative-index computations, exact jump/polar decompositions and the sinh-capacity formulation exist. Small-aperture positivity is established.

**(a) Known-method work.** Apply existing finite-aperture and source-coordinate results with their exact domains. Finite matrix algebra is known work once its entries are given; determining their signs at every aperture is not.

**(b) Open mathematics — B-RH.** Bound the complete negative direction at every aperture: prime, Gamma, polar and cross terms together. In the complete form, positive jump energy coexists with the signed pole plane. Factorial-span positivity, a near-null sequence, injective divisor evaluation and a nondegenerate quotient leave possible negative directions. A uniform positive gap in the original primitive graph norm is already obstructed.

Theorem source: [capacity criterion](../../../formal/GaloisForLFunctions/RHTower/WeilMarkovPoleCapacity.lean).

Walls 11–13; O2.

### FU — CCM-FU signed prime scheduling

**Established.** Finite prescribed-prime scheduling and fixed-cutoff complete-graph approximation exist. A prime-exhaustive history can decrease energy at selected block cutoffs. The one-sided completed Abel receiver retains lattice and polar terms.

**(a) Known-method work.** Instantiate the finite scheduling and graph-error theorems for a fixed target; account for their stated constants.

**(b) Open mathematics — B-RH.** Prove the uniform upper bound for the literal completed Abel moment `A(M)/M`, paying the seed, inherited action, covariance, endpoints and drift between selected cutoffs. Small diagonal cost for a newly chosen block does not pay its interaction with earlier blocks. A sequence of favorable endpoints is not a bound on the whole history.

Walls 1, 7, 10, 14; O4.

### RP — Route-P / SP-E history floor

**Established.** The linear-floor receiver, hyperbola/centroid/square-debt identities and low-LCM payment exist. Native first-jet synthesis is bounded and noncompact; strong differentiation does not imply operator-norm differentiation. Positive damping shells can converge strongly to zero while retaining nonzero trace.

**(a) Known-method work.** Reuse the source and singular-domain dictionaries; compute a fixed finite history exactly.

**(b) Open mathematics — B-RH.** Prove the complete-history lower floor, simultaneously controlling centroid, square debt, high-LCM terms and moving-core transport. Neglecting the trace boundary mass or replacing strong convergence by trace-norm convergence is not a repair. The positive survivor of that obstruction is the exact shell scale law.

Walls 1, 10, 14; O4.

### PA — Prime–archimedean source passivity

**Established.** Trace/current recovery, RH-equivalent passivity and compact signed-moment criteria exist. Each fixed Hausdorff order is eventually positive in the shift. Bernstein probability measures can tomographically recover an off-line packet if it exists.

**(a) Known-method work.** Compute finite orders/shift ranges and use existing reconstruction. These are finite applications, not completion of all orders.

**(b) Open mathematics — B-RH.** Prove the high-frequency current sign, the required arbitrarily thin exponential Bernstein-mismatch envelope, or all residual low-shift signs across unbounded orders. A positive saddle band still has an uncontrolled signed complement. Constructing the all-order compact moment measure would itself close RH; passive deletion and finite atom repair cannot construct it.

Walls 2, 6, 12, 15; O2/O3.

### MC — Möbius cancellation at half power

**Established.** Mertens/Möbius, Hilbert, Liouville and square-source receivers exist. Exact signed decompositions pay several restricted regions. BVI supplies fixed-horizon laws, all fixed moments, magnitude-pattern laws and sharp finite observability.

**(a) Known-method work.** Reuse exact Vaughan/divisor expansions and the correct Möbius source weights. Evaluating all 25 ordered pairings in the five-component expansion at a specified finite cutoff is known work.

**(b) Open mathematics — B-RH.** Prove half-power cancellation, equivalently the required global signed bilinear bound with principal counterterm and high-product remainder together. Fixed-ratio limits do not bound a ratio growing with the cutoff. Unsigned sparsity, lower gradient bounds and qualitative fixed-shift correlations do not supply the complete weighted bound. The raw unrenormalized defect has a linear obstruction and must not be targeted by a blanket sublinear estimate.

Walls 1, 7, 10, 11; O1.

### TT — Theta-tail and heat–Cassini currents

**Established.** Seam/tail identities, Wold thresholds, natural-cutoff energy receivers and odd reflected-prime/Doob formulations exist. The stated full-translation average erases transverse depth. An abstract Ruelle continuation theorem has no proved zeta identification.

**(a) Known-method work.** Use existing identities on a fixed admitted test class; keep the arithmetic source and full signed covariance.

**(b) Open mathematics — B-RH.** Prove the signed nonlocal covariance/Wold decay or full odd/primitive sign across every rapidity and test scale. A positive kernel, a finite prefix or a generic continuation theorem is not this inequality. The compact periodic-chirp failure is scoped to that family, not all theta constructions.

Walls 4, 7, 13, 15; O2/O3.

### LA — Line anchor

**Established.** Logarithmic-derivative, heat-slice and zero-count receivers are established. Finite-height and fixed-slice controls leave exceptional configurations. Nonintegrability of the Riemann–von Mangoldt remainder constrains specified perturbation models.

**(a) Known-method work.** Verify a specified finite range or reuse the slice index computation. Such checks are bounded tasks only when a concrete range and certification method are given.

**(b) Open mathematics — B-RH.** Establish the all-height arithmetic sign, including low-order slices and near-double off-line pairs. Forward heat regularization must reach the actual required time; it cannot be extrapolated backward by continuity alone. In the standard de Bruijn–Newman normalization, the known theorem is the lower bound `Λ_DN≥0`, whereas RH requires `Λ_DN≤0`. [Rodgers–Tao](https://arxiv.org/abs/1801.05914).

Walls 3, 4; O3/O8.

### TG — Topological sub-unit gate

**Established.** Boundary winding, integer index and source-sensitive transgression identities exist. Integrality can finish an argument once a nonnegative integer is independently shown smaller than one.

**(a) Known-method work.** Apply that elementary final implication; verify the finite matrix identity on its declared domain.

**(b) Open mathematics — B-RH.** Produce the matrix-complete identity `E_base=E_residual+Tr T_D`, prove `E_residual≥0`, and obtain the sub-unit trace for every required disc; alternatively prove the source central-gap bound at exponent zero. Index construction does not bound the index, and finite trace identities do not establish the global sign.

Walls 12, 14, 15; O4/O6.

### HF — Positive Hodge form on arithmetic cohomology

**Established.** Native arithmetic realizations, complete trace formulas and PBAP/full-Weil receivers exist. Some low-ratio inequalities are proved, but every nonzero smooth blind even-polar test with the stated finite second moment has `S/L>27`. A zero-built positive rational-dilation form additionally requires simple zeros.

**(a) Known-method work.** Apply existing cohomology, trace and common-core identities. The `S/L≤27` inequalities apply only within that ratio range; the stated smooth blind class lies outside it.

**(b) Open mathematics — B-RH.** Prove complete prime-blind positivity in the actual high-ratio regime, or remove the unpaid high-frequency sinh-dominance premise.

**(b) Open mathematics — B-C.** a source-defined positive Hodge/cup/trace construction and a faithful global native completion remain separate construction problems. A form on an already selected zero algebra is not that construction; RH does not assert simplicity. Origin energy loss and native topology escape must be addressed in any chosen limit argument.

Walls 5, 11–15; O2/O6/O7.

### CHMD — Causal Hyperbolic–Modular Duality

**Established.** Prime-wave, discrepancy-derivative, Möbius-rest and odd-sector spectral receivers exist. The signed radical is the resolvent's `1/2` eigenspace. Cardinal projections span the primitive bound-state band, but do not make it empty. One-signed odd eigenstates above `1/2` are excluded; sign-changing ones remain.

**(a) Known-method work.** Reuse the established source-domain energy and nodal identities. Keep the original source graph or an explicitly specified quotient norm: original source mass does not descend through the signed radical.

**(b) Open mathematics — B-RH.** Bound the complete signed wave/derivative pairing uniformly, or prove the full odd jump-versus-potential inequality, excluding all sign-changing eigenstates with `μ>1/2`. Nodal comparisons retain the primitive `oneL` defect. Finite multiplicity of each eigenvalue does not imply finite dimension of the entire band accumulating at `1/2`. The full resolvent cannot be declared compact from the no-Weyl-above-threshold theorem. Fixed-coefficient absorption and a uniform original-graph-norm primitive gap are failed shortcuts, not unfinished estimates.

Theorem source: [quotient parity and mass obstruction](../../../formal/GaloisForLFunctions/RHTower/CHMDQuotientParityAndCoercivity.lean).

Walls 1, 12–15; O2.

### TH — Theta moment positivity

**Established.** Exact theta moments, heat-current receivers and finite-rank sign regions are available.

**(a) Known-method work.** Evaluate specified finite moment matrices; reuse existing fixed-rank results. Generic Gaussian moment calculations do not supply a missing theorem about the literal prime remainder.

**(b) Open mathematics — B-RH.** Prove all-degree Hankel/Bezoutian positivity at the parameter specified by the receiver, or its equivalent same-time phase/current sign, retaining the full discrete-prime remainder. “For every degree, eventually in another parameter” cannot be replaced by “at one admissible parameter, for every degree.” Classical eventual Jensen hyperbolicity illustrates progress with this quantifier limitation, not a solution of it. [Griffin–Ono–Rolen–Zagier](https://arxiv.org/abs/1902.07321).

Walls 3, 4, 12; O3.

### RN — Theta renewal and singular comparison

**Established.** Native Green solvers, multiplicity-preserving packets, fixed-Gaussian realization and a literal compact cone-positive renewal determinant exist. Resonances are identified with eigenvalues; positivity preservation does not force that spectrum to be real. The unregularized whole-source native extension has a topology obstruction.

**(a) Known-method work.** Apply the realized operators and determinant identities on their established domains.

**(b) Open mathematics — B-RH/B-C.** Prove the mixed prime-plus-Gamma-versus-pole inequality, global seam/cusp gluing and boundary-current orientation. If native completion is used, supply a changed topology, regularization or normalization with proved fidelity. Reciprocal-square tomography and a zero-side quartet criterion observe the obstruction without paying its arithmetic sign.

Walls 10, 13–15; O2/O6/O7.

### WD — Ward orientation and horizontal collision

**Established.** Exact Ward identities, global cap integrability and multiplicity readouts exist. The actual nonnegative cap vanishes exactly under RH.

**(a) Known-method work.** Compute or transport the existing cap on a specified finite source. Integrability and formation are already available.

**(b) Open mathematics — B-RH.** Prove the global cap is zero, or a complete signed prime–Gamma contraction with uniform ownership/absorption estimates for every zero block. Nonnegativity is the wrong endpoint: it allows a strictly positive cap. Pair-exchange antisymmetry can annihilate an oriented readout even when squared displacement survives; a source bound on that surviving quantity is needed.

Walls 3, 12, 15; O4/O8.

### LI — Paired Li and prime–Gamma balances

**Established.** Literal paired histories, finite primitive receivers and closed-ideal classifications exist.

**(a) Known-method work.** Reuse the exact paired formula and compute finite coefficients with certified error. Those operations do not establish eventual sign.

**(b) Open mathematics — B-RH.** Prove the source lower floor `Re H_N≥K_N−C` throughout the stated growing window `0<t≤c log(2N+1)`, or the equivalent finite lower bound for the literal primitive. First-crossing and outside correlations remain part of the target. Taking positive diagonal pieces or assuming the lower floor inside a completion hypothesis does not close it.

Walls 1, 10, 12; O4.

### SZ — Suzuki screw and shifted-kernel limits

**Established.** The literal arithmetic Hankel operator exists and is compact self-adjoint at every positive shift and aperture. Gamma graph closure, radial Cesàro admission and almost-everywhere carrier reconstruction are established. Screw positivity is a classical RH criterion as well as a corpus receiver. [Suzuki](https://arxiv.org/abs/2206.03682).

**(a) Known-method work.** Reuse these admission and reconstruction results; inspect a specified finite shifted problem.

**(b) Open mathematics — B-RH.** Prove the source Wronskian sign with the moving infinite head and leakage paid, and the cusp-preserving control needed as the shift tends to zero. Self-adjointness permits negative spectrum; compactness at each positive shift supplies no uniform unshifted limit. The missing estimate is not operator existence.

Walls 2, 4, 12, 14; O2/O4/O7.

### PM — FZZ-P Haar approximation

**Established.** For `φ_a(t)={1/(at)}−2{1/(2at)}`, approximation of the dyadic Haar target in `L²(0,1]` is RH-equivalent. Witness self-similarity, Fourier reconstruction and exact pronic transfers exist. Power-damped source energy is bounded unconditionally for `ε≥1/2`.

**(a) Known-method work.** Apply the existing cell/energy equivalences and endpoint theorem. Preserve the correct measure under inversion; finite traces and local approximation can be checked directly.

**(b) Open mathematics — B-RH.** Obtain unconditional global Haar approximation, top-octave/origin control for every admitted witness, or horizon-uniform complete pronic budgets for arbitrarily small positive damping. Local density on `(δ,1]` does not control `δ↓0`. Active-pair drift, conditional-head means, interior means and signed complements must be combined before taking limits. The separate **PW-B branch remains a candidate** and is assessed below.

Theorem source: [exact pronic receiver](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean).

Walls 1, 2, 7, 10; O1/O7.

### JAS — Joint ancestry

**Established.** Full-product/large-prime positivity receivers hold without quasi-RH or no-chain side assumptions. The square-shell finite-power-window criterion, full-support Gamma–theta admission and forward creation are established.

**(a) Known-method work.** Apply full-support source admission and exact shell mass/rank compression.

**(b) Open mathematics — B-RH.** Prove exceptional constant-vector sign on enough shells, all-amplitude shell positivity, or subpower square-shell Riesz bounds over the required window `m<k≤m+m/log(m+1)` for every exponent. Typical-phase positivity and strong prime-cutoff exhaustion do not control exceptional vectors. A bounded power window still moves to infinity and is not a finite verification.

Walls 3, 6, 7, 12; O1/O3/O8.

### CTF — Chronological tail and Báez–Duarte approximation

**Established.** The discrete distance criterion, bounded chronological-row criterion and dual sampling criterion are established. Unrestricted coefficient rows are dense; bounded vanishing-error rows force the Möbius coefficients. Classical Báez–Duarte restriction to integer dilates is established externally too. [Báez–Duarte](https://arxiv.org/abs/math/0205003).

**(a) Known-method work.** Reuse the exact two-sided equivalences and finite Gram calculations. Verify any proposed coefficient row against its actual bounds and divisor identity.

**(b) Open mathematics — B-RH.** Construct admissible bounded rows with vanishing global error, prove `d_N→0`, or prove the dual sampling estimate independently. Unbounded density does not meet a bounded-row constraint. A tapered Möbius row has a prime-power head, not exact undamped divisor cancellation. A sub-logarithmic Selberg diagonal or an unpaid growing-moment comparison cannot be assumed as “standard sieve work.”

Walls 1, 2, 7, 10; O1/O7.

### HCF — Gaussian heat trace / critical feature variance

**Established.** Exact heat-trace/moment receivers, finite-rank positivity and singular-block index laws exist. All-degree positivity on two prime-log grids, with their polar constraints, is RH-equivalent. A single grid and finitely many offsets with the same step admit off-line aliases.

**(a) Known-method work.** Compute fixed-rank forms and use exact polar-atom subtraction. Two-grid information and mixed reconstruction theorems are available with their stated hypotheses.

**(b) Open mathematics — B-RH.** Prove positivity of both literal prime–archimedean grid forms at all degrees, or the one-sided vertical/prime-chirp bound or cofinal entropy-deficit estimate. Two marginal grids need not reconstruct arbitrary packets; an RH positivity criterion and complete tomography are different statements. Neither finite degree nor fixed-profile eventual height positivity supplies the uniformity needed here.

Walls 3, 4, 7, 12; O3/O8.

### XN — Xi Newton invariant discs

**Established.** Disc coverage plus a self-map margin is an RH criterion. The actual margin obeys `ΔQ=4(r²−|z−c|²)|ξ″|²≥0` inside the disc. Fixed-disc pole repairs preserve root jets but not self-mapping.

**(a) Known-method work.** Evaluate an explicitly specified finite disc and its Green-potential formula. No global covering algorithm is supplied by that calculation.

**(b) Open mathematics — B-RH.** Construct line-centered discs covering every zero, with `Q≥0` throughout each disc. A subharmonic function can have nonnegative boundary and negative interior; the displayed Laplacian has precisely the wrong implication for that shortcut. The full interior curvature cost requires an arithmetic bound. Global scalar damping of the stated form is obstructed except for the trivial choice.

Walls 3, 4, 15; O8.

### BAG — Deterministic zeta self-return

**Established.** Finite Dirichlet heads have positive-density uniform returns. Unconditioned Carlson tail mean square and arbitrary-order truncation exist. The corpus proves that the stated physical disc recurrence implies RH; it does not claim the converse for this exact formulation.

**(a) Known-method work.** Use the exact centered head/tail decomposition and the established unconditioned mean square.

**(b) Open mathematics — B-RH.** Prove centered-tail smallness on the **same** finite-head return heights, with enough uniformity for each required right-strip disc. If the conditioning event has density `κ`, a generic unconditioned second-moment bound `A` gives only `A/κ`. Prove the actual joint parameter balance; neither randomness nor an unsupported asserted cutoff law supplies it. Positive-density events for separate pieces need not have useful intersection.

Walls 2, 7; O5.

### EWU — Even pole-weight uniqueness

**Established.** Even positivity forces the actual von Mangoldt weights and RH. Blind minimizers exist; their minima are antitone in aperture and positive at small apertures. Conservation, collar inequalities and purification are established.

**(a) Known-method work.** Apply those identities on their exact even/polar/blind class. Evaluate a fixed finite model without treating it as the full minimum.

**(b) Open mathematics — B-RH.** Prove the actual even blind minimum nonnegative at every aperture. The remaining complete negative prime–polar pairing is not paid by origin energy, a finite collar or restricted factorial positivity. Subtracting the ground minimum makes the residual invariant under constant shifts while the sign of the minimum changes; that residual cannot certify the missing sign. Origin concentration and polar escape obstruct naive limit passage.

Walls 8, 11–13; O2/O7.

### GTA — Transverse Schur charge

**Established.** Positive quartic theta-stage charge and the RH-equivalent rank-uniform decay receiver exist. Finite truncations converge strongly even in the presence of the hypothetical obstruction.

**(a) Known-method work.** Reuse the finite Schur packet formulas and their exact positivity.

**(b) Open mathematics — B-RH.** Derive uniform transverse-energy decay across all sufficiently late actual packets, independently of the zero divisor. A positive quartic quantity need not tend to zero. Strong convergence for each fixed packet does not give a bound uniform in packet rank or changing source.

Walls 7, 12, 15; O4/O7.

### OWU — Odd Weil-weight uniqueness

**Established.** Odd positivity for actual `Λ` is RH-equivalent. Odd-positive minorant/ray criteria, ground operators, dual attainment and divisor detection exist. A finite set of nonreal zeros of a ground generator is not proved empty.

**(a) Known-method work.** Apply exact odd-sector decompositions and the THIM correction identity, retaining the local mass correction.

**(b) Open mathematics — B-RH.** Prove full odd positivity, or produce an odd-positive arithmetic weight with the required all-scale ray sign. Arbitrary odd tests retain reflected-prime and cosh-pole costs. Low-prime collar duality leaves a diagonal potential; `θ·sourcePair` remains unpaid. Uniform cosh-by-sinh absorption fails; shared-cutoff primitive families with small absolute energy do not prove every odd energy nonnegative.

Walls 11–15; O2.

### PBM — Prime boundary monodromy / regularized log-zeta abscissa

**Established.** Convergence of the fixed regularized prime or log-zeta series at every real `σ>1/2` is RH-equivalent. The current route is an abscissa criterion; actual monodromy belongs to DR. Compact-quotient comparisons and a prime-gap continuation theorem exist.

**(a) Known-method work.** Reuse the exact Abel identities and coefficient definitions. Pole subtraction is already performed.

**(b) Open mathematics — B-RH.** Establish critical-abscissa cancellation of those fixed coefficients. Analytic continuation of some related series is not convergence of the required series. A proposed prime-gap second-moment route must reach its stated exponent **and** discharge its zero-freeness condition. A fixed zero-free half-plane above the critical line leaves the convergence requirement for every `σ>1/2` unresolved.

Walls 1, 6, 10; O1.

### RB — Robin/Nicolas divisor-sum criterion

**Established.** Eventual Robin and Nicolas inequalities are exact receivers. Fixed exponent-defect classes have margins; moving valuation defects force hypothetical large counterexamples to contain growing lcm cores. Restriction to colossally abundant integers is established.

**(a) Known-method work.** Apply the extremal reduction and finite valuation identities; certify a specified finite range if useful.

**(b) Open mathematics — B-RH.** Prove the required sign on the increasingly prime-saturated extremal integers/primorials. Necessary divisibility by every integer in a growing short range is consistent with extremely large integers; it is not a contradiction. Leading Mertens asymptotics do not determine the critical remainder. Elementary formulations do not make this routine. [Lagarias's related exact criterion](https://arxiv.org/abs/math/0008177).

Walls 1, 9, 11; O1.

## 4. Candidates: all 19 named entries, plus PW-B

Candidate status does not mean a known proof merely lacks implementation. In these entries, the source, decisive estimate or source-to-receiver landing remains unconstructed. A zero-based argument is legitimate if its decisive premise is proved independently; the objection is assuming the desired zero property while building the proposed producer.

### ACT — Arithmetic criticality / folded supersolution

**Established.** Finite ground-state representation and finite Allegretto–Piepenbrink equivalence exist. The infinite folded theorem is a **sufficient criterion**, assuming both a pointwise supersolution and admissible factorization of every compact odd `C²` test. It does not establish the converse or construct that function.

**Obstruction.** Every single shifted theta ground state is a strict folded subsolution near the origin: prime 2 forces failure. This excludes the single-shift supersolution construction. The result does not establish a classification of all positive odd profiles; any broader assertion requires its own admissibility and origin-limit argument.

**(a) Known-method work.** Reuse the exact representation and the scoped obstruction.

**(b) Open mathematics — B-C/B-RH.** on a specified admissible factorization class, prove remainder domination of the reflected-collar defect; then justify coverage/density of the full odd test class. Existence of an admissible replacement profile is itself unresolved.

Theorem source: [source theorem and survivor](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ShiftedGroundStateOriginFailure.lean).

Walls 12, 13, 15; O2/O6.

### APF — Arithmetic paired Fredholm

**Established.** Fredholm index and cycle-trace Fourier reconstruction are established.

**(a) Known-method work.** Apply the finite trace algebra on a specified admissible subspace. The full CHMD resolvent has an infinite threshold eigenspace, so compactness cannot supply a Hilbert–Schmidt trace there.

**(b) Open mathematics — B-C.** Construct a source-defined exhaustion and prove vanishing of all relevant trace coefficients. Those coefficients already encode off-line contributions; recovering them is not making them vanish. Any new trace-class hypothesis must be proved for the actual operator or a precisely chosen spectral subband.

Walls 12, 14, 15; O4/O6.

### BSH — Arithmetic mate curvature

**Established.** Curvature/ideal diagnostics distinguish radial characters `n^(2 Re s−1)`; finite cutoffs can be trace-blind.

**(a) Known-method work.** Reuse the diagnostic formulas. Generic Cauchy–Riemann identities are not the missing arithmetic mate.

**(b) Open mathematics — B-C.** Construct the literal prime–Gamma section and mate identity that forces the required character at actual Xi zeros. Setting that character to zero in the definition assumes the desired location. Source construction and independent orientation remain missing.

Walls 12, 15; O6.

### BVI — Bézout–valuation incidence

**Established.** Successor/pronic identities, sharp finite moment cones, exact prefix recovery, valuation clocks, fixed-linear-horizon laws and PM/FZZ-P transfers exist. A complete two-moment universal improvement is impossible because the cone is sharp. Direct `Λ(k(k+1))` readout vanishes for `k≥2`.

**(a) Known-method work.** Apply the power-damped source identities, coordinate inversions and finite Gram expansion. The five-component Vaughan decomposition retains all 25 ordered pairings. Finite specialization supplies an exact expression, with no half-power cancellation bound implied.

**(b) Open mathematics — B-RH.** Bound the **complete** log-renormalized weighted remainder for arbitrarily small positive damping, uniformly in horizon. Include positive active drift, shared-birth covariance, conditional means, signed prime-clock complement, diagonal and endpoints. The logarithmic calibration has a nonsummable majorant below half damping. The active-boundary difference can be summable while both main energies remain uncontrolled.

**(b) Open mathematics — B-C.** A direct source-to-CHMD sign transfer is still missing. Clock identification and an odd-chain receiver do not establish it. BVI is a productive arithmetic interface to existing routes, not an independently closed route.

Walls 1, 7, 10, 11; O1/O7.

### CDC — Constitutive dagger

**Established.** Calibrated confluence characterizes `Re s=1/2`; entropy/curvature identities and diffusive total-work limits exist.

**(a) Known-method work.** Reuse those identities on their native fibres. Renaming them as a dagger adjoint on another space does not prove transport.

**(b) Open mathematics — B-C.** Construct one arithmetic, pre-divisor potential that descends on all relevant closed error fibres and couples the spectral parameter to actual Xi vanishing. Small individual defects can accumulate nonzero total work. The construction must prove its global descent, not assume the critical character.

Walls 12, 15; O6/O7.

### DR — Dyadic Xi roots

**Established.** Finite monodromy/Kummer information and capped root atlases exist; appropriate global zero-free roots would select the line.

**(a) Known-method work.** Use finite cover compatibility and the existing regularized-series identities. A Littlewood–Paley decomposition by itself supplies no global root.

**(b) Open mathematics — B-C/B-RH.** Prove global continuation, common-root compatibility and source convergence on the full strict-right domain. Arbitrarily many finite roots on different covers need not yield one globally compatible root. Naive smooth prime-germ and positive-root constructions are already refuted in their stated classes.

Walls 1, 4, 6, 15; O1/O6.

### EGC — Pole-safe contour

**Established.** Fixed-shift copy corrections, enclosed mass cancellation, arithmetic-ray reconstruction and a nonzero Gamma floor are established. Inner cancellation holds while retaining all zero copies.

**(a) Known-method work.** Apply the inner-contour cancellation identity and calculate its explicit remainder at a specified cutoff.

**(b) Open mathematics — B-C.** Prove the expanding outer-contour covariance/sign that excludes off-line copies. Centered prime-2 ray sign is not this outer sign. Faster-than-reciprocal decay of the raw complete extractor conflicts with its Gamma floor; the survivor is the exact arithmetic/Gamma decomposition, not an arbitrarily small error.

Walls 1, 10, 15; O4/O7.

### EWJ — Euler/Wold jets

**Established.** Exact finite-depth jets and compact-quotient diagnostics exist.

**(a) Known-method work.** Compute finite jets using the established formulas. An intertwiner between the BVI successor predictor and an EWJ realization requires a separate mathematical construction.

**(b) Open mathematics — B-C.** Establish zero-independent source admission and exhaustive norm control at unbounded depth, then a precise RH landing. Fixed-history recovery can miss the persistent transverse operator gap. Finite feasibility alone does not identify the completed source.

Walls 7, 14, 15; O6/O7.

### FEL — Theta likelihood

**Established.** Probability, conditional KL and adaptive full-reveal accounting exist, including posterior entropy deficit and spot debt.

**(a) Known-method work.** Apply the finite-history identities to a specified reveal process, retaining posterior entropy deficit and spot debt.

**(b) Open mathematics — B-C.** Derive a cofinal arithmetic zero-to-contrast balance that selects the line. Correct accounting can describe either outcome; adaptive conditioning and coarsening do not provide the required independent sign. All reveal costs must remain in the comparison.

Walls 7, 12, 15; O4/O6.

### HJ — Hurwitz reflection

**Established.** The exact prime-2 two-seed residual vanishes iff the parameter is on the line; it agrees with SEC's first-prime seam. Zero-indexed orientation isometries transport the negative Weil obstruction into an even witness. HCF's two-grid signs provide an equivalent global target.

**(a) Known-method work.** Evaluate the residual and apply the reflection formulas at a specified parameter.

**(b) Open mathematics — B-C/B-RH.** Force the residual to vanish, or the corresponding even witness to be nonnegative, from actual arithmetic source input at every Xi zero. The constructed parity/heat witnesses are still divisor-indexed. Functional-equation-even projection alone cannot erase the obstruction.

Walls 4, 12, 15; O3/O6.

### IRK — Rotation-algebra trace

**Established.** Finite-word traces, winding and completed Xi-jet invertibility classifications exist, including nilpotent jets.

**(a) Known-method work.** Reuse those trace calculations and keep the pre-completion source distinct from its completed relation.

**(b) Open mathematics — B-C.** Construct a global arithmetic Poisson/projective lift whose integral analytic count is tied to the correct source defect. Rank plus irrational Chern contribution does not by itself select the divisor. An inverse on off-line completed fibres is a classification, not an arithmetic exclusion.

Walls 5, 12, 14, 15; O6.

### MSC — Möbius–Sonin transport

**Established.** The full squarefree discrepancy has an unconditional critical logarithmic `L²` source; natural strict-right evaluation columns pair to the actual discrepancy moment.

**(a) Known-method work.** Use this existing Hilbert admission. Generic collar transport does not identify it with a different completed Sonin form.

**(b) Open mathematics — B-C.** Prove the source-faithful bridge to a nonnegative Sonin/Weil energy or another sufficient RH sign, preserving the full signed source and divisor/conormal data. Membership in `L²` and faithful evaluation give no such sign. Inverse overlap remains an obligation where that mechanism is used.

Walls 1, 12, 13; O6/O7.

### PCS — Singular co-shift

**Established.** The wall ground and exact shift-plus-defect formulas exist. Finite-prime projections converge strongly but retain norm and ideal gaps.

**Obstruction.** The native shift is non-surjective, its co-shift has a nonzero kernel, and chronological dilation is invertible. The claimed full-carrier isometric identification is obstructed; it is not unfinished Mellin-isometry work.

**(a) Known-method work.** Reuse the correct Mellin/dilation identities with the nonzero defect retained.

**(b) Open mathematics — B-C.** prove source-natural wall-class annihilation while preserving the forward mode. Any new PCS–CTF bridge must specify a smaller carrier, quotient or defect-bearing intertwiner and prove that it retains the needed RH information.

Theorem source: [carrier obstruction](../../../formal/GaloisForLFunctions/RHTower/PCSChronologicalDilationCarrierObstruction.lean).

Walls 7, 14, 15; O6/O7.

### PTR — Photonic source

**Established.** Finite lossless stacks are real-rooted. The converse Xi approximation uses unknown Xi zeros in the stack impedances, so it is not an independent producer. The continuum Poisson port has norm/Calkin distance one from identity at every positive depth gap.

**(a) Known-method work.** Use the finite stack and port calculations. Combining existing cosine constructions does not remove their source dependence or operator gap.

**(b) Open mathematics — B-C.** Construct a prime-faithful continuum port before inserting the desired divisor, with a proved faithful transfer limit to Xi; or prove an independent zero-loss theorem in the actual continuum topology. Finite local ports and fixed-depth handoffs are failed subclasses, not universal bans on physical realizations.

Walls 5, 12–15; O6/O7.

### RFHM — Support grade

**Established.** Exact entropy/survival accounting and the full synchronized Gamma–theta source exist over all finite prime supports, phases and unbounded Mellin grades. Forward creation and strong exhaustion are established.

**(a) Known-method work.** Specialize the synchronized source and its finite-grade identities to a specified support and phase.

**(b) Open mathematics — B-C.** Find a source-defined phase/depth/compound law that breaks the relevant inverse covariance and proves wall orientation. Reversible sewing and forward creation alone permit the unwanted counterpart. Entropy identities are bookkeeping until an independent arithmetic inequality selects a direction.

Walls 7, 12, 15; O6.

### SC — Stokes/Witt–Krein

**Established.** Rigged fibres and common-null-set Fourier reconstruction exist; canonical polarization is wall-singular. Native Witt/Selberg coordinate algebra is available elsewhere in the corpus.

**(a) Known-method work.** Reuse finite coordinate conversion where its definitions agree. An algebra isomorphism alone is not a positive arithmetic polarization.

**(b) Open mathematics — B-C.** Construct a source-fixed cross-fibre indefinite restriction/index that selects the critical wall, with its singular boundary under control. A chamber-constant invariant or positive majorant chosen after the desired sign does not do so.

Walls 12, 14, 15; O6.

### SEC — Adjacent prime seam

**Established.** Essential norm equals seam jump. At the stated factorial-Fock time, an off-line parameter has a nonzero boundary-pole residue; boundedness at every actual Xi zero is an RH criterion. Asymptotic smallness across large primes is already automatic.

**(a) Known-method work.** Use the exact seam/jet formulas. Finite-prefix discrepancy recovery does not establish equality of endpoint charges.

**(b) Open mathematics — B-C/B-RH.** Derive exact eventual compactness or the required factorial-Fock jet boundedness from arithmetic input. The indexed divisor test does not supply its own boundedness. Replace neither exact zero by asymptotic smallness nor an infinite jet condition by finitely many jets.

Walls 4, 12, 14, 15; O3/O6.

### W1C — Clifford–Dirac / centred Lee–Yang

**Established.** Finite ferromagnetic Lee–Yang and Hermitian-pencil real-rootedness are available. The bare proposed operator lacks the required point spectrum/compact resolvent; finite local Euler-pencil identification is obstructed.

**(a) Known-method work.** Apply the finite-spin theorem and calculate the density/centering constraints for specified couplings.

**(b) Open mathematics — B-C.** Construct arithmetic couplings whose centered slow-field law converges to Riemann's measure, or a faithful arithmetic scattering denominator with the right domain and density. Interaction and limit fidelity are mathematical construction problems. Postulating that convergence effectively supplies the missing producer; finite ferromagnetism does not prove it.

Walls 5, 12–15; O6/O7.

### WBF — Source certificates

**Established.** Abstract genealogy Gram/determinant theorems classify bounded scalar streams and expose finite-prefix versus completed Calkin gaps. Their definitions contain no primes, zeta or Xi.

**(a) Known-method work.** Apply the scalar theorem to an explicitly supplied stream. “Check small prime levels” is not yet a defined arithmetic task for this framework.

**(b) Open mathematics — B-C.** Define the arithmetic certificate stream, prove depth-uniform completion and establish faithful landing on Xi/Weil positivity. Abstract nonemptiness or magnitude recovery neither identifies the stream nor supplies its sign. Both the arithmetic source and its RH implication remain unconstructed.

Walls 6, 12, 14, 15; O6/O7.

### PM–PW-B — Physical cusp forcing, embedded candidate

**Established.** Retarded responses, contact identities and positive-damping admission exist for each `q : XiZeroCopy`. Principal response channels have polynomial growth. The Eisenstein value factors through both zeta and another L-function, so its vanishing does not isolate zeta by itself.

**(a) Known-method work.** Reuse these source-contact and fixed-damping identities with their actual indexing. No missing physical integral is automatically a routine global estimate.

**(b) Open mathematics — B-C.** Give an independent arithmetic source formulation and a complete small-damping energy ceiling; prove that the contact action actually reaches the optical-magnitude/ordered-cap/all-divisor-extinction receiver. Admission for every fixed `c>0` does not control the required `c→0⁺` behavior. Removing zero indexing and proving the receiver landing are substantive construction obligations.

Walls 1, 7, 12–15; O6/O7.

## 5. The 15 hard constraints

These walls have different logical roles: some are RH-strength targets, some exclude a particular mechanism, and some specify what a proposed construction must preserve. A successful route must resolve the walls it encounters; it need not construct every optional alternative. The established column describes available work, while the final column identifies the remaining research and the limit of each obstruction.

| Wall | Mathematical obstruction | Established results and known-method applications | Open task and scope |
|---|---|---|---|
| **1. Square-root barrier** | The exact global Möbius/prime-error receivers reach RH strength. Known auxiliary estimates in the corpus miss that exponent or sign. | Exponent/Abel transfers, restricted cancellation and exact source decompositions exist. | **B-RH:** critical cancellation. A fixed exponent between `1/2` and `1` is meaningful partial progress. Do not infer every proof must explicitly estimate the same prime sum; see the 2026 claims in §7. |
| **2. Jensen gap** | A square-mean upper bound need not establish the required logarithmic-mean equality/outer factor. | BSY, mollifier and distance criteria identify the gap; finite computations and changes of coordinates are available. | **B-RH:** establish the exact equality or approximation floor. A sufficiently sharp moment argument with proved equality control is not ruled out merely because it uses moments. |
| **3. Local clustering** | Particular localized detectors lose control when the relevant microscopic window contains a costly cluster. Global density alone does not control each selected window. | Power-sum identities and cluster-aware receivers survive. |

**(b) Open mathematics — B-C/B-RH.** a quantitative cluster estimate or a detector that controls clusters collectively. No universal theorem says every RH proof must first improve a prescribed microscopic count. |
| **4. Shift/axis threshold** | Forward shifts and heat flow only give sign beyond their proved strip/time threshold. | Exact strip contraction and finite/fixed-time criteria exist. | **B-RH:** reach the actual critical parameter with all tests. Positive-shift construction or forward smoothing is not uniform control at zero shift/time. |
| **5. Missing Frobenius geometry** | A function-field proof cannot be transplanted without the arithmetic object, trace identity and positivity/purity input it uses. | Existing function-field machinery is reusable once those hypotheses are met. |

**(b) Open mathematics — B-C.** construct an arithmetic geometric realization. Neither Frobenius nor a field over `F₁` is proved necessary for every RH proof. This is an optional architecture, not an additional universally necessary conjecture. |
| **6. Probability cone** | Absolute-convergence Euler-product positivity does not automatically persist in the critical strip. | Finite products and genuine probability representations in their convergence domains are available. | **B:** construct the required strip representation or bound by independent input. Analytic continuation preserves analytic identities, not positivity automatically. |
| **7. Almost-all versus every case** | Typical phases, mean-square control and density-one statements leave the exceptional function/height the receiver must exclude. | Finite return sets and unconditioned distribution laws are useful inputs. | **B:** prove the needed conditioned/uniform bound or separately exclude the remaining exceptions. The failure is a quantifier gap, not a prohibition on averaging methods. |
| **8. Admixture rigidity** | In the fixed full zeta Weil problem, a positive weight is forced to be `Λ`; small admixture cannot evade the same constraint. | Exact uniqueness and defect identities survive. | **B-RH:** positivity of actual `Λ`. The full cone is either empty or the prescribed point according to RH; uniqueness does not prove nonemptiness. Changed archimedean/polar data define a different problem requiring comparison. |
| **9. Temperedness/data fidelity** | Weak analytic axioms admit shifted-zeta or Beurling countermodels. | They identify which particular hypothesis packages do not distinguish zeta. | The shifted pair changes poles/completion as well as coefficient size. It does **not** prove temperedness is the sole missing axiom, or that every possible proof must isolate it in the same way. Keep exact zeta data. |
| **10. Oscillation and transport** | A saving for an oscillatory sum is not automatically a saving for the actual zero-detecting sum after changing phase, weight or contour. | Exact transport formulas, finite Fourier identities and restricted bilinear bounds exist. | **B:** prove the transported estimate with residues, stationary regions and scale dependence retained. The wall does not forbid all linear methods or all use of oscillation. |
| **11. Node criticality** | The specified prime-blind positivity criterion requires every prime-power node; generic density or two-moment information misses arithmetic incidence. | Exact node criticality, valuation clocks and sharp finite moment cones are established. | **B-RH:** source sign on the full required blind class. Distinguishing `4` from `6` is progress in information, not proof of positivity. Do not extend a theorem about this cone to every RH representation. |
| **12. Forced dual measure** | Full positivity has rigid dual spectral consequences and can have near-null directions; an independently constructed certificate is missing. | Duality, uniqueness, negative-index and capacity descriptions are available. | **B-RH:** construct/prove the certificate from arithmetic. A measure forced to equal the zero measure is **not circular merely for that reason**. Circularity is assuming the positivity/location needed to construct it. An inequality proof need not first present a separate Hilbert–Pólya operator. |
| **13. Cone mismatch** | Pointwise nonnegativity and positive-definite autocorrelation are different cones; one cannot substitute for the other. | Explicit two-way witnesses and restricted collar bounds are established. The blind nonnegative theorem bounds the measure of the positivity set within its specified class. | **B:** transfer the required complete-form sign. The measure bound does not bound arbitrary support diameter. Copositivity is not generally PSD; sign-changing odd tests remain essential. |
| **14. Size/topology law** | Under the specified spectral-shift comparison, a trace-class perturbation cannot supply a nonintegrable counting discrepancy. Several finite ports have stronger model-specific failures. | Nonintegrability and native strong/norm/trace distinctions give precise size constraints. |

**(b) Open mathematics — B-C.** a faithful realization in a compatible topology. This does not exclude every compact-resolvent operator, every regularized trace, or every arithmetic trace-class convolution. Different operators and normalizations must not be conflated. |
| **15. Support versus generic positivity** | Positive zero currents and positive-definite theta transforms can coexist with off-line zeros. | Exact divisor counts and squared-displacement detectors survive loss of odd orientation. | **B:** an independent bound forcing the relevant support/defect to the line. A statistic need not change sign under reflection to detect nonzero displacement; a nonnegative even defect forced to zero can suffice. |

These constraints do not establish that an RH proof must be nonlinear, singular, noncompact, Frobenius-like, or outside existing mathematics.

## 6. Supporting programmes: established results and open gaps

### 6.1 BVI/PM: complete weighted energy

For the literal interior prefix `I_ε(n)=pmBezoutInteriorPrefix ε n`, the sufficient receiver is

\[
\forall\delta>0\;\exists\varepsilon\in(0,\delta)\;\exists B_\varepsilon<\infty\;
\forall T\ge1:\qquad
\sum_{n=1}^{T}\frac{I_\varepsilon(n)^2}{n(n+1)}\le B_\varepsilon.
\]

This is the criterion `riemannHypothesis_of_pmBezoutInteriorPronicEnergy_bounded` in the [receiver source](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean). The unconditional bound holds for `ε≥1/2`. The constant may grow as `ε↓0`, but must be independent of the horizon.

The [five-component calibration](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/CompletePronicVaughanCalibration.lean) expands the whole energy into 25 ordered Gram terms. It imports an existing bound of order `n^(1−ε)/(log n)^4` for the centered source. Squaring and dividing by the pronic weight gives a majorant of order

\[
\frac{n^{-2\varepsilon}}{(\log n)^8},
\]

which is nonsummable for `0<ε<1/2`. **This disproves the usefulness of that majorant for summability, not boundedness of the actual energy.** The active-boundary energy difference is absolutely summable. No horizon-uniform bound for the complete source energy is established in the required small-damping regime.

A concrete further research target is a dyadic estimate for the actual mixed Gram sum cancelling the diagonal up to a summable residual. That is an arithmetic producer target. A change of signs in abstract components shows diagonal information is insufficient, but is not a second Möbius source and not a universal parity no-go.

### 6.2 BiScale: finite recovery and graph-error control

Mixed quadratic prime-anchor observations recover the specified finite coordinates up to global sign; arithmetic phase selects the sign. A terminal Möbius taper anchor is `−w(p)/p`; for BV it is live exactly when `p<X`. A highest-dyadic anchor is zero on squarefree-supported rows once it is a nonsquarefree power: that recovery chart does not apply to those rows.

For literal finite synthesis, the [complete graph-error theorem](../../../formal/GaloisForLFunctions/BiScaleUncertainty/PrimeAnchorCompleteGraphError.lean) bounds the signed-energy error by

\[
K^2+2K\|F_{\rm reference}\|.
\]

At fixed cutoff, the exhibited inversion bound costs `B_k N√N H_N` times the coordinate-error scale, together with anchor loss; the reference norm also grows. These are already proved quantitative estimates. **What remains is obtaining actual observation errors small enough to pay these losses in the required changing-cutoff regime, and a faithful receiver comparison.** Recovery alone does not sign the recovered energy.

The tightness counterexample has bounded complete graph norm, vanishing diagonal cost and no Cauchy subsequence. Its positive survivor is relative compactness at fixed cutoff under a bound on literal total amplitude, without a center restriction. This does not provide a cofinal compactness theorem when the cutoff and amplitude grow.

### 6.3 APT: prime sign, translated-tent approximation and model detection

The [negative-singleton theorem](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeSingletonNegative.lean) proves

\[
P_\infty\le -\frac{4\log2}{390\pi^4}<0.
\]

The bound includes the entire harmonic tail. It is not an isolated negative harmonic masquerading as the full prime channel. The full Weil expression subtracts that channel, and also contains Gamma and polar terms. This excludes positivity of that prime kernel. It does not supply a negative complete Weil witness.

For finite translated-tent patterns, the [joint approximation theorem](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTranslatedTentApproximation.lean) gives full prime/Gamma/polar error at most `1/(q+1)` by choosing the smoothing index from an explicit coefficient/slope/aperture cost. Every finite pattern parameter may grow with `q`, with its cost included in the smoothing choice.

The [native detector specification](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTentOffLineDetection.lean) uses the same smoothed family to annihilate an entire on-line lattice and give a strictly negative value on the specified lattice-plus-reflected-pair **model**. It retains the full square diagonal and reflection defect, with a positive margin.

**Still open:** positivity on a sufficient actual arithmetic family or a contradiction for an actual off-line zeta zero. Model negativity does not identify the model form with the literal zeta form. The direct **critical-tail** full-form comparison and lattice-diagonal analysis are different, unfinished problems: that critical physical source lies outside the strip covered by the sampling theorem. The bounded-primitive polar endpoint controls one boundary cost; the Gamma cutoff remains uncontrolled. Finite readout decay alone still proves neither blindness nor detection without the complete comparison.

### 6.4 THIM: local correction and primitive small-energy families

Every fixed universal cosh-by-sinh integrated coefficient fails on the specified compact even-profile class. The [obstruction source](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/OddPolarAbsorptionBoundaryAndCompensatedHorizon.lean) retains the exact least nonnegative local mass correction and an exponential confinement law. **Paying that correction with jump energy for arbitrary tests is still open.**

Applying the same cutoff to theta **before** two normalized shifts produces an eventually nonzero compact primitive family with both hyperbolic moments zero and complete original energy bounded in absolute value by a fixed-shift constant times `(n+1)⁻²`. The [primitive-horizon theorem](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/CanonicalOddPrimitiveHorizonBounds.lean) is a positive survivor with all edge and moving-mass errors retained. It proves neither finite-horizon nonnegative sign nor density of the family in all primitive sources. It is not a Nyman approximant merely because its energy tends to zero.

### 6.5 ACT: remainder versus reflected collar

For the shifted source `ω_a`, the [identity](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ShiftedGroundStateOriginFailure.lean) is

\[
E(\Phi\omega_a u)=R_a(u)
-4\int_0^\infty u(x)^2\omega_a(x)\Phi(x)
\bigl(C_a(x)-\sinh(a/2)\sinh(x/2)\bigr)\,dx.
\]

Here `R_a` is the nonnegative folded remainder, and `C_a` is the complete reflected collar. The theorem assumes even compact `C²` `u` and `FoldedAdmissible`. Near-origin collar excess kills the single-shift supersolution proposal; the identity itself survives. To use it for RH, prove the domination inequality and admissible coverage of the full receiving class. The nonnegativity of `R_a` alone does not imply domination of the collar term.

### 6.6 SRT: resolution and selectivity

SquareRootThreshold proves that some isolated off-line models are invisible at fixed resolution. For actual zeta it also gives small-aperture/windowed positivity and eventual single-height positivity for each **fixed** compact profile. The profile-dependent threshold is decisive: this is not uniform all-profile positivity at a common height or aperture.

The open problem is joint profile/height/aperture control that forces every hypothetical off-line zero to become visible. Such a theorem needs an independent arithmetic estimate. Fixed-resolution positivity does not supply it.

## 7. Relevant literature and the remaining gap

Established results and unverified preprint claims have different status. The latter are listed as claims, without using them as proved inputs.

| Source | Result or claim | Remaining gap |
|---|---|---|
| [Clay RH status](https://www.claymath.org/millennium/riemann-hypothesis/) | RH remains listed as unsolved. | Complete RH-equivalent targets remain open. |
| [Báez–Duarte](https://arxiv.org/abs/math/0205003) | Integer-dilate Nyman–Beurling criterion. | The receiver is classical; constructing the required approximation is the open part. |
| [BSY criterion proof](https://arxiv.org/abs/1306.0856) | Logarithmic critical-line integral equality characterizes RH. | Merely proving a second-moment estimate is a different statement. |
| [Griffin–Ono–Rolen–Zagier](https://arxiv.org/abs/1902.07321) | Fixed-degree eventual Jensen hyperbolicity and specified low-degree results. | Do not erase the distinction between fixed degree and the full all-degree criterion. |
| [Rodgers–Tao](https://arxiv.org/abs/1801.05914) | Standard de Bruijn–Newman constant is nonnegative. | The opposite bound needed for RH is not obtained by this theorem. |
| [Suzuki](https://arxiv.org/abs/2206.03682) | Screw-function equivalents and partial unconditional results. | A new screw formulation is not by itself a new sign producer. |
| [Frank–Lenz–Wingert](https://authors.library.caltech.edu/records/5ke56-ymh17) | Ground-state transforms and Allegretto–Piepenbrink-type theory for suitable nonlocal Dirichlet forms. | Ground-state criticality has established parent theory. Applicability to the complete folded arithmetic form must be proved. |
| [Quasi-RH at `7/8`](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf), [quasi-RH at `11/12`](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf) | The manuscripts assert zero-free half-planes `Re s>7/8` and `Re s>11/12`, respectively, for classes including zeta. | Unverified preprint claims. Even assuming either theorem, the interval down to `1/2` remains unresolved. |
| [Ordinary two-point correlations, 24 September 2026](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) | The manuscript claims a logarithmic saving for fixed affine Liouville pairs, and qualitative ordinary correlations for the stated nonpretentious class. It explicitly disclaims growing-affine-coefficient uniformity. | Unverified preprint claim. Its stated conclusions do not supply the complete moving-weight small-damping BVI estimate. |
