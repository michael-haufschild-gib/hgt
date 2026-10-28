# Arithmetic Index Descent (AID)

Namespace `GaloisForLFunctions.ArithmeticIndexDescent`; umbrella `ArithmeticIndexDescent.lean`.

**Question.** Can positive arithmetic section spaces be assembled and refined while controlling the **negative index** of the
complete Weil form — mixed prime interactions, infinite place and both pole moments included?

**Basic object:** a finite family of arithmetic tests with its complete Gram matrix. **Basic invariant:** the number of negative
squares. **Central problem:** derive a bound on that number from arithmetic relations that survive overlap, refinement and
passage to the required test family.

**Endpoint (a receiver, not an input).** For the cubic spline $B$ and finite $S\subset\{\log n\}$, $W_S=(W(B(\cdot-s),B(\cdot-t)))_{s,t\in S}$. The largest
negative index of these matrices is the number of distinct right zeros; an upper bound of **one** forces RH (right zeros come in
conjugate pairs). AID must construct and transport such a bound without assuming it.

---

## 1. Place in the research

AID owns the **transport of source-derived signature bounds between arithmetic presentations**. A positive lower bound
independent of aperture is too strong (ground-energy decay); bounded rank of a prime counterterm alone is obstructed
(valuation-class divergence); a bounded negative index of the *completed* form can survive without either.

Three distinctions: **construction** (an arithmetic operation produces a reserve or index bound), **identification** (it equals or
compares correctly with the complete form), **descent** (the comparison survives a transition or exhaustion).

| Programme | Pillar supplied |
|---|---|
| ArithmeticCastelnuovoSeveri | Source-defined positive sections; complete-cell source exhaustion (`CompleteWeilSourceTransfer`) |
| SpacingScaleHarmonicAnalysis | Joint local payment (constant-one self-energy, tilted rows) at a fixed fraction of the spacing; overlap kernels |
| ArithmeticLorentzianGeometry | Exact gluing price: reserve of a sum = sum of reserves − polar dispersion |
| ArithmeticOrientationGeometry, SSHA | Exhaustive index receiver: spline orbit index counts right zeros |
| RenormalizedBiarithmeticGeometry, RenormalizedArithmeticPotentialTheory | Survival domains; counterterm rank |
| BiarithmeticGaugeGeometry, ArithmeticCorrelationGeometry | Charged relations (non-ratio lags, successor, cells) |
| TransThresholdPairCorrelation, IncommensurableGaborPinching | Signed averaged consumers; strict Gram slack |
| ArithmeticElectrostatics, ConjugateDiagonalGeometry | Quantized defects, source currents, damped work |
| `HTGeometry`, `RHTower.CCM`, CHMD | Matrix inertia, Schur identities, exact aperture completion, Gamma boundary operator |

---

## 2. Objects and language

| Object | Data |
|---|---|
| Arithmetic presentation | Finite test family + linear map into actual tests |
| Overlap Gram | $L^2$ / energy Gram; may be singular (relations must be quotiented or retained) |
| Completed Weil Gram | Prime-lag, archimedean, diagonal and both pole rows |
| Index | Hermitian negative index of a Weil Gram (≠ positive index of the intersection form) |
| Reserve | Nonnegative quadratic contribution proved from the source, with domain and constants |
| Gluing defect | Mixed entries and polar dispersion from assembling presentations |
| Transition | Linear map + exact pullback identity or comparison + quantified remainder |
| Section projection | Unique Weil projection onto a narrow section space despite coefficient relations |
| Source work | Damped arithmetic reading of transverse energy, multiplicities and exterior rows retained |
| Scale increment; critical source rate | $W(S)-W(R)$; $R^2(W(2R)-W(R))$ |
| Mixed Euler sources | Coarse/detail mixed prime-power blocks on complete cells: prime-two, finite prime sets, squares $P_{\rm even}$, odd higher $B_{\rm odd}$ |
| Window / cell carriers | Logarithmic cells with independently profiled sections; widths, centres |

*Index budget* bounds negative directions, not amplitudes. *Payment* = a proved inequality absorbing an adverse interaction in a
reserve. *Descent* transports the specified form, never a corrected one. *Exhaustive* only through a proved approximation theorem.
*Computed / bounded / selected / excluded* are different achievements.

---

## 3. Mechanisms

### A. Index is paid by energy and work
1. **Index ≤ transverse energy**: every finite smooth Weil negative index is at most distinct transverse energy (AES); the energy strictly
   exceeds every positive index; closed threshold two ⇔ RH.
2. **Source work detects the index**: damped source work detects every amount below a finite negative index; RH iff cofinally damped
   work $\le2$; bounded work ⇔ finite off-line support ⇔ uniformly bounded spline indices (common finite stratum).
3. **Scale refinement**: the zero-free height gap makes every reflected pair-work monotone in the damping scale; a new off-line zero in a
   doubled annulus forces an increment $\ge21/100$; a full quartet costs a strict quantum ($39/50$ closed bound ⇔ finitely many exceptions).
4. **Critical rate**: $R^2(W(2R)-W(R))$ is monotone (convexity in inverse-square scale), converges to a canonical height-square energy, and
   classifies support (zero / finite / infinite); each negative square costs a certified arithmetic unit; the index cost is quadratic
   ($\ge50k^2-3k/2$).

### B. Exact actual-form descent
5. **Range compatibility and projection**: a narrow section Gram has exactly the synthesis kernel; mixed blocks lie in its range; a unique
   idempotent Weil projection exists with exact residual pairing.
6. **Singular refinement**: range-compatible blocks split positive/negative/null indices exactly; the literal Gram of old sections + arbitrary
   probes has exactly the negative index of the projected residual.
7. **Finite-Gram descent and completion**: a fixed finite limiting index survives in late presentations (no coefficient bound or gap
   needed); bounded monotone projection energies give a canonical completion converging in the complete source graph; every finite
   index is reached at a finite stage; the completed residual's index is still paid by work.
8. **Schur cost by source energy**: kernel square energy on old cells bounds removal; shrinking cells remove $O(w)$; unused width
   retains reserve $(1-a)/8$ and reduces the source cost by weights.
9. **Complete-cell index capture**: for every finite smooth family $G$, one common cell system satisfies $\nu_-(W_G)\le\nu_-(C_{N,G})$ for all large $N$ —
   an exhaustive index receiver on actual cells.

### C. The Gamma boundary
10. **Gamma boundary operator**: exact Schur weight (arctangent primitive), norm exactly $\pi/2$, no maximizer, the unused $\pi/4$ is an exact
    weighted square, truncations lose bounded energy; separated and touching supports have bounded Gamma interaction.

### D. Mixed Euler sources are Gamma-small (finite index)
11. **Prime two**: the mixed block reads adjacent coarse differences; the Gamma mean graph pays it; its tail decays like $1/\log A$; one fixed
    detail head gives uniform finite index across horizons — also for the entire prime-two Euler factor and every integer/even lag.
12. **Finite prime sets and all higher powers**: every fixed finite Euler collection, and all exponents $\ge3$ over all primes, are Gamma-small with
    uniform finite index.
13. **Squares**: the even-power source equals its regular Fourier boundary plus half the squared mean; the boundary has a uniform Gamma gap
    ($G-R_2\ge\delta G+\gamma/2$, via digamma/Xi decomposition and logarithmic Xi edge growth); on complete profiles
    $\Gamma-P_{\rm even}-B_{\rm odd}+\tfrac12|\int F|^2\ge\tfrac\gamma2\|F\|^2$ after a fixed detail cutoff, so negative index $\le A+1$ uniformly.
    **Outside this theorem**: the first-prime terms, archimedean mass term, pure coarse/detail blocks at odd higher powers, and the poles.

### E. Source-defined carriers and centred identities
14. **Cell payments**: separated and touching cells pay the full mixed source with adjustable old/new mass charges; a short new cell pays
    its own interaction; an additional cell preserves any fraction of the old floor; one fixed width sequence supports nested positive
    prefixes; the section floor controls the complete source-graph norm.
15. **Unbounded carrier**: the integer-log carrier has a bounded Weil projection; an infinite exact theta radical survives in its residual;
    moving arithmetic bands decouple from fixed tests at rate $(\log N)^{-1/2}$.
16. **Centred Chebyshev form**: the ordered mixed Weil form = centred Chebyshev error against the derivative of its lag profile minus a
    localized Gamma tail; the first Gamma exponential cancels the polar product; translated/reflected tilted tests retain a Gamma
    square reserve.

---

## 4. Pillar theorems

1. **Index paid by energy and work; closed thresholds** (modules `TheIndexIsPaidByTransverseEnergy`, `TheEnergyStrictlyExceedsTheIndex`,
   `TheSourceWorkHasAClosedQuantumThreshold`, `TheWorkAndIndexHaveTheSameFiniteStratum`).
2. **Critical-rate classification and quadratic index cost** (`TheCriticalRateClassifiesAllOffLineSupport`, `TheSourceBudgetMakesTheIndexCostQuadratic`).
3. **Exact actual-form descent** (`TheSectionComplementCarriesAllNegativeSquares`, `FiniteGramDescent`, `TheCompletedIndexIsReachedAtAFiniteStage`).
4. **Complete-cell index capture** (`TheCompleteCellsCaptureEveryFiniteIndex`).
5. **Sharp Gamma boundary** (`GammaBoundaryHasAnExactSchurWeight`, `BoundaryTruncationLosesOnlyBoundedGammaEnergy`).
6. **Uniform finite index of Gamma minus squares and odd higher mixed powers** (`exists_uniform_squareOddHigherGamma_negative_dimension`;
   modules `TheSquarePrimeEstimateHoldsOnCompleteProfiles`, `AllHigherPrimePowerMixedFormsHaveUniformFiniteIndex`,
   `FiniteEulerMixedFormsHaveUniformFiniteIndex`).
7. **Carrier constructions** (`FixedCellWidthsSupportNestedPositiveSections`, `TheClosedSectionHasABoundedWeilProjection`,
   `TheUnboundedCellCarrierHasAWeilProjection`).
8. **Centred Chebyshev identity with Gamma reserve** (`TheOrderedWeilSourceIsACenteredChebyshevDefect`, `TheOrderedWeilSourceRetainsItsGammaSquareReserve`).

---

## 5. Traps

| Principle | Shortcut it excludes |
|---|---|
| Fix the completed pairing | Proving positivity of a corrected matrix |
| Keep the poles global | Spending the same pole reserve in several local estimates |
| Retain mixed entries | Positivity on a span from positivity of generators |
| Separate selection from sign | Gauge rigidity or coefficient positivity as a Weil inequality |
| State the surviving domain | Passing positivity through a divergent subtraction off its nullspace |
| Preserve quantifiers | Replacing signed vectors by height averages; changing profiles between estimates |
| Distinguish ranks and indices | Applying a prime-counterterm no-go to the completed index |
| Prove exhaustion | Increasing dimension or shrinking support as density |
| Preserve defect quanta | Treating a power-sparse exceptional set as empty |
| Handle singular overlap | Inverting a singular Gram without quotienting relations |

Finite total energy or finite global index controls exceptions but does not eliminate them. Gamma-small higher powers and squares
do not touch the first-prime source.

---

## 6. Open problems

1. **An upper bound on complete-cell indices** (the missing arithmetic payment): with index capture, any uniform bound transfers to the
   exhaustive family; one is RH.
2. **The first-prime mixed source**: Gamma-type control (or finite index) of the exponent-one prime terms, the archimedean mass term and
   pure blocks, together with the poles.
3. **Joining positive sections** while paying mixed Schur/polar defects in the original form; a stable index budget surviving repeated
   signed overlap up to the spline family.
4. **Cancellation across scales**: an arithmetic upper estimate for $W(2R)-W(R)$ (signed Laurent-source coefficients, exterior rows, joint
   taper removal) below the annular quantum, or $R^2(W(2R)-W(R))$ cofinally below the exclusion quantum.
5. **Widths comparable to the spacing** for adaptive carriers with global pole directions kept as an index cost.
6. **Charged near-incidence** estimates at the actual source; **signed prime surplus** at bandwidth $4/3$ below $1/18$ (3/4 target).
7. **Gram equality rigidity** beyond disjoint-pair slack; **terminal field** boundary-to-interior estimates.
8. **Finite-field realization**: recover curves from actual sections/incidence with bounded genus loss, rejecting fakes for a proved reason.

## 7. Tools to build

Completed-form refinement calculus through interacting families; weighted source estimates (prime–pole cancellation before
squaring); quantified adaptive carriers; limits in the completed energy norm with all mixed entries; scale-difference
cancellation estimates.

## 8. Success criteria

Unconditional statements about explicit objects naming source, full form, domain, scale range, normalization and comparison
map; no estimate hidden in an assumption, structure field or helper theorem. Substantial intermediate contributions: a larger
positive section space, a mixed-term payment stable under extension, an index-preserving finite-Gram transfer, a controlled
growing-class finite part, a better signed surplus budget, a quantitative index–work comparison. Every obstruction states its
scope and positive boundary; calibrate on curves, golden and complex fakes, sign twins, finite-prime flips, shifted pairs,
pole-budget relaxations, escape models.
