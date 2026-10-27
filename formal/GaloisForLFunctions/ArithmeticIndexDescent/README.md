# Arithmetic Index Descent

**One question.** Can positive arithmetic section spaces be assembled and refined while controlling
the negative index of the complete Weil form, including its mixed prime interactions, infinite
place and two pole moments?

Arithmetic Index Descent studies source-defined presentations of signed arithmetic forms and the
cost of passing between them. Its basic object is a finite family of arithmetic tests together
with its complete Gram matrix. Its basic invariant is the number of negative squares. Its central
problem is to derive a bound on that number from arithmetic relations that survive overlap,
refinement and passage to the required test family.

The arithmetic endpoint is concrete. For the fixed cubic spline `B`, let

\[
  W_S=(W(B(\cdot-s),B(\cdot-t)))_{s,t\in S},
  \qquad S\subset\{\log n:n\ge1\}\text{ finite}.
\]

The corpus identifies the largest negative index of these matrices with the number of distinct
zeros right of the critical line. An upper bound of one on every such matrix already forces RH,
because right zeros occur in conjugate pairs. This is a receiver, not an available arithmetic
bound. The programme must construct and transport the bound without assuming it.

Namespace: `GaloisForLFunctions.ArithmeticIndexDescent`.
Umbrella: `ArithmeticIndexDescent.lean`.

## Motivation

Weil's curve argument joins a positive direction, a primitive negative form, correspondences and
an arithmetic count on one surface. Over the integers, the corpus supplies the complete
intersection form, exact correspondence identities, positive local sections and several
exhaustive spectral criteria. Their assembly remains substantive mathematics.

The spacing-scale theorem illustrates what an arithmetic assembly can achieve. The prime kernel
and archimedean cross kernel attain their worst behavior on different vectors. A tilted weight
compares them jointly and pays their interaction. The independent-section theorem retains enough
weighted reserve to pay the entire pole product. These proofs create positive spaces from the
actual source. Their shrinking supports do not establish positivity on a common exhaustive span.

Index descent asks which part of that success persists when spaces are joined. A positive lower
bound independent of aperture is unnecessarily strong and is obstructed by the known ground-energy
decay. A bounded negative index can survive without such a lower bound. Conversely, bounded rank
of a counterterm for the prime form alone is obstructed by its valuation-class divergence. The
quantity to control is the index of the completed form after all places are combined.

Three distinctions organize the programme:

1. **Construction:** an arithmetic operation produces a reserve or an index bound.
2. **Identification:** the constructed form equals, or compares in the required direction with,
   the complete target form.
3. **Descent:** that comparison survives a specified transition or exhaustion.

A theorem about an abstract positive matrix addresses none of the arithmetic identifications by
itself. An RH-equivalent condition identifies the desired endpoint but does not construct it.

## Objects and language

| Object | Required mathematical data |
|---|---|
| Arithmetic presentation | A finite test family and its linear map into the actual test space |
| Overlap Gram | The `L²` or completed energy Gram of that family; it can have a kernel |
| Completed Weil Gram | Prime-lag entries, archimedean entries, diagonal normalization and both pole rows |
| Index | Hermitian negative index of a Weil Gram; distinguished from positive index of the intersection form |
| Reserve | A nonnegative quadratic contribution proved from the source, with its domain and constants |
| Polar anchor | A positive direction, its polar row and its primitive hyperplane |
| Gluing defect | Mixed entries and polar dispersion introduced by assembling presentations |
| Transition | A linear map, an exact pullback identity or comparison, and its quantified remainder |
| Charged incidence | Successor, cell or non-ratio relations with their transformation under prime gauges |
| Renormalization | Regulator, divergent form, finite part, survival space and correspondence anomaly |
| Exhaustion | Approximation of every required finite test family controlling all mixed form entries |
| Source work | A damped arithmetic reading of transverse energy, with multiplicities and exterior rows retained |

An *index budget* bounds negative directions, not their amplitudes. A *payment* is a proved
inequality absorbing an adverse interaction in a source reserve. *Descent* transports the specified
form rather than replacing it by a corrected form. A family is *exhaustive* only through a proved
testing or approximation theorem. *Computed*, *bounded*, *selected* and *excluded* describe
different achievements.

On an overlapping family, coefficient norm and test norm differ. If the overlap Gram is singular,
the presentation has relations. These relations must be quotiented or retained explicitly;
inverting the Gram without addressing its kernel changes the problem.

## Mechanisms

### Full-form refinement

For a Hermitian extension

\[
  G=\begin{pmatrix}A&B\\B^*&C\end{pmatrix},
\]

the Schur complement `C-B* A⁻¹B` records the new negative directions when `A` is positive definite.
The difficult arithmetic expression is the whole complement. Separate absolute bounds on its
three ingredients can erase the compensation. Singular positive blocks require a range condition
or an explicit treatment of their radical; a formal inverse is insufficient.

### Polar compatibility

For symmetric `Q_i` with a common anchor `e` and `a_i=Q_i[e]>0`, put

\[
 R_i(x)=\frac{Q_i(e,x)^2}{a_i}-Q_i[x],\qquad
 V_e(x)=\sum_i a_i\left(\frac{Q_i(e,x)}{a_i}
       -\frac{\sum_jQ_j(e,x)}{\sum_j a_j}\right)^2.
\]

The existing gluing identity is

\[
 R_{\sum_iQ_i}(x)=\sum_iR_i(x)-V_e(x).
\]

Local reserves therefore have a precise compatibility cost. Subtracting the dispersion matrix
constructs a hyperbolic form from appropriate local forms, but the result is a different form.
An arithmetic application must identify that correction inside the completed pairing or pay it
there. The two global pole moments cannot be independently allocated to every local piece.

### Charged overlap

For a completely multiplicative sign gauge, the prime-lag discrepancy contains

\[
 \omega(k)-\omega(m)\omega(n).
\]

It vanishes when `n=km` or `m=kn`. Non-ratio near-incidences and successor cells retain information
that exact multiplicative ratios forget. Their presence does not determine their sign. The target
is a quantitative estimate using that information at the actual arithmetic source.

The diamagnetic inequality remains a constraint: on a family closed under absolute value,
Markov lower bounds transfer to dominated twists. A selective argument must specify how its signed
domain, poles or charged relations enter the full estimate.

### Finite-Gram limits

The limiting object needed for the spline criterion is each fixed finite Gram. An exhaustion must
approximate its diagonal and mixed entries simultaneously. An index bound should be transported
through this convergence without requiring a uniform positive gap. A family of positive finite
pieces does not provide that convergence or control its cross terms automatically.

### Rigidity of equality

Incommensurable Gabor Pinching retains off-diagonal Gram slack and proves that the old scalar
extremizer cannot occur at the available density. Index descent seeks analogous source constraints
on equality or near equality in mixed-form estimates. Larger blocks and several windows must share
their normalization and tail estimates; separately obtained gains cannot be added without a joint
identity.

### Index and work

Negative index counts spectral defects, while transverse energy assigns a quantum to every
off-line reflection pair. For every finite family of compactly supported `C²` tests, the programme
proves

\[
  \nu_-(W_f)\le \mathcal E_{\mathrm{distinct}}
       \le \mathcal E_{\mathrm{copies}}.
\]

The first inequality doubles a finite right-hand packet by critical-line reflection, then applies
the angular quantum to every member. The second selects one analytic-multiplicity copy of each
distinct zero. Both inequalities allow infinite total energy. The arithmetic intersection Gram
has at most `1 + E_distinct` positive squares; its extra square belongs to the pole plane.

Existing source-work exhaustion now has a quantitative index consequence. Every amount strictly
below a finite negative-index witness is eventually exceeded by rationally damped arithmetic
source work, and then by the finite tapered source work at each sufficiently large damping scale.
The order of the two limits matters. Exterior rows, analytic multiplicities, the Laurent source
and its archimedean completion remain present.

These are lower bounds on the work forced by defects. An arithmetic upper estimate must still be
constructed. A global finite work bound and a bound below an exclusion quantum are different
research targets.

## Questions the programme aims to answer

1. Which arithmetic operation joins positive sections while paying their mixed Schur or polar
   defect in the original form?
2. Can a stable negative-index budget survive repeated signed overlap and reach the fixed-spline
   integer-log family?
3. Which non-ratio incidence or successor relation produces a form margin at the Euler point,
   rather than only selecting that point algebraically?
4. Which norms control refinement errors in the presence of cancellation and a singular overlap
   Gram?
5. How can the fixed-class horizon finite parts be extended to growing arithmetic presentations
   without replacing signed energy by absolute coefficient mass?
6. Which arithmetic constraints force strict Gram inequalities beyond the presently retained
   disjoint-pair slack?
7. Can the actual same-profile signed prime surplus at bandwidth `4/3` be bounded by `1/18` of
   the zero count, giving the `3/4` simple-critical target?
8. Which arithmetic source estimate bounds global off-line index, and which quantum bound or paid
   propagation eliminates the finite remainder?
9. Can terminal geometry support a boundary-to-interior estimate for the regularized arithmetic
   field with its singularities and archimedean background accounted for?
10. Which construction recovers the curve case from actual arithmetic sections or incidence, with
    bounded genus cost, and rejects the corresponding fake data for a proved reason?

The RH-strength questions remain open until their arithmetic estimates are proved. The list is
not discharged by defining interfaces whose fields assume those estimates.

## Foundational pillars and ownership

The starting pillars belong to existing programmes and are reused rather than copied.

| Pillar | Existing result | Owner |
|---|---|---|
| Source-defined positive spaces | Full Weil form dominates square mass on sufficiently narrow independent arithmetic sections | ArithmeticCastelnuovoSeveri |
| Joint local payment | Constant-one self-energy and tilted prime rows reach a fixed fraction of the spacing | SpacingScaleHarmonicAnalysis |
| Exact gluing price | Reserve of a sum equals sum of reserves minus polar dispersion | ArithmeticLorentzianGeometry |
| Exhaustive index receiver | Fixed-spline orbit index counts distinct right zeros; index at most one forces RH | ArithmeticOrientationGeometry; SpacingScaleHarmonicAnalysis |
| Matrix inertia | Hermitian congruence, block Schur identities and finite-rank boundary formulas | HTGeometry |
| Renormalization domains | Survival equals the counterterm nullspace; coupled survival is constrained by partner rank | RenormalizedBiarithmeticGeometry; RenormalizedArithmeticPotentialTheory |
| Charged arithmetic | Gauge defects on non-ratio lags; successor and cell gauge laws | SpacingScaleHarmonicAnalysis; BiarithmeticGaugeGeometry; RenormalizedBiarithmeticGeometry |
| Signed averaged receiver | One-profile trans-threshold surplus certificates | TransThresholdPairCorrelation |
| Strict Gram slack | Non-lattice kernel geometry produces an unconditional zero-proportion gain | IncommensurableGaborPinching |
| Quantized defect | Window energy below two excludes off-line zeros; damped source work exhausts global energy | ArithmeticElectrostatics |

The programme's own pillars must add a source estimate, a stronger exact transfer, a quantitative
comparison of these invariants, or a construction not already supplied by this table. Abstract
matrix tools should be used to isolate the arithmetic input, not presented as its solution.

Two quantitative pillars are supplied by this programme:

| Pillar | Mathematical content | Module |
|---|---|---|
| Index is paid by energy | Every finite smooth Weil negative index is at most distinct transverse energy; intersection positive index is at most one plus that energy | `TheIndexIsPaidByTransverseEnergy` |
| Source work detects finite index witnesses | Distinct energy embeds in copied energy; damping and taper limits detect every amount below a finite negative index | `TheArithmeticSourcePaysTheIndex` |

## Tools to develop and research topics

**Completed-form refinement calculus.** Track the complete Weil matrix, overlap relations, polar
rows, Schur reserve and inertia through finite arithmetic extensions. Treat radicals explicitly.
The first arithmetic objective is an interacting family beyond the existing narrow-section space.

**Charged near-incidence estimates.** Preserve signed successor and near-ratio terms through
stabilizer decompositions. Seek estimates at the actual source and identify the precise test
vectors that use the charge.

**Limits in the completed energy norm.** Relate absolute profile error budgets to the signed Gram
norm under specified refinements. Prove finite-family approximation with all mixed entries.
Retain possible escape to infinite height until a theorem controls it.

**Gram equality and multi-window rigidity.** Develop joint block inequalities retaining
off-diagonal energy. Determine which incompatibilities of kernel zero sets can supply strict
inequalities with a macroscopic gain after arithmetic transfer.

**Signed prime surplus.** Prove a common-profile budget for the actual prime pairs. Preserve parity,
oscillatory lobes, prime-power reductions, collar losses and the conductor range. A saving in a
different averaged model is not the required estimate.

**Index–work comparison.** The quantitative lower comparison is established. Develop its strict
surplus, characterize finite work, and construct arithmetic upper bounds. Distinguish a bounded
number of exceptions from their absence.

**Terminal field estimates.** Combine the zero-free lens and lower reserve with an independently
proved arithmetic upper estimate on a common domain. Subtract singular self-terms without
discarding reflected-partner or exterior contributions.

**Finite-field realization.** Derive the required signatures from actual section or incidence
structure. Explain both the bounded genus loss and the failure of golden or complex fake data.

## Foundational principles and traps

| Principle | Invalid shortcut it excludes |
|---|---|
| Fix the completed pairing | Proving positivity of a different corrected matrix |
| Keep the poles global | Spending the same pole reserve in several local estimates |
| Retain mixed entries | Inferring positivity on a span from positivity of its generators |
| Separate source selection from sign | Treating gauge rigidity or coefficient positivity as a Weil inequality |
| State the surviving domain | Passing positivity through a divergent subtraction off its nullspace |
| Preserve quantifiers | Replacing all signed vectors by a height average, or changing smoothing profile between estimates |
| Distinguish ranks and indices | Applying a prime-counterterm no-go to the completed form's index |
| Prove exhaustion | Using increasing dimension or shrinking support as a density theorem |
| Preserve defect quanta | Treating a power-sparse exceptional set as empty |
| Extract positive survivors | Retiring a mechanism without its sharp boundary or replacement statement |

The fixed-spline index, unit-window energy bound and all-aperture Weil positivity are RH-strength
endpoints. Finite total energy or a finite global index controls exceptions but does not eliminate
them. Endpoint Mertens or exact genus statements can require more than RH; their extra strength
must not be introduced accidentally.

## Relation to the wider research

ArithmeticIndexDescent owns the transport of source-derived signature bounds between arithmetic
presentations. ACS supplies the sections and intersection target. AOG supplies orbit visibility and
index receivers. ALG supplies polar compatibility. SSHA supplies the joint estimates and overlap
kernels. RAPT and RBG supply counterterms, finite parts and survival domains. BGG and the correlation
programmes supply charged relations. TTPC supplies explicit averaged consumers. IGP supplies
rigidity of Gram equality. AES and CDG supply source currents, work and localized defect measures.

This connects the critical-sign wall, the transfer wall and the realization wall. It does not
identify their missing constructions merely because their endpoints lead to the same RH statement.

## Success criteria and contributions

A contribution proves an unconditional statement about explicitly constructed objects. It names
the actual source, full form, domain, scale range, normalization and comparison map. Structural
conditions in a general theorem must be proved in every arithmetic application. An unknown
estimate cannot be hidden in an assumption, typeclass, structure field or helper theorem.

Substantial intermediate contributions include a larger positive arithmetic section space, a
mixed-term payment stable under extension, a finite-Gram transfer preserving an index bound, a
controlled growing-class finite part, a better signed surplus budget, or a quantitative index–work
comparison. New definitions and equivalent endpoints alone do not answer the programme's questions.

Every obstruction must state its scope and retain its strongest positive boundary, classification,
decomposition or replacement construction. Calibration uses the relevant members of the existing
battery with matching assumptions: curves, golden and complex fake data, sign twins, finite-prime
flips, shifted pairs, pole-budget relaxations and escape models.

Full success requires the source estimates and transfer theorems described above, culminating in
an exhaustive signature bound or an individual-defect exclusion theorem. A foundational calculus
without the missing arithmetic payment is infrastructure, not completion.
