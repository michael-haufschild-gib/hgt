# Arithmetic Lorentzian Geometry

Arithmetic Lorentzian geometry studies how arithmetic constructions produce a quadratic form
with at most one positive square, and how that signature survives composition and passage to a
limit. Its target is the specified intersection form of the scaling surface, including the
infinite place and the pole plane. The Hodge index of that form is equivalent to RH. A useful
construction must therefore explain the origin of its sign, not merely express that sign in
another language.

Its scope includes both constructing individual signature certificates and controlling their
compatibility. Anchors, Schur reserves and polar dispersion quantify that compatibility;
corrected gluing, grouping and linear restriction supply a composition calculus. The arithmetic
question is which source energy pays these costs while retaining the specified pairing.

The guiding analogy with combinatorial Hodge theory is an inductively closed class of objects:
elementary objects have a proved signature; restriction, links and composition preserve it;
the constructed pairing is the pairing of interest. An arithmetic version needs all three
steps. Nonnegative coefficients, connected support and a Frobenius-shaped identity do not by
themselves complete them.

Namespace: `GaloisForLFunctions.ArithmeticLorentzianGeometry`.
Umbrella: [ArithmeticLorentzianGeometry.lean](../ArithmeticLorentzianGeometry.lean).

## Motivation and mathematical target

The corpus has several descriptions of the missing arithmetic sign. Weil positivity, Hodge
index, positive equivariant realization and certain critical cancellation estimates have
receivers that lead to RH. These receivers do not provide the arithmetic input they consume.
Meanwhile, local positive models, gauge rigidity, source currents and finite parts explain
increasingly precisely what a successful input must retain.

ALG asks whether the sign can be produced by an arithmetic construction whose elementary steps
can each be justified. Its language combines the affine monoid of the integers—successor `S`,
dilations `M_p`, and `M_p S = S^p M_p`—with signatures, primitive hyperplanes, links and comparison
of quadratic forms. The monoid supplies operations, not an automatic positivity theorem.

Local Hodge inequalities can fail to combine because their normalized polar rows disagree.
The reserve–dispersion identity makes this failure quantitative: a global signature requires
local reserves to pay the disagreement. This gives the programme a concrete construction
problem—derive that payment from arithmetic—and a way to test proposed local-to-global routes
before passing to an infinite family.

Three problems must remain separate:

1. **Construction:** build a form with a proved signature from elementary arithmetic objects.
2. **Identification:** prove its equality with, pullback relation to, or suitable domination of
   the actual intersection form. Include the Γ-term, the two pole moments and the diagonal.
3. **Exhaustion:** carry the comparison to every required signed test in a topology controlling
   the full pairing.

An abstract Lorentzian model solves only the first problem. A finite positive family solves a
restricted instance. Neither becomes an RH proof without the remaining bridges.

## Objects and language

For a finite real symmetric matrix `Q`, write

\[
 B_Q(x,y)=x^TQy,\qquad Q[x]=B_Q(x,x).
\]

`IsHyperbolic Q` means the reverse Cauchy–Schwarz inequality

\[
 Q[x]Q[y]\le B_Q(x,y)^2\quad\text{whenever }Q[x]>0.
\]

For symmetric matrices this is equivalent to having at most one positive square. The term
*hyperbolic* here describes a quadratic form; it does not assert real-rootedness of an associated
univariate polynomial. `IsLorentzian Q` adds entrywise nonnegativity in the specified coordinates.
That extra condition depends on the coordinates.

The programme uses the following objects.

| Object | Mathematical role |
|---|---|
| Finite test spaces and their actual Gram matrices | Keep the target pairing visible throughout construction |
| Pole plane `⟨H,V⟩`, with `H²=V²=0` and `H·V=1` | Supplies a positive direction and records global degree data |
| Positive anchor `e`, with `Q[e]>0` | Defines the polar row and the primitive hyperplane |
| Polar row `B_Q(e,−)/Q[e]` | Measures the degree normalization seen by a local form |
| Schur reserve `R_Q(x)=B_Q(e,x)²/Q[e]−Q[x]` | Measures the negative energy left after the positive direction is removed |
| Polar dispersion `V_e` and its positive semidefinite matrix `C_e` | Measure the exact incompatibility of local polar rows |
| Corrected assembly `Glue_e(Q_i)=Σ_i Q_i−C_e(Q_i)` | Combines local reserves while preserving the total anchor row |
| Links and symmetric incidence tensors | Encode a local-to-global construction with independently proved local signs |
| Prime ladders, successor maps and logarithmic cells | Supply arithmetic operations and their compatibility relations |
| Gauges with a fixed infinite-place and pole structure | Distinguish changing coordinates from changing the completed arithmetic source |
| Counterterms, finite parts and comparison maps | Record exactly which form and which test space survive renormalization |
| Exhaustions with explicit norms | Specify what a finite signature theorem can reach |

Real quadratic forms and Hermitian forms have distinct APIs. Complex test spaces must retain
conjugation and the relevant Hermitian inertia; a real calculation is not automatically its
complex analogue.

## Foundational principles

**Fix the pairing.** Every arithmetic signature claim must name the full form and its test
space. A positive form manufactured from prime data is insufficient without identification or
comparison in the direction needed by the target.

**Prove local signature from the source.** A link definition cannot contain the desired Hodge
inequality as an unproved field. In a successful induction the links belong to a class whose
signature has already been proved by arithmetic, counting or a valid closure operation.

**Measure compatibility.** Local signatures need not add. Local polar directions can disagree;
overlapping tests have cross terms; separate local regulators can spend the same pole budget
repeatedly. These costs belong in the theorem.

**Separate gauge selection from sign production.** The successor connection and the fixed
archimedean kernel can identify the Euler gauge. This does not establish Hodge index in that
gauge. Conversely, prime-side unitary equivalence can preserve spectrum while erasing the
arithmetic distinction needed by a proof.

**Keep global resources global.** The two pole moments and the positive direction cannot be
allocated independently at every prime. A comparison must show how the allocations recombine.

**Treat the limit as mathematics.** Growing dimension, shrinking support and fixed-scale
overlap are different properties. Prove density or a sufficient orbit criterion in the topology
required by the form. Height-averaged pair correlation does not imply a uniform all-vector
inequality without a separate argument.

**State the scope of an obstruction.** Failure of one localizer, counterterm class or symmetry
mechanism does not exclude every future geometry. Extract the sharp boundary or positive
construction exposed by that failure.

## Core mechanisms

### Degree-two signature calculus

[LorentzianFormsAtDegreeTwo](LorentzianFormsAtDegreeTwo.lean) proves the equivalence between
reverse Cauchy–Schwarz, absence of a positive definite plane, and nonpositivity on the kernel of
a linear functional. It supplies three basic construction operations:

* Pullback by any linear map preserves hyperbolicity. A nonnegative map also preserves the
  entrywise sign of a Lorentzian form.
* If `Q[x] ≤ Q′[x]` for every `x` and `Q′` is hyperbolic, then `Q` is hyperbolic
  (`IsHyperbolic.of_le`). Subtracting a positive semidefinite form is an instance.
* Forms nonpositive on a common fixed hyperplane can be added. The CND API uses the hyperplane
  `Σ x_i=0`. Unrestricted addition fails, even for positive rank-one forms.

The symmetric product of two nonnegative linear forms gives an elementary Lorentzian quadratic.
Higher-degree products and derivatives require a higher-degree theory with its support and
signature conditions; they are not consequences of the quadratic API alone.

### Polar gluing and its exact price

For forms `Q_i` sharing a positive anchor `e`, put

\[
 a_i=Q_i[e],\quad b_i(x)=B_{Q_i}(e,x),\quad
 A=\sum_i a_i,\quad b(x)=\sum_i b_i(x).
\]

Their polar dispersion is

\[
 V_e(x)=\sum_i a_i\left(\frac{b_i(x)}{a_i}-\frac{b(x)}A\right)^2.
\]

[PolarGluingAndDispersion](PolarGluingAndDispersion.lean) establishes the exact gluing law

\[
 R_{\sum_iQ_i}(x)=\sum_i R_{Q_i}(x)-V_e(x).
\]

Thus the sum is hyperbolic exactly when summed reserves pay dispersion for every vector. This
criterion does not assume that the local forms are hyperbolic. When their reserves vanish,
alignment of the normalized polar rows is necessary and sufficient.

The dispersion has a canonical matrix

\[
 C_e(Q_i)=\sum_i\frac{(Q_i e)(Q_i e)^T}{a_i}
       -\frac{((\sum_i Q_i)e)((\sum_i Q_i)e)^T}{A}.
\]

It is positive semidefinite and its bilinear pairing with `e` vanishes. The corrected form

\[
 \operatorname{Glue}_e(Q_i)=\sum_iQ_i-C_e(Q_i)
\]

preserves the total polar row and adds local reserves exactly. Consequently it is hyperbolic
for an anchored family of hyperbolic forms. Grouping pieces decomposes the correction into
within-group and between-group corrections without changing the total correction. Corrected
assembly is associative as a quadratic form. Both correction and assembly commute with linear
pullback when the anchor is carried along with the tests. These identities support coherent
finite restrictions; they do not supply an analytic limit theorem.

The sharp two-plane calibration is

\[
 Q_{t,r}=\begin{pmatrix}1&t\\t&t^2-r\end{pmatrix}.
\]

Each plane is hyperbolic exactly when `r≥0`; `Q_{t,r}+Q_{−t,r}` is hyperbolic exactly when
`r≥t²`. Their gluing correction is `diag(0,2t²)`. Thus arbitrarily good local signatures still
require a quantitative compatibility estimate. The correction need not be the smallest repair
when local reserves are already available.

The scalar variance identity is reused from `HTGeometry.schurComplement_sum_eq`; the matrix
construction, reserve criterion and signature closure are its role here. An arithmetic
application must identify or pay this correction in the *actual* pairing. Hyperbolicity of
`Q−C_e` alone cannot imply hyperbolicity of the larger form `Q`.

The reusable tools expose each part of this mechanism:

| Tool | Role in a construction |
|---|---|
| `anchorReserve_sum` | Compute the exact reserve lost under addition |
| `isHyperbolic_sum_iff_dispersion_le` | Test whether available reserves pay the loss |
| `isHyperbolic_polarGlue` | Construct a hyperbolic corrected assembly |
| `isHyperbolic_sum_iff_alignment_of_zero_reserve` | Identify the rigidity required when no local reserve remains |
| `polarGluingCorrection_group`, `qf_polarGlue_group` | Compose corrections and assemblies consistently across a hierarchy |
| `qf_polarGluingCorrection_pullback`, `qf_polarGlue_pullback` | Transport the construction through finite linear restrictions |

### Links and trickle-down

[TheHodgeIndexTricklesDown](TheHodgeIndexTricklesDown.lean) proves a local-to-global signature
theorem for a nonnegative symmetric incidence tensor with hyperbolic links and connected
support. Connectivity joins the local positive directions; without it, separate components can
supply separate positive squares.

[TheMetzlerDichotomy](TheMetzlerDichotomy.lean) identifies the remaining burden sharply. In the
connected Metzler regime with a positive weight whose image is positive, weighted trickle-down
is equivalent to hyperbolicity. Producing that inequality is substantive; introducing it as a
hypothesis does not construct a Hodge index.

[TheFrobeniusLadderIsMetzler](TheFrobeniusLadderIsMetzler.lean) calibrates this against curve
data. The Frobenius Gram has the expected entrywise sign and connected support, but the golden
fake still fails weighted trickle-down. Actual section or incidence structure must distinguish
curves from the fake. A proof starting with purity may calibrate the language, but cannot count
as an independent proof of purity.

### Gauge fixing and the successor connection

[TheSignIsAGaugeFixing](TheSignIsAGaugeFixing.lean) formalizes why the prime kernel alone does
not select the Euler point: completely multiplicative unit phases act by diagonal unitary
conjugacy. Requiring simultaneous nonnegative entries with a fixed positive coupling kernel
can rigidify the gauge.

[TheSuccessorConnectionIsTheArchimedeanGaugeField](TheSuccessorConnectionIsTheArchimedeanGaugeField.lean)
identifies the successor connection on the adjacent archimedean edges after the prime twist is
removed. Nonnegative adjacent couplings recover trivial prime phases on the corresponding
finite horizon. Successor shift itself has examples of both signs for its change in the atomic
prime form, even on nonnegative profiles. The useful object is therefore its connection and
compatibility with the other kernels; a monotonicity assertion for the shift would be false.

These are finite, specified-kernel results. They do not classify a global positivity locus of
all completed twists. Dirichlet characters vanish at nonunits and therefore are not points of
the full unit prime torus. Vertical characters also change which completed archimedean data are
being compared. Both distinctions must be retained in any classification.

### The arithmetic bridge and the critical domain

[TheHodgeIndexOfTheScalingSurfaceIsHyperbolicity](TheHodgeIndexOfTheScalingSurfaceIsHyperbolicity.lean)
relates the actual scaling-surface signature to finite Hermitian Gram matrices and RH. It also
shows why entrywise nonnegativity in a freely chosen finite nef basis does not certify the
signature: a basis change preserves inertia.

The analytic source of usable finite certificates lies partly outside ALG. SSHA proves
stability at a fixed small fraction of the atomic spacing. ACS further pays both pole moments
on independent arithmetic sections, obtaining the full Weil lower bound by square mass.
These are genuine arithmetic positive spaces. They are not known to exhaust the target space.
SSHA's fixed-spline integer-log family supplies a precise exhaustive endpoint: vanishing
negative index for every finite subfamily is equivalent to RH.

ALG should connect these results by source-defined comparison and composition. It should not
replace the missing overlap or exhaustion theorem by a new name for it.

### Higher-degree coefficients and the Turán layer

[LorentzianPolynomialsAndTheTuranLayer](LorentzianPolynomialsAndTheTuranLayer.lean) defines
homogeneous Lorentzian coefficient functions using nonnegative coefficients, M-convex support
and hyperbolicity of every quadratic derivative. In two variables it proves equivalence with
interval support and ultra-log-concavity of the binomially normalized coefficients.

It also proves Lorentzianity of every homogenized binomial transform
`Σ_k binom(d,k) γ_(n+k) x^k y^(d−k)` of the even Taylor coefficient sequence
`ξ(1/2+x)=Σ_k γ_k x^(2k)`. This is an unconditional Turán layer. Pólya's criterion uses the
factorially normalized sequence `k! γ_k`; its Newton inequalities are stronger, and
Lorentzianity still does not give real-rootedness. The coefficient normalization is part of
the theorem, not a dispensable convention.

## Research questions and tools to develop

**Arithmetic polar compatibility.** Find a decomposition of the complete intersection form
whose anchors and reserves are source-defined. Determine whether the infinite-place cross
energy, section relations or successor connection pay polar dispersion. The first useful
result is an exact identity and payment on a larger explicit test family, with a reserve that
can survive extension.

**Coherent multiscale assembly.** Construct arithmetic decompositions whose anchors and
restriction maps respect the gluing calculus. Use the grouping law to separate within-block
and between-block costs, then seek bounds uniform under refinement. Determine how much
correction remains necessary after available local reserves are allocated. Associativity and
pullback compatibility settle the finite algebra; uniform payment and passage to the limiting
arithmetic form remain research questions.

**An inductive arithmetic class.** Construct sections or incidence objects whose links remain
in the same class. Prove the local signature from counting or another independent arithmetic
operation. Over finite fields, this construction must reject the golden and complex fake data
for a named reason. Over the integers, identify which operation replaces the relevant count,
flatness or product-formula estimate.

**Signed overlap and exhaustion.** Retain the overlap Gram, prime lag form, archimedean cross
form and both poles in one estimate. Quantify errors in the actual overlap norm. Establish a
transfer theorem to an exhaustive family; do not infer it from increasing dimension or a
height-averaged statistic.

**Higher-degree arithmetic lifts.** Extend the coefficient theory with products, nonnegative
substitutions and derivatives when a candidate arithmetic lift requires them. The decisive
theorem is an identity for its Hessian or links. The Euler product
and the scale substitution `a ↦ Σ a_p log p` alone do not realize the Γ-factor or the pole plane.

**Finite-field realization.** Recover the curve signature from actual sections or counting
without using the desired purity as input. Determine which primitive operations carry the
information absent from abstract point counts. Do not claim a universal impossibility of
bounded-degree lifts from the failure of one proposed lift.

**Gauge classification.** Study simultaneous gauges for the full specified kernels, including
boundary and conductor data. Determine what successor curvature or quantitative flatness
forces. Separate classification of sources from positivity at a selected source.

**Turán and stability.** Identify an arithmetic operation producing the stronger factorially
normalized inequalities or real stability beyond the established Turán layer. Real stability
and Jensen real-rootedness impose stronger requirements. A log-concavity theorem must not be
promoted to RH.

**Conformal dynamics and reflection.** Study maps satisfying `TᵀQT=λQ`, and reflection forms on
the affine algebra, when those maps arise from an arithmetic construction. A boost on an
indefinite fibre does not create a positive invariant metric. Construct the positive source or
identify the exact obstruction and its survivor.

**Exceptional extinction.** Combine the geometric defect with the energy and work theories of
AES. A pointwise source estimate below one transverse-energy quantum, or a proved propagation
law contradicting a global budget, could exclude an off-line zero. Average rarity alone cannot.

## Traps and boundaries

| Tempting inference | Required correction |
|---|---|
| Every prime piece is positive, so the global form has Hodge index | Specify the forms, their common pole allocation, and the dispersion or cross-term payment |
| Subtracting a positive correction proves the original signature | It proves the signature of a different, smaller form; identify the target or prove the required domination |
| Nonnegative coefficients and connectivity imply Hodge index | The golden calibration passes these tests; local signature still needs proof |
| A positive Euler product gives a Lorentzian arithmetic Hessian | Define the polynomial and prove the Hessian identity, including mixed derivatives |
| The scale map is the archimedean place | A substitution is not an identity with the completed Γ-term and finite part |
| A nef shift repairs the arithmetic form | It changes coordinates; a regulator subtraction changes the form |
| A common gauge proves positivity | It selects coordinates or a source; it does not prove a signature |
| Positive local sections already exhaust the Weil criterion | Their shrinking supports require a separate signed transfer theorem |
| Fixed-scale average statistics control every signed vector | The quantifiers and norms differ; prove the passage |
| Lorentzian log-concavity implies Jensen real-rootedness | Real stability is stronger |
| A symmetry obstruction excludes every geometry | The conclusion applies to the specified localization and invariance mechanism |

## Relation to the surrounding research

| Programme | Interface with ALG |
|---|---|
| ArithmeticCastelnuovoSeveri | Scaling surface, pole plane, Hodge target, curve calibrations and source-defined arithmetic sections |
| ArithmeticOrientationGeometry | Weil planes, correlations and Rosati signs |
| ArithmeticIntersectionTheory | Prime ladders, transfers and renormalization cocycles |
| ArithmeticEffectivityTheory | Counting, Riemann–Roch growth and the distinction between a constructed cone and assumed effectivity |
| BiarithmeticGaugeGeometry; ArithmeticCorrelationGeometry | Prime gauge torus, successor connection and source selection |
| ArithmeticPolarization; ConjugateDiagonalGeometry | Positive versus equivariant pairings and their exact defect |
| ArithmeticElectrostatics | Currents, transverse energy, quantization and source work |
| RenormalizedArithmeticPotentialTheory; RenormalizedBiarithmeticGeometry | Counterterm rank, finite parts and surviving domains |
| SpacingScaleHarmonicAnalysis | Joint analytic payment, overlap kernels and exhaustive test criteria |
| IncommensurableGaborPinching | Retaining structural Gram slack when separate scalar estimates discard it |
| HTGeometry | Inertia, Schur complements and projection identities reused by the signature calculus |

ALG owns construction and composition of signature certificates. It should reuse the source
estimates and exact identities in these programmes, while making the missing arithmetic bridge
explicit.

## Pillar theorems and success criteria

The foundation rests on the degree-two equivalences and domination theorem; the finite-Gram
bridge to the actual scaling surface; the trickle-down theorem and its Metzler boundary; common
gauge rigidity; the bivariate Lorentzian–Turán equivalence; and the reserve–dispersion gluing
law with its matrix correction, composition rules and sharp calibration. These pillars
describe valid mechanisms and their limits. They do not assert the
unproved arithmetic input needed to reach the full Weil form.

A contribution must supply an unconditional theorem about explicitly defined objects. General
algebraic criteria must expose their structural conditions and prove them when applied to
arithmetic. An unknown analytic estimate cannot be hidden in a premise, instance or structure.
The Lean development, not a paper-only argument, establishes the result.

A contribution toward RH must identify the producer or transfer step it improves. If it claims
to distinguish the arithmetic source, it must explain its behavior on the relevant sign twin or
fake datum. If it retires a mechanism, it must retain its strongest positive boundary,
classification or replacement construction. New vocabulary or another RH-equivalent endpoint
alone is not enough.

Full success means a source-defined signature construction for the actual Weil intersection
form on an exhaustive signed family. Intermediate successes include a new arithmetic section
space, a proved dispersion payment, an independently constructed link signature, a quantitative
overlap transfer, or an exceptional-extinction theorem. Each must say exactly which domain it
controls and which arithmetic step remains open.
