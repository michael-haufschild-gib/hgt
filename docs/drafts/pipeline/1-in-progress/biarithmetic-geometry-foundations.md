# Biarithmetic Geometry: finite horizons, signed incidence, and obstruction theory

- **ID:** biarithmetic-geometry-foundations
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** ../../../reports/review-2410/opus.md, especially §§2–4
- **Statement:** Develop the finite-horizon geometry of the joint additive and multiplicative action of the integers, including signed observation, payment obstructions, and arithmetic escape modules.

## Goal

Carry out the full programme requested in the attached brief. Its completion criterion includes
the questions, tools, and criteria K1–K5 in the source report; a collection of definitions or
receiver equivalences does not complete it. All new Lean leaves belong to
`formal/GaloisForLFunctions/BiarithmeticGeometry/`, with sibling umbrella
`BiarithmeticGeometry.lean`. A foundational README must explain mathematics, not record sessions.
The `hgtl7` skill is expressly excluded. No numerical experiments or computation-based proofs.

Every significant finding must be formalized. Only a completed Lean source check
and transitive axiom audit establish a proved result. Paper arguments are proof
plans, never a stopping point or a substitute for a checked theorem. Incomplete
contribution cards remain in `1-in-progress`, including those with complete paper
arguments; their formalized components have separate `3-formalized` cards.

Current instruction: finish open Lean work and formalize findings with existing
paper proofs, then pause. Complete this verification and formalization queue;
do not expand the research frontier before pausing. The full programme remains
incomplete, and the eventual pause must not be reported as goal completion.

Handle proof review, promotion, and documentation directly. Do not write or use
Python automation for these tasks. The prepared promotion helper and its queued
driver were removed. Pending-check manifests remain as data only.

The closeout scope includes the existing proof plans on the digital-energy,
payment-graph, paid-Gram-stability, normalized-cube, divisor-positivity,
intrinsic-golden, critical-continuum-defect, one-prime-Fredholm, digit-profile,
golden-digital-module, circle-Fourier, critical-phase-collapse, and
logarithmic-chirp cards. Distinguish their exact source claims from their
abstract sequence or kernel lemmas. Checking a proper subset does not close
its parent card. Open programme questions without a proof plan remain open.

## Gates

- [x] 0 → 1: source report read fully; existing ACS/AOG foundations and relevant corpus searched.
- [ ] Every significant finding has a dependency-closed Lean proof.
- [ ] Each new leaf passes `lake --old env lean`; all main declarations audited with
  `#print axioms`; imports wired without compiling umbrellas.
- [ ] Full programme: every source question and K1–K5 discharged, or a false proposed statement
  replaced by its strongest proved positive survivor without claiming the original statement.

## Requirements and evidence needed

| Source requirement | Required evidence | Status |
|---|---|---|
| Own folder, umbrella, foundational README | Current files, verified imports, mathematical exposition | Present; fifty-eight direct-checked and axiom-audited leaves |
| Horizon-complete objects; sign visibility | Exact signed finite-horizon laws and quantitative period/prefix comparison | Open |
| Truncated affine representation theory | Source-defined action, boundary calculus, classification/calibration | Open |
| A1–A2: paid ideal annihilates escape; hull inclusion | Actual receiver theorem, not an assumed ideal inclusion | Proved for every actual common Gram limit; ADR foundations reused, four interfaces directly checked and axiom-audited |
| A3: regular-variation dilation law | Precise subsequence hypotheses proved for source or exact unconditional classification | Actual source open; scalar logarithmic-chirp tangent proof plan recorded, Lean pending |
| A4: moving translations and covariance | Construction at a corrected scale with controlled boundaries | Proposed square-root scale collapses for actual source; ADR has formalized the stronger source-power collapse, with exact capped costs and uniform budgets; nonzero action at a corrected scale remains open |
| Golden module and white-noise battery | Actual signed-data checks, not just positivity/dilation checks | Golden inverse-zeta digital-module derivation on a separate in-progress card; antipodality-only white-noise exclusion refuted by ADR's unique positive extension |
| B1: payment cohomology and Euler characteristic | Well-posed definition and exact relation to corpus box defect | Literal dimension identity refuted; degree/torsion survivor formalized; one-prime graph-norm complex and Fredholm phases have proof plans, with Lean obligations outstanding |
| B2: Mayer–Vietoris and prime-power jumps | Exact sequence with source-defined restriction maps | Open |
| B3–B4: duality and certified-window vanishing | Independent duality and source comparison | Open |
| C1–C2: Stepanov calibration and replacement identity | Finite-field calibration and signed integer source test | Open |
| Quantitative Class III | New off-diagonal signed estimate, or sharp obstruction plus positive survivor | Open |
| Infinite-rank coercivity | Precise transfer law or complete countermodel classification | Open |
| Bounded-conductor amplification | Well-defined operation class; proof or counterexample | General question open; specified normalized cube fully formalized, including exact arithmetic classification and complex-root purity |
| Orientation | Ring-selective polarization with independent sign proof | Open |
| K1 | Curve cohomology dimension `2g`, Serre duality, Weil calibration | Open |
| K2 | Golden, Beurling, shifted-pair, Estermann, parity, node-4/node-6 tests | Open |
| K3 | Source-defined recovery of PNT, VK band, Guth–Maynard density | Open |
| K4 | New certified window, band exponent, or actual escape-family classification | Open |
| K5 | Every finite-horizon assertion formalized without unproved analytic premises | Open |

## Approach

### Verification state

| Leaf | Current proof check | Axiom audit |
|---|---|---|
| `HorizonAffineActions` | Direct leaf passed; dependency olean created | Main declarations clean |
| `HorizonBoundaryCalculus` | Direct leaf passed | Main declarations clean |
| `AffineNormalizationFreedom` | Direct leaf passed | Main declarations clean |
| `ArithmeticEulerCharacteristic` | Direct leaf passed, including all-aperture formula | Main declarations clean |
| `SharedBudgetDescent` | Direct leaf passed | Main declarations clean |
| `PaidKernelsVanishOnEscape` | Direct leaf passed with reduced imports | Main declarations clean |
| `ExactPrefixVisibility` | Direct leaf passed, including full covariance-fibre criterion | Main declarations clean |
| Contractive Wiener synthesis | Reuse concurrently developed AOT `BoundedMultiplicativeSequencesActOnWienerAlgebras`; own duplicate draft removed | Covered by transitive universal-interface audit |
| Actual Wiener representation and nonempty hull | Reuse ADR `TheCofactorLimitIsAWienerModule`; dependency olean now available; duplicate scratch removed | Covered by transitive universal-interface audit |
| `DiagonalScalingCountermodel` | Direct leaf passed, including cyclicity and stationary repair | Main declarations clean |
| `FiniteAffineUnitaryRigidity` | Direct leaf passed for all real expansion factors greater than one | Main declarations clean |
| `PrimePowerTransitionGroups` | Direct leaf passed, including all-aperture kernel formula | Main declarations clean |
| `PrimeLogJumpDomain` | Direct repository leaf passed; stage-3 card | Main declarations clean |
| `FiniteAffineQuotient` | Direct repository leaf passed; stage-3 card | Main declarations clean |
| `AffineInvariantSubspaces` | Direct repository leaf passed; stage-3 card | Six main declarations clean |
| `WeightedBaseFiveDigits` | Direct repository leaf passed; stage-3 card | Five main declarations clean |
| `WeightedDigitMoments` | Direct repository leaf passed; stage-3 card | Five main declarations clean |
| `WeightedDigitEnumeration` | Direct repository leaf passed; stage-3 card | Six main declarations clean |
| `DigitPronicBlocks` | Direct repository leaf passed; stage-3 card | Three main declarations clean |
| `WeightedDigitPronicEnergy` | Direct repository leaf passed; stage-3 card | Three main declarations clean |
| `DigitCofactorConvolution` | Direct repository leaf passed; stage-3 card | Three main declarations clean |
| `CofactorPaymentCriterion` | Direct repository leaf passed; stage-3 card | Two main declarations clean |
| `FiveTowerKernelLift` | Direct repository leaf passed; stage-3 card | Three main declarations clean |
| `PrimeFivePaymentCriterion` | Direct repository leaf passed; stage-3 card | Five main declarations clean |
| `FiniteGeometricConvolution` | Direct repository leaf passed; stage-3 card | Four main declarations clean |
| `GeometricFutureTail` | Direct repository leaf passed; stage-3 card | Four main declarations clean |
| `GeometricTowerDigitReceiver` | Direct repository leaf passed; stage-3 card | Five main declarations clean |
| `GoldenInverseSeries` | Direct repository leaf passed; stage-3 card | Six main declarations clean |
| `GoldenArithmeticSource` | Direct repository leaf passed; stage-3 card | Six main declarations clean |
| `GoldenSourceAdmission` | Direct repository leaf passed; stage-3 card | Five main declarations clean |
| `SignedTowerAdmission` | Direct repository leaf passed; stage-3 card | Three main declarations clean |
| `GoldenPrimePayment` | Direct repository leaf passed; stage-3 card | Five main declarations clean |
| `IntrinsicGoldenSeries` | Direct repository leaf passed; stage-3 card | Six main declarations clean |
| `CriticalUnpaidSequence` | Direct repository leaf passed; stage-3 card | Seven main declarations clean |
| `CriticalWienerLift` | Direct repository leaf passed; stage-3 card | Four main declarations clean |
| `ComplexCriticalWienerLift` | Direct repository leaf passed; stage-3 card | Five main declarations clean |
| `CriticalGoldenPaymentQuotients` | Direct repository leaf passed; stage-3 card | Three main declarations clean |
| `PronicEnergyDomain` | Direct repository leaf passed; stage-3 card | Four main declarations clean |
| `CofactorGraphDomain` | Direct repository leaf passed; stage-3 card | Five main declarations clean |
| `PaidGraphIdentification` | Direct repository leaf passed; stage-3 card | Two main declarations clean |
| `PronicDilationOperators` | Direct repository leaf passed; stage-3 card | Six main declarations clean |
| `PronicWienerCoordinates` | Direct repository leaf passed; stage-3 card | Both main declarations clean |
| `CriticalPartialSumCore` | Direct repository leaf passed; stage-3 card | Seven main declarations clean |
| `GoldenNormalizedCube` | Direct repository leaf passed; stage-3 card | Four main declarations clean |
| `NormalizedCubicTrace` | Direct repository leaf passed; stage-3 card | Five main declarations clean |
| `CriticalGoldenPaymentNonclosed` | Direct repository leaf passed; stage-3 card | Six main declarations clean |
| `CofactorGraphClosedness` | Direct repository leaf passed; stage-3 card | Two main declarations clean |
| `DigitRefinement` | Direct repository leaf passed; stage-3 card | Nine main declarations clean |
| `DigitalCircleFourier` | Direct repository leaf passed; stage-3 card | Three main declarations clean |
| `FinitePronicStepEmbedding` | Direct repository leaf passed; stage-3 card | Two main declarations clean |
| `GoldenDivisorResponse` | Direct repository leaf passed; stage-3 card | Five main declarations clean |
| `GeometricPoleExtraction` | Direct repository leaf passed; stage-3 card | Four main declarations clean |
| `GeometricShellHilbert` | Direct repository leaf passed; stage-3 card | Six main declarations clean |
| `CriticalGoldenClosure` | Direct repository leaf passed; stage-3 card | Four main declarations clean |
| `PronicFiniteExtension` | Direct repository leaf passed; stage-3 card | Four main declarations clean |
| `NormalizedCubicRootLaw` | Direct repository leaf passed; stage-3 card | Eight main declarations clean |
| `PowerTailCoefficients` | Direct repository leaf passed; stage-3 card | Five main declarations clean |
| `PowerTailIndependence` | Direct repository leaf passed; stage-3 card | Five main declarations clean |
| `PaidSourcePerturbations` | Direct repository leaf passed; stage-3 card | Five main declarations clean |
| `FullWienerAnnihilation` | Consolidated ADR interfaces and direct repository leaf passed | Four chosen and universal declarations clean |

Completed main-declaration axiom audits for fifty-eight checked leaves report only `propext`,
`Classical.choice`, and `Quot.sound`. Audits used isolated Lean source copies; each leaf also passed its direct source check. The literal-B1
no-go is closed in `5-failed/biarithmetic-literal-dimension-euler-characteristic.md`; its
positive survivor and exact prefix visibility now have separate stage-3 cards.

### Construction principles

Audit proposed foundations before importing their conclusions. Preserve two distinct invariants:
integer cohomological indices and real weighted arithmetic masses. Construct finite-horizon affine
actions directly, retaining cutoff defects and signed coefficients. Compare all abstractions to
actual divisor rows before asserting consequences for RH.

## Mathematical audit: Euler characteristic

The proposed literal identity `dim H⁰ - dim H¹ = E(s)` cannot hold for ordinary finite-dimensional
vector spaces. Below the first prime, the existing corpus gives `E(s) = exp(s) + s - 1`.
At `s = log(3/2)`, this is `1/2 + log(3/2)`, strictly between `1/2` and `1` because
`0 < log(3/2) < 1/2`. It is not an integer. The obstruction and its all-aperture positive replacement are Lean-certified with clean transitive axiom audits.

Positive replacement to develop: a real weighted Euler characteristic / arithmetic degree together
with a separate integer obstruction index. Prove exact finite additivity and node-jump laws for
the weighted object; do not call positive and negative parts dimensions. A weighted identity
alone does not provide a payment sheaf, duality, or a vanishing theorem.

### Stronger positive replacement: horizon torsion

[PROVED HERE, paper and Lean] Let `L_N = lcm(1,...,N)` and `Q_N=L_N/N` for `N≥1`.
Since `N | L_N`, `Q_N` is a positive integer. The classical identity `ψ(N)=log L_N` gives

`E(log N) = (N-1) - log Q_N`.

Thus the box defect is an integer degree minus a logarithmic torsion charge, not an ordinary
Euler characteristic. The finite group `Z/Q_N Z` has order `Q_N`. This is a canonical arithmetic
candidate for the torsion term, with no positivity or zero-location hypothesis. The formula does
not yet construct sheaf cohomology. It uses a succinct integer invariant, not an enumeration of a
complete period. The identity `log L_N=ψ(N)` is classical (Mathlib
`Chebyshev.psi_eq_log_lcmUpto`); the programme contribution is the exact type-correct replacement
for B1 and its subsequent obstruction calculus, not a novelty claim for that identity.

[PROVED HERE, paper and Lean] The full positive replacement extends across each cell:
for `log N ≤ s < log(N+1)` with `N≥1`,

`E(s) = (N-1) - log Q_N + (exp(s)-N) + (s-log N)`.

The prime-power count is constant within this half-open cell, so subtract its value at `log N`.
The two remaining terms are exactly the archimedean evolution. Every nonnegative aperture lies
in exactly one such cell (`N=floor(exp s)`). This separates the quantized torsion datum from
continuous evolution on all apertures, not merely at the integer lattice. This theorem closes the literal-B1 no-go together with its strongest positive survivor; the general payment-cohomology programme remains open.

### Finite-horizon joint rigidity

[PROVED HERE, paper and Lean] On `V_N = span(e_0,...,e_N)`, define truncated pushforwards
`Ue_j=e_(j+1)` and `D_p e_j=e_(pj)`, with out-of-range vectors zero. They satisfy
`D_p U = U^p D_p` exactly. For `p≥2`, the common commutant of `U` and `D_p` consists precisely of
scalar operators. Indeed `D_p A e_0=Ae_0`; a `D_p`-fixed vector has all positive coordinates zero,
by induction using the coordinate `i/p<i` when `p|i`, and zero otherwise. Hence `Ae_0=c e_0`.
Commutation with `U` gives `Ae_j=c e_j` for every `j`, and linearity proves the claim.

The origin is essential: it is the multiplicatively fixed vector that generates the entire
horizon under addition. This is a joint additive/multiplicative rigidity theorem, not an energy
estimate or an orientation theorem. Scalar twists `D_p -> a(p)D_p` preserve the affine relation;
the relation cannot select an analytic dilation normalization by itself.

Lean: `HorizonAffineActions.lean` passed the direct leaf check
`lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/HorizonAffineActions.lean`.
Main declarations: `horizonAffine_comp`, `horizon_ring_relation`,
`horizon_double_fixed_iff`, `horizon_joint_commutant`. Axiom audit of composition, fixed space
and common commutant reports only `propext`, `Classical.choice`, `Quot.sound`.
The module's olean was created for the normalization and boundary leaves that import it.

### Repairing kernels and escape: proof plan with exact corpus dependencies

For a coefficient source `c` with absolutely convergent mean `m_c`, write `A_c` for its centered
divisor prefix. THIM `weightCenteredPrefix_dirichletConv` gives exactly

`A_(k*c)(n) = Σ_(j≤n) k(j) A_c(floor(n/j)) + m_c A_k(n)`.

THIM `pronicNorm_weightCenteredPrefix_le_critical` uniformly bounds `A_k` for every critical
Wiener kernel. If `k*c` is paid, its prefix is uniformly bounded as well. Therefore the cofactor
packet on the right has uniformly bounded pronic norm. On actual escape its squared norm divided
by `dampedMobiusEnergy ε T` tends to zero. For finite `k`, ADR
`cofactorGram_quadratic_eq` and convergence of the common Gram table imply its limiting quadratic
form is zero. This proves the finite-kernel part of A1 once the source and norm bridges are checked.

For infinite kernels, do NOT assume that finite truncations of a paid kernel are paid. Extend the
packet action using the proved `j^(-1/2)` contraction and its Wiener tail, then use the exact full
convolution law. This supplies a valid route to the full annihilator statement; density of finite
supports in the entire algebra alone is insufficient.

[PROVED HERE, paper and Lean] `PaidKernelsVanishOnEscape.lean` proves the full-kernel
normalization statement directly, before a Hilbert completion. For every subcritical damping,
either the actual receiver is admitted, or **every** critical Wiener kernel whose convolution
with the actual source is paid has normalized cofactor-action energy tending to zero.
The finite-horizon action is `Σ_(j≤n) k(j) A_ε(floor(n/j))`. The convolution identity and the
uniform critical-kernel prefix bound give a constant independent of `T`; division by escaping
receiver energy proves convergence. No truncation is asserted paid. The GNS and Bohr-hull
comparison remain separate obligations.

### Full Wiener representation and annihilation: dependency-closed paper argument

[PROVED IN ADR/AOT; reused and transitively audited] The actual common cofactor Gram limit has a Hilbert
realization with total vectors `δ_j`, `||δ_1||=1`, and bounded maps
`V_p δ_j=δ_(pj)`, `||V_p||≤p^(-1/2)`. These follow from the actual packet contraction,
complexification, and completion. The developing corpus leaf
`ArithmeticDefectRigidity/TheCofactorLimitCarriesACyclicDilationAction.lean` now states this
source construction; its checked dependency artifacts must be obtained before reuse.

For `a∈W_(1/2)`, `π(a)=Σ a(n)V_n` converges absolutely in operator norm and satisfies
`||π(a)||≤||a||_W`. Point masses multiply by `V_m V_n=V_(mn)`, and their norm-convergent
expansion in AOT extends this to a unital algebra representation. The source vector is cyclic.
This uses the actual packet bound, not a newly postulated representation.

For the full-kernel bridge, expand the squared norm as the absolutely convergent double Gram
series. Both finite-horizon and limiting kernels have bound `1/sqrt(jk)`. The summable product
majorant `|a(j)|/sqrt(j) * |a(k)|/sqrt(k)` therefore permits dominated convergence along the
common Gram subsequence. The limit of the full normalized action energy is exactly
`||π(a)δ_1||²`. The already proved full-kernel payment bound makes this limit zero on escape.
The real and imaginary parts are both paid by the definition of AOT's complex paid ideal.
Hence `π(a)δ_1=0`. Commutativity kills every `δ_j`, and continuity plus totality gives `π(a)=0`.
Thus the paid ideal is contained in the operator kernel, with no assertion that paid
truncations exist. Hull inclusion reverses ideal inclusion. The representation kernel is
proper because the unit fixes the nonzero cyclic vector; the commutative Banach-algebra
character theorem makes its Bohr hull nonempty.

### Full Wiener bridge through single covariance series

[PROVED IN ADR; programme interfaces directly checked and audited] Double Gram summation is unnecessary for annihilation. Fix one
cofactor `k`. The normalized pairing of the full repairing action with row `k` tends to zero:
its first pronic norm is bounded, its second is at most `sqrt(E_T)/sqrt(k)`, and `E_T` escapes.
At each horizon the pairing is exactly the finite sum `Σ_j g(j) K_T(j,k)`, because rows with
`j>T` vanish. The bound `|K_T(j,k)|≤1/sqrt(jk)` gives a summable single-series majorant for
any critical Wiener kernel. Dominated convergence therefore gives `Σ_j g(j)K(j,k)=0`.
Apply this separately to the paid real and imaginary components of a complex kernel. The
coefficient series for the actual Wiener representation identifies this sum with the inner
product of its receiver image against `δ_k`. Density of the cofactor vectors forces that image
to vanish; commutativity and cyclicity then force the full operator to vanish. This proves the
same ideal and hull inclusions without asserting that any finite truncation is paid.

### Distinct meanings of first cohomology

The finite-field calibration also requires separating ambient geometric `H¹` from unpaid
obstruction. A genus-`g` curve has ambient `dim H¹=2g` even when its Weil bound holds. Thus the
same unmodified group cannot simultaneously have dimension `2g` and vanish precisely when the
Weil bound holds for every positive-genus curve. An adverse subspace, relative group, or a separate
obstruction complex is needed. No comparison of such complexes has yet been proved.

### Shared-capacity descent

[PROVED HERE, paper and Lean; transitive axiom audit clean] On a finite discrete set of `k` atoms, let an admissible
allocation have nonnegative values and total mass at most a common budget `B≥0`. Restrictions
are admissible. Every singleton-admissible allocation glues to an admissible global allocation
iff `k≤1` or `B=0`. Necessity: the constant allocation `B` would require `kB≤B`. Sufficiency:
sum the pointwise bounds when `k≤1`, and all entries vanish when `B=0`.
For `k+1` singleton windows the sharp possible excess is exactly `kB`, attained by the constant
allocation. This is a complete calibration of the shared-resource failure, not a theorem that
the actual arithmetic allocation functor is this model. It proves that local payment plus
restriction alone does not justify naming a payment sheaf. Positive repair requires tracking
resource locations and compatible quotas in the site.

### Absorbing boundary calculus

[PROVED HERE, paper and Lean; transitive axiom audit clean] With the cell pairing
`<v,w>_N = Σ_(j=0)^N v_j w_j`, every positive affine map has the exact signed identity

`<T_(a,b)v,T_(a,b)w>_N + Σ_(aj+b>N) v_j w_j = <v,w>_N`.

The map `j -> aj+b` is injective. Each surviving cell therefore contributes its original
bilinear coefficient once, and each escaped cell contributes only to the boundary term.
For `v=w`, this gives contraction with the exact nonnegative loss, rather than a false
isometry claim. This is a source-independent boundary law, not an arithmetic cancellation bound.

More generally, every observable invariant under the absorbing successor is constant: iterate
the successor `N+1` times to send every vector to zero. This classifies the failure of exact
translation invariance at finite horizon. The signed boundary identity above is its positive
replacement. Also, scalar common commutant does not imply irreducibility; all tail subspaces
are invariant under positive affine maps. No irreducibility assertion is used.

### Exact visibility inside a complete-period observation fibre

[PROVED HERE, paper and Lean] Fix the actual finite row `c` and let
`Y_q=selbergMultiplesCoord N c q`, `R_q(M)=Re(pmRamanujanPrimitive q M)`.
Define `V_N(M,c)=Σ_(q=2)^N |R_q(M)Y_q|`. Among all independent Selberg sign changes fixing
the mean, the maximum absolute centered-prefix readout is exactly `V_N(M,c)`, and the diameter
of the readouts is exactly `2 V_N(M,c)`. All these rows have identical complete-period lag
covariances. This is a quantitative classification inside an observation fibre, not a bound
for the Möbius source itself.

Proof: the corpus's exact signed expansion is
`L_N(M,c^ε)=Σ_(q=2)^N ε_q R_q(M)Y_q`. The triangle inequality gives the upper bound.
Choose `ε_q=sign(R_q(M)Y_q)`, with either sign at zero, and choose the opposite signs for the
minimum. Set `ε_1=1` separately, so the mean is preserved. The extrema are `V` and `-V`.
The existing orbit classification identifies these independent sign choices with the complete
period observation fibre. The primitive `R_q(M)` retains the precise horizon dependence;
replacing it by a coarse horizon/period ratio would discard this mode information.

The bound holds throughout the full covariance fibre, without a separate mean condition:
equality of all complete-period covariances gives equality of the squared nonconstant Selberg
coordinates, hence equality of their absolute values. Apply the signed expansion and triangle
inequality. Consequently covariance determines the centered prefix if and only if `V=0`,
equivalently every product `R_q(M)Y_q` vanishes. Necessity follows from the two opposite extrema;
sufficiency follows from the universal bound. This is an exact information criterion for every
prefix and every finite row, not merely an example of blindness.

### Dilation of tangent kernels: quantifiers to retain

[PAPER DERIVATION; Lean pending] For `m=floor(T/p)`, rows `v,w` vanishing at zero satisfy

`<D_p v,D_p w>_T = (1/p)<v,w>_m
  - v(m)w(m) [1/(T+1)-1/(p(m+1))]`.

Every complete dilation fibre has exactly `1/p` of its original pronic mass; only the last
incomplete fibre contributes the displayed boundary term. For actual damped receiver rows,
the existing `O(n^(1-ε))` source bound makes this correction `O(T^(-2ε))` for fixed cofactors.
Thus regular variation of the base energy transfers a tangent kernel at horizons `T_n` to a
kernel at `floor(T_n/p)`, with scalar factor `p^(-1-α)`. It does **not** by itself identify
these two tangent kernels. The off-diagonal assertion A3 needs a dilation-stationary extraction
or a proved uniqueness of the tangent; regular variation of the scalar energy proves only the
diagonal law without that additional argument. This is an open quantifier audit, not a claimed
counterexample for the actual Möbius source. Preserve the entire family of tangents before
asserting an isometry law inside one member.

### A finite countermodel to inferring off-diagonal scaling from diagonal scaling

[PROVED HERE, paper and Lean; transitive axiom audit clean] Let `B(x,x)=x₀²+x₁²+x₂²+(2/3)x₀x₁` on `R³`, and let
`P` cyclically permute the three coordinate vectors. Then
`(2/3)|x|² ≤ B(x,x) ≤ (4/3)|x|²`, so every power of `P` distorts `B` by at most a factor 2.
Put `u_j=P^(v₂(j))e₀`, `V_p=p⁻¹P^(v₂(p))` and `K(j,k)=B(u_j,u_k)/(jk)`.
Unique factorization gives the multiplicative action and `V_p(u_j/j)=u_(pj)/(pj)`.
The three vectors at indices 1, 2 and 4 span the whole space, so this is a cyclic rank-three
module, not a merely formal kernel.

It satisfies every coarse cofactor Gram constraint: `K(1,1)=1`, PSD, the radius bound,
and packet dilation contraction `1/p`. For `p≥2`, the last follows from `2/p²≤1/p`; for `p=1`
it is equality. Every diagonal is exactly `K(j,j)=j⁻²`, so all diagonals have the exponent-one
scaling law. Nevertheless `K(1,2)=1/6` whereas `K(2,4)=0`, contradicting homogeneous
off-diagonal scaling by `2⁻²`. On `x=e₀+e₂`, `B(V₂x,V₂x)/B(x,x)=1/3>1/4`, so the stronger
operator contraction also fails.

This model does not claim realization by the actual receiver or a regularly varying scalar
row. It isolates exactly the invalid implication from diagonal scaling plus the existing Gram
constraints to the full A3 identity. Its positive survivor is a complete explicit cyclic
representation with a uniform distortion bound and exact orbit norms. The exact countermodel, positive cyclic representation, and stationary repair are now
formalized and axiom-audited. The failed-route card retires only this coarse-data implication.

There is also an exact stationary repair of this model. Average the three forms
`B(P^r x,P^r y)`, `r=0,1,2`. The resulting Gram matrix has diagonal 1 and every off-diagonal
entry `1/9`; it is positive definite and `P`-invariant. Its kernel has the full scaling law
`Kbar(pj,pk)=p⁻² Kbar(j,k)`. This shows precisely what averaging adds, while preserving all
diagonals and the underlying cyclic representation. Averaging a family of actual tangents
would still need a separate realization theorem; a convex mixture need not be one source
subsequence limit.

### Scalar regular variation with a moving covariance phase

The stronger, smooth source `v(n)=n^β cos((log n)²)`, `1/2<β<1`, now has a
dependency-closed paper proof in
`../1-in-progress/biarithmetic-logarithmic-chirp-tangents.md`. It has bounded increments,
regularly varying pronic energy of index `2β-1`, and an explicit compact family of
infinite-rank tangents, none individually homogeneous. An exact positive boundary-loss
identity constructs the cyclic dilation representations. Haar averaging produces a
homogeneous diagonal kernel which is not an individual tangent. Lean formalization and
full novelty audit remain open. The discontinuous source below is an earlier, weaker
candidate, not an additional theorem or source assumption.

[NEW CANDIDATE; paper and novelty audits required before any theorem claim] A stronger test
than the finite cyclic model is the continuous scalar row `v(x)=x^β q(log x)`, where
`1/2<β<1` and `q` is the square wave with `q(t+log 2)=-q(t)`. Its quadratic energy against
`dx/x²` is exactly `(T^(2β-1)-1)/(2β-1)`. Writing `α=2β-1`, the candidate tangent at logarithmic
phase `θ` is

`K_θ(j,k)=(jk)^(-β) α ∫₀^∞ exp(-αu) q(θ-u-log j) q(θ-u-log k) du`.

It obeys `K_θ(pj,pk)=p^(-2β) K_(θ-log p)(j,k)`. The phase has period `log 2`. The entry `(1,3)`
is a nonconstant continuous exponential smoothing of a square wave product. If one full kernel
were homogeneous under dilation 3, the identities at all further cofactor indices would make
that entry constant along the irrational rotation by `log 3`, hence everywhere, a contradiction.
Thus scalar regular variation alone need not supply a homogeneous individual tangent.

The positive candidate is a compact phase family with exact dilation transport and a stationary
phase average. That average is `(jk)^(-β)` times the square-wave autocorrelation at `log(j/k)`.
It need not be an individual horizon limit. This continuum calculation is not yet a theorem
about integer pronic energies, bounded source increments, or the Möbius receiver. The discrete
floor errors and any smoothing of the jumps must be proved separately. Do not use it as a
counterexample to an assertion restricted to the actual arithmetic source.

### Moving translations: further quantifier audit

[PAPER ARGUMENT; Lean pending] The affine covariance relation does not by itself exclude any
positive escape exponent. On a one-dimensional space take `U_t=1` and `V_p=p^(-(1+α)/2)`.
For every `α≥0` this has unit cyclic vector, homogeneous Gram kernel
`K(j,k)=(jk)^(-(1+α)/2)`, critical packet contraction, and exact affine covariance. Thus A4
requires information about the actual translation action beyond its existence and covariance.
The moving-translation lower scale from C9 is necessary for survival, not a sufficient
nontriviality theorem.

[PROVED HERE, paper and Lean; transitive axiom audit clean] There is a sharp finite-dimensional constraint: a continuous unitary real-translation group
covariant with an invertible dilation of factor `p>1` is trivial. Conjugacy gives
`tr(U_t)=tr(U_(t/p))`; iteration and continuity give `tr(U_t)=dim H`. In an orthonormal basis,
`Σ ||U_t e_i-e_i||²=2 dim H-2 Re tr(U_t)=0`, so `U_t=1`. This proves that a nontrivial unitary
translation limit with invertible dilation must be infinite-dimensional. It does not establish
that actual escape translations are nontrivial, unitary, or invertibly dilatable.

For a regularly varying scalar power row, translations of order `sqrt(E_T)` can still vanish
in normalized energy: this scale is `o(T)`, whereas the dominant row mass lies near `T`.
Any proposed A4 construction must retain this calibration rather than identifying the
necessary threshold with guaranteed survival.

The concurrent ADR paper card `../2-fully-proven/square-root-energy-translations-still-disappear.md`
now proves more for the actual source. Its increments lie in an interval of width one, giving
`|A(n+k)-A(n)-A(k)|<=min(n,k)` and exact pronic envelope `2k-H_k`. Recentered translations
therefore have a linear budget; sublinearity sharpens it to little-oh linear. Every recentered
shift with bounded `k/E` disappears, while raw shifts with bounded `k^2/E` disappear. Resetting
only the origin has a distinct possible boundary component and cannot be conflated with
recentring. The owning programme has since formalized the source-power strengthening in
`ArithmeticDefectRigidity/TheSourcePowerSavingControlsMovingSuccessors.lean`.
Its source statements and proofs were inspected together with the stage-3 card
`../3-formalized/the-source-power-saving-enlarges-the-invisible-translation-scale.md`.
The actual Vinogradov--Korobov saving gives `A(n)=o(n^(1-epsilon))`. Exact capped
pronic costs then give recentered energy `o(k^(1-epsilon))` and raw energy
`o(k^(2(1-epsilon)))`, uniformly in the observation horizon. Thus bounded ratios of
these powers to escaping energy still force normalized displacement to zero.
The owner records direct source checks and standard-axiom audits. This is the
stronger positive source theorem exposed by the failed scale proposal; it does
not construct a nonzero translation action at any larger scale.
The narrow nontrivial-survival proposal is closed with this positive survivor in
`../5-failed/biarithmetic-square-root-translation-selectivity.md`. Bare A4 existence
can still be satisfied by the identity action; the failed inference is selectivity
at that scale, not existence of a trivial covariant family.

### Infinite positive jump weights: a domain test

[PAPER PROOF; novelty and Lean audits pending] For translations on `L²(R)` by shifts
`λ_j→+∞`, consider the unrenormalized positive form
`Q(f)=Σ_j w_j ||τ_(λ_j)f-f||²`, with `w_j≥0`. Its finite-energy domain is all of `L²(R)`
when `Σ w_j<∞`, since each summand norm squared is at most `4||f||²`. When `Σ w_j=∞`,
its finite-energy domain is exactly `{0}`. Indeed
`<τ_(λ_j)f,f>→0`, hence the jump norm squared tends to `2||f||²`; for `f≠0` its tail
is bounded below by `||f||²`, and the weighted sum diverges.

The vanishing of translation correlations follows without a number-theoretic estimate:
approximate `f` in `L²` by a compactly supported function. Its distant translates have
disjoint support, and Cauchy–Schwarz bounds the two approximation errors uniformly in the
translation. Thus non-summable weights on the distinct prime logarithms cannot create a
nontrivial densely defined positive jump form on the ordinary Lebesgue scaling line.

For summable weights, the Fourier symbol `Σ w_j |exp(itλ_j)-1|²` is continuous and has
arbitrarily small values at arbitrarily large frequencies: choose a finite head with small
tail, use simultaneous recurrence on that head, and bound the tail by `4Σ_tail w_j`.
Its exact zero set is the annihilator of the subgroup generated by the positive-weight shifts.
If that subgroup is dense, this zero set is `{0}`, so every compact frequency annulus has a
positive minimum, although no uniform high-frequency gap exists.

These are calibration statements for positive jump sums, not a solution of topic 6 for the
actual Weil form or for an arbitrary singular spectral representation. In particular a Bohr
space with pure point spectrum need not have vanishing translation correlations. Any proposed
unbounded-weight transfer must state its representation and nontrivial form domain. This is
the classical Lévy-form issue in the programme's coordinates; no novelty claim is made yet.

External calibration: Schilling, *An Introduction to Lévy and Feller Processes*,
[Chapter 7](https://arxiv.org/pdf/1603.00251), uses the classical Lévy condition
`∫ min(|y|²,1) dν(y)<∞`, which forces finite mass away from zero. Our elementary regular-
representation domain argument is consistent with this condition. The corpus's
`PrimeBurnolPrimeLevyMeasure` has infinite mass at jumps `1/p→0`, so it is not contradicted
by a theorem about jumps `log p→∞`.

### Canonical arithmetic transition groups

[PROVED HERE, paper and Lean; transitive axiom audit clean] The period orders `L_N=lcm(1,...,N)` form a divisibility
filtration. Consequently the reduction maps `Z/L_(N+1)Z → Z/L_N Z` are surjective, with
cyclic kernel of order `J_N=L_(N+1)/L_N`. The exact logarithmic jump is
`log J_N=ψ(N+1)-ψ(N)=Λ(N+1)`. Hence the transition kernel is trivial off prime powers
and has order `p` at `N+1=p^r`, `r≥1`. This is a canonical finite-group filtration on
the actual integer horizon, distinguishing the nodes 4 and 6.

At a fixed positive horizon `N`, reduction to `Z/NZ` also gives the exact sequence
`0 → Z/Q_N Z → Z/L_N Z → Z/N Z → 0`, where the injection multiplies by `N`.
Thus the torsion datum in the Euler formula is a concrete kernel. The quotient `Q_N`
itself need not form a divisibility filtration, so its transition maps cannot be borrowed
from those of `L_N` without proof. These elementary cyclic-group sequences calibrate B2;
they are not asserted to be Mayer–Vietoris for a payment complex. The construction uses
the actual prime-power divisor, but supplies no orientation or cancellation estimate.
The period groups can have more than polynomially many elements. Their symbolic group orders
calibrate the arithmetic charge; they are not horizon-complete observation objects or a
justification for enumerating a full period.

## External calibration

- Joachim Cuntz, *C*-algebras associated with the ax+b-semigroup over N*,
  <https://arxiv.org/abs/math/0611541>: existing operator-algebraic setting for the affine relations.
- Gerard van der Geer and René Schoof, *Effectivity of Arakelov Divisors and the Theta Divisor
  of a Number Field*, <https://arxiv.org/abs/math/9802121>: arithmetic `h⁰` is real-valued; it is
  not an ordinary vector-space dimension. This distinction must survive the new definitions.

## No-go closure

The literal ordinary-dimension B1 identity and the diagonal-to-mixed homogeneity implication
are retired. Their all-aperture degree/torsion and stationary-metric survivors are Lean-proved
and axiom-audited. Its separate failed-route card records
the precise scope. Every further negative result must likewise carry its strongest
dependency-closed positive survivor and a separate paper and Lean audit.

## Worktree preservation

At entry, unrelated edits existed in ADR, AOG, BVI, RHTower and research reports. Preserve them.
New work is confined to this programme and its own pipeline cards unless a required import is
added to a shared umbrella.

### Exact natural affine submodule classification

[PROVED HERE, paper and Lean; transitive axiom audit clean] Successor invariance alone forces a subspace of the natural horizon cell module to be a coordinate tail. The minimal nonzero coordinate and descending elimination prove the converse to tail invariance. Consequently there are exactly `N+2` invariant subspaces, all comparable, and the representation is indecomposable. This is a classical single-Jordan-block calibration, not a classification of every module of the finite image algebra. Card: `../3-formalized/biarithmetic-affine-invariant-subspaces.md`; leaf `AffineInvariantSubspaces.lean`.

### Shared Wiener foundation consolidation

`FullWienerAnnihilation.lean` now imports ADR's complete covariance and annihilation
foundation. Both universal interfaces quantify over every `ActualCofactorLimit`, and the
chosen-module interfaces are retained. The scratch audit and direct repository check passed;
all four transitive audits use standard axioms only. The duplicate local implementation was
removed after verifying that no other Lean leaf imported it. A1–A2 hold for every actual
common Gram limit, while classification of those kernels and their zero hulls remains open.

### Paid perturbation invariance

The complete arguments in `../3-formalized/biarithmetic-paid-source-perturbations.md`
and `../1-in-progress/biarithmetic-paid-perturbations-preserve-escape-grams.md` show that adding
a paid source preserves its repairing ideal and, up to nonzero scalar normalization, every
cofactor Gram tangent. `PaidSourcePerturbations.lean` passed its direct repository check
and all five transitive axiom audits. No Lean Gram comparison is claimed yet.
`WeightedDigitMoments.lean` passed its direct check and all five axiom audits; the exact
real pronic norm equivalence is now checked in `WeightedDigitPronicEnergy.lean`.
The complete source payment criterion remains separate work.

### Spectral and index distinctions exposed by concurrent Q-III work

The formalized weighted-white family `K_sigma(j,k)=1_(j=k)j^(-2sigma)` has exact stronger dilation contraction while its critical-Wiener representation remains faithful. Its annihilator hull is therefore the entire Bohr polydisk. The positive repair is a nonempty operator hull defined by `|bohrEval(a,omega)|<=||pi(a)||`, which satisfies the dilation-radius bound. Closed representation image identifies both hulls, including for every finite-dimensional actual cofactor module. See `../3-formalized/strong-dilation-contraction-does-not-shrink-the-annihilator-hull.md`; all three source modules passed final checks and standard-axiom audits. The failed generic inference is retired with this positive survivor.

The same programme has checked that closed Wiener quotients cannot have countably infinite Hamel dimension. Finite module dimension agrees with finite quotient dimension by cyclicity, density, and closedness. Infinite Hilbert dimension and algebraic quotient dimension must remain distinct. See `../3-formalized/closed-wiener-annihilators-have-no-countable-hamel-index.md`. These results correct proposed generic inferences; actual-source zero-hull containment remains open.

The golden critical source gives an explicit stronger paper calibration:
`../1-in-progress/biarithmetic-critical-payment-has-continuum-defect.md` constructs
a continuum of independent unpaid classes inside the paid ideal's Wiener closure.
The graph-norm inclusion defines a canonical one-prime payment complex. Its Fredholm
index is zero below threshold and minus one above; the critical range is nonclosed,
with one-dimensional reduced cokernel and continuum-dimensional algebraic cokernel.
See `../1-in-progress/biarithmetic-one-prime-payment-fredholm-phase.md`. These statements
remain paper results and do not supply the missing curve comparison or Riemann--Roch.

### Golden source reduction and finite digit foundation

The ordinary-floor golden source is exactly `delta_1-(I_a-I_b)/sqrt(5)`, with `I_t=localFactorInverse 5 t`. Since `b<sqrt(5)`, its secondary tower is critical Wiener. Its paid ideal therefore equals the primary tower's ideal. This source identity, exact rational mean, and ideal equality are formalized and axiom-audited in `GoldenArithmeticSource.lean`. Equality of normalized Gram families after scaling remains a paper result. The finite digit identities are formalized and axiom-audited in `WeightedBaseFiveDigits.lean`, with card `../3-formalized/biarithmetic-weighted-digit-identities.md`. These support the family classification without completing it.

### Exact digital energy and the critical payment domain

The full paper proof in `../1-in-progress/biarithmetic-digital-energy-and-prime-tower-payment.md` gives finite two-sided pronic norm bounds for arbitrary weighted digit rows, using the exact finite digit second moment. Those real norm bounds and their exact summability criterion are now Lean-checked and axiom-audited. The real source comparison for every nonzero `|a|<5` is directly checked in `PrimeFivePaymentCriterion`: prime-five repairing kernels are characterized by a weighted `ell2` condition on partial pole sums. At critical contact it is ordinary normalized partial-sum square summability. The complex golden transfer is directly checked and audited in `GoldenPrimePayment`, including the exact critical parameter and the fully paid zero endpoint. Strictness over zero evaluation and the explicit unpaid limit remain pending Lean verification. The golden parent also gives a paper circle model for every escaping damping, including exact dilation spectral radii; no blanket zeta nonvanishing on the Fourier progression is assumed.

### Current golden formalization queue

`WeightedBaseFiveDigits`, `WeightedDigitMoments`, and `GoldenInverseSeries` are directly
checked, axiom-audited, and wired into the umbrella. Their obsolete proof scratch files have
been removed. `WeightedBaseFiveDigits` now has an olean for the importing tower draft.
`PaidSourcePerturbations` passed its direct check and all five transitive axiom audits;
its dependency olean exists and its obsolete audit driver has been removed.

Active drafts:
- `GeometricTowerDigitReceiver.lean`: direct source check, dependency build, and all five
  transitive audits passed; stage-3 card present and obsolete audit driver removed.
- `GoldenArithmeticSource.lean`: actual series lift, exact rational mean, and paid-ideal
  reduction passed direct check and six audits. Stage-3 card present; obsolete scratch removed.
  Its dependency olean is now built for the admission and intrinsic-series importers.
- `FiniteGeometricConvolution.lean`: finite geometric square-sum bound passed its
  direct source check and all four audits. Stage-3 card and dependency olean present.
- `DigitRefinement.lean`: exact grid refinement, uniform supremum bound,
  uniform convergence, integer interpolation, exact base-five scaling, right continuity,
  and interpolation at every nonnegative base-five rational. Direct source check
  and all nine transitive audits passed; stage-3 card and umbrella import present.
- `WeightedDigitEnumeration.lean`: natural-index enumeration of complete
  digit words, exact logarithmic block length, geometric-row comparison, and actual
  integer block second moment. The missing `WeightedDigitMoments` dependency olean
  was built successfully. All six transitive audits and the direct source check passed;
  the production leaf is wired and has a stage-3 card. Its dependency olean is built.
  The paper proof is the enumeration on the digital-energy card.
- `DigitPronicBlocks.lean`: exact block mass, variance lower bound, and absolute-digit
  upper bound passed the direct source check and three clean audits. Stage-3 card
  and dependency olean present.
- `WeightedDigitPronicEnergy.lean`: exact complete-block partition,
  normalized finite energy bounds, and bounded-energy iff weighted square summability;
  passed all three audits and its direct source check. Production source is wired
  and has a stage-3 card; its scratch and logs have been removed. Its missing
  dependency olean is now built for the actual prime-five payment importer.
- `DigitCofactorConvolution.lean`: exact prime-five packet as a digit
  readout of causal geometric convolution, followed by partial-pole-sum factorization.
  Direct repository check and all three audits passed; stage-3 card present.
  Its missing dependency olean is now built for the actual payment importer.
- `CofactorPaymentCriterion.lean`: general actual-mean convolution
  identity and equivalence of payment with bounded full cofactor norm. Reuses the
  proved critical-Wiener mean-correction bound. Direct check and both audits passed;
  stage-3 card present and obsolete scratch removed. Its missing dependency
  olean is built for the prime-five payment criterion.
- `FiveTowerKernelLift.lean`: arbitrary prime-five coefficient lift,
  exact critical-Wiener coefficient criterion, and complete finite cofactor reindexing.
  Uses the inspected `Nat.le_log_of_pow_le` and existing local-factor weight theorem;
  first check, three audits, and direct source check passed. Production copy is wired,
  stage-3 card present, and obsolete scratch removed. Read-after-lift recovery for
  every supported row is included. Its missing dependency olean is now built.
- `PrimeFivePaymentCriterion.lean`: exact actual geometric-source
  payment criterion for arbitrary critical prime-five kernels. Reduces full payment
  to the weighted square sum of partial pole sums through the three preceding
  interfaces. Scratch verification and all five transitive axiom audits passed
  after correcting one empty-interval API argument. Production copy is wired;
  its direct repository source check passed and a stage-3 card is present.
  Its missing dependency olean is built for the complex golden and isometric
  Wiener-lift importers; obsolete scratch and logs have been removed.
  It also normalizes arbitrary `ell1` coefficients and specializes payment at
  `a=sqrt(5)` to ordinary coefficient partial sums in `ell2`. The general real
  criterion now covers every nonzero `a` with `|a|<5`; the sign-free paper proof
  is recorded on the digital-energy card.
- `GoldenPrimePayment.lean`: complex norm-square assembly of the
  real prime-five criterion and transfer through the actual golden paid-ideal
  identity. Tower support is explicit; no extra analytic premise is used.
  Its real criterion dependency is checked and built. Scratch verification and
  all five transitive audits passed after supplying explicit real and imaginary
  rows to the support-recovery lemma. The production leaf is wired, its direct
  source check passed, and its stage-3 card is present. It includes
  the exact golden critical parameter and the fully paid zero-parameter endpoint.
- `GoldenDivisorResponse.lean`: exact valuation reduction of the
  ordinary divisor response, realization at powers of five, antitonicity in the
  valuation and source parameter, and upper bound one. First check passed the
  valuation reduction, power realization, and parameter-monotonicity audits.
  Valuation monotonicity needs the explicitly qualified `Finset.sum_range_succ`
  instead of a shadowing theorem; that repair is queued. The complete positivity
  phase and divergence remain obligations on their in-progress card.
- `/tmp/BiarithmeticGoldenDivisorPositivity.lean`: exact rational limit and
  greatest lower bound, finite estimate `D_M<=1-M*t` beyond the pole, the
  complete positivity phase for all `t>=0`, and payment in the positivity
  chamber. Unchecked. The wider parameter range and finite bound have paper
  proofs recorded on the positivity card before any Lean claim.
- `FinitePronicStepEmbedding.lean`: exact finite signed covariance
  as the existing step-Gram integral of truncated rows. Finite absolute sums
  discharge the step theorem's boundedness premise for arbitrary source rows.
  First check found an ambiguous `mem_range` in the zero-tail proof; it is
  now explicitly `Finset.mem_range`, with recheck pending. Scaling, interval
  restriction, and limiting-profile comparison remain separate obligations.
- `CriticalUnpaidSequence.lean`: exact inverse-square-root-tail
  coefficient sequence, norm two, zero total sum, divergent partial-sum squares,
  and corrected finite approximants at exact distance `2/sqrt(N+1)`. Revised
  scratch check passed all seven axiom audits. Direct repository check passed;
  stage-3 card and umbrella import present. The paper argument is on the
  digital-energy and critical-defect cards.
- `CofactorGraphDomain.lean`: actual finite cofactor coordinate
  functionals, closed graph in `W_(1/2) x ell2`, inherited completeness, injective
  input projection, and exact square-summability domain. Initial check passed
  the first four audits; the domain theorem stopped at missing `ENNReal` notation
  scope. Revised scratch and all five audits passed; direct repository check
  passed. Stage-3 card and umbrella import present.
  Actual paid-ideal identification is checked in `PaidGraphIdentification`;
  the graph-norm ideal action remains pending.
- `PronicEnergyDomain.lean`: exact positive-cell reindexing,
  bounded finite pronic norms iff summable total energy, actual receiver admission,
  and complex real/imaginary decomposition. Revised scratch check and all four
  audits passed. Direct repository check passed; stage-3 card and umbrella import
  present. This is the total-energy bridge for identifying the graph image
  with the actual paid ideal.
- `PaidGraphIdentification.lean`: complexifies the actual centered
  source prefix and identifies the graph's Wiener image with the actual paid ideal.
  Every paid kernel has a unique square-summable graph output. Scratch check,
  both transitive audits, and direct repository check passed. Stage-3 card
  and umbrella import present; obsolete scratch and logs removed.
- `SignedTowerAdmission.lean`: exact admission radius for every
  real `|a|<5`, invariance under the prime-five sign flip, and the unpaid negative
  critical endpoint. Scratch check, all three audits, and direct repository
  check passed. Umbrella import and stage-3 card present.
- `CriticalPartialSumCore.lean`: corrected finite complex
  truncations, exact coefficient and square-energy tail errors, zero evaluation
  forced by payment, and convergence in both parts of the graph norm. First
  check passed the four algebraic/finite-tail audits. Limit proofs needed the
  normed infinite-sum import and explicit constant-limit types. The next check
  also exposed the missing complex completeness instance and an inferred
  composed limit function; `Complex.Basic` and an explicit partial-sum limit
  type fixed those two issues. Revised scratch, all seven audits, and direct
  repository check passed; stage-3 card and umbrella import present.
  The exact error equalities strengthen the earlier upper bound and have been
  paper-audited on the payment-graph card before formal verification.
- `CriticalWienerLift.lean`: uses AOT's actual `toWiener`
  embedding, exact normalized tower norm and distance identities, and actual
  critical paid-ideal membership. Initial check found a support-function beta
  reduction, a zero-branch simplification, and an obsolete subtraction-application
  name. The revised check passes the mass, norm, and membership audits; the
  distance proof needs only the defining reduction of `realFn` at zero.
  Revised scratch and all four audits passed; direct repository check passed.
  Stage-3 card and umbrella import present. Existing embedding
  and coefficient/term laws were source-inspected before drafting.
- `ComplexCriticalWienerLift.lean`: assembles real and imaginary
  lifts into the actual complex one-prime subalgebra, with exact norm and distance,
  linearity, and the critical golden payment criterion. Scratch check and all five
  axiom audits and direct repository check passed. Stage-3 card and umbrella
  import present; obsolete scratch and logs removed. Corpus search
  found the general AOT weight isometry; the draft reuses the actual real embedding
  and the source-inspected `LSeries.norm_term_eq` rather than a new Wiener carrier.
- `CriticalGoldenPaymentNonclosed.lean`: lifts the explicit
  unpaid sequence and its finite repairs into the actual Wiener algebra,
  proves their exact distances, and transfers nonclosedness to the critical
  golden paid ideal. Scratch check, all six transitive audits, and direct
  repository check passed. Stage-3 card and umbrella import are present.
- `CriticalGoldenClosure.lean`: corrected finite complex
  kernels pay the actual critical golden source; exact Wiener errors tend to
  the absolute total evaluation. Zero evaluation therefore places the full
  one-prime lift in the full actual paid-ideal closure. Scratch check and all
  four audits and direct repository check passed; stage-3 card and umbrella
  import are present.
  No converse for the full ideal's
  closure is asserted.
- `PowerTailCoefficients.lean`: power-tail differences with
  exact norm two and zero evaluation for every positive exponent; square
  partial-sum energy iff the exponent exceeds one half. First check passed the
  finite partial sums, absolute summability, and exact energy-threshold audits;
  the shifted limit needed explicit function-composition reduction. That repair
  passed recheck and all five transitive audits. Production source and import
  and stage-3 card are present; direct repository check passed. This
  supplies the explicit coefficient family for the continuum defect; finite
  complex independence and quotient cardinality remain separate obligations.
- `PowerTailIndependence.lean`: normalized smallest-exponent
  limit for finite complex combinations, divergent power-energy lower bound,
  and coefficient independence modulo square partial sums. Revised scratch
  passed all five audits after explicit composition reduction, direct finite
  division algebra, and an explicit subtype binder. Production source and
  umbrella import and stage-3 card are present; direct repository check passed. The actual
  quotient lower bounds remain separate.
- `/tmp/BiarithmeticPowerTailWienerFamily.lean`: actual norm-two golden kernels
  for all positive power-tail exponents, actual payment iff the exponent exceeds
  one half, and membership of the whole family in the full paid-ideal closure.
  Unchecked; depends on power coefficients and the generic actual-closure bridge.
- `CriticalGoldenPaymentQuotients.lean`: actual paid subspace,
  its closure, closure-defect and unreduced quotient, canonical comparison map,
  and rank-at-most-continuum for both quotients. Scratch check and all three
  axiom audits and direct repository check passed; stage-3 card and umbrella
  import present. Obsolete scratch and logs removed. Reuses the existing
  actual Wiener coefficient cardinality bound; no Banach theorem is applied to
  a non-Hausdorff quotient.
- `/tmp/BiarithmeticCriticalGoldenContinuumDefect.lean`: finite coefficient
  relations in the actual quotient reduce to the power-tail independence
  theorem. The open unpaid exponent interval gives continuum many independent
  classes already in the closure defect; ambient coefficient cardinality gives
  equality for both actual quotients. Unchecked, with all preceding power-tail,
  closure, and quotient leaves as dependencies. The intrinsic-source claim
  remains separate even after this ordinary-floor draft is verified.
- `/tmp/BiarithmeticCriticalCoefficientDomain.lean`: actual complex `ell1`
  partial-sum submodule, exact closure as the augmentation kernel, attained
  distance to that kernel, and continuous annihilator classification. Reuses
  the corpus augmentation functional. Five audits drafted; first check pending.
- `/tmp/BiarithmeticCriticalReducedCokernel.lean`: exact quotient norm, linear
  isometry with `C`, and reduced dimension one for the preceding domain.
  Four audits drafted; first check pending.
- `/tmp/BiarithmeticCriticalCoefficientNonclosed.lean`: the explicit unpaid
  norm-two boundary vector in actual complex `ell1`, its zero evaluation,
  finite-core approximation, and nonclosedness of the coefficient payment
  submodule. Four audits drafted; unchecked. Reuses the checked real
  inverse-square-root-tail witness rather than a new asymptotic example.
- `/tmp/BiarithmeticCriticalCoefficientWienerRealization.lean`: actual complex
  coefficient linear isometry, summable inverse coordinates, exact prime-five
  range, and actual paid-domain identification. Six audits drafted; unchecked.
- `NormalizedCubicTrace.lean`: exact integral trace
  classification for fixed-determinant cubic amplification at every prime,
  with the four nonzero small-prime survivors and forced square-root trace
  bound. First scratch check found a missing algebra tactic and the unloaded
  prime-number normalization extension. The divisibility equation is now an
  explicit ring calculation, and compositeness of four follows directly from
  its divisor two. Revised scratch check, all five audits, and direct repository
  check passed. Stage-3 card and umbrella import present.
- `GoldenNormalizedCube.lean`: exact actual golden root
  product and trace after normalized cubing, negative first two transformed
  counts, and comparison with the original source's nonnegative counts.
  Scratch check, all four audits, and direct repository check passed; stage-3
  card and umbrella import present. Fixed determinant is not asserted to be analytic conductor.
- `NormalizedCubicRootLaw.lean`: field-valued determinant,
  trace, and normalization identities; real and complex reciprocal-root
  point-count bridges to the integral classification, and actual square-root
  root norms for every surviving pair. Scratch check and all eight audits passed.
  Direct repository check passed; stage-3 card and umbrella import present.
  The complete specified normalized-cube parent moved to stage 3, with the
  general bounded-conductor question still open.
- `GoldenSourceAdmission.lean`: positive tower threshold and actual golden admission
  phase passed direct check and five audits. Stage-3 card present; obsolete scratch removed.
- `IntrinsicGoldenSeries.lean`: exact intrinsic counting-pole cancellation
  using the actual source mean, cumulative-count partial fractions and coefficients, and
  both damping endpoints. Direct repository check and all six audits passed.
  Stage-3 card and umbrella import present; obsolete scratch removed.
- `GeometricPoleExtraction.lean`: exact primary-pole
  polynomial division, quadratic remainder bound for cubic numerators, and
  absolute summability retaining the double pole at one. Direct source check
  and all four audits passed; stage-3 card and umbrella import are present.
- `/tmp/BiarithmeticIntrinsicGoldenRemainder.lean`: actual intrinsic residue,
  strict negative sign on the positive-damping escape interval, quadratic
  numerator, exact coefficient decomposition, and critically weighted absolute
  summability. Eight audits drafted; first check pending. Neither the intrinsic
  tangent classification nor its payment criterion is yet proved.
- `/tmp/BiarithmeticFiveShellPronicEnergy.lean`: exact signed shell pairing,
  complete-prefix weight, and equivalence of finite shell square energy with
  all-cutoff pronic bounds. Four audits drafted; unchecked.
- `/tmp/BiarithmeticFiveShellShifts.lean`: exact norm-lattice floor shifts,
  weighted energy scaling, finite geometric boundary defect, and the precise
  geometric shell convergence radius. Five audits drafted; unchecked.
- `/tmp/BiarithmeticGeometricShellTangents.lean`: full-horizon geometric
  shell escape, paid finite boundaries, exact norm-lattice Gram limit, and
  rank-one finite-packet identity. Four audits drafted; unchecked.
- `/tmp/BiarithmeticIntrinsicGoldenTangents.lean`: actual intrinsic source
  decomposition on integer shells, finite remainder energy, full-horizon
  escape, and the actual norm-lattice Gram limit. Five audits drafted;
  unchecked, including its pending analytic and shell dependencies.
- `GeometricShellHilbert.lean`: the canonical geometric
  kernel completion is isometric to the complex line, with exact shift
  eigenvalues and composition. Reuses corpus Gram completion and total-feature
  unitary equivalence. Direct source check and all six audits passed;
  stage-3 card and umbrella import are present.
- `/tmp/BiarithmeticIntrinsicGoldenTangentModule.lean`: actual-source
  limit comparison, canonical completed-module isometry, complex dimension one,
  and exact norm-lattice shift eigenvalues. Four audits drafted; unchecked.
- `/tmp/BiarithmeticIntrinsicPointKernelEnergy.lean`: exact centered point
  response of the actual intrinsic count, uniform affine tail, and total
  shell-energy bound `6*5^(-r)`. First check failed in the geometric majorants:
  a power rewrite targeted the square instead of the geometric factor, and
  induction retained an unrelated bound. Targeted rewrites, a clean induction
  context, and removal of two redundant tactics repair those failures; recheck
  and all four clean audits remain required. Infinite
  Wiener synthesis and the intrinsic convolution/payment bridge remain.
- `/tmp/BiarithmeticIntrinsicWienerSynthesis.lean`: actual intrinsic point
  responses in the completed shell space, exact norm-square identification,
  critical inverse-square-root point bound, and a bounded linear extension
  from the actual Wiener algebra. Reuses AOT `sequenceExtension`; five audits
  drafted, unchecked. Coordinate identification with the actual infinite
  centered convolution remains a separate required bridge.
- `/tmp/BiarithmeticIntrinsicKernelPayment.lean`: the actual norm-lattice
  mean as a continuous coefficient functional, exact infinite synthesis
  coordinates, and the intrinsic critical-kernel energy bound `6*||k||_W^2`.
  Equality on actual Wiener point masses supplies the coordinate comparison.
  Five audits drafted; unchecked. Convolution with an arbitrary mean-summable
  intrinsic source and the final repairing-domain criterion still remain.
- `PronicDilationOperators.lean`: exact completed pronic dilation
  norms, coordinate formula, multiplicative composition, and contractive Wiener
  representation, using the existing
  `HTGeometry.PNatBlock` library and the public pronic fibre-mass identity.
  Revised scratch passed all six audits after explicit square-root nonnegativity
  and the elementary quotient-order bound replaced two failed rewrites.
  Direct source check passed; stage-3 card and umbrella import present. The reuse and specialization
  proof are recorded on the payment-graph card.
- `PronicWienerCoordinates.lean`: continuous unnormalized row
  coordinates, exact floor-dilation intertwining, and equality of the integrated
  Wiener action with every finite cofactor coordinate. Scratch check, both
  audits, and direct repository check passed. Stage-3 card and umbrella import
  present.
  Operator-series evaluation reuses Mathlib's
  `ContinuousLinearMap.apply` and `HasSum.mapL`, source-inspected through the
  corpus's operator-series proofs.
- `PronicFiniteExtension.lean`: reuses the corpus's exact `lp`
  coordinate isometry, embeds arbitrary finite source horizons, and derives the
  full complex formal cofactor composition law from the completed representation.
  Scratch check, all four audits, and direct repository check passed; stage-3
  card and umbrella import are present. The finite-extension proof is recorded on the payment-graph card;
  it imposes no growth premise on the original arithmetic row.
- `/tmp/BiarithmeticPronicGraphAction.lean`: invariant source graph under the
  actual Wiener product, exact input/output action, unit and composition,
  and the contractive bound for its inherited complete maximum norm.
  Injectivity of the graph input map gives the bounded complex-linear action
  and its contractive unital Wiener representation. Unchecked; depends on the
  pronic finite-extension draft.
- `CofactorGraphClosedness.lean`: ambient Wiener closedness
  iff a uniform output-energy norm bound on the complete graph. Uses the
  source-inspected Banach injective closed-range theorem, not the corpus's
  Hilbert-only version. First check found an unloaded nonnegative-real notation;
  the explicit `NNReal` carrier now replaces it. Revised scratch check and both
  audits and direct repository check passed. Stage-3 card and umbrella import
  are present.
- `GeometricFutureTail.lean`: joint absolute summability of
  the backward geometric tail, its resolvent recurrence, and explicit `b/(1-b)` coefficient-norm
  bound, for the strict one-prime Fredholm phase. First check found an implicit
  pair-projection arithmetic goal, the missing complex analytic structures,
  and a no-op rewrite in the tail bound. Explicit projection types,
  `Complex.Basic`, and a typed tail identity now address those failures;
  the next check still exposed ambiguous pair-projection inference. Destructured
  pairs and explicit function arguments to `Summable.comp_injective` now remove
  that inference work. Revised scratch check, all four audits, and direct
  repository check passed. Stage-3 card and umbrella import present.
  The product injection and nonnegative-series proof are recorded
  on that in-progress card.
- `/tmp/BiarithmeticGeometricCausalDivision.lean`: the strict expanding complex
  response has finite square energy iff its reciprocal evaluation vanishes;
  exact negative-future-tail formula and explicit absolute-sum bound. First
  check found one redundant tactic after field normalization; removed, with
  recheck pending. Its future-tail dependency is checked and built. This
  addresses the sequence domain, with
  transfer to the actual one-prime payment complex still separate.
- `/tmp/BiarithmeticStrictPrimePayment.lean`: exact normalization of the actual
  complex tower criterion as a geometric causal-response domain, then the
  strict evaluation-kernel classification for the actual tower and golden
  source. Unchecked; depends on complex lifting and geometric division.
  This source transfer does not yet bundle the domain as a Fredholm complex.
- `/tmp/BiarithmeticSubcriticalCausalBound.lean`: full complex causal
  response summability and the quantitative absolute-sum bound `||g||_1/(1-q)`
  for `0<=q<1`, reusing the checked finite geometric mass identity.
  Four audits drafted; unchecked. This supplies the subcritical analytic
  domain estimate required by the Fredholm construction.
- `/tmp/BiarithmeticGeometricCoefficientDomain.lean`: the complex causal
  square-energy submodule, its subcritical and critical specializations,
  norm-one surjective reciprocal evaluation, and the strict evaluation-kernel
  identity. Six audits drafted; unchecked. The corpus's general
  `LinearPMap.IsFredholm` and hyperplane-index theorem are the intended index
  interfaces; the Hilbert-only bounded Fredholm interface does not fit `ell1`.
- `/tmp/BiarithmeticGeometricCoefficientFredholm.lean`: the actual
  coefficient-domain partial inclusion, zero kernel, subcritical index zero,
  strict index minus one, critical nonclosed-range obstruction, and the exact
  nonnegative Fredholm parameter locus. Seven audits drafted; unchecked.
  Uses the existing general partial-map Fredholm theory. Complete graph-norm
  packaging and the actual-source inclusion comparison remain separate.
- `/tmp/BiarithmeticGeometricCoefficientGraph.lean`: finite causal
  coefficient functionals, the closed complete response graph, its bounded
  injective input, exact domain image, and unique output. Five audits drafted;
  unchecked. The norm is the product maximum. Quantitative graph/input norm
  comparisons and ordinary-source graph calibration remain obligations.
- `/tmp/BiarithmeticGeometricGraphNormBounds.lean`: explicit complete
  response bounds, coefficient contraction, and the subcritical and strict
  two-sided graph/input norm comparisons. Reuses the inspected finite-sum
  `ell1`-to-`ell2` proof mechanism and the drafted causal estimates.
  Five audits drafted; unchecked. Actual-source graph calibration remains.

The exact source-to-digit recurrence and actual golden source reduction both have stage-3
cards. The admission threshold also has a stage-3 card, including its unpaid critical endpoint.

The corpus's `HTGeometry/L1PeriodizationFourier.lean` already contains
`fourierCoeffOn_l1PeriodizationAtScale` for every integrable complex seed. Together with
`RHTower.integral_Ioi_zero_fract_cpow`, it supplies the full-strip circle coefficient law.
The formalized card is `../3-formalized/biarithmetic-digital-circle-fourier.md`.
`DigitalCircleFourier.lean` passed its direct check and all three transitive
axiom audits. The critical-line seed alone is already in
`RHTower/ZetaCriticalLineNotSquareIntegrable.lean`; the new draft extends the seed to the
whole open strip needed by the golden family.


### Quantitative digital profile errors

The covariance-error card now records a direct annular proof plan: fixed
annulus refinement error `O(a^(-M))` becomes unnormalized block error
`O((a/5)^M)` after exact source scaling, summable for every `1<a<5`.
This treats strict and critical asymptotics by the same finite-block
identity and even gives a cofactor-uniform additive bound. It does not
justify unweighted summation against infinite critical Wiener kernels.
Compact profile bounds, exact scaled block embedding, annular integration,
and the final covariance comparison all remain Lean obligations.
`/tmp/BiarithmeticDigitProfileCompactBounds.lean` drafts nonnegativity,
the compact bound, positive annular lower bound, cofactor-uniform product
error, and the scaled pointwise error with ratio `a/5`. Five audits are
drafted; this file remains unchecked.
`/tmp/BiarithmeticDigitProfileAnnularIntegrals.lean` drafts measurable
profile limits, integrability on every partial fundamental annulus,
the positive diagonal bound `4/25`, and the integrated error with ratio
`a/5`. Four audits drafted; unchecked.
`/tmp/BiarithmeticFinitePronicIntervalEmbedding.lean` drafts exact finite
prefix and block-difference interval integrals, reusing the corpus's
frozen-cell integrability and pronic cell formula. Three audits drafted;
unchecked. The actual scaled digit specialization remains an obligation.
`/tmp/BiarithmeticIntrinsicCenteredConvolution.lean` drafts the actual
inverse-norm centered convolution identity, paid kernel mean correction,
and exact comparison with the golden receiver series. Seven audits
drafted; unchecked. Full intrinsic repairing-domain classification remains.
`/tmp/BiarithmeticDigitAnnularStepComparison.lean` drafts the exact
floor-cofactor grid identity and scaled partial-annulus comparison with
the actual finite pronic covariance block. Two audits drafted; unchecked.
`/tmp/BiarithmeticDigitCovarianceBoundedError.lean` drafts exact full-block
telescoping and the uniform bounded covariance error for every `1<a<5`,
including empty final partial blocks. Three audits drafted; unchecked.

`/tmp/BiarithmeticPaidGramStability.lean` drafts own-energy normalization
and all-subsequence invariance under paid perturbations, reusing ADR's
finite pairing bound. First check found norm-wrapper conversion, scalar
function reduction, a unit-cofactor rewrite, and an untargeted absolute-value
rewrite. Explicit conversions and targeted simplification repair those errors;
recheck and eight clean audits remain required. Actual golden specialization
remains a separate obligation on the paid-perturbations card.
`/tmp/BiarithmeticGoldenGramReduction.lean` drafts that actual-source
specialization with escape derived from the checked admission threshold.
Four audits drafted; unchecked.

The in-progress card `biarithmetic-digital-profile-bounded-covariance-error.md` proposes that
geometric digit-grid refinements converge uniformly, with an explicit geometric tail.
Combining that tail with the power envelope and the exact pronic step embedding improves
strict-regime covariance asymptotics to a bounded absolute error. Critical block errors are
summable, giving logarithmic covariance growth with bounded remainder. For positive golden
damping, both mixed-root covariances are absolutely summable because `a*b/5=t^2<1`.
These stronger statements remain unproved; their Lean proofs and source-module transfer
remain in progress. They do not discharge the actual Möbius-source classification gate.

The exact annular identity now gives a further dependency-closed paper boundary
law in `../1-in-progress/biarithmetic-critical-phase-collapse.md`: every strict
phase kernel converges to the unique critical table as `a` decreases to
`sqrt(5)`, uniformly in phase. The explicit phase variation is at most
`(a^2/5-1)/sqrt(jk)`. Dominated double-series convergence extends this to
every two fixed critical Wiener kernels. Lean verification remains pending;
this does not imply continuity or closedness of the actual payment domains.


### Further positive structures exposed by the golden boundary

`../3-formalized/biarithmetic-signed-tower-admission.md` extends the tower
admission radius to every real parameter with `|a|<5`: payment holds exactly
for `|a|<sqrt(5)`. Both critical signs escape. The exact signed digit norm criterion and actual receiver identity prove
this classification. Direct Lean check and all three axiom audits passed.

`../1-in-progress/biarithmetic-payment-graph-norm.md` develops a canonical complete graph
norm on the actual paid ideal, even when its Wiener-norm image is not closed. Ambient
closedness is exactly a uniform total-energy bound on all paid kernels. At the critical
one-prime boundary, corrected finite kernels form a core in the graph norm.

`../1-in-progress/biarithmetic-intrinsic-golden-module.md` makes the other ambient action
explicit: exact cancellation gives intrinsic centered series
`[t/(5-5t+t^2)] P(u)(1-t^2*u)/[(1-u)^2(1-au)(1-bu)]`.
A nonzero geometric row plus a paid remainder yields the unique rank-one norm-lattice
kernel and its weighted partial-sum payment domain. These remain obligations with Lean
construction and source comparisons still pending; they do not replace the ordinary-floor
infinite-dimensional module classification.

The in-progress card `biarithmetic-golden-divisor-positivity-phase.md`
proposes a classification of a local source constraint of the ordinary-floor lift. Its divisor
responses lie in `[0,1]` exactly for `0<=t<=1/5`; their exact infimum below
the primary pole is `(1-t)(1-5t)/[(1-alpha*t)(1-beta*t)]`, and at or beyond
that pole they tend to negative infinity along powers of five. Thus every
escaping ordinary golden lift fails actual Möbius divisor-response positivity,
whereas every positivity-compatible lift is paid. This remains a formalization obligation
and does not refute intrinsic Beurling positivity.

The repaired `CriticalGoldenPaymentNonclosed` scratch check and all six
transitive audits passed. Direct production check also passed; its umbrella
import and stage-3 card are present.

`DigitRefinement` passed its revised scratch check and all nine transitive
axiom audits and its direct repository check. Stage-3 card and umbrella import
are present.
`PowerTailCoefficients` passed its repaired scratch check, all five transitive
audits, and its direct repository check. `PowerTailIndependence` also passed
its five audits and direct source check. Both stage-3 cards and imports are
present; the actual lifted quotient dimension remains pending.

`DigitalCircleFourier` passed its direct repository check and all three
transitive audits. The umbrella import and stage-3 card are present.
The source-profile/cyclic-module comparison is not part of this leaf.

`FinitePronicStepEmbedding` passed its direct source check and both
transitive audits. The umbrella import and stage-3 card are present.

`GoldenDivisorResponse` passed its direct repository check and all five
transitive audits. The umbrella import and stage-3 card are present.
The full positivity-parameter classification remains in its dependent draft.

Pending source check: `/tmp/BiarithmeticDigitParameterContinuity.lean` contains finite-row parameter continuity, a common geometric refinement bound on every parameter half-line above one, and continuity of the actual digit profile at every spatial point. No declaration in this draft is yet certified.

Pending source check: `/tmp/BiarithmeticDigitAnnularContinuity.lean` applies dominated convergence to actual annular digit products and their normalized full-annulus ratio. It depends on the unchecked annular integrability and parameter-continuity drafts.

Pending source check: `/tmp/BiarithmeticDigitCovarianceMainTerms.lean` derives the balanced expanding covariance formula and a horizon-uniform linear-shell error at the exact critical weight `sqrt(5)`. Its bounded-error dependency chain remains unchecked.

Pending source check: `/tmp/BiarithmeticDigitCriticalGramLimit.lean` uses
`Nat.log 5 (N+1)` to obtain the actual full-horizon critical covariance per
shell, its diagonal-normalized ratio, and full diagonal energy escape.
Exact positive-cell reindexing also transfers this to `normalizedSourceGram`.
Seven audits are drafted; its bounded-error dependencies remain unchecked.

Pending source check: `/tmp/BiarithmeticDigitAnnularPhaseVariation.lean`
gives the exact balanced annular quotient, its phase-variation estimate,
and uniform critical collapse. Four audits are drafted; the strict actual
source-limit comparison and full fixed-kernel covariance extension remain.

Pending source check: `/tmp/BiarithmeticChirpPhaseRigidity.lean` contains the three-rotation rigidity argument and the exact nondegenerate prime-two angle. It does not yet identify these three samples with actual source tangents; the discrete asymptotics, tangent realization, and boundary-loss representation remain outstanding.

Pending source check: `/tmp/BiarithmeticChirpPhaseGroup.lean` constructs the
compact closure group of the actual logarithmic phase flow and derives its
cofactor multiplicativity by closedness. Integer-horizon realization is pending.

Pending source check: `/tmp/BiarithmeticChirpCauchyKernel.lean` drafts strict
finite-packet positivity of the explicit chirp kernel by an invertible
diagonal congruence of the corpus's Cauchy Gram. Four audits are pending.
This does not establish the discrete source asymptotic or tangent realization.

Pending source check: `/tmp/BiarithmeticChirpSourceRegularity.lean` drafts
the actual scalar chirp row, its derivative and derivative decay, and an
explicit uniform integer-increment bound. Four audits remain unchecked.

Pending source check: `/tmp/BiarithmeticChirpPacketIntegral.lean` drafts
the exact weighted half-line realization of the explicit chirp kernel,
its integrability, and strictly positive energy for nonzero finite packets.
Three audits are pending after the Cauchy-kernel dependency.

Pending source check: `/tmp/BiarithmeticChirpHaarAverage.lean` drafts the
actual phase group's normalized Haar measure, nontriviality of distinct
coordinate characters, and the exact diagonal kernel average. Five audits
are pending. The source-tangent exclusion remains a separate obligation.

Pending source check: `/tmp/BiarithmeticChirpFloorError.lean` drafts the
actual chirp's uniform floor error and absolute summability of each fixed
pronic cofactor covariance correction. It uses the power `n^(β-2)` and
depends on the regularity draft. Five audits are pending.

Pending source check: `/tmp/BiarithmeticComplexShellShift.lean` constructs complex normalized shell shifts with exact isometry and semigroup laws. This is the missing bounded-operator input for the existing intrinsic infinite-kernel convolution proof plan.

Pending source check: `/tmp/BiarithmeticIntrinsicShellConvolution.lean` constructs bounded convolution by every actual critical Wiener kernel, identifies its finite Cauchy coordinates, and proves weighted shell-energy stability with operator bound `||k||`. This addresses the infinite-kernel action required by the intrinsic centered-convolution proof plan.

Pending source check: `/tmp/BiarithmeticIntrinsicPaymentDomain.lean` identifies the actual centered filtered receiver, pays its mean correction and geometric remainder, and reduces full intrinsic payment to weighted square summability of its geometric causal response. Every analytic input has a queued Lean proof obligation; no additional source hypothesis is used. The draft also identifies intrinsic payment with actual ordinary golden payment on the one-prime algebra throughout positive-damping escape.
